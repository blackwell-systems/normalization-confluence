// Command gogen turns Rocq's MiniML JSON extraction into Go.
//
// Usage: gogen [-pkg name] [-o out.go] [-allow-unary f,g] extraction.json
//
// It accepts the MiniML fragment the verified checkers extract to, and fails on
// anything else rather than guess:
//   - inductives (possibly parameterized) become generic Go structs; a value is
//     a pointer and its constructor a tag. The inductives ExtrGo.v maps become
//     Go bool and int64 (prims.go);
//   - top-level terms and fixpoints become Go functions, generic over the type
//     variables of their declared MiniML type. Local lambdas become curried Go
//     closures, and so do partial applications of globals;
//   - Hindley-Milner inference (declared types for globals, monomorphic locals)
//     gives every Go type the output needs, and every generic use is
//     instantiated explicitly;
//   - a match becomes a switch. A self tail call becomes a loop, with a fresh
//     copy of the parameters per iteration so that closures never see a later
//     iteration's values. prim_andb is a short-circuit &&, and its right operand
//     is in tail position, as OCaml's (&&) is.
//
// The output is gofmt'd and depends only on the input, so regenerating from the
// same extraction gives the same bytes.
package main

import (
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"go/format"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
)

// genError is a refusal: input gogen does not accept, or output it cannot
// produce. fail panics with one; Generate turns it into an error.
type genError string

func (e genError) Error() string { return "gogen: " + string(e) }

func fail(f string, a ...any) { panic(genError(fmt.Sprintf(f, a...))) }

// ===== types and inference =====

// Ty is a MiniML type during inference.
type Ty struct {
	K    byte // 'm' meta variable, 'p' rigid parameter, 'c' type constructor, 'a' arrow
	Name string
	Args []*Ty // 'c': type arguments; 'a': [left, right]
	ref  *Ty   // 'm': what it is bound to
}

func meta() *Ty { return &Ty{K: 'm'} }

func arrow(l, r *Ty) *Ty { return &Ty{K: 'a', Args: []*Ty{l, r}} }

func (t *Ty) res() *Ty {
	for t.K == 'm' && t.ref != nil {
		t = t.ref
	}
	return t
}

func occurs(m, t *Ty) bool {
	t = t.res()
	if t == m {
		return true
	}
	for _, a := range t.Args {
		if occurs(m, a) {
			return true
		}
	}
	return false
}

func unify(a, b *Ty, where string) {
	a, b = a.res(), b.res()
	if a == b {
		return
	}
	if a.K == 'm' {
		if occurs(a, b) {
			fail("%s: occurs check", where)
		}
		a.ref = b
		return
	}
	if b.K == 'm' {
		unify(b, a, where)
		return
	}
	if a.K != b.K || a.Name != b.Name || len(a.Args) != len(b.Args) {
		fail("%s: cannot unify %s with %s", where, show(a), show(b))
	}
	for i := range a.Args {
		unify(a.Args[i], b.Args[i], where)
	}
}

func show(t *Ty) string {
	t = t.res()
	switch t.K {
	case 'm':
		return "?"
	case 'p':
		return t.Name
	case 'a':
		return "(" + show(t.Args[0]) + " -> " + show(t.Args[1]) + ")"
	}
	s := t.Name
	for _, a := range t.Args {
		s += " " + show(a)
	}
	return "(" + s + ")"
}

// ===== program model =====

type Ind struct {
	Name   string
	Params []string
	Ctors  []*Ctor
}

type CtorRef struct {
	Ind *Ind
	Idx int
}

type Alias struct {
	Params []string
	Value  *Node
}

type Global struct {
	Name  string
	Type  *Node // declared MiniML type
	NVars int   // its type variables are 1..NVars
	Value *Node
	Arity int
	Prim  bool
}

type Gen struct {
	inds    map[string]*Ind
	ctors   map[string]CtorRef
	aliases map[string]*Alias
	globals map[string]*Global
	order   []*Global
	types   map[*Node]*Ty   // inferred type of each expression node
	insts   map[*Node][]*Ty // instantiation of each global or constructor use

	out    *bytes.Buffer
	tmp    int
	selfFn *Global  // function being emitted, for tail calls
	params []string // its loop-carried parameter names
}

// tyOf converts a MiniML type. vars maps type:var names and type:varidx
// indices (as strings) to types.
func (g *Gen) tyOf(n *Node, vars map[string]*Ty) *Ty {
	switch n.What {
	case "type:arrow":
		return arrow(g.tyOf(n.Left, vars), g.tyOf(n.Right, vars))
	case "type:glob":
		var args []*Ty
		for _, a := range n.Args {
			args = append(args, g.tyOf(a, vars))
		}
		if al, ok := g.aliases[n.Name]; ok {
			if len(args) != len(al.Params) {
				fail("type %s applied to %d arguments, wants %d", n.Name, len(args), len(al.Params))
			}
			sub := map[string]*Ty{}
			for i, p := range al.Params {
				sub[p] = args[i]
			}
			return g.tyOf(al.Value, sub)
		}
		return &Ty{K: 'c', Name: n.Name, Args: args}
	case "type:var", "type:varidx":
		v, ok := vars[n.Name]
		if !ok {
			fail("unbound type variable %s", n.Name)
		}
		return v
	}
	fail("unsupported type node %s", n.What)
	return nil
}

func maxVaridx(n *Node) int {
	if n == nil {
		return 0
	}
	m := 0
	if n.What == "type:varidx" {
		fmt.Sscan(n.Name, &m)
	}
	for _, c := range append([]*Node{n.Left, n.Right}, n.Args...) {
		if k := maxVaridx(c); k > m {
			m = k
		}
	}
	return m
}

// unwrap drops lambdas that bind nothing (extraction emits them for eta-reduced
// definitions such as nfv := tget).
func unwrap(n *Node) *Node {
	if n == nil {
		return nil
	}
	for n.What == "expr:lambda" && len(n.Argnames) == 0 {
		n = n.Body
	}
	n.Body, n.Expr, n.Func, n.Nameval = unwrap(n.Body), unwrap(n.Expr), unwrap(n.Func), unwrap(n.Nameval)
	for _, c := range n.Cases {
		unwrap(c)
	}
	if n.What == "expr:apply" || n.What == "expr:constructor" {
		for i := range n.Args {
			n.Args[i] = unwrap(n.Args[i])
		}
	}
	return n
}

func (g *Gen) load(root *Node) {
	if root.What != "module" {
		fail("expected a module, got %s", root.What)
	}
	if root.NeedMagic || root.NeedDummy {
		fail("the extraction needs Obj.magic or a dummy (need_magic=%v, need_dummy=%v): not typable in Go", root.NeedMagic, root.NeedDummy)
	}
	seenMapped := map[string]bool{}
	for _, d := range root.Decls {
		switch d.What {
		case "decl:ind":
			if mt, ok := mappedTypes[d.Name]; ok {
				// sumbool and bool both map to go_bool: one declaration each.
				if len(d.Argnames) != 0 || len(d.Ctors) != len(mt.ctors) {
					fail("mapped type %s has an unexpected shape", d.Name)
				}
				for _, c := range d.Ctors {
					mc, ok := mt.ctors[c.Name]
					if !ok || mc.arity != len(c.Argtypes) {
						fail("mapped type %s: unexpected constructor %s", d.Name, c.Name)
					}
				}
				seenMapped[d.Name] = true
				continue
			}
			if strings.HasPrefix(d.Name, "go_") {
				fail("unknown mapped type %s", d.Name)
			}
			if _, dup := g.inds[d.Name]; dup {
				fail("duplicate inductive %s", d.Name)
			}
			ind := &Ind{Name: d.Name, Params: d.Argnames, Ctors: d.Ctors}
			g.inds[d.Name] = ind
			for i, c := range d.Ctors {
				if _, dup := g.ctors[c.Name]; dup {
					fail("duplicate constructor %s", c.Name)
				}
				g.ctors[c.Name] = CtorRef{ind, i}
			}
		case "decl:type":
			if _, dup := g.aliases[d.Name]; dup {
				fail("duplicate type %s", d.Name)
			}
			g.aliases[d.Name] = &Alias{Params: d.Argnames, Value: d.Value}
		case "decl:term":
			g.addGlobal(d.Name, d.Type, d.Value)
		case "decl:fixgroup":
			for _, f := range d.Fixlist {
				g.addGlobal(f.Name, f.Type, f.Value)
			}
		default:
			fail("unsupported declaration %s", d.What)
		}
	}
	for name, mt := range mappedTypes {
		for cname := range mt.ctors {
			if _, clash := g.ctors[cname]; clash {
				fail("constructor %s clashes with mapped type %s", cname, name)
			}
		}
	}
	ci, ok := g.inds["comparison"]
	if !ok {
		ci = &Ind{Name: "comparison", Ctors: []*Ctor{{Name: "Eq"}, {Name: "Lt"}, {Name: "Gt"}}}
		g.inds["comparison"] = ci
		for i, c := range ci.Ctors {
			g.ctors[c.Name] = CtorRef{ci, i}
		}
	}
	if len(ci.Params) != 0 || len(ci.Ctors) != 3 || ci.Ctors[0].Name != "Eq" || ci.Ctors[1].Name != "Lt" || ci.Ctors[2].Name != "Gt" {
		fail("comparison is not Eq | Lt | Gt")
	}
}

func (g *Gen) addGlobal(name string, ty, val *Node) {
	val = unwrap(val)
	if _, dup := g.globals[name]; dup {
		fail("duplicate global %s (JSON extraction drops module qualifiers)", name)
	}
	gl := &Global{Name: name, Type: ty, Value: val, NVars: maxVaridx(ty)}
	if p, ok := prims[name]; ok {
		gl.Prim, gl.Arity = true, p.arity
	} else if strings.HasPrefix(name, "prim_") {
		fail("unknown prim %s", name)
	} else if val.What == "expr:lambda" {
		gl.Arity = len(val.Argnames)
	}
	g.globals[name] = gl
	g.order = append(g.order, gl)
}

// scheme instantiates a global's declared type with fresh metas.
func (g *Gen) scheme(gl *Global) (*Ty, []*Ty) {
	vars := map[string]*Ty{}
	var inst []*Ty
	for i := 1; i <= gl.NVars; i++ {
		m := meta()
		vars[fmt.Sprint(i)] = m
		inst = append(inst, m)
	}
	return g.tyOf(gl.Type, vars), inst
}

// mappedOf returns the mapped type a constructor name belongs to, if any.
func mappedOf(ctor string) (string, *mappedCtor) {
	for name, mt := range mappedTypes {
		if mc, ok := mt.ctors[ctor]; ok {
			return name, mc
		}
	}
	return "", nil
}

// ctorType returns a constructor's argument types and result type, with fresh
// metas for the inductive's parameters (also returned).
func (g *Gen) ctorType(name string) ([]*Ty, *Ty, []*Ty) {
	if tn, mc := mappedOf(name); mc != nil {
		t := &Ty{K: 'c', Name: tn}
		// A mapped constructor's argument is a nat (nat_succ) or a positive
		// (pos_xI, pos_xO, n_pos, z_pos, z_neg).
		argTy := "go_pos"
		if tn == "go_nat" {
			argTy = "go_nat"
		}
		var args []*Ty
		for i := 0; i < mc.arity; i++ {
			args = append(args, &Ty{K: 'c', Name: argTy})
		}
		return args, t, nil
	}
	cr, ok := g.ctors[name]
	if !ok {
		fail("unknown constructor %s", name)
	}
	vars := map[string]*Ty{}
	res := &Ty{K: 'c', Name: cr.Ind.Name}
	var inst []*Ty
	for _, p := range cr.Ind.Params {
		m := meta()
		vars[p] = m
		inst = append(inst, m)
		res.Args = append(res.Args, m)
	}
	var args []*Ty
	for _, a := range cr.Ind.Ctors[cr.Idx].Argtypes {
		args = append(args, g.tyOf(a, vars))
	}
	return args, res, inst
}

type env struct {
	name string
	ty   *Ty
	goid string
	next *env
}

func (e *env) look(n string) *env {
	for ; e != nil; e = e.next {
		if e.name == n {
			return e
		}
	}
	return nil
}

func (g *Gen) infer(n *Node, e *env) *Ty {
	t := g.infer1(n, e)
	g.types[n] = t
	return t
}

func (g *Gen) infer1(n *Node, e *env) *Ty {
	switch n.What {
	case "expr:rel":
		b := e.look(n.Name)
		if b == nil {
			fail("unbound variable %s", n.Name)
		}
		return b.ty
	case "expr:global":
		gl, ok := g.globals[n.Name]
		if !ok {
			fail("unknown global %s", n.Name)
		}
		t, inst := g.scheme(gl)
		g.insts[n] = inst
		return t
	case "expr:constructor":
		args, res, inst := g.ctorType(n.Name)
		g.insts[n] = inst
		if len(n.Args) != len(args) {
			fail("constructor %s applied to %d arguments, wants %d", n.Name, len(n.Args), len(args))
		}
		for i, a := range n.Args {
			unify(g.infer(a, e), args[i], "constructor "+n.Name)
		}
		return res
	case "expr:apply":
		ft := g.infer(n.Func, e)
		for _, a := range n.Args {
			r := meta()
			unify(ft, arrow(g.infer(a, e), r), "application")
			ft = r
		}
		return ft
	case "expr:lambda":
		var ts []*Ty
		for _, a := range n.Argnames {
			m := meta()
			ts = append(ts, m)
			e = &env{name: a, ty: m, next: e}
		}
		r := g.infer(n.Body, e)
		for i := len(ts) - 1; i >= 0; i-- {
			r = arrow(ts[i], r)
		}
		return r
	case "expr:let":
		t := g.infer(n.Nameval, e)
		return g.infer(n.Body, &env{name: n.Name, ty: t, next: e})
	case "expr:case":
		st := g.infer(n.Expr, e)
		r := meta()
		for _, c := range n.Cases {
			ce := e
			switch c.Pat.What {
			case "pat:wild":
			case "pat:rel":
				ce = &env{name: c.Pat.Name, ty: st, next: ce}
			case "pat:constructor":
				args, res, _ := g.ctorType(c.Pat.Name)
				unify(st, res, "pattern "+c.Pat.Name)
				if len(c.Pat.Argnames) != len(args) {
					fail("pattern %s binds %d, wants %d", c.Pat.Name, len(c.Pat.Argnames), len(args))
				}
				for i, a := range c.Pat.Argnames {
					ce = &env{name: a, ty: args[i], next: ce}
				}
			default:
				fail("unsupported pattern %s", c.Pat.What)
			}
			unify(g.infer(c.Body, ce), r, "case branch")
		}
		return r
	case "expr:exception":
		return meta()
	}
	fail("unsupported expression %s", n.What)
	return nil
}

// unaryNames are the standard library's nat arithmetic functions, as JSON
// extraction prints them (without module qualifier, and with a numeric suffix
// when a name is taken). ExtrGo.v maps plus, minus and mult; the copies
// PeanoNat's Nat module re-exports (Nat.add, Nat.mul, Nat.pow, ...) are not
// mapped, as in ExtrOcamlNatInt, and extract to their unary definitions.
var unaryNames = regexp.MustCompile(`^(add|sub|mul|pow|div|modulo|pred|min|max|double|square)[0-9]*$`)

// refuseUnary refuses unmapped unary nat arithmetic: a global named like a
// standard nat operation whose type takes and returns only go_nat. Its cost in
// time and stack is linear in the numbers it gets (Nat.mul on 2^20 is about
// 2^20 nested calls), so a use of it is a performance bug in the extracted
// checker, unless allowed by name.
func (g *Gen) refuseUnary(allow []string) {
	allowed := map[string]bool{}
	for _, a := range allow {
		allowed[a] = true
	}
	var found []string
	for _, gl := range g.order {
		if gl.Prim || allowed[gl.Name] || !unaryNames.MatchString(gl.Name) || !natOnly(gl.Type) {
			continue
		}
		found = append(found, gl.Name)
	}
	if len(found) > 0 {
		sort.Strings(found)
		fail("unmapped unary nat arithmetic: %s (extracted as its Rocq definition, linear in time and stack; map it in ExtrGo.v, avoid it, or allow it with -allow-unary)", strings.Join(found, ", "))
	}
}

// natOnly reports whether a MiniML type is go_nat -> ... -> go_nat.
func natOnly(t *Node) bool {
	switch t.What {
	case "type:arrow":
		return natOnly(t.Left) && natOnly(t.Right)
	case "type:glob":
		return t.Name == "go_nat" && len(t.Args) == 0
	}
	return false
}

// ===== Go emission =====

func (g *Gen) goTy(t *Ty) string {
	t = t.res()
	switch t.K {
	case 'm':
		return "struct{}" // never constrained, so never inspected
	case 'p':
		return t.Name
	case 'a':
		return "func(" + g.goTy(t.Args[0]) + ") " + g.goTy(t.Args[1])
	}
	if mt, ok := mappedTypes[t.Name]; ok {
		return mt.goType
	}
	if _, ok := g.inds[t.Name]; !ok {
		fail("unknown type %s", t.Name)
	}
	return "*I_" + goIdent(t.Name) + g.tyArgs(t.Args)
}

func (g *Gen) tyArgs(ts []*Ty) string {
	if len(ts) == 0 {
		return ""
	}
	var s []string
	for _, t := range ts {
		s = append(s, g.goTy(t))
	}
	return "[" + strings.Join(s, ", ") + "]"
}

func goIdent(s string) string {
	var b strings.Builder
	for _, r := range s {
		switch {
		case r == '\'':
			b.WriteString("_p")
		case r == '_' || r >= 'a' && r <= 'z' || r >= 'A' && r <= 'Z' || r >= '0' && r <= '9':
			b.WriteRune(r)
		default:
			fmt.Fprintf(&b, "_%x", r)
		}
	}
	return b.String()
}

func (g *Gen) fresh(base string) string {
	g.tmp++
	return fmt.Sprintf("%s_%d", goIdent(base), g.tmp)
}

func (g *Gen) emitInds() {
	names := make([]string, 0, len(g.inds))
	for n := range g.inds {
		names = append(names, n)
	}
	sort.Strings(names)
	for _, n := range names {
		ind := g.inds[n]
		vars := map[string]*Ty{}
		var tp []string
		for _, p := range ind.Params {
			vars[p] = &Ty{K: 'p', Name: "P_" + goIdent(p)}
			tp = append(tp, "P_"+goIdent(p)+" any")
		}
		tparams := ""
		if len(tp) > 0 {
			tparams = "[" + strings.Join(tp, ", ") + "]"
		}
		fmt.Fprintf(g.out, "type I_%s%s struct {\n\ttag uint8\n", goIdent(n), tparams)
		for ci, c := range ind.Ctors {
			for ai, a := range c.Argtypes {
				fmt.Fprintf(g.out, "\tf%d_%d %s\n", ci, ai, g.goTy(g.tyOf(a, vars)))
			}
		}
		g.out.WriteString("}\n\n")
		// Shared values for the nullary constructors of non-parameterized types.
		if len(ind.Params) == 0 {
			for ci, c := range ind.Ctors {
				if len(c.Argtypes) == 0 {
					fmt.Fprintf(g.out, "var C_%s = &I_%s{tag: %d}\n", goIdent(c.Name), goIdent(n), ci)
				}
			}
			g.out.WriteString("\n")
		}
		// A constructor function per constructor, for front ends that build
		// inputs (they never depend on tags or field names).
		var targs []string
		for _, p := range ind.Params {
			targs = append(targs, "P_"+goIdent(p))
		}
		self := "*I_" + goIdent(n)
		if len(targs) > 0 {
			self += "[" + strings.Join(targs, ", ") + "]"
		}
		for ci, c := range ind.Ctors {
			var ps, fs []string
			fs = append(fs, fmt.Sprintf("tag: %d", ci))
			for ai, a := range c.Argtypes {
				ps = append(ps, fmt.Sprintf("a%d %s", ai, g.goTy(g.tyOf(a, vars))))
				fs = append(fs, fmt.Sprintf("f%d_%d: a%d", ci, ai, ai))
			}
			fmt.Fprintf(g.out, "// K_%s builds the constructor %s.\nfunc K_%s%s(%s) %s {\n\treturn &%s{%s}\n}\n\n",
				goIdent(c.Name), c.Name, goIdent(c.Name), tparams, strings.Join(ps, ", "), self, self[1:], strings.Join(fs, ", "))
		}
	}
}

// konst folds a tree of mapped number constructors to its value.
func konst(n *Node) (int64, bool) {
	if n.What != "expr:constructor" {
		return 0, false
	}
	_, mc := mappedOf(n.Name)
	if mc == nil || mc.konst == nil {
		return 0, false
	}
	var vs []int64
	for _, a := range n.Args {
		v, ok := konst(a)
		if !ok {
			return 0, false
		}
		vs = append(vs, v)
	}
	return mc.konst(vs)
}

// ---- expressions: emit statements into g.out, return a Go expression ----

func (g *Gen) expr(n *Node, e *env) string {
	switch n.What {
	case "expr:rel":
		return e.look(n.Name).goid
	case "expr:constructor":
		return g.ctorExpr(n, e)
	case "expr:global":
		return g.apply(n, nil, e)
	case "expr:apply":
		if n.Func.What == "expr:global" {
			return g.apply(n.Func, n.Args, e)
		}
		f := g.expr(n.Func, e)
		for _, a := range n.Args {
			f = f + "(" + g.expr(a, e) + ")"
		}
		return g.bind(f)
	case "expr:lambda":
		return g.lambda(n.Argnames, n.Body, g.types[n], e)
	case "expr:let":
		v := g.expr(n.Nameval, e)
		id := g.fresh(n.Name)
		fmt.Fprintf(g.out, "%s := %s\n_ = %s\n", id, v, id)
		return g.expr(n.Body, &env{name: n.Name, ty: g.types[n.Nameval], goid: id, next: e})
	case "expr:case":
		r := g.fresh("r")
		fmt.Fprintf(g.out, "var %s %s\n", r, g.goTy(g.types[n]))
		g.caseStmt(n, e, func(body *Node, be *env) {
			v := g.expr(body, be)
			fmt.Fprintf(g.out, "%s = %s\n", r, v)
		}, true)
		return r
	case "expr:exception":
		fmt.Fprintf(g.out, "panic(%q)\n", "gogen: extracted exception: "+n.Msg)
		return "*new(" + g.goTy(g.types[n]) + ")"
	}
	fail("unsupported expression %s", n.What)
	return ""
}

// bind evaluates a Go expression once into a temporary.
func (g *Gen) bind(v string) string {
	id := g.fresh("t")
	fmt.Fprintf(g.out, "%s := %s\n", id, v)
	return id
}

func (g *Gen) ctorExpr(n *Node, e *env) string {
	if v, ok := konst(n); ok {
		return fmt.Sprintf("int64(%d)", v)
	}
	if _, mc := mappedOf(n.Name); mc != nil {
		var as []string
		for _, a := range n.Args {
			as = append(as, g.expr(a, e))
		}
		s := mc.build(as)
		if len(as) == 0 {
			return s
		}
		return g.bind(s)
	}
	cr := g.ctors[n.Name]
	if len(n.Args) == 0 && len(cr.Ind.Params) == 0 {
		return "C_" + goIdent(n.Name)
	}
	fs := []string{fmt.Sprintf("tag: %d", cr.Idx)}
	for i, a := range n.Args {
		fs = append(fs, fmt.Sprintf("f%d_%d: %s", cr.Idx, i, g.expr(a, e)))
	}
	return g.bind(fmt.Sprintf("&I_%s%s{%s}", goIdent(cr.Ind.Name), g.tyArgs(g.insts[n]), strings.Join(fs, ", ")))
}

// apply emits a use of a global applied to args (possibly none, possibly more
// than its arity).
func (g *Gen) apply(f *Node, args []*Node, e *env) string {
	gl := g.globals[f.Name]
	if gl.Name == "prim_andb" && len(args) == 2 {
		r := g.fresh("b")
		fmt.Fprintf(g.out, "%s := %s\n", r, g.expr(args[0], e))
		fmt.Fprintf(g.out, "if %s {\n", r)
		fmt.Fprintf(g.out, "%s = %s\n", r, g.expr(args[1], e))
		g.out.WriteString("}\n")
		return r
	}
	var vs []string
	for _, a := range args {
		vs = append(vs, g.expr(a, e))
	}
	if len(vs) < gl.Arity {
		// Partial application: a curried closure over the remaining arguments.
		t := g.types[f].res()
		for range vs {
			t = t.Args[1].res()
		}
		var rest []string
		var restTy []*Ty
		for i := len(vs); i < gl.Arity; i++ {
			rest = append(rest, g.fresh("a"))
			restTy = append(restTy, t.Args[0])
			t = t.Args[1].res()
		}
		s := "return " + g.callGlobal(gl, f, append(append([]string{}, vs...), rest...))
		ret := t
		for i := len(rest) - 1; i >= 0; i-- {
			s = fmt.Sprintf("func(%s %s) %s {\n%s\n}", rest[i], g.goTy(restTy[i]), g.goTy(ret), s)
			ret = arrow(restTy[i], ret)
			if i > 0 {
				s = "return " + s
			}
		}
		return g.bind(s)
	}
	call := g.callGlobal(gl, f, vs[:gl.Arity])
	for _, v := range vs[gl.Arity:] {
		call += "(" + v + ")"
	}
	return g.bind(call)
}

func (g *Gen) callGlobal(gl *Global, f *Node, vs []string) string {
	if gl.Prim {
		if gl.Name == "prim_andb" {
			return "(" + vs[0] + " && " + vs[1] + ")"
		}
		return prims[gl.Name].fn + "(" + strings.Join(vs, ", ") + ")"
	}
	return "F_" + goIdent(gl.Name) + g.tyArgs(g.insts[f]) + "(" + strings.Join(vs, ", ") + ")"
}

func (g *Gen) lambda(argnames []string, body *Node, t *Ty, e *env) string {
	var ids []string
	var tys []*Ty
	tt := t.res()
	for _, a := range argnames {
		id := g.fresh(a)
		ids = append(ids, id)
		tys = append(tys, tt.Args[0])
		e = &env{name: a, ty: tt.Args[0], goid: id, next: e}
		tt = tt.Args[1].res()
	}
	saved, savedSelf := g.out, g.selfFn
	g.out = &bytes.Buffer{}
	g.selfFn = nil // no tail-call loops inside closures
	for _, id := range ids {
		fmt.Fprintf(g.out, "_ = %s\n", id)
	}
	g.tail(body, e)
	s := g.out.String()
	g.out, g.selfFn = saved, savedSelf
	ret := tt
	for i := len(ids) - 1; i >= 0; i-- {
		s = fmt.Sprintf("func(%s %s) %s {\n%s}", ids[i], g.goTy(tys[i]), g.goTy(ret), s)
		ret = arrow(tys[i], ret)
		if i > 0 {
			s = "return " + s + "\n"
		}
	}
	return g.bind(s)
}

// caseStmt emits a switch over n's scrutinee, calling branch for each case body
// in the environment its pattern extends. With mustMatch, a value no case
// matches panics (only possible for a mapped number outside its type).
func (g *Gen) caseStmt(n *Node, e *env, branch func(*Node, *env), mustMatch bool) {
	s := g.expr(n.Expr, e)
	st := g.types[n.Expr].res()
	hasWild := false
	if mt, ok := mappedTypes[st.Name]; ok && st.K == 'c' {
		g.out.WriteString("switch {\n")
		for _, c := range n.Cases {
			be := e
			if c.Pat.What == "pat:wild" || c.Pat.What == "pat:rel" {
				hasWild = true
				g.out.WriteString("default:\n")
				be = g.bindPatRel(c.Pat, s, st, be)
			} else {
				mc := mt.ctors[c.Pat.Name]
				args, _, _ := g.ctorType(c.Pat.Name)
				fmt.Fprintf(g.out, "case %s:\n", mc.cond(s))
				for i, p := range mc.proj(s) {
					a := c.Pat.Argnames[i]
					id := g.fresh(a)
					fmt.Fprintf(g.out, "%s := %s\n_ = %s\n", id, p, id)
					be = &env{name: a, ty: args[i], goid: id, next: be}
				}
			}
			branch(c.Body, be)
		}
	} else {
		fmt.Fprintf(g.out, "switch %s.tag {\n", s)
		for _, c := range n.Cases {
			be := e
			if c.Pat.What == "pat:wild" || c.Pat.What == "pat:rel" {
				hasWild = true
				g.out.WriteString("default:\n")
				be = g.bindPatRel(c.Pat, s, st, be)
			} else {
				cr := g.ctors[c.Pat.Name]
				args, res, _ := g.ctorType(c.Pat.Name)
				unify(st, res, "pattern")
				fmt.Fprintf(g.out, "case %d:\n", cr.Idx)
				for i, a := range c.Pat.Argnames {
					if a == "_" {
						continue
					}
					id := g.fresh(a)
					fmt.Fprintf(g.out, "%s := %s.f%d_%d\n_ = %s\n", id, s, cr.Idx, i, id)
					be = &env{name: a, ty: args[i], goid: id, next: be}
				}
			}
			branch(c.Body, be)
		}
	}
	if !hasWild && mustMatch {
		g.out.WriteString("default:\npanic(\"gogen: no case matches\")\n")
	}
	g.out.WriteString("}\n")
}

// bindPatRel binds a variable pattern (pat:rel) to the scrutinee s; a
// wildcard binds nothing.
func (g *Gen) bindPatRel(p *Node, s string, st *Ty, e *env) *env {
	if p.What != "pat:rel" {
		return e
	}
	id := g.fresh(p.Name)
	fmt.Fprintf(g.out, "%s := %s\n_ = %s\n", id, s, id)
	return &env{name: p.Name, ty: st, goid: id, next: e}
}

// tail emits statements that return the value of n.
func (g *Gen) tail(n *Node, e *env) {
	switch n.What {
	case "expr:let":
		v := g.expr(n.Nameval, e)
		id := g.fresh(n.Name)
		fmt.Fprintf(g.out, "%s := %s\n_ = %s\n", id, v, id)
		g.tail(n.Body, &env{name: n.Name, ty: g.types[n.Nameval], goid: id, next: e})
		return
	case "expr:case":
		// The switch always has a default, and every branch ends in a return,
		// a continue of the enclosing loop or a panic, so nothing follows it.
		g.caseStmt(n, e, g.tail, true)
		return
	case "expr:apply":
		if n.Func.What == "expr:global" {
			gl := g.globals[n.Func.Name]
			if gl.Name == "prim_andb" && len(n.Args) == 2 {
				fmt.Fprintf(g.out, "if !%s {\nreturn false\n}\n", g.expr(n.Args[0], e))
				g.tail(n.Args[1], e)
				return
			}
			if g.selfFn != nil && gl == g.selfFn && len(n.Args) == gl.Arity {
				var vs []string
				for _, a := range n.Args {
					vs = append(vs, g.expr(a, e))
				}
				fmt.Fprintf(g.out, "%s = %s\ncontinue\n", strings.Join(g.params, ", "), strings.Join(vs, ", "))
				return
			}
		}
	}
	fmt.Fprintf(g.out, "return %s\n", g.expr(n, e))
}

func (g *Gen) emitGlobal(gl *Global) {
	if gl.Prim {
		return
	}
	vars := map[string]*Ty{}
	var tp []string
	for i := 1; i <= gl.NVars; i++ {
		name := fmt.Sprintf("T%d", i)
		vars[fmt.Sprint(i)] = &Ty{K: 'p', Name: name}
		tp = append(tp, name+" any")
	}
	t := g.tyOf(gl.Type, vars)
	// Infer the body against the declared type, rigid in its variables.
	unify(g.infer(gl.Value, nil), t, "declaration "+gl.Name)

	body := gl.Value
	ret := t.res()
	var params, names []string
	var ptys []*Ty
	if gl.Arity > 0 {
		body = gl.Value.Body
		for _, a := range gl.Value.Argnames {
			id := goIdent(a) + "_in"
			names = append(names, id)
			ptys = append(ptys, ret.Args[0])
			params = append(params, fmt.Sprintf("%s %s", id, g.goTy(ret.Args[0])))
			ret = ret.Args[1].res()
		}
	}
	tparams := ""
	if len(tp) > 0 {
		tparams = "[" + strings.Join(tp, ", ") + "]"
	}
	fmt.Fprintf(g.out, "func F_%s%s(%s) %s {\n", goIdent(gl.Name), tparams, strings.Join(params, ", "), g.goTy(ret))
	g.out.WriteString("for {\n")
	var e *env
	for i, a := range gl.Value.Argnames {
		if gl.Arity == 0 {
			break
		}
		// A fresh copy per iteration, so closures capture this iteration's value.
		id := g.fresh(a)
		fmt.Fprintf(g.out, "%s := %s\n_ = %s\n", id, names[i], id)
		e = &env{name: a, ty: ptys[i], goid: id, next: e}
	}
	g.selfFn, g.params = gl, names
	g.tail(body, e)
	g.selfFn = nil
	g.out.WriteString("}\n}\n\n")
}

// Generate turns a MiniML JSON extraction into a gofmt'd Go file of package
// pkg. srcName is recorded in the header (only its base name, so the output
// does not depend on where the input lives).
func Generate(raw []byte, pkg, srcName string) ([]byte, error) {
	return GenerateWith(raw, pkg, srcName, Options{})
}

// Options adjusts what Generate accepts.
type Options struct {
	// AllowUnary names unmapped unary nat arithmetic functions to accept (see
	// unaryArithmetic). Each one is a known cost, to be removed in the proof.
	AllowUnary []string
}

// GenerateWith is Generate with options.
func GenerateWith(raw []byte, pkg, srcName string, opts Options) (src []byte, err error) {
	defer func() {
		if r := recover(); r != nil {
			ge, ok := r.(genError)
			if !ok {
				panic(r)
			}
			src, err = nil, ge
		}
	}()
	root := decode(json.RawMessage(raw), "root")
	g := &Gen{inds: map[string]*Ind{}, ctors: map[string]CtorRef{}, aliases: map[string]*Alias{},
		globals: map[string]*Global{}, types: map[*Node]*Ty{}, insts: map[*Node][]*Ty{}, out: &bytes.Buffer{}}
	g.load(root)
	g.refuseUnary(opts.AllowUnary)
	fmt.Fprintf(g.out, "// Code generated by gogen from %s (module %s). DO NOT EDIT.\n\npackage %s\n\n", filepath.Base(srcName), root.Name, pkg)
	g.emitInds()
	// Emit in name order, numbering temporaries per function, so the output
	// does not depend on the order the prover's standard library declares
	// things in (Coq 8.x and Rocq 9.x differ there).
	sort.Slice(g.order, func(i, j int) bool { return g.order[i].Name < g.order[j].Name })
	for _, gl := range g.order {
		g.tmp = 0
		g.emitGlobal(gl)
	}
	g.out.WriteString(runtime)
	src, ferr := format.Source(g.out.Bytes())
	if ferr != nil {
		return nil, genError(fmt.Sprintf("generated code does not parse: %v", ferr))
	}
	return src, nil
}

func main() {
	pkg := flag.String("pkg", "main", "Go package name")
	out := flag.String("o", "", "output file (default stdout)")
	allowUnary := flag.String("allow-unary", "", "comma-separated unary nat arithmetic functions to accept (see Options.AllowUnary)")
	flag.Parse()
	if flag.NArg() != 1 {
		fmt.Fprintln(os.Stderr, "usage: gogen [-pkg name] [-o out.go] [-allow-unary f,g] extraction.json")
		os.Exit(2)
	}
	raw, err := os.ReadFile(flag.Arg(0))
	if err != nil {
		fmt.Fprintln(os.Stderr, "gogen:", err)
		os.Exit(1)
	}
	var opts Options
	if *allowUnary != "" {
		opts.AllowUnary = strings.Split(*allowUnary, ",")
	}
	src, err := GenerateWith(raw, *pkg, flag.Arg(0), opts)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if *out == "" {
		os.Stdout.Write(src)
	} else if err := os.WriteFile(*out, src, 0o644); err != nil {
		fmt.Fprintln(os.Stderr, "gogen:", err)
		os.Exit(1)
	}
}
