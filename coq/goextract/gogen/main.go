// SPIKE (spike/go-extraction): gogen turns Coq's JSON extraction (MiniML) into Go.
//
// Usage: gogen -pkg main -o out.go fast_core.json
//
// It accepts the MiniML fragment check_fast extracts to and fails loudly on
// anything else:
//   - inductives (possibly parameterized) become generic Go structs, values are
//     pointers, the constructor is a tag; nat and bool are mapped (see prims);
//   - top-level terms and fixpoints become Go functions, generic over the type
//     variables of their declared MiniML type; local lambdas become curried Go
//     closures; partial applications of globals become closures;
//   - Hindley-Milner inference (declared types for globals, monomorphic locals)
//     supplies every Go type the output needs, and every generic call is
//     instantiated explicitly;
//   - match becomes a switch on the tag; self tail calls become loops (a fresh
//     copy of the parameters per iteration, so closures never see a later
//     iteration's values); prim_andb is short-circuit, and its right operand is
//     in tail position, as OCaml's (&&) is.
//
// The prims are the only hand-written semantics: each one is the Go meaning of a
// constant ExtractGo.v maps (the same set ExtrOcamlNatInt maps). nat is int64;
// with -checked (the default) every operation that can grow a nat panics on
// overflow instead of wrapping, so the int64 mapping is exact or the run stops.
package main

import (
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"go/format"
	"os"
	"sort"
	"strings"
)

// ===== MiniML JSON =====

type Node struct {
	What        string            `json:"what"`
	Name        json.RawMessage   `json:"name"`
	Argnames    []string          `json:"argnames"`
	Body        *Node             `json:"body"`
	Expr        *Node             `json:"expr"`
	Cases       []*Node           `json:"cases"`
	Pat         *Node             `json:"pat"`
	Func        *Node             `json:"func"`
	Args        json.RawMessage   `json:"args"`
	Nameval     *Node             `json:"nameval"`
	Value       *Node             `json:"value"`
	Type        *Node             `json:"type"`
	Left        *Node             `json:"left"`
	Right       *Node             `json:"right"`
	Fixlist     []*Node           `json:"fixlist"`
	Constrs     []*Ctor           `json:"constructors"`
	Msg         string            `json:"msg"`
	Decls       []*Node           `json:"declarations"`
	Extra       map[string]any    `json:"-"`
	args        []*Node           // decoded Args (expressions or types)
	unknownKeys map[string]json.RawMessage
}

type Ctor struct {
	Name     string  `json:"name"`
	Argtypes []*Node `json:"argtypes"`
}

func (n *Node) name() string {
	var s string
	if json.Unmarshal(n.Name, &s) == nil {
		return s
	}
	var i int
	if json.Unmarshal(n.Name, &i) == nil {
		return fmt.Sprint(i)
	}
	return ""
}

func (n *Node) argList() []*Node {
	if n.args == nil && len(n.Args) > 0 {
		if err := json.Unmarshal(n.Args, &n.args); err != nil {
			fail("args of %s: %v", n.What, err)
		}
	}
	return n.args
}

func fail(f string, a ...any) {
	fmt.Fprintf(os.Stderr, "gogen: "+f+"\n", a...)
	os.Exit(1)
}

// ===== types and inference =====

type Ty struct {
	K    byte // 'm' meta, 'p' rigid parameter, 'c' constructor, 'a' arrow
	Name string
	Args []*Ty // 'c': type arguments; 'a': [left, right]
	ref  *Ty   // 'm': binding
}

func meta() *Ty { return &Ty{K: 'm'} }

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

func arrow(l, r *Ty) *Ty { return &Ty{K: 'a', Args: []*Ty{l, r}} }

// tyOf converts a MiniML type. vars maps type:var names and type:varidx indices
// (as strings) to Go types.
func tyOf(n *Node, vars map[string]*Ty) *Ty {
	switch n.What {
	case "type:arrow":
		return arrow(tyOf(n.Left, vars), tyOf(n.Right, vars))
	case "type:glob":
		t := &Ty{K: 'c', Name: n.name()}
		for _, a := range n.argList() {
			t.Args = append(t.Args, tyOf(a, vars))
		}
		return t
	case "type:var", "type:varidx":
		v, ok := vars[n.name()]
		if !ok {
			fail("unbound type variable %s", n.name())
		}
		return v
	}
	fail("unsupported type node %s", n.What)
	return nil
}

// maxVaridx returns the largest type:varidx in a declared type (its arity as a
// scheme).
func maxVaridx(n *Node) int {
	if n == nil {
		return 0
	}
	m := 0
	if n.What == "type:varidx" {
		fmt.Sscan(n.name(), &m)
	}
	for _, c := range []*Node{n.Left, n.Right} {
		if k := maxVaridx(c); k > m {
			m = k
		}
	}
	for _, a := range n.argList() {
		if k := maxVaridx(a); k > m {
			m = k
		}
	}
	return m
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

type Global struct {
	Name   string
	Type   *Node // declared MiniML type
	NVars  int
	Value  *Node
	Arity  int
	Prim   *Prim
	Fixgrp bool
}

type Prim struct {
	Arity int
	Go    string // a Go function name, or "" for operators handled inline
}

// The Go meaning of each constant ExtractGo.v maps. Every one is total on
// int64 values in range; the checked forms panic rather than wrap.
var prims = map[string]*Prim{
	"prim_add":     {2, "natAdd"},
	"prim_sub":     {2, "natSub"},
	"prim_mul":     {2, "natMul"},
	"prim_eqb":     {2, "natEqb"},
	"prim_compare": {2, "natCompare"},
	"prim_ltb":     {2, "natLtb"},
	"prim_div2":    {1, "natDiv2"},
	"prim_andb":    {2, ""},
}

type Gen struct {
	inds    map[string]*Ind
	ctors   map[string]CtorRef
	globals map[string]*Global
	order   []*Global
	types   map[*Node]*Ty   // inferred type of each expression node
	insts   map[*Node][]*Ty // explicit instantiation of each global / constructor use
	checked bool

	out    *bytes.Buffer
	tmp    int
	selfFn *Global   // function being emitted (for tail calls)
	params []string  // its loop-carried parameter names
}

func (g *Gen) load(root *Node) {
	if root.What != "module" {
		fail("expected a module, got %s", root.What)
	}
	for _, d := range root.Decls {
		switch d.What {
		case "decl:ind":
			name := d.name()
			if name == "bool" || name == "nat" {
				continue // mapped: Go bool and int64
			}
			if _, dup := g.inds[name]; dup {
				fail("duplicate inductive %s", name)
			}
			ind := &Ind{Name: name, Params: d.Argnames, Ctors: d.Constrs}
			g.inds[name] = ind
			for i, c := range d.Constrs {
				if _, dup := g.ctors[c.Name]; dup {
					fail("duplicate constructor %s", c.Name)
				}
				g.ctors[c.Name] = CtorRef{ind, i}
			}
		case "decl:term":
			g.addGlobal(d.name(), d.Type, d.Value, false)
		case "decl:fixgroup":
			for _, f := range d.Fixlist {
				g.addGlobal(f.name(), f.Type, f.Value, true)
			}
		default:
			fail("unsupported declaration %s", d.What)
		}
	}
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
	n.Body, n.Expr, n.Func, n.Nameval, n.Value = unwrap(n.Body), unwrap(n.Expr), unwrap(n.Func), unwrap(n.Nameval), unwrap(n.Value)
	for _, c := range n.Cases {
		unwrap(c)
	}
	if n.What == "expr:apply" || n.What == "expr:constructor" {
		as := n.argList()
		for i := range as {
			as[i] = unwrap(as[i])
		}
	}
	return n
}

func (g *Gen) addGlobal(name string, ty, val *Node, fix bool) {
	val = unwrap(val)
	if _, dup := g.globals[name]; dup {
		fail("duplicate global %s (JSON extraction drops module qualifiers)", name)
	}
	gl := &Global{Name: name, Type: ty, Value: val, NVars: maxVaridx(ty), Fixgrp: fix}
	if p, ok := prims[name]; ok {
		gl.Prim = p
		gl.Arity = p.Arity
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
	return tyOf(gl.Type, vars), inst
}

// ctorType returns the constructor's argument types and result type with fresh
// metas for the inductive's parameters.
func (g *Gen) ctorType(name string) ([]*Ty, *Ty, []*Ty) {
	switch name {
	case "true", "false":
		return nil, &Ty{K: 'c', Name: "bool"}, nil
	case "0":
		return nil, &Ty{K: 'c', Name: "nat"}, nil
	case "nat_succ":
		n := &Ty{K: 'c', Name: "nat"}
		return []*Ty{n}, n, nil
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
		args = append(args, tyOf(a, vars))
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
		b := e.look(n.name())
		if b == nil {
			fail("unbound variable %s", n.name())
		}
		return b.ty
	case "expr:global":
		gl, ok := g.globals[n.name()]
		if !ok {
			fail("unknown global %s", n.name())
		}
		t, inst := g.scheme(gl)
		g.insts[n] = inst
		return t
	case "expr:constructor":
		args, res, inst := g.ctorType(n.name())
		g.insts[n] = inst
		as := n.argList()
		if len(as) != len(args) {
			fail("constructor %s applied to %d args, wants %d (partial constructors are eta-expanded by extraction)", n.name(), len(as), len(args))
		}
		for i, a := range as {
			unify(g.infer(a, e), args[i], "constructor "+n.name())
		}
		return res
	case "expr:apply":
		ft := g.infer(n.Func, e)
		for _, a := range n.argList() {
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
		return g.infer(n.Body, &env{name: n.name(), ty: t, next: e})
	case "expr:case":
		st := g.infer(n.Expr, e)
		r := meta()
		for _, c := range n.Cases {
			ce := e
			switch c.Pat.What {
			case "pat:wild":
			case "pat:constructor":
				args, res, _ := g.ctorType(c.Pat.name())
				unify(st, res, "pattern "+c.Pat.name())
				if len(c.Pat.Argnames) != len(args) {
					fail("pattern %s binds %d, wants %d", c.Pat.name(), len(c.Pat.Argnames), len(args))
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
	switch t.Name {
	case "nat":
		return "int64"
	case "bool":
		return "bool"
	}
	return "*" + goIdent("I_"+t.Name) + g.tyArgs(t.Args)
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
				fmt.Fprintf(g.out, "\tf%d_%d %s\n", ci, ai, g.goTy(tyOf(a, vars)))
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
	}
}

// ---- expressions: emit statements into g.out, return a Go expression ----

func (g *Gen) expr(n *Node, e *env) string {
	switch n.What {
	case "expr:rel":
		return e.look(n.name()).goid
	case "expr:constructor":
		return g.ctorExpr(n, e)
	case "expr:global":
		return g.apply(n, nil, e)
	case "expr:apply":
		if n.Func.What == "expr:global" {
			return g.apply(n.Func, n.argList(), e)
		}
		f := g.expr(n.Func, e)
		for _, a := range n.argList() {
			f = f + "(" + g.expr(a, e) + ")"
		}
		return g.bind(f, g.types[n])
	case "expr:lambda":
		return g.lambda(n.Argnames, n.Body, g.types[n], e)
	case "expr:let":
		v := g.expr(n.Nameval, e)
		id := g.fresh(n.name())
		fmt.Fprintf(g.out, "%s := %s\n_ = %s\n", id, v, id)
		return g.expr(n.Body, &env{name: n.name(), ty: g.types[n.Nameval], goid: id, next: e})
	case "expr:case":
		r := g.fresh("r")
		fmt.Fprintf(g.out, "var %s %s\n", r, g.goTy(g.types[n]))
		g.caseStmt(n, e, func(body *Node, be *env) {
			v := g.expr(body, be)
			fmt.Fprintf(g.out, "%s = %s\n", r, v)
		})
		return r
	case "expr:exception":
		fmt.Fprintf(g.out, "panic(%q)\n", n.Msg)
		return "*new(" + g.goTy(g.types[n]) + ")"
	}
	fail("unsupported expression %s", n.What)
	return ""
}

// bind evaluates a Go expression once into a temporary.
func (g *Gen) bind(v string, t *Ty) string {
	id := g.fresh("t")
	fmt.Fprintf(g.out, "%s := %s\n", id, v)
	return id
}

func (g *Gen) ctorExpr(n *Node, e *env) string {
	name := n.name()
	as := n.argList()
	switch name {
	case "true", "false":
		return name
	case "0":
		return "int64(0)"
	case "nat_succ":
		// Fold literals: S (S 0) is the constant 2.
		k, inner := 1, as[0]
		for inner.What == "expr:constructor" && inner.name() == "nat_succ" {
			k++
			inner = inner.argList()[0]
		}
		if inner.What == "expr:constructor" && inner.name() == "0" {
			return fmt.Sprintf("int64(%d)", k)
		}
		return g.bind(fmt.Sprintf("natAddK(%s, %d)", g.expr(inner, e), k), nil)
	}
	cr := g.ctors[name]
	if len(as) == 0 && len(cr.Ind.Params) == 0 {
		return "C_" + goIdent(name)
	}
	var fs []string
	fs = append(fs, fmt.Sprintf("tag: %d", cr.Idx))
	for i, a := range as {
		fs = append(fs, fmt.Sprintf("f%d_%d: %s", cr.Idx, i, g.expr(a, e)))
	}
	return g.bind(fmt.Sprintf("&I_%s%s{%s}", goIdent(cr.Ind.Name), g.tyArgs(g.insts[n]), strings.Join(fs, ", ")), nil)
}

// apply emits a use of a global applied to args (possibly none, possibly more
// than its arity).
func (g *Gen) apply(f *Node, args []*Node, e *env) string {
	gl := g.globals[f.name()]
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
	ft := g.types[f]
	if len(vs) < gl.Arity {
		// Partial application: a curried closure over the remaining arguments.
		var rest []string
		var restTy []*Ty
		t := ft.res()
		for i := 0; i < len(vs); i++ {
			t = t.Args[1].res()
		}
		for i := len(vs); i < gl.Arity; i++ {
			id := g.fresh("a")
			rest = append(rest, id)
			restTy = append(restTy, t.Args[0])
			t = t.Args[1].res()
		}
		call := g.callGlobal(gl, f, append(append([]string{}, vs...), rest...))
		s := "return " + call
		for i := len(rest) - 1; i >= 0; i-- {
			retTy := t
			for j := len(rest) - 1; j > i; j-- {
				retTy = arrow(restTy[j], retTy)
			}
			s = fmt.Sprintf("func(%s %s) %s {\n%s\n}", rest[i], g.goTy(restTy[i]), g.goTy(retTy), s)
			if i > 0 {
				s = "return " + s
			}
		}
		return g.bind(s, nil)
	}
	call := g.callGlobal(gl, f, vs[:gl.Arity])
	for _, v := range vs[gl.Arity:] {
		call += "(" + v + ")"
	}
	return g.bind(call, nil)
}

func (g *Gen) callGlobal(gl *Global, f *Node, vs []string) string {
	if gl.Prim != nil {
		if gl.Name == "prim_andb" {
			return "(" + vs[0] + " && " + vs[1] + ")"
		}
		return gl.Prim.Go + "(" + strings.Join(vs, ", ") + ")"
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
	inner := g.out.String()
	g.out, g.selfFn = saved, savedSelf
	s := inner
	ret := tt
	for i := len(ids) - 1; i >= 0; i-- {
		s = fmt.Sprintf("func(%s %s) %s {\n%s}", ids[i], g.goTy(tys[i]), g.goTy(ret), s)
		ret = arrow(tys[i], ret)
		if i > 0 {
			s = "return " + s + "\n"
		}
	}
	return g.bind(s, nil)
}

func (g *Gen) caseStmt(n *Node, e *env, branch func(*Node, *env)) {
	s := g.expr(n.Expr, e)
	st := g.types[n.Expr].res()
	switch {
	case st.K == 'c' && st.Name == "nat":
		fmt.Fprintf(g.out, "switch {\n")
		for _, c := range n.Cases {
			be := e
			switch {
			case c.Pat.What == "pat:wild":
				g.out.WriteString("default:\n")
			case c.Pat.name() == "0":
				fmt.Fprintf(g.out, "case %s == 0:\n", s)
			default:
				fmt.Fprintf(g.out, "case %s > 0:\n", s)
				a := c.Pat.Argnames[0]
				id := g.fresh(a)
				fmt.Fprintf(g.out, "%s := %s - 1\n_ = %s\n", id, s, id)
				be = &env{name: a, ty: st, goid: id, next: e}
			}
			branch(c.Body, be)
		}
	case st.K == 'c' && st.Name == "bool":
		fmt.Fprintf(g.out, "switch %s {\n", s)
		for _, c := range n.Cases {
			if c.Pat.What == "pat:wild" {
				g.out.WriteString("default:\n")
			} else {
				fmt.Fprintf(g.out, "case %s:\n", c.Pat.name())
			}
			branch(c.Body, e)
		}
	default:
		fmt.Fprintf(g.out, "switch %s.tag {\n", s)
		for _, c := range n.Cases {
			be := e
			if c.Pat.What == "pat:wild" {
				g.out.WriteString("default:\n")
			} else {
				cr := g.ctors[c.Pat.name()]
				args, res, _ := g.ctorType(c.Pat.name())
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
	g.out.WriteString("}\n")
}

// tail emits statements that return the value of n.
func (g *Gen) tail(n *Node, e *env) {
	switch n.What {
	case "expr:let":
		v := g.expr(n.Nameval, e)
		id := g.fresh(n.name())
		fmt.Fprintf(g.out, "%s := %s\n_ = %s\n", id, v, id)
		g.tail(n.Body, &env{name: n.name(), ty: g.types[n.Nameval], goid: id, next: e})
		return
	case "expr:case":
		g.caseStmt(n, e, g.tail)
		g.out.WriteString("panic(\"unreachable: non-exhaustive match\")\n")
		return
	case "expr:apply":
		if n.Func.What == "expr:global" {
			gl := g.globals[n.Func.name()]
			as := n.argList()
			if gl.Name == "prim_andb" && len(as) == 2 {
				fmt.Fprintf(g.out, "if !%s {\nreturn false\n}\n", g.expr(as[0], e))
				g.tail(as[1], e)
				return
			}
			if g.selfFn != nil && gl == g.selfFn && len(as) == gl.Arity {
				var vs []string
				for _, a := range as {
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
	if gl.Prim != nil {
		return
	}
	vars := map[string]*Ty{}
	var tp []string
	for i := 1; i <= gl.NVars; i++ {
		name := fmt.Sprintf("T%d", i)
		vars[fmt.Sprint(i)] = &Ty{K: 'p', Name: name}
		tp = append(tp, name+" any")
	}
	t := tyOf(gl.Type, vars)
	// Infer the body against the declared type, rigid in its variables.
	g.types[gl.Value] = nil
	unify(g.infer(gl.Value, nil), t, "declaration "+gl.Name)

	var names []string
	var e *env
	body := gl.Value
	tt := t
	var params []string
	if gl.Arity > 0 {
		body = gl.Value.Body
		for _, a := range gl.Value.Argnames {
			id := goIdent(a) + "_in"
			params = append(params, fmt.Sprintf("%s %s", id, g.goTy(tt.Args[0])))
			names = append(names, id)
			tt = tt.Args[1].res()
		}
	}
	tparams := ""
	if len(tp) > 0 {
		tparams = "[" + strings.Join(tp, ", ") + "]"
	}
	fmt.Fprintf(g.out, "func F_%s%s(%s) %s {\n", goIdent(gl.Name), tparams, strings.Join(params, ", "), g.goTy(tt))
	g.out.WriteString("for {\n")
	for i, a := range gl.Value.Argnames {
		if gl.Arity == 0 {
			break
		}
		// A fresh copy per iteration, so closures capture this iteration's value.
		id := g.fresh(a)
		fmt.Fprintf(g.out, "%s := %s\n_ = %s\n", id, names[i], id)
		e = &env{name: a, ty: g.paramTy(t, i), goid: id, next: e}
	}
	g.selfFn, g.params = gl, names
	g.tail(body, e)
	g.selfFn = nil
	g.out.WriteString("}\n}\n\n")
}

func (g *Gen) paramTy(t *Ty, i int) *Ty {
	t = t.res()
	for ; i > 0; i-- {
		t = t.Args[1].res()
	}
	return t.Args[0]
}

const runtime = `
// ===== prims: the Go meaning of the constants ExtractGo.v maps =====

func natAdd(a, b int64) int64 {
	r := a + b
	if checked && r < a {
		panic("nat overflow in add")
	}
	return r
}

func natAddK(a int64, k int64) int64 { return natAdd(a, k) }

func natSub(a, b int64) int64 {
	if a < b {
		return 0
	}
	return a - b
}

func natMul(a, b int64) int64 {
	if checked && a != 0 && b != 0 {
		r := a * b
		if r/b != a || r < 0 {
			panic("nat overflow in mul")
		}
		return r
	}
	return a * b
}

func natEqb(a, b int64) bool { return a == b }

func natLtb(a, b int64) bool { return a < b }

func natDiv2(a int64) int64 { return a / 2 }

func natCompare(a, b int64) *I_comparison {
	if a == b {
		return C_Eq
	}
	if a < b {
		return C_Lt
	}
	return C_Gt
}
`

func main() {
	pkg := flag.String("pkg", "main", "Go package name")
	out := flag.String("o", "", "output file (default stdout)")
	checked := flag.Bool("checked", true, "panic on nat overflow instead of wrapping")
	flag.Parse()
	if flag.NArg() != 1 {
		fail("usage: gogen [-pkg p] [-o out.go] extraction.json")
	}
	raw, err := os.ReadFile(flag.Arg(0))
	if err != nil {
		fail("%v", err)
	}
	var root Node
	if err := json.Unmarshal(raw, &root); err != nil {
		fail("%v", err)
	}
	g := &Gen{inds: map[string]*Ind{}, ctors: map[string]CtorRef{}, globals: map[string]*Global{},
		types: map[*Node]*Ty{}, insts: map[*Node][]*Ty{}, out: &bytes.Buffer{}, checked: *checked}
	g.load(&root)
	if _, ok := g.inds["comparison"]; !ok {
		g.inds["comparison"] = &Ind{Name: "comparison", Ctors: []*Ctor{{Name: "Eq"}, {Name: "Lt"}, {Name: "Gt"}}}
	}
	if g.inds["comparison"].Ctors[0].Name != "Eq" || g.inds["comparison"].Ctors[1].Name != "Lt" || g.inds["comparison"].Ctors[2].Name != "Gt" {
		fail("comparison constructors are not Eq, Lt, Gt")
	}
	fmt.Fprintf(g.out, "// Code generated by gogen from %s. DO NOT EDIT.\n\npackage %s\n\n", flag.Arg(0), *pkg)
	fmt.Fprintf(g.out, "const checked = %v\n\n", *checked)
	g.emitInds()
	for _, gl := range g.order {
		g.emitGlobal(gl)
	}
	g.out.WriteString(runtime)
	src, ferr := format.Source(g.out.Bytes())
	if ferr != nil {
		src = g.out.Bytes()
		fmt.Fprintf(os.Stderr, "gogen: gofmt failed (writing unformatted): %v\n", ferr)
	}
	if *out == "" {
		os.Stdout.Write(src)
	} else if err := os.WriteFile(*out, src, 0o644); err != nil {
		fail("%v", err)
	}
	if ferr != nil {
		os.Exit(1)
	}
}
