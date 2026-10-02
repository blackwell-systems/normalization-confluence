// SPIKE (spike/go-extraction): the rules oracle's front end over the Go code
// gogen generated from checkBuild's JSON extraction (astcore_gen.go). A port of
// extraction/ast_main.ml: same machine and pairs formats, same validation, same
// output lines and exit codes (0 verified convergent, 1 not, 2 usage or parse
// error). See ast_main.ml for the formats.
package main

import (
	"errors"
	"fmt"
	"os"
	"strconv"
	"strings"
)

const maxAbs = 2147483647

type sexp struct {
	atom string
	list []sexp
	isList bool
}

type parseError string

func failf(f string, a ...any) { panic(parseError(fmt.Sprintf(f, a...))) }

func tokenize(s string) []string {
	var out []string
	var buf strings.Builder
	flush := func() {
		if buf.Len() > 0 {
			out = append(out, buf.String())
			buf.Reset()
		}
	}
	for i := 0; i < len(s); i++ {
		switch c := s[i]; c {
		case '(', ')':
			flush()
			out = append(out, string(c))
		case ' ', '\t', '\n', '\r':
			flush()
		default:
			buf.WriteByte(c)
		}
	}
	flush()
	return out
}

func parseAll(toks []string) []sexp {
	pos := 0
	var parse func() sexp
	parse = func() sexp {
		if pos >= len(toks) {
			failf("unexpected end of input")
		}
		t := toks[pos]
		pos++
		switch t {
		case "(":
			l := sexp{isList: true}
			for {
				if pos >= len(toks) {
					failf("unterminated (")
				}
				if toks[pos] == ")" {
					pos++
					return l
				}
				l.list = append(l.list, parse())
			}
		case ")":
			failf("unexpected )")
		}
		return sexp{atom: t}
	}
	var forms []sexp
	for pos < len(toks) {
		forms = append(forms, parse())
	}
	return forms
}

// decimal checks an optional '-' then 1 to maxDigits digits; it returns the
// digit count.
func decimal(s string, maxDigits int) int {
	start := 0
	if len(s) > 0 && s[0] == '-' {
		start = 1
	}
	if len(s) == start || len(s)-start > maxDigits {
		failf("expected decimal integer, got %s", s)
	}
	for _, c := range s[start:] {
		if c < '0' || c > '9' {
			failf("expected decimal integer, got %s", s)
		}
	}
	return len(s) - start
}

func intOf(s string) int64 {
	decimal(s, 10)
	v, _ := strconv.ParseInt(s, 10, 64)
	if v > maxAbs || v < -maxAbs {
		failf("integer out of range (|n| <= 2147483647): %s", s)
	}
	return v
}

var outOfFragment bool

func valueOf(s string) int64 {
	if decimal(s, 19) > 10 {
		outOfFragment = true
		return 0
	}
	v, _ := strconv.ParseInt(s, 10, 64)
	if v > maxAbs || v < -maxAbs {
		outOfFragment = true
		return 0
	}
	return v
}

func natOf(s string) int64 {
	v := intOf(s)
	if v < 0 {
		failf("expected non-negative integer, got %s", s)
	}
	return v
}

var nvars int64 = -1

func varIndex(s string) int64 {
	i := natOf(s)
	if nvars < 0 {
		failf("doms must come before any rule")
	}
	if i >= nvars {
		failf("variable index %d out of range (%d variables)", i, nvars)
	}
	return i
}

func isAtom(x sexp, a string) bool { return !x.isList && x.atom == a }

func head(x sexp) string {
	if x.isList && len(x.list) > 0 && !x.list[0].isList {
		return x.list[0].atom
	}
	return ""
}

func list[A any](xs []A) *I_list[A] {
	l := K_Nil[A]()
	for i := len(xs) - 1; i >= 0; i-- {
		l = K_Cons(xs[i], l)
	}
	return l
}

func buildExpr(x sexp) *I_expr {
	l := x.list
	switch {
	case head(x) == "var" && len(l) == 2 && !l[1].isList:
		return K_EVar(varIndex(l[1].atom))
	case head(x) == "lit" && len(l) == 2 && !l[1].isList:
		return K_ELit(valueOf(l[1].atom))
	case head(x) == "add" && len(l) == 3:
		return K_EAdd(buildExpr(l[1]), buildExpr(l[2]))
	case head(x) == "sub" && len(l) == 3:
		return K_ESub(buildExpr(l[1]), buildExpr(l[2]))
	}
	failf("malformed expr")
	return nil
}

func buildPred(x sexp) *I_pred {
	l := x.list
	preds := func() *I_list[*I_pred] {
		var ps []*I_pred
		for _, p := range l[1:] {
			ps = append(ps, buildPred(p))
		}
		return list(ps)
	}
	switch {
	case head(x) == "le" && len(l) == 3:
		return K_PLe(buildExpr(l[1]), buildExpr(l[2]))
	case head(x) == "lt" && len(l) == 3:
		return K_PLt(buildExpr(l[1]), buildExpr(l[2]))
	case head(x) == "eq" && len(l) == 3:
		return K_PEq(buildExpr(l[1]), buildExpr(l[2]))
	case head(x) == "and":
		return K_PAnd(preds())
	case head(x) == "or":
		return K_POr(preds())
	case head(x) == "not" && len(l) == 2:
		return K_PNot(buildPred(l[1]))
	}
	failf("malformed pred")
	return nil
}

type assign = *I_prod[int64, *I_expr]
type gevent = *I_prod[*I_pred, *I_list[assign]]

func buildTransform(x sexp) *I_list[assign] {
	if head(x) != "do" {
		failf("malformed transform (expected (do ...))")
	}
	var as []assign
	for _, a := range x.list[1:] {
		if head(a) != "set" || len(a.list) != 3 || a.list[1].isList {
			failf("malformed assign")
		}
		i := varIndex(a.list[1].atom)
		as = append(as, K_Pair(i, buildExpr(a.list[2])))
	}
	return list(as)
}

func ints(xs []sexp, conv func(string) int64) []int64 {
	var out []int64
	for _, x := range xs {
		if x.isList {
			failf("expected integer")
		}
		out = append(out, conv(x.atom))
	}
	return out
}

func buildMachine(forms []sexp) (m *I_machine, nv, ni, ne int) {
	nvars, outOfFragment = -1, false
	var doms, mins []int64
	haveDoms, haveMins := false, false
	var invs, evs []gevent
	for _, f := range forms {
		l := f.list
		switch {
		case head(f) == "doms":
			ds := ints(l[1:], natOf)
			for _, d := range ds {
				if d < 1 {
					failf("every domain must be at least 1")
				}
			}
			if haveDoms {
				failf("doms given twice")
			}
			doms, haveDoms = ds, true
			nvars = int64(len(ds))
		case head(f) == "mins":
			ms := ints(l[1:], valueOf)
			if haveMins {
				failf("mins given twice")
			}
			mins, haveMins = ms, true
		case head(f) == "inv" && len(l) == 3:
			invs = append(invs, K_Pair(buildPred(l[1]), buildTransform(l[2])))
		case head(f) == "ev" && len(l) == 2:
			evs = append(evs, K_Pair(K_PAnd(K_Nil[*I_pred]()), buildTransform(l[1])))
		case head(f) == "evwhen" && len(l) == 3:
			evs = append(evs, K_Pair(buildPred(l[1]), buildTransform(l[2])))
		default:
			failf("unknown top-level form (expected doms/mins/inv/ev/evwhen)")
		}
	}
	if !haveDoms {
		failf("missing doms")
	}
	if !haveMins {
		mins = make([]int64, len(doms))
	}
	if len(mins) != len(doms) {
		failf("mins must give one minimum per variable")
	}
	for i, d := range doms {
		if v := mins[i] + d - 1; v > maxAbs || v < -maxAbs {
			outOfFragment = true
		}
	}
	return K_Build_machine(list(doms), list(mins), list(invs), list(evs)), len(doms), len(invs), len(evs)
}

func readAll(path string) (string, error) {
	st, err := os.Stat(path)
	if err != nil {
		return "", err
	}
	if st.Size() > 64*1024*1024 {
		return "", errors.New("input larger than 64 MiB")
	}
	b, err := os.ReadFile(path)
	return string(b), err
}

func readPairs(content string, nevents int) *I_option[*I_list[*I_prod[int64, int64]]] {
	var toks []string
	for _, t := range strings.Split(strings.NewReplacer("\n", " ", "\t", " ", "\r", " ").Replace(content), " ") {
		if t != "" {
			toks = append(toks, t)
		}
	}
	if len(toks) == 2 && toks[0] == "pairs" && toks[1] == "all" {
		return K_None[*I_list[*I_prod[int64, int64]]]()
	}
	if len(toks) < 2 || toks[0] != "pairs" {
		failf("expected 'pairs all' or 'pairs k a1 b1 ...'")
	}
	k := natOf(toks[1])
	rest := toks[2:]
	if int64(len(rest)) != 2*k {
		failf("expected %d pair entries, got %d", 2*k, len(rest))
	}
	var ps []*I_prod[int64, int64]
	for i := 0; i+1 < len(rest); i += 2 {
		a, b := natOf(rest[i]), natOf(rest[i+1])
		if a >= int64(nevents) || b >= int64(nevents) {
			failf("declared pair (%d, %d) names an event past the %d events", a, b, nevents)
		}
		ps = append(ps, K_Pair(a, b))
	}
	return K_Some(list(ps))
}

// catch runs f and turns a parseError into an error.
func catch(f func()) (err error) {
	defer func() {
		if r := recover(); r != nil {
			pe, ok := r.(parseError)
			if !ok {
				panic(r)
			}
			err = errors.New(string(pe))
		}
	}()
	f()
	return nil
}

func main() {
	if len(os.Args) < 2 || len(os.Args) > 3 {
		fmt.Fprintln(os.Stderr, "usage: astchecker <machine-file> [<pairs-file>]")
		os.Exit(2)
	}
	content, err := readAll(os.Args[1])
	if err != nil {
		fmt.Fprintln(os.Stderr, "cannot read machine file")
		os.Exit(2)
	}
	var m *I_machine
	var nv, ni, ne int
	if err := catch(func() { m, nv, ni, ne = buildMachine(parseAll(tokenize(content))) }); err != nil {
		fmt.Fprintln(os.Stderr, "parse error: "+err.Error())
		os.Exit(2)
	}
	pairs := K_None[*I_list[*I_prod[int64, int64]]]()
	npairs := -1
	if len(os.Args) == 3 {
		pc, rerr := readAll(os.Args[2])
		if rerr != nil {
			fmt.Fprintln(os.Stderr, "cannot read pairs file: "+rerr.Error())
			os.Exit(2)
		}
		if err := catch(func() { pairs = readPairs(pc, ne) }); err != nil {
			fmt.Fprintln(os.Stderr, "pairs file error: "+err.Error())
			os.Exit(2)
		}
		if pairs.tag == 0 {
			npairs = 0
			for l := pairs.f0_0; l.tag == 1; l = l.f1_1 {
				npairs++
			}
		}
	}
	if outOfFragment {
		fmt.Print("FAIL: outside the certified fragment: a literal, minimum or maximum exceeds |2147483647| (gsm's Go int could wrap)\n")
		os.Exit(1)
	}
	fmt.Printf("compensation_free=%v\n", F_compensationFree(m))
	if !F_bounded(m) {
		fmt.Print("FAIL: outside the certified fragment: some expression can exceed |2147483647| (gsm's Go int could wrap)\n")
		os.Exit(1)
	}
	if !F_signSafe(m) {
		fmt.Print("FAIL: outside the certified fragment: a write can store a negative value into a two-valued variable with min 0 (a gsm Bool stores value <> 0, the model clamps)\n")
		os.Exit(1)
	}
	if !F_wfc(m) {
		fmt.Print("FAIL: compensation does not terminate (WFC): repair from some state never reaches a valid state\n")
		os.Exit(1)
	}
	declared := "every pair"
	if npairs >= 0 {
		declared = fmt.Sprintf("%d declared pairs", npairs)
	}
	if F_checkBuild(m, pairs) {
		fmt.Printf("OK: %d vars, %d invariants, %d events, %s; machine verified convergent from its RULES (repair terminates from every state; declared pairs commute on valid states and the zero state)\n", nv, ni, ne, declared)
		os.Exit(0)
	}
	fmt.Print("FAIL: machine does NOT converge (a declared pair does not commute on a valid state or the zero state)\n")
	os.Exit(1)
}
