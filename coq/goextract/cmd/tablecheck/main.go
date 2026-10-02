// Command tablecheck is the table oracle's front end over the Go that gogen
// generates from check_fn's extraction (package oracle). It is a port of
// extraction/main.ml: the same tables format (versions 1 and 2), validation,
// output lines and exit codes (0 verified convergent, 1 not, 2 input error);
// see main.ml for the format. tests/run.sh checks it against the regression
// cases, and against the OCaml checker when one is given.
package main

import (
	"fmt"
	"os"
	"strconv"
	"strings"

	"github.com/blackwell-systems/normalization-confluence/coq/goextract/oracle"
)

func failInput(msg string) {
	fmt.Fprintln(os.Stderr, "input error: "+msg)
	os.Exit(2)
}

// natOf accepts a non-negative decimal integer below 2^31, as main.ml does.
func natOf(s string) int64 {
	if len(s) == 0 || len(s) > 10 {
		failInput("expected non-negative decimal integer, got " + s)
	}
	for _, c := range s {
		if c < '0' || c > '9' {
			failInput("expected non-negative decimal integer, got " + s)
		}
	}
	v, err := strconv.ParseInt(s, 10, 64)
	if err != nil || v > 2147483647 {
		failInput("integer out of range: " + s)
	}
	return v
}

func list[A any](xs []A) *oracle.I_list[A] {
	l := oracle.K_Nil[A]()
	for i := len(xs) - 1; i >= 0; i-- {
		l = oracle.K_Cons(xs[i], l)
	}
	return l
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: checker <tables-file>")
		os.Exit(2)
	}
	st, err := os.Stat(os.Args[1])
	if err != nil {
		failInput(err.Error())
	}
	if st.Size() > 1024*1024*1024 {
		failInput("input larger than 1 GiB")
	}
	raw, err := os.ReadFile(os.Args[1])
	if err != nil {
		failInput(err.Error())
	}
	norm := strings.NewReplacer("\n", " ", "\t", " ", "\r", " ").Replace(string(raw))
	var toks []string
	for _, t := range strings.Split(norm, " ") {
		if t != "" {
			toks = append(toks, t)
		}
	}
	pos := 0
	next := func(what string) string {
		if pos >= len(toks) {
			failInput("unexpected end of input, expected " + what)
		}
		pos++
		return toks[pos-1]
	}
	keyword := func(k string) {
		if t := next(k); t != k {
			failInput("expected " + k + ", got " + t)
		}
	}
	nat := func(what string) int64 { return natOf(next(what)) }
	v2 := len(toks) > 0 && toks[0] == "gsm-tables"
	if v2 {
		keyword("gsm-tables")
		if ver := next("format version"); ver != "2" {
			failInput("unsupported tables format version " + ver)
		}
	}
	n := nat("n")
	ne := nat("nE")
	if n < 1 {
		failInput("n must be at least 1 (state 0 is the zero state)")
	}
	// Bound the work before allocating: every remaining token is one entry.
	if n*ne > int64(len(toks)) {
		failInput(fmt.Sprintf("expected %d step entries (n=%d, nE=%d)", n*ne, n, ne))
	}
	nf := make([]int64, n)
	pairs := oracle.K_None[*oracle.I_list[*oracle.I_prod[int64, int64]]]()
	declared := "every pair"
	if v2 {
		keyword("nf")
		for i := range nf {
			nf[i] = nat("nf entry")
		}
		keyword("pairs")
		if pos < len(toks) && toks[pos] == "all" {
			pos++
		} else {
			k := nat("pair count or all")
			if 2*k > int64(len(toks)-pos) {
				failInput(fmt.Sprintf("expected %d pair entries", 2*k))
			}
			ps := make([]*oracle.I_prod[int64, int64], k)
			for i := range ps {
				a := nat("pair event")
				b := nat("pair event")
				if a >= ne || b >= ne {
					failInput(fmt.Sprintf("declared pair (%d, %d) names an event past nE=%d", a, b, ne))
				}
				ps[i] = oracle.K_Pair(a, b)
			}
			pairs = oracle.K_Some(list(ps))
			declared = fmt.Sprintf("%d declared pairs", k)
		}
	} else {
		for i := range nf {
			nf[i] = int64(i)
		}
	}
	if int64(len(toks)-pos) != n*ne {
		failInput(fmt.Sprintf("expected %d step entries (n=%d, nE=%d), got %d", n*ne, n, ne, len(toks)-pos))
	}
	rows := make([][]int64, ne)
	for e := range rows {
		rows[e] = make([]int64, n)
		for s := range rows[e] {
			rows[e][s] = nat("step entry")
		}
	}
	// check_fn (TableFn.v) over accessors on the arrays, shaped like gsm's
	// gate: pure, total, the parsed (non-negative) entries, 0 out of range.
	nfA := func(s int64) int64 {
		if s >= 0 && s < n {
			return nf[s]
		}
		return 0
	}
	zero := func(int64) int64 { return 0 }
	rowA := make([]func(int64) int64, ne)
	for e := range rows {
		r := rows[e]
		rowA[e] = func(s int64) int64 {
			if s >= 0 && s < n {
				return r[s]
			}
			return 0
		}
	}
	stA := func(e int64) func(int64) int64 {
		if e >= 0 && e < ne {
			return rowA[e]
		}
		return zero
	}
	if oracle.F_check_fn(n, ne, nfA, stA, pairs) {
		fmt.Printf("OK: %d states, %d events, %s; tables verified convergent (normal forms and steps land on valid states; declared pairs commute on valid states and the zero state)\n", n, ne, declared)
		os.Exit(0)
	}
	fmt.Print("FAIL: tables do NOT converge (a normal form or step leaves the valid states, or a declared pair does not commute on a valid state or the zero state)\n")
	os.Exit(1)
}
