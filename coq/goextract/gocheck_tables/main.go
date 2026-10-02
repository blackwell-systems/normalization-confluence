// SPIKE (spike/go-extraction): the table oracle's front end over the Go code
// gogen generated from check_tables' JSON extraction (tablescore_gen.go), to show
// the generator is not specific to check_fast. Same input format, validation and
// exit codes as gocheck (a port of extraction/main_fast.ml).
package main

import (
	"fmt"
	"os"
	"strconv"
	"strings"
	"time"
)

func failInput(msg string) {
	fmt.Fprintln(os.Stderr, "input error: "+msg)
	os.Exit(2)
}

// natOf accepts a non-negative decimal integer below 2^31, as main_fast.ml does.
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

// Coq values, built with the generated types (list: Nil tag 0, Cons tag 1;
// option: Some tag 0, None tag 1; prod: Pair tag 0).
func list[A any](xs []A) *I_list[A] {
	l := &I_list[A]{tag: 0}
	for i := len(xs) - 1; i >= 0; i-- {
		l = &I_list[A]{tag: 1, f1_0: xs[i], f1_1: l}
	}
	return l
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: gocheck <tables-file>")
		os.Exit(2)
	}
	t0 := time.Now()
	f, err := os.Open(os.Args[1])
	if err != nil {
		failInput(err.Error())
	}
	st, _ := f.Stat()
	if st.Size() > 1024*1024*1024 {
		failInput("input larger than 1 GiB")
	}
	raw, err := os.ReadFile(os.Args[1])
	if err != nil {
		failInput(err.Error())
	}
	toks := strings.Fields(strings.NewReplacer("\n", " ", "\t", " ", "\r", " ").Replace(string(raw)))
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
	if n*ne > int64(len(toks)) {
		failInput(fmt.Sprintf("expected %d step entries (n=%d, nE=%d)", n*ne, n, ne))
	}
	nf := make([]int64, n)
	pairs := &I_option[*I_list[*I_prod[int64, int64]]]{tag: 1} // None: every pair
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
			ps := make([]*I_prod[int64, int64], k)
			for i := range ps {
				a := nat("pair event")
				b := nat("pair event")
				if a >= ne || b >= ne {
					failInput(fmt.Sprintf("declared pair (%d, %d) names an event past nE=%d", a, b, ne))
				}
				ps[i] = &I_prod[int64, int64]{f0_0: a, f0_1: b}
			}
			pairs = &I_option[*I_list[*I_prod[int64, int64]]]{tag: 0, f0_0: list(ps)}
		}
	} else {
		for i := range nf {
			nf[i] = int64(i)
		}
	}
	if int64(len(toks)-pos) != n*ne {
		failInput(fmt.Sprintf("expected %d step entries (n=%d, nE=%d), got %d", n*ne, n, ne, len(toks)-pos))
	}
	rows := make([]*I_list[int64], ne)
	row := make([]int64, n)
	for e := range rows {
		for s := range row {
			row[s] = nat("step entry")
		}
		rows[e] = list(row)
	}
	t1 := time.Now()
	tries := make([]*I_trie, len(rows))
	for i, r := range rows {
		tries[i] = F_of_list(r)
	}
	ok := F_check_tables(n, ne, F_of_list(list(nf)), list(tries), pairs)
	t2 := time.Now()
	if os.Getenv("GOCHECK_TIME") != "" {
		fmt.Fprintf(os.Stderr, "parse+build %v, check_fast %v\n", t1.Sub(t0), t2.Sub(t1))
	}
	if ok {
		fmt.Printf("OK: %d states, %d events; tables verified convergent\n", n, ne)
		os.Exit(0)
	}
	fmt.Println("FAIL: tables do NOT converge")
	os.Exit(1)
}
