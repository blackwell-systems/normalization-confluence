// SPIKE: time the route A sketch (tablecheck.CheckTables, hand-written flat
// slices) on a version 2 tables file. Minimal parsing, no input validation.
package main

import (
	"fmt"
	"os"
	"strconv"
	"strings"
	"time"

	"example.com/goosecheck/tablecheck"
)

func main() {
	raw, err := os.ReadFile(os.Args[1])
	if err != nil {
		panic(err)
	}
	toks := strings.Fields(string(raw))
	pos := 2 // "gsm-tables 2"
	num := func() uint64 {
		v, err := strconv.ParseUint(toks[pos], 10, 64)
		if err != nil {
			panic(err)
		}
		pos++
		return v
	}
	n, nE := num(), num()
	pos++ // nf
	nf := make([]uint64, n)
	for i := range nf {
		nf[i] = num()
	}
	pos++ // pairs
	var pa, pb []uint64
	if toks[pos] == "all" {
		pos++
		for i := uint64(0); i < nE; i++ {
			for j := i + 1; j < nE; j++ {
				pa, pb = append(pa, i), append(pb, j)
			}
		}
	} else {
		k := num()
		for i := uint64(0); i < k; i++ {
			pa, pb = append(pa, num()), append(pb, num())
		}
	}
	t := make([]uint64, n*nE)
	for i := range t {
		t[i] = num()
	}
	t0 := time.Now()
	ok := tablecheck.CheckTables(n, nE, nf, t, pa, pb)
	fmt.Println(ok, time.Since(t0))
}
