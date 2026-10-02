package semantics

import (
	"fmt"
	"os"
	"regexp"
	"strings"
	"testing"
)

func show[A any](l *I_list[A]) []string {
	out := []string{}
	for ; l.tag == 1; l = l.f1_1 {
		out = append(out, fmt.Sprint(l.f1_0))
	}
	return out
}

// rocqValues reads compute.out (Rocq's Compute of each value, in the order
// SemanticsCompute.v lists them) into one list of printed elements per value.
func rocqValues(t *testing.T) [][]string {
	raw, err := os.ReadFile("compute.out")
	if err != nil {
		t.Fatal(err)
	}
	scope := regexp.MustCompile(`%(Z|N|positive|nat)`)
	var out [][]string
	for _, block := range strings.Split(string(raw), "     = ")[1:] {
		body := strings.SplitN(block, "\n     : ", 2)[0]
		body = scope.ReplaceAllString(strings.Join(strings.Fields(body), " "), "")
		var elems []string
		for _, e := range strings.Split(body, "::") {
			e = strings.Trim(strings.TrimSpace(e), "()")
			if e != "nil" {
				elems = append(elems, e)
			}
		}
		out = append(out, elems)
	}
	return out
}

// The generated Go computes exactly what Rocq computes for every value of
// Semantics.v.
func TestGoMatchesRocqCompute(t *testing.T) {
	gov := []struct {
		name string
		v    []string
	}{
		{"t_clos", show(F_t_clos())}, {"t_swap", show(F_t_swap())}, {"t_mut", show(F_t_mut())},
		{"t_shadow", show(F_t_shadow())}, {"t_zdiv", show(F_t_zdiv())}, {"t_nat", show(F_t_nat())},
		{"t_pa", show(F_t_pa())}, {"t_poly", show(F_t_poly())}, {"t_big", show(F_t_big())},
		{"t_and", show(F_t_and())}, {"t_cmp", show(F_t_cmp())}, {"t_z", show(F_t_z())},
		{"t_n", show(F_t_n())}, {"t_pos", show(F_t_pos())}, {"t_dec", show(F_t_dec())},
		{"t_rec", show(F_t_rec())}, {"t_opt", show(F_t_opt())}, {"t_comp", show(F_t_comp())},
		{"t_sort", show(F_t_sort())}, {"t_unused", show(F_t_unused())}, {"t_exn", show(F_t_exn())},
	}
	rocq := rocqValues(t)
	if len(rocq) != len(gov) || len(gov) < 20 {
		t.Fatalf("compute.out has %d values, the test compares %d", len(rocq), len(gov))
	}
	for i, g := range gov {
		if strings.Join(g.v, " ") != strings.Join(rocq[i], " ") {
			t.Errorf("%s: Go gives %v, Rocq computes %v", g.name, g.v, rocq[i])
		}
	}
}
