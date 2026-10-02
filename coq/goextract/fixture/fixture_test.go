package fixture

import (
	"reflect"
	"testing"
)

func ints(l *I_list[int64]) []int64 {
	out := []int64{}
	for ; l.tag == 1; l = l.f1_1 {
		out = append(out, l.f1_0)
	}
	return out
}

func list(xs ...int64) *I_list[int64] {
	l := K_Nil[int64]()
	for i := len(xs) - 1; i >= 0; i-- {
		l = K_Cons(xs[i], l)
	}
	return l
}

// The generated Go computes what Fixture.v defines.
func TestFixture(t *testing.T) {
	for n := int64(0); n < 6; n++ {
		if got, want := F_fx_let(n), (2*n)*(2*n)+1; got != want {
			t.Errorf("fx_let %d = %d, want %d", n, got, want)
		}
		want := int64(0)
		if n == 3 {
			want = 1
		}
		if got := F_fx_nat_wild(n); got != want {
			t.Errorf("fx_nat_wild %d = %d, want %d", n, got, want)
		}
		if got := F_fx_over(n); got != 2*n+1 {
			t.Errorf("fx_over %d = %d, want %d", n, got, 2*n+1)
		}
		var cl []int64
		for i := int64(1); i <= n; i++ {
			cl = append(cl, i)
		}
		if got := ints(F_fx_closures(n)); !reflect.DeepEqual(got, append([]int64{}, cl...)) && !(len(got) == 0 && len(cl) == 0) {
			t.Errorf("fx_closures %d = %v, want %v (each closure keeps its own iteration's n)", n, got, cl)
		}
	}
	for z, want := range map[int64]int64{0: 0, 1: 1, 5: 1, -1: 2, -7: 2} {
		if got := F_fx_z_wild(z); got != want {
			t.Errorf("fx_z_wild %d = %d, want %d", z, got, want)
		}
	}
	for p, want := range map[int64]int64{1: 1, 2: 3, 3: 4, 100: 101} {
		if got := F_fx_pos_rel(p); got != want {
			t.Errorf("fx_pos_rel %d = %d, want %d", p, got, want)
		}
	}
	if F_fx_list_wild(list()) != 0 || F_fx_list_wild(list(4)) != 1 || F_fx_list_wild(list(4, 5)) != 1 {
		t.Errorf("fx_list_wild: want 0 for [] and 1 otherwise")
	}
	got := F_fx_partial(list(0, 1, 5))
	var pairs [][2]int64
	for l := got; l.tag == 1; l = l.f1_1 {
		pairs = append(pairs, [2]int64{l.f1_0.f0_0, l.f1_0.f0_1})
	}
	if want := [][2]int64{{7, 2}, {7, 3}, {7, 7}}; !reflect.DeepEqual(pairs, want) {
		t.Errorf("fx_partial = %v, want %v", pairs, want)
	}
}
