// Package primcheck checks gogen's prims and mapped constructors against their
// Rocq definitions (decision 5 of the Go oracle plan). PrimRef.v names every
// constant ExtrGo.v maps and probes every mapped constructor; package mapped is
// that file generated under ExtrGo.v (the Go prims), package plain the same file
// generated with no directives (the Rocq definitions on unary and binary
// inductives). Every reference and probe must agree on every input below.
package primcheck

import (
	"fmt"
	"math/big"
	"math/rand"
	"reflect"
	"testing"

	M "github.com/blackwell-systems/normalization-confluence/coq/goextract/primcheck/mapped"
	P "github.com/blackwell-systems/normalization-confluence/coq/goextract/primcheck/plain"
)

const maxI = int64(1<<63 - 1)

// Input ranges. The largest values make the checked arithmetic overflow; the
// Go side must then panic (fail closed), which agree checks. nat is unary in package plain, so its range stays small; the
// binary types reach past 2^31 through the random samples and the int64
// extremes.
var (
	natR = rng(0, 24)
	posR = append(rng(1, 70), 1<<31-1, 1<<31, 1<<32+5, 1<<40+3, maxI-1, maxI)
	nR   = append(rng(0, 70), 1<<31, 1<<40+2, maxI-1, maxI)
	zR   = append(rng(-70, 70), 1<<31, -(1 << 31), 1<<40+1, -(1<<40 + 1), maxI, -maxI, -maxI+1, -maxI-1)
)

func rng(lo, hi int64) []int64 {
	var r []int64
	for i := lo; i <= hi; i++ {
		r = append(r, i)
	}
	return r
}

func random(r *rand.Rand, n int, lo, hi int64) []int64 {
	out := make([]int64, n)
	for i := range out {
		out[i] = lo + r.Int63n(hi-lo+1)
	}
	return out
}

// beyondInt64 reports whether a canonical value holds a number int64 cannot.
func beyondInt64(v any) bool {
	switch x := v.(type) {
	case P.Num:
		n, ok := new(big.Int).SetString(string(x), 10)
		return ok && !n.IsInt64()
	case [2]any:
		return beyondInt64(x[0]) || beyondInt64(x[1])
	case []any:
		for _, e := range x {
			if beyondInt64(e) {
				return true
			}
		}
	}
	return false
}

// agree runs the Go side m and compares it with the Rocq side p. If the Go side
// panics (checked arithmetic), the exact Rocq result must hold a number outside
// int64: failing closed is the only allowed difference.
func agree(t *testing.T, name string, args []any, m func() any, p any) {
	t.Helper()
	var mv any
	panicked := func() (bad bool) {
		defer func() {
			if r := recover(); r != nil {
				bad = true
			}
		}()
		mv = M.Canon(m())
		return false
	}()
	if panicked {
		if !beyondInt64(p) {
			t.Errorf("%s%v: Go prim panics, but the Rocq result %v fits in int64", name, args, p)
		}
		return
	}
	if !reflect.DeepEqual(mv, p) {
		t.Errorf("%s%v: Go prim gives %v, Rocq definition gives %v", name, args, mv, p)
	}
}

type unary struct {
	name string
	dom  []int64
	m    func(int64) any
	p    func(int64) any
}

type binary struct {
	name   string
	da, db []int64
	m      func(int64, int64) any
	p      func(int64, int64) any
}

func TestPrimsMatchTheirRocqDefinitions(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	bigPos := random(r, 60, 1, 1<<30)
	bigZ := random(r, 60, -(1 << 30), 1<<30)
	bigN := random(r, 60, 0, 1<<30)
	pos2 := append(append([]int64{}, posR...), bigPos...)
	z2 := append(append([]int64{}, zR...), bigZ...)
	n2 := append(append([]int64{}, nR...), bigN...)
	c := P.Canon

	unaries := []unary{
		{"nat_div2", natR, func(a int64) any { return M.F_ref_nat_div2()(a) }, func(a int64) any { return c(P.F_ref_nat_div2()(P.Nat(a))) }},
		{"pos_succ", pos2, func(a int64) any { return M.F_ref_pos_succ()(a) }, func(a int64) any { return c(P.F_ref_pos_succ()(P.Pos(a))) }},
		{"pos_pred", pos2, func(a int64) any { return M.F_ref_pos_pred()(a) }, func(a int64) any { return c(P.F_ref_pos_pred()(P.Pos(a))) }},
		{"n_succ", n2, func(a int64) any { return M.F_ref_n_succ()(a) }, func(a int64) any { return c(P.F_ref_n_succ()(P.N(a))) }},
		{"n_pred", n2, func(a int64) any { return M.F_ref_n_pred()(a) }, func(a int64) any { return c(P.F_ref_n_pred()(P.N(a))) }},
		{"z_succ", z2, func(a int64) any { return M.F_ref_z_succ()(a) }, func(a int64) any { return c(P.F_ref_z_succ()(P.Z(a))) }},
		{"z_pred", z2, func(a int64) any { return M.F_ref_z_pred()(a) }, func(a int64) any { return c(P.F_ref_z_pred()(P.Z(a))) }},
		{"z_opp", z2, func(a int64) any { return M.F_ref_z_opp()(a) }, func(a int64) any { return c(P.F_ref_z_opp()(P.Z(a))) }},
		{"z_abs", z2, func(a int64) any { return M.F_ref_z_abs()(a) }, func(a int64) any { return c(P.F_ref_z_abs()(P.Z(a))) }},
		{"z_abs_n", z2, func(a int64) any { return M.F_ref_z_abs_n()(a) }, func(a int64) any { return c(P.F_ref_z_abs_n()(P.Z(a))) }},
		{"z_of_n", n2, func(a int64) any { return M.F_ref_z_of_n()(a) }, func(a int64) any { return c(P.F_ref_z_of_n()(P.N(a))) }},
		// Probes: every mapped constructor built and matched.
		{"probe_nat", natR, func(a int64) any { return M.Canon(M.F_probe_nat(a)) }, func(a int64) any { return c(P.F_probe_nat(P.Nat(a))) }},
		{"probe_pos_bits", pos2, func(a int64) any { return M.Canon(M.F_probe_pos_bits(a)) }, func(a int64) any { return c(P.F_probe_pos_bits(P.Pos(a))) }},
		{"probe_n", n2, func(a int64) any { return M.Canon(M.F_probe_n(a)) }, func(a int64) any { return c(P.F_probe_n(P.N(a))) }},
		{"probe_z", z2, func(a int64) any { return M.Canon(M.F_probe_z(a)) }, func(a int64) any { return c(P.F_probe_z(P.Z(a))) }},
	}
	for _, u := range unaries {
		for _, a := range u.dom {
			agree(t, u.name, []any{a}, func() any { return u.m(a) }, u.p(a))
		}
	}

	natB := func(name string, m func(int64) func(int64) any, p func(*P.I_nat) func(*P.I_nat) any) binary {
		return binary{name, natR, natR, func(a, b int64) any { return m(a)(b) }, func(a, b int64) any { return c(p(P.Nat(a))(P.Nat(b))) }}
	}
	posB := func(name string, m func(int64) func(int64) any, p func(*P.I_positive) func(*P.I_positive) any) binary {
		return binary{name, posR, pos2, func(a, b int64) any { return m(a)(b) }, func(a, b int64) any { return c(p(P.Pos(a))(P.Pos(b))) }}
	}
	nB := func(name string, m func(int64) func(int64) any, p func(*P.I_n) func(*P.I_n) any) binary {
		return binary{name, nR, n2, func(a, b int64) any { return m(a)(b) }, func(a, b int64) any { return c(p(P.N(a))(P.N(b))) }}
	}
	zB := func(name string, m func(int64) func(int64) any, p func(*P.I_z) func(*P.I_z) any) binary {
		return binary{name, zR, z2, func(a, b int64) any { return m(a)(b) }, func(a, b int64) any { return c(p(P.Z(a))(P.Z(b))) }}
	}
	// lift adapts a curried generated function to the uniform shape above.
	type i2i = func(int64) func(int64) int64
	type i2c = func(int64) func(int64) *M.I_comparison
	li := func(f i2i) func(int64) func(int64) any {
		return func(a int64) func(int64) any { return func(b int64) any { return f(a)(b) } }
	}
	lc := func(f i2c) func(int64) func(int64) any {
		return func(a int64) func(int64) any { return func(b int64) any { return M.Canon(f(a)(b)) } }
	}
	binaries := []binary{
		natB("nat_add", li(M.F_ref_nat_add()), func(a *P.I_nat) func(*P.I_nat) any { return func(b *P.I_nat) any { return P.F_ref_nat_add()(a)(b) } }),
		natB("nat_sub", li(M.F_ref_nat_sub()), func(a *P.I_nat) func(*P.I_nat) any { return func(b *P.I_nat) any { return P.F_ref_nat_sub()(a)(b) } }),
		natB("nat_mul", li(M.F_ref_nat_mul()), func(a *P.I_nat) func(*P.I_nat) any { return func(b *P.I_nat) any { return P.F_ref_nat_mul()(a)(b) } }),
		natB("nat_eqb", func(a int64) func(int64) any { return func(b int64) any { return M.F_ref_nat_eqb()(a)(b) } },
			func(a *P.I_nat) func(*P.I_nat) any { return func(b *P.I_nat) any { return P.F_ref_nat_eqb()(a)(b) } }),
		natB("nat_ltb", func(a int64) func(int64) any { return func(b int64) any { return M.F_ref_nat_ltb(a, b) } },
			func(a *P.I_nat) func(*P.I_nat) any { return func(b *P.I_nat) any { return P.F_ref_nat_ltb(a, b) } }),
		natB("nat_compare", lc(M.F_ref_nat_compare()), func(a *P.I_nat) func(*P.I_nat) any {
			return func(b *P.I_nat) any { return P.F_ref_nat_compare()(a)(b) }
		}),
		natB("probe_sumbool", func(a int64) func(int64) any { return func(b int64) any { return M.F_probe_sumbool(a, b) } },
			func(a *P.I_nat) func(*P.I_nat) any { return func(b *P.I_nat) any { return P.F_probe_sumbool(a, b) } }),

		posB("pos_add", li(M.F_ref_pos_add()), func(a *P.I_positive) func(*P.I_positive) any {
			return func(b *P.I_positive) any { return P.F_ref_pos_add()(a)(b) }
		}),
		posB("pos_sub", li(M.F_ref_pos_sub()), func(a *P.I_positive) func(*P.I_positive) any {
			return func(b *P.I_positive) any { return P.F_ref_pos_sub()(a)(b) }
		}),
		posB("pos_mul", li(M.F_ref_pos_mul()), func(a *P.I_positive) func(*P.I_positive) any {
			return func(b *P.I_positive) any { return P.F_ref_pos_mul()(a)(b) }
		}),
		posB("pos_min", li(M.F_ref_pos_min()), func(a *P.I_positive) func(*P.I_positive) any {
			return func(b *P.I_positive) any { return P.F_ref_pos_min()(a)(b) }
		}),
		posB("pos_max", li(M.F_ref_pos_max()), func(a *P.I_positive) func(*P.I_positive) any {
			return func(b *P.I_positive) any { return P.F_ref_pos_max()(a)(b) }
		}),
		posB("pos_compare", lc(M.F_ref_pos_compare()), func(a *P.I_positive) func(*P.I_positive) any {
			return func(b *P.I_positive) any { return P.F_ref_pos_compare()(a)(b) }
		}),

		nB("n_add", li(M.F_ref_n_add()), func(a *P.I_n) func(*P.I_n) any { return func(b *P.I_n) any { return P.F_ref_n_add()(a)(b) } }),
		nB("n_sub", li(M.F_ref_n_sub()), func(a *P.I_n) func(*P.I_n) any { return func(b *P.I_n) any { return P.F_ref_n_sub()(a)(b) } }),
		nB("n_mul", li(M.F_ref_n_mul()), func(a *P.I_n) func(*P.I_n) any { return func(b *P.I_n) any { return P.F_ref_n_mul()(a)(b) } }),
		nB("n_min", li(M.F_ref_n_min()), func(a *P.I_n) func(*P.I_n) any { return func(b *P.I_n) any { return P.F_ref_n_min()(a)(b) } }),
		nB("n_max", li(M.F_ref_n_max()), func(a *P.I_n) func(*P.I_n) any { return func(b *P.I_n) any { return P.F_ref_n_max()(a)(b) } }),
		nB("n_div", li(M.F_ref_n_div()), func(a *P.I_n) func(*P.I_n) any { return func(b *P.I_n) any { return P.F_ref_n_div()(a)(b) } }),
		nB("n_modulo", li(M.F_ref_n_modulo()), func(a *P.I_n) func(*P.I_n) any { return func(b *P.I_n) any { return P.F_ref_n_modulo()(a)(b) } }),
		nB("n_compare", lc(M.F_ref_n_compare()), func(a *P.I_n) func(*P.I_n) any { return func(b *P.I_n) any { return P.F_ref_n_compare()(a)(b) } }),

		zB("z_add", li(M.F_ref_z_add()), func(a *P.I_z) func(*P.I_z) any { return func(b *P.I_z) any { return P.F_ref_z_add()(a)(b) } }),
		zB("z_sub", li(M.F_ref_z_sub()), func(a *P.I_z) func(*P.I_z) any { return func(b *P.I_z) any { return P.F_ref_z_sub()(a)(b) } }),
		zB("z_mul", li(M.F_ref_z_mul()), func(a *P.I_z) func(*P.I_z) any { return func(b *P.I_z) any { return P.F_ref_z_mul()(a)(b) } }),
		zB("z_min", li(M.F_ref_z_min()), func(a *P.I_z) func(*P.I_z) any { return func(b *P.I_z) any { return P.F_ref_z_min()(a)(b) } }),
		zB("z_max", li(M.F_ref_z_max()), func(a *P.I_z) func(*P.I_z) any { return func(b *P.I_z) any { return P.F_ref_z_max()(a)(b) } }),
		zB("z_compare", lc(M.F_ref_z_compare()), func(a *P.I_z) func(*P.I_z) any { return func(b *P.I_z) any { return P.F_ref_z_compare()(a)(b) } }),
	}
	for _, b := range binaries {
		for _, x := range b.da {
			for _, y := range b.db {
				agree(t, b.name, []any{x, y}, func() any { return b.m(x, y) }, b.p(x, y))
			}
		}
	}

	// andb, compare_cont and the constructor-building probes.
	for _, x := range []bool{false, true} {
		for _, y := range []bool{false, true} {
			agree(t, "andb", []any{x, y}, func() any { return M.F_ref_andb()(x)(y) }, c(P.F_ref_andb(P.Bool(x), P.Bool(y))))
		}
		agree(t, "probe_bool", []any{x}, func() any { return M.F_probe_bool(x) }, c(P.F_probe_bool(P.Bool(x))))
	}
	for _, k := range []string{"Eq", "Lt", "Gt"} {
		for _, x := range posR {
			for _, y := range posR[:20] {
				agree(t, "pos_compare_cont", []any{k, x, y},
					func() any { return M.F_ref_pos_compare_cont()(M.Cmp(k))(x)(y) }, c(P.F_ref_pos_compare_cont()(P.Cmp(k))(P.Pos(x))(P.Pos(y))))
			}
		}
	}
	for i := 0; i < 400; i++ {
		bits := make([]bool, r.Intn(40))
		for j := range bits {
			bits[j] = r.Intn(2) == 1
		}
		agree(t, "probe_pos_mk", []any{fmt.Sprint(bits)}, func() any { return M.F_probe_pos_mk(M.Bools(bits)) }, c(P.F_probe_pos_mk(P.Bools(bits))))
	}
	for _, tag := range []int64{0, 1, 2, 3} {
		for _, p := range pos2 {
			agree(t, "probe_n_mk", []any{tag, p}, func() any { return M.F_probe_n_mk(tag, p) }, c(P.F_probe_n_mk(P.Nat(tag), P.Pos(p))))
			agree(t, "probe_z_mk", []any{tag, p}, func() any { return M.F_probe_z_mk(tag, p) }, c(P.F_probe_z_mk(P.Nat(tag), P.Pos(p))))
		}
	}
}
