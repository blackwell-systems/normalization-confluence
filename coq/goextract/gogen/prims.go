package main

import "fmt"

// The Go meaning of every symbol ExtrGo.v introduces. These definitions and the
// mapped types below are the only hand-written semantics in the output.
//
// Numbers (nat, positive, N, Z) are int64. Every operation that can leave the
// int64 range panics instead of wrapping ("checked" arithmetic), so a result is
// either the exact mathematical value or the run stops: a gate built on the
// output fails closed. A match on a value its type cannot hold (a negative nat,
// a positive below 1) matches no branch and panics too.

// mappedType is an inductive mapped to a Go type by ExtrGo.v.
type mappedType struct {
	goType string
	ctors  map[string]*mappedCtor
}

type mappedCtor struct {
	arity int
	// build returns a Go expression for the constructor applied to args.
	build func(args []string) string
	// konst folds the constructor applied to constant args, if it can.
	konst func(args []int64) (int64, bool)
	// cond is a Go condition true exactly when s was built by this constructor.
	cond func(s string) string
	// proj returns Go expressions for the constructor's arguments, given cond.
	proj func(s string) []string
}

func fixed(v int64) *mappedCtor {
	return &mappedCtor{
		build: func([]string) string { return fmt.Sprintf("int64(%d)", v) },
		konst: func([]int64) (int64, bool) { return v, true },
		cond:  func(s string) string { return fmt.Sprintf("%s == %d", s, v) },
		proj:  func(string) []string { return nil },
	}
}

const maxInt64 = int64(^uint64(0) >> 1)

var mappedTypes = map[string]*mappedType{
	"go_bool": {"bool", map[string]*mappedCtor{
		"true": {build: func([]string) string { return "true" }, cond: func(s string) string { return s },
			proj: func(string) []string { return nil }},
		"false": {build: func([]string) string { return "false" }, cond: func(s string) string { return "!" + s },
			proj: func(string) []string { return nil }},
	}},
	"go_nat": {"int64", map[string]*mappedCtor{
		"nat_0": fixed(0),
		"nat_succ": {arity: 1,
			build: func(a []string) string { return "natSucc(" + a[0] + ")" },
			konst: func(a []int64) (int64, bool) { return a[0] + 1, a[0] >= 0 && a[0] < maxInt64 },
			cond:  func(s string) string { return s + " > 0" },
			proj:  func(s string) []string { return []string{s + " - 1"} }},
	}},
	"go_pos": {"int64", map[string]*mappedCtor{
		"pos_xI": {arity: 1,
			build: func(a []string) string { return "posXI(" + a[0] + ")" },
			konst: func(a []int64) (int64, bool) { return 2*a[0] + 1, a[0] >= 1 && a[0] < maxInt64/2 },
			cond:  func(s string) string { return s + " > 1 && " + s + "%2 == 1" },
			proj:  func(s string) []string { return []string{s + " / 2"} }},
		"pos_xO": {arity: 1,
			build: func(a []string) string { return "posXO(" + a[0] + ")" },
			konst: func(a []int64) (int64, bool) { return 2 * a[0], a[0] >= 1 && a[0] <= maxInt64/2 },
			cond:  func(s string) string { return s + " > 1 && " + s + "%2 == 0" },
			proj:  func(s string) []string { return []string{s + " / 2"} }},
		"pos_xH": fixed(1),
	}},
	"go_n": {"int64", map[string]*mappedCtor{
		"n_0": fixed(0),
		"n_pos": {arity: 1,
			build: func(a []string) string { return a[0] },
			konst: func(a []int64) (int64, bool) { return a[0], true },
			cond:  func(s string) string { return s + " > 0" },
			proj:  func(s string) []string { return []string{s} }},
	}},
	"go_z": {"int64", map[string]*mappedCtor{
		"z_0": fixed(0),
		"z_pos": {arity: 1,
			build: func(a []string) string { return a[0] },
			konst: func(a []int64) (int64, bool) { return a[0], true },
			cond:  func(s string) string { return s + " > 0" },
			proj:  func(s string) []string { return []string{s} }},
		"z_neg": {arity: 1,
			build: func(a []string) string { return "zOpp(" + a[0] + ")" },
			konst: func(a []int64) (int64, bool) { return -a[0], a[0] > 0 },
			cond:  func(s string) string { return s + " < 0" },
			proj:  func(s string) []string { return []string{"zOpp(" + s + ")"} }},
	}},
}

// prims maps each prim_* symbol to its arity and Go function. prim_andb has no
// function: gogen compiles it to a short-circuit &&.
var prims = map[string]struct {
	arity int
	fn    string
}{
	"prim_andb":             {2, ""},
	"prim_nat_add":          {2, "zAdd"},
	"prim_nat_sub":          {2, "natSub"},
	"prim_nat_mul":          {2, "zMul"},
	"prim_nat_eqb":          {2, "eqb"},
	"prim_nat_compare":      {2, "compare"},
	"prim_nat_ltb":          {2, "ltb"},
	"prim_nat_div2":         {1, "natDiv2"},
	"prim_pos_add":          {2, "zAdd"},
	"prim_pos_succ":         {1, "natSucc"},
	"prim_pos_pred":         {1, "posPred"},
	"prim_pos_sub":          {2, "posSub"},
	"prim_pos_mul":          {2, "zMul"},
	"prim_pos_min":          {2, "min64"},
	"prim_pos_max":          {2, "max64"},
	"prim_pos_compare":      {2, "compare"},
	"prim_pos_compare_cont": {3, "compareCont"},
	"prim_n_add":            {2, "zAdd"},
	"prim_n_succ":           {1, "natSucc"},
	"prim_n_pred":           {1, "nPred"},
	"prim_n_sub":            {2, "natSub"},
	"prim_n_mul":            {2, "zMul"},
	"prim_n_min":            {2, "min64"},
	"prim_n_max":            {2, "max64"},
	"prim_n_div":            {2, "nDiv"},
	"prim_n_modulo":         {2, "nModulo"},
	"prim_n_compare":        {2, "compare"},
	"prim_z_add":            {2, "zAdd"},
	"prim_z_succ":           {1, "zSucc"},
	"prim_z_pred":           {1, "zPred"},
	"prim_z_sub":            {2, "zSub"},
	"prim_z_mul":            {2, "zMul"},
	"prim_z_opp":            {1, "zOpp"},
	"prim_z_abs":            {1, "zAbs"},
	"prim_z_min":            {2, "min64"},
	"prim_z_max":            {2, "max64"},
	"prim_z_compare":        {2, "compare"},
	"prim_z_of_n":           {1, "id64"},
	"prim_z_abs_n":          {1, "zAbs"},
}

// runtime is appended to every generated file. Each function is total on the
// values its Rocq counterpart accepts, and panics where int64 would wrap.
const runtime = `
// ===== the Go meaning of ExtrGo.v's symbols (gogen prims.go) =====

const minInt64 = -1 << 63

func zAdd(a, b int64) int64 {
	r := a + b
	if (a > 0 && b > 0 && r < 0) || (a < 0 && b < 0 && r >= 0) {
		panic("gogen: int64 overflow in add")
	}
	return r
}

func zSub(a, b int64) int64 {
	r := a - b
	if (b < 0 && r < a) || (b > 0 && r > a) {
		panic("gogen: int64 overflow in sub")
	}
	return r
}

func zMul(a, b int64) int64 {
	if a == 0 || b == 0 {
		return 0
	}
	r := a * b
	if r/b != a || (a == -1 && b == minInt64) || (b == -1 && a == minInt64) {
		panic("gogen: int64 overflow in mul")
	}
	return r
}

func zOpp(a int64) int64 {
	if a == minInt64 {
		panic("gogen: int64 overflow in opp")
	}
	return -a
}

func zAbs(a int64) int64 {
	if a < 0 {
		return zOpp(a)
	}
	return a
}

func zSucc(a int64) int64 { return zAdd(a, 1) }
func zPred(a int64) int64 { return zSub(a, 1) }
func natSucc(a int64) int64 { return zAdd(a, 1) }
func posXI(p int64) int64 { return zAdd(zMul(2, p), 1) }
func posXO(p int64) int64 { return zMul(2, p) }

func natSub(a, b int64) int64 {
	if a <= b {
		return 0
	}
	return a - b
}

func posSub(a, b int64) int64 {
	if a <= b {
		return 1
	}
	return a - b
}

func posPred(a int64) int64 {
	if a <= 1 {
		return 1
	}
	return a - 1
}

func nPred(a int64) int64 {
	if a <= 0 {
		return 0
	}
	return a - 1
}

func nDiv(a, b int64) int64 {
	if b == 0 {
		return 0
	}
	return a / b
}

func nModulo(a, b int64) int64 {
	if b == 0 {
		return a
	}
	return a % b
}

func natDiv2(a int64) int64 { return a / 2 }

func min64(a, b int64) int64 {
	if a < b {
		return a
	}
	return b
}

func max64(a, b int64) int64 {
	if a > b {
		return a
	}
	return b
}

func id64(a int64) int64 { return a }

func eqb(a, b int64) bool { return a == b }

func ltb(a, b int64) bool { return a < b }

func compare(a, b int64) *I_comparison {
	if a == b {
		return C_Eq
	}
	if a < b {
		return C_Lt
	}
	return C_Gt
}

func compareCont(c *I_comparison, a, b int64) *I_comparison {
	if a == b {
		return c
	}
	return compare(a, b)
}
`
