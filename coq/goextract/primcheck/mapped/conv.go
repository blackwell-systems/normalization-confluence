package mapped

import (
	"strconv"

	"github.com/blackwell-systems/normalization-confluence/coq/goextract/primcheck/plain"
)

// Conversions for primcheck on the int64 representation ExtrGo.v maps to.

// Bools is the list bs.
func Bools(bs []bool) *I_list[bool] {
	l := K_Nil[bool]()
	for i := len(bs) - 1; i >= 0; i-- {
		l = K_Cons(bs[i], l)
	}
	return l
}

// Cmp is the comparison named Eq, Lt or Gt.
func Cmp(c string) *I_comparison {
	return map[string]*I_comparison{"Eq": C_Eq, "Lt": C_Lt, "Gt": C_Gt}[c]
}

// Canon turns a result into int64, bool, string (comparison), []any (list) or
// [2]any (pair), as plain.Canon does.
func Canon(x any) any {
	switch v := x.(type) {
	case plain.Num, string, []any, [2]any:
		return v
	case int64:
		return plain.Num(strconv.FormatInt(v, 10))
	case bool:
		return v
	case *I_comparison:
		return []string{"Eq", "Lt", "Gt"}[v.tag]
	case *I_list[bool]:
		out := []any{}
		for ; v.tag == 1; v = v.f1_1 {
			out = append(out, v.f1_0)
		}
		return out
	case *I_prod[int64, int64]:
		return [2]any{Canon(v.f0_0), Canon(v.f0_1)}
	case *I_prod[int64, bool]:
		return [2]any{Canon(v.f0_0), v.f0_1}
	}
	panic("mapped.Canon: unexpected type")
}
