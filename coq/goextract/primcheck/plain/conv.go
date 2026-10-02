package plain

import "math/big"

// Conversions between int64 and the inductive representation the plain
// extraction computes on (unary nat, binary positive), for primcheck. They use
// only the generated constructors and the tags fixed by the Rocq declarations.

// Nat is n in unary.
func Nat(n int64) *I_nat {
	r := K_O()
	for ; n > 0; n-- {
		r = K_S(r)
	}
	return r
}

// Pos is p >= 1 in binary.
func Pos(p int64) *I_positive { return posU(uint64(p)) }

func posU(p uint64) *I_positive {
	if p == 1 {
		return K_XH()
	}
	if p%2 == 0 {
		return K_XO(posU(p / 2))
	}
	return K_XI(posU(p / 2))
}

// N is n >= 0.
func N(n int64) *I_n {
	if n == 0 {
		return K_N0()
	}
	return K_Npos(Pos(n))
}

// Z is z.
func Z(z int64) *I_z {
	switch {
	case z == 0:
		return K_Z0()
	case z > 0:
		return K_Zpos(Pos(z))
	}
	return K_Zneg(posU(uint64(-(z + 1)) + 1)) // -z overflows at the int64 minimum
}

// Bool is b.
func Bool(b bool) *I_bool {
	if b {
		return K_True()
	}
	return K_False()
}

// Bools is the list bs.
func Bools(bs []bool) *I_list[*I_bool] {
	l := K_Nil[*I_bool]()
	for i := len(bs) - 1; i >= 0; i-- {
		l = K_Cons(Bool(bs[i]), l)
	}
	return l
}

// Cmp is the comparison named Eq, Lt or Gt.
func Cmp(c string) *I_comparison {
	return map[string]*I_comparison{"Eq": K_Eq(), "Lt": K_Lt(), "Gt": K_Gt()}[c]
}

// Canon turns a result into a canonical value: a number as Num (exact, not
// bounded by int64), a bool, a comparison as "Eq", "Lt" or "Gt", a list as
// []any, a pair as [2]any.
func Canon(x any) any {
	switch v := x.(type) {
	case *I_nat:
		var n int64
		for ; v.tag == 1; v = v.f1_0 {
			n++
		}
		return Num(big.NewInt(n).String())
	case *I_positive:
		return Num(pos(v).String())
	case *I_n:
		if v.tag == 0 {
			return Num("0")
		}
		return Num(pos(v.f1_0).String())
	case *I_z:
		switch v.tag {
		case 0:
			return Num("0")
		case 1:
			return Num(pos(v.f1_0).String())
		}
		return Num(new(big.Int).Neg(pos(v.f2_0)).String())
	case *I_bool:
		return v.tag == 0
	case *I_comparison:
		return []string{"Eq", "Lt", "Gt"}[v.tag]
	case *I_list[*I_bool]:
		out := []any{}
		for ; v.tag == 1; v = v.f1_1 {
			out = append(out, Canon(v.f1_0))
		}
		return out
	case *I_prod[*I_nat, *I_positive]:
		return [2]any{Canon(v.f0_0), Canon(v.f0_1)}
	case *I_prod[*I_nat, *I_bool]:
		return [2]any{Canon(v.f0_0), Canon(v.f0_1)}
	}
	panic("plain.Canon: unexpected type")
}

// Num is an exact integer, in decimal.
type Num string

func pos(v *I_positive) *big.Int {
	switch v.tag {
	case 0:
		r := new(big.Int).Lsh(pos(v.f0_0), 1)
		return r.Add(r, big.NewInt(1))
	case 1:
		return new(big.Int).Lsh(pos(v.f1_0), 1)
	}
	return big.NewInt(1)
}
