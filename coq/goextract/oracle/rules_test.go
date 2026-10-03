package oracle

// The generated checkBuildC (step tables from the rules packed in blocks,
// what rulecheck runs) and checkBuildT (step tables in check_fast's cells)
// against the generated checkBuild (the pairwise rules check), on random
// machines. AstCompact.v and AstTables.v prove them equal on every machine and
// declaration (checkBuildC_eq, checkBuildT_eq); this checks gogen's
// translation of all three. The machines are
// not limited to what the front end admits: domains may be 0, variable
// indices may name no variable, and declared pairs may name events past the
// last. The test also requires both verdicts to occur, so the sweep covers
// rejections. GOEXTRACT_LONG=1 runs ten times as many machines.

import (
	"math/rand"
	"os"
	"testing"
)

type rgen struct{ r *rand.Rand }

func (g rgen) expr(nv, d int) *I_expr {
	if d <= 0 || g.r.Intn(10) < 4 {
		if g.r.Intn(10) < 6 {
			extra := 0
			if g.r.Intn(20) == 0 {
				extra = 2
			}
			return K_EVar(int64(g.r.Intn(nv + extra)))
		}
		if g.r.Intn(40) == 0 {
			return K_ELit([]int64{2147483647, -2147483647, 1073741824}[g.r.Intn(3)])
		}
		return K_ELit(int64(g.r.Intn(9) - 4))
	}
	if g.r.Intn(2) == 0 {
		return K_EAdd(g.expr(nv, d-1), g.expr(nv, d-1))
	}
	return K_ESub(g.expr(nv, d-1), g.expr(nv, d-1))
}

func (g rgen) pred(nv, d int) *I_pred {
	r := g.r.Intn(20)
	switch {
	case d <= 0 || r < 12:
		a, b := g.expr(nv, 1), g.expr(nv, 1)
		switch g.r.Intn(3) {
		case 0:
			return K_PLe(a, b)
		case 1:
			return K_PLt(a, b)
		}
		return K_PEq(a, b)
	case r < 15:
		return K_PNot(g.pred(nv, d-1))
	}
	ps := make([]*I_pred, g.r.Intn(3))
	for i := range ps {
		ps[i] = g.pred(nv, d-1)
	}
	if g.r.Intn(2) == 0 {
		return K_PAnd(lst(ps))
	}
	return K_POr(lst(ps))
}

func (g rgen) xform(nv int) *I_list[*I_prod[int64, *I_expr]] {
	as := make([]*I_prod[int64, *I_expr], 1+g.r.Intn(2))
	for i := range as {
		as[i] = K_Pair(int64(g.r.Intn(nv)), g.expr(nv, 2))
	}
	return lst(as)
}

func (g rgen) machine() (*I_machine, *I_option[*I_list[*I_prod[int64, int64]]]) {
	nv := 1 + g.r.Intn(3)
	doms, mins := make([]int64, nv), make([]int64, nv)
	for i := range doms {
		doms[i] = int64(1 + g.r.Intn(4))
		if g.r.Intn(50) == 0 {
			doms[i] = 0
		}
		if g.r.Intn(2) == 0 {
			mins[i] = int64(g.r.Intn(6) - 3)
		}
	}
	type rule = *I_prod[*I_pred, *I_list[*I_prod[int64, *I_expr]]]
	invs := make([]rule, g.r.Intn(3))
	for i := range invs {
		invs[i] = K_Pair(g.pred(nv, 1), g.xform(nv))
	}
	evs := make([]rule, 1+g.r.Intn(4))
	for i := range evs {
		guard := K_PAnd(K_Nil[*I_pred]())
		if g.r.Intn(2) == 0 {
			guard = g.pred(nv, 1)
		}
		evs[i] = K_Pair(guard, g.xform(nv))
	}
	p := K_None[*I_list[*I_prod[int64, int64]]]()
	if g.r.Intn(2) == 0 {
		ps := make([]*I_prod[int64, int64], g.r.Intn(4))
		for i := range ps {
			extra := 0
			if g.r.Intn(10) == 0 {
				extra = 1
			}
			ps[i] = K_Pair(int64(g.r.Intn(len(evs)+extra)), int64(g.r.Intn(len(evs))))
		}
		p = K_Some(lst(ps))
	}
	return K_Build_machine(lst(doms), lst(mins), lst(invs), lst(evs)), p
}

func TestCheckBuildTDifferential(t *testing.T) {
	count := 20000
	if os.Getenv("GOEXTRACT_LONG") != "" {
		count = 200000
	}
	for _, seed := range []int64{1, 2} {
		g := rgen{rand.New(rand.NewSource(seed))}
		verdicts := map[bool]int{}
		for i := 0; i < count; i++ {
			m, p := g.machine()
			old, tab, cmp := F_checkBuild(m, p), F_checkBuildT(m, p), F_checkBuildC(m, p)
			if old != tab || old != cmp {
				t.Fatalf("seed %d machine %d: checkBuild=%v checkBuildT=%v checkBuildC=%v", seed, i, old, tab, cmp)
			}
			verdicts[old]++
		}
		if verdicts[true] == 0 || verdicts[false] == 0 {
			t.Fatalf("seed %d: verdicts %v, want both", seed, verdicts)
		}
		t.Logf("seed %d: %d machines agree (%d accepted, %d rejected)", seed, count, verdicts[true], verdicts[false])
	}
}
