package oracle

// The generated check_fast against a direct Go reading of check_tables
// (TableCheck.v), at every trie depth up to 2^20 states, with corruptions at
// the trie's boundary indices (16^k - 1, 16^k, 16^k + 1, n - 1). Contributed by
// the adversarial review of the Go oracle.
//
// go test runs the deterministic cases, including rejections at trie depth 3
// and 4 and at 2^20 states (skipped with -short). GOEXTRACT_LONG=1 adds the
// random sweep with repetitions at every size; the goextract workflow runs it
// nightly.

import (
	"math/rand"
	"os"
	"testing"
)

func lst[A any](xs []A) *I_list[A] {
	l := K_Nil[A]()
	for i := len(xs) - 1; i >= 0; i-- {
		l = K_Cons(xs[i], l)
	}
	return l
}

// fast runs the generated check_fast. pairs nil means every pair.
func fast(n, ne int, nf []int64, rows [][]int64, pairs [][2]int64) bool {
	rs := make([]*I_list[int64], ne)
	for e := range rows {
		rs[e] = lst(rows[e])
	}
	p := K_None[*I_list[*I_prod[int64, int64]]]()
	if pairs != nil {
		ps := make([]*I_prod[int64, int64], len(pairs))
		for i, q := range pairs {
			ps[i] = K_Pair(q[0], q[1])
		}
		p = K_Some(lst(ps))
	}
	return F_check_fast(int64(n), int64(ne), lst(nf), lst(rs), p)
}

// reference is check_tables read directly: declared pairs name events below
// nE; every NF entry and every step is a valid state; every declared pair
// commutes on the valid states and the zero state.
func reference(n, ne int, nf []int64, rows [][]int64, pairs [][2]int64) bool {
	inV := func(x int64) bool { return x < int64(n) && nf[x] == x }
	ps := pairs
	if ps == nil {
		for i := 0; i < ne; i++ {
			for j := i + 1; j < ne; j++ {
				ps = append(ps, [2]int64{int64(i), int64(j)})
			}
		}
	}
	for _, q := range ps {
		if q[0] >= int64(ne) || q[1] >= int64(ne) {
			return false
		}
	}
	for s := 0; s < n; s++ {
		if !inV(nf[s]) {
			return false
		}
		for e := 0; e < ne; e++ {
			if !inV(rows[e][s]) {
				return false
			}
		}
	}
	T := func(e, s int64) int64 {
		if s < int64(n) {
			return rows[e][s]
		}
		return 0
	}
	for s := 0; s < n; s++ {
		if !(nf[s] == int64(s) || s == 0) {
			continue
		}
		for _, q := range ps {
			if T(q[0], T(q[1], int64(s))) != T(q[1], T(q[0], int64(s))) {
				return false
			}
		}
	}
	return true
}

// machine: n states as (x, y) with x < X; even events bump x, odd events bump
// y, both modulo, so every pair commutes.
func machine(r *rand.Rand, n, ne int) ([]int64, [][]int64) {
	X := 1 + r.Intn(n)
	for n%X != 0 {
		X = 1 + r.Intn(n)
	}
	Y := n / X
	nf := make([]int64, n)
	for s := range nf {
		nf[s] = int64(s)
	}
	rows := make([][]int64, ne)
	for e := range rows {
		rows[e] = make([]int64, n)
		k := 1 + e/2
		for s := 0; s < n; s++ {
			x, y := s%X, s/X
			if e%2 == 0 {
				x = (x + k) % X
			} else {
				y = (y + k) % Y
			}
			rows[e][s] = int64(y*X + x)
		}
	}
	return nf, rows
}

// boundaries are the indices where the 16-ary trie changes depth or child.
func boundaries(n int) []int {
	var out []int
	for _, b := range []int{0, 1, 15, 16, 17, 255, 256, 257, 4095, 4096, 4097, 65535, 65536, 65537, n / 2, n - 2, n - 1} {
		if b >= 0 && b < n {
			out = append(out, b)
		}
	}
	return out
}

func pick(r *rand.Rand, n int) int {
	if r.Intn(2) == 0 {
		b := boundaries(n)
		return b[r.Intn(len(b))]
	}
	return r.Intn(n)
}

// corrupt applies one of four corruptions at state s. Each makes check_tables
// reject (on an otherwise convergent machine with s valid and nonzero, or for
// kind 3 any s).
func corrupt(kind int, n int, nf []int64, rows [][]int64, s int, r *rand.Rand) {
	switch kind {
	case 0: // a step to a state that is not valid: the out-of-range id n
		rows[0][s] = int64(n)
	case 1: // NF lands on a state that is not valid
		v := (s + 1) % n
		nf[v] = int64((v + 1) % n)
		if nf[v] == int64(v) {
			nf[v] = int64(n)
		}
	case 2: // NF points past the states
		nf[s] = int64(n)
	case 3: // two events stop commuting at s: e0 jumps to a valid state other
		// than its own target
		rows[0][s] = int64((int(rows[0][s]) + 1) % n)
	}
	_ = r
}

func agreeOn(t *testing.T, what string, n, ne int, nf []int64, rows [][]int64, pairs [][2]int64) bool {
	t.Helper()
	want := reference(n, ne, nf, rows, pairs)
	if got := fast(n, ne, nf, rows, pairs); got != want {
		t.Errorf("%s (n=%d, nE=%d, pairs=%v): check_fast=%v, check_tables=%v", what, n, ne, pairs, got, want)
	}
	return want
}

// Rejections at trie depths 0 to 4: every corruption at every boundary index.
func TestBigDifferentialBoundaries(t *testing.T) {
	sizes := []int{1, 2, 15, 16, 17, 255, 256, 257, 4095, 4096, 4097, 65535, 65536, 65537}
	if !testing.Short() {
		sizes = append(sizes, 1<<20)
	}
	r := rand.New(rand.NewSource(1))
	for _, n := range sizes {
		rejected := 0
		idx := boundaries(n)
		if n == 1<<20 {
			idx = []int{4097, 65537, n - 1} // depth 3, 4 and the last state
		}
		for kind := 0; kind < 4; kind++ {
			for _, s := range idx {
				nf, rows := machine(rand.New(rand.NewSource(int64(n))), n, 2)
				corrupt(kind, n, nf, rows, s, r)
				if !agreeOn(t, "boundary corruption", n, 2, nf, rows, nil) {
					rejected++
				}
			}
		}
		nf, rows := machine(rand.New(rand.NewSource(int64(n))), n, 2)
		if !agreeOn(t, "uncorrupted", n, 2, nf, rows, nil) {
			t.Errorf("n=%d: the uncorrupted machine is rejected", n)
		}
		if n >= 4097 && rejected == 0 {
			t.Errorf("n=%d: no corruption was rejected (the cases do not reach depth >= 3)", n)
		}
	}
}

// The random sweep from the review, with repetitions at every size.
func TestBigDifferentialSweep(t *testing.T) {
	if os.Getenv("GOEXTRACT_LONG") == "" {
		t.Skip("set GOEXTRACT_LONG=1 (the nightly run does)")
	}
	r := rand.New(rand.NewSource(7))
	sizes := []int{1, 2, 15, 16, 17, 255, 256, 257, 4095, 4096, 4097, 65535, 65536, 65537, 1 << 20}
	agree, acc := 0, 0
	for _, n := range sizes {
		reps := 12
		if n >= 65535 {
			reps = 4
		}
		for rep := 0; rep < reps; rep++ {
			ne := 1 + r.Intn(3)
			nf, rows := machine(r, n, ne)
			var pairs [][2]int64
			if r.Intn(2) == 0 {
				pairs = [][2]int64{}
				for i := 0; i < r.Intn(4); i++ {
					pairs = append(pairs, [2]int64{int64(r.Intn(ne)), int64(r.Intn(ne))})
				}
			}
			switch r.Intn(5) {
			case 0:
				rows[r.Intn(ne)][pick(r, n)] = int64(pick(r, n))
			case 1:
				s := pick(r, n)
				if s != 0 {
					nf[s] = 0
					for e := range rows {
						for k := range rows[e] {
							if rows[e][k] == int64(s) {
								rows[e][k] = 0
							}
						}
					}
					if r.Intn(2) == 0 {
						rows[r.Intn(ne)][pick(r, n)] = int64(s)
					}
				}
			case 2:
				nf[pick(r, n)] = int64(pick(r, n))
			case 3:
				rows[r.Intn(ne)][pick(r, n)] = int64(n + r.Intn(3))
			}
			if agreeOn(t, "random", n, ne, nf, rows, pairs) {
				acc++
			}
			agree++
		}
	}
	t.Logf("%d cases, %d accepted", agree, acc)
}
