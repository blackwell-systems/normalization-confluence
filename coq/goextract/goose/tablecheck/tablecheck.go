// SPIKE (spike/go-extraction): Route A sketch. The table check written by hand in
// the Goose subset, for translation by Goose and a refinement proof against
// check_tables (TableCheck.v) in Perennial. Not verified.
//
// Tables are flat: nf has n entries; t has nE*n entries, row e at t[e*n:(e+1)*n];
// the declared pairs are (pa[i], pb[i]). The caller expands "every pair".
package tablecheck

func inV(n uint64, nf []uint64, x uint64) bool {
	if x >= n {
		return false
	}
	return nf[x] == x
}

// CheckTables decides check_tables' property: declared pairs name events below
// nE; NF and every step land on valid states; every declared pair commutes on
// the valid states and the zero state.
func CheckTables(n uint64, nE uint64, nf []uint64, t []uint64, pa []uint64, pb []uint64) bool {
	if uint64(len(nf)) != n || len(pa) != len(pb) {
		return false
	}
	if nE != 0 && uint64(len(t))/nE != n {
		return false
	}
	if uint64(len(t)) != n*nE {
		return false
	}
	for i := 0; i < len(pa); i++ {
		if pa[i] >= nE || pb[i] >= nE {
			return false
		}
	}
	for s := uint64(0); s < n; s++ {
		if !inV(n, nf, nf[s]) {
			return false
		}
		for e := uint64(0); e < nE; e++ {
			if !inV(n, nf, t[e*n+s]) {
				return false
			}
		}
		if nf[s] == s || s == 0 {
			for i := 0; i < len(pa); i++ {
				a := pa[i]
				b := pb[i]
				if t[a*n+t[b*n+s]] != t[b*n+t[a*n+s]] {
					return false
				}
			}
		}
	}
	return true
}
