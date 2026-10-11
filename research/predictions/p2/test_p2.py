#!/usr/bin/env python3
"""Sanity tests for the P2 search. Usage: python3 test_p2.py path/to/p2search  (about 30 s).

1. Known instances: the best-response cycle printed in Ackermann et al. (2011, Thm 3) is a
   blocking-pair cycle here; a cyclic 3-by-3 market has its 3 known stable matchings.
2. Stable matching counts: for every n = 3 profile, "exactly one stable matching" (counted over
   all 34 matchings) agrees with "man-optimal = woman-optimal" (Gale-Shapley both ways).
3. The C search and the Python reference agree: full-space counts for n = 2 and n = 3, and
   (k, cycle, fair) on 400 random n = 4 profiles.
4. The P2 instance: one stable matching, and the round-robin loop word returns to x through
   unstable matchings.
"""
import random
import subprocess
import sys
from collections import Counter
from itertools import permutations, product

from p2ref import Market, analyse, from_one_based, run

BIN = sys.argv[1] if len(sys.argv) > 1 else "./p2search"


def gale_shapley(prop, rec):
    """prop[i]: proposer i's list; rec[j]: receiver j's list. Returns partner of each proposer."""
    n = len(prop)
    rank = [{x: k for k, x in enumerate(l)} for l in rec]
    nxt, held, free = [0] * n, [-1] * n, list(range(n))
    while free:
        i = free.pop()
        j = prop[i][nxt[i]]
        nxt[i] += 1
        if held[j] < 0:
            held[j] = i
        elif rank[j][i] < rank[j][held[j]]:
            free.append(held[j])
            held[j] = i
        else:
            free.append(i)
    out = [-1] * n
    for j, i in enumerate(held):
        out[i] = j
    return out


def test_known():
    agmrv = from_one_based([[2, 3, 1], [1, 2, 3], [3, 1, 2]], [[1, 3, 2], [2, 1, 3], [1, 2, 3]])
    cyc = [(-1, 2, 3), (3, 2, -1), (3, 1, -1), (3, -1, 1), (2, -1, 1), (-1, 2, 1), (-1, 2, 3)]
    cyc = [tuple(v - 1 if v > 0 else -1 for v in c) for c in cyc]
    for a, b in zip(cyc, cyc[1:]):
        assert any(agmrv.update(a, m, w) == b for m in range(3) for w in range(3))
    sm, fair, comps = analyse(agmrv)
    assert len(sm) == 2 and fair
    # cyclic market: man i ranks w_i, w_i+1, w_i+2; woman j ranks m_j+1, m_j+2, m_j
    cyc3 = Market([[(i + k) % 3 for k in range(3)] for i in range(3)],
                  [[(j + 1 + k) % 3 for k in range(3)] for j in range(3)])
    sm, _, _ = analyse(cyc3)
    assert sorted(sm) == sorted([(0, 1, 2), (1, 2, 0), (2, 0, 1)]), sm
    print("known instances: ok")


def test_counts_vs_gs():
    perms = list(permutations(range(3)))
    for mp in product(perms, repeat=3):
        for wp in product(perms, repeat=3):
            mk = Market([list(p) for p in mp], [list(p) for p in wp])
            k = len([s for s in __import__("p2ref").matchings(3) if mk.stable(s)])
            mo = gale_shapley(mp, wp)
            wo = gale_shapley(wp, mp)
            wo_as_men = [-1] * 3
            for w, m in enumerate(wo):
                wo_as_men[m] = w
            assert (k == 1) == (mo == wo_as_men)
            assert mk.stable(tuple(mo)) and mk.stable(tuple(wo_as_men))
    print("n=3 uniqueness vs Gale-Shapley: ok")


def full_counts_python(n):
    perms = list(permutations(range(n)))
    c = Counter()
    for mp in product(perms, repeat=n):
        for wp in product(perms, repeat=n):
            sm, fair, comps = analyse(Market([list(p) for p in mp], [list(p) for p in wp]))
            k = len(sm)
            c[(k, "all")] += 1
            c[(k, "cyc")] += bool(comps)
            c[(k, "fair")] += bool(fair)
    return c


def full_counts_c(n):
    out = subprocess.run([BIN, str(n)], capture_output=True, text=True, check=True).stdout
    c = Counter()
    for line in out.splitlines():
        if line.startswith("k "):
            f = line.split()
            k = int(f[1])
            c[(k, "all")] = int(f[5])
            c[(k, "cyc")] = int(f[9])
            c[(k, "fair")] = int(f[13])
    return c


def test_c_vs_python():
    for n in (2, 3):
        a, b = full_counts_python(n), full_counts_c(n)
        a = Counter({k: v for k, v in a.items() if v})
        b = Counter({k: v for k, v in b.items() if v})
        assert a == b, (n, a, b)
    rnd = random.Random(2026)
    perms = list(permutations(range(4)))
    profs = [[rnd.choice(perms) for _ in range(8)] for _ in range(400)]
    inp = "\n".join(" ".join("".join(map(str, p)) for p in pr) for pr in profs) + "\n"
    out = subprocess.run([BIN, "check", "4"], input=inp, capture_output=True, text=True,
                         check=True).stdout.split("\n")
    for pr, line in zip(profs, out):
        sm, fair, comps = analyse(Market([list(p) for p in pr[:4]], [list(p) for p in pr[4:]]))
        assert line.split() == [str(len(sm)), str(int(bool(comps))), str(int(bool(fair)))], (pr, line)
    print("C vs Python (n=2, n=3 full; 400 random n=4): ok")


def test_instance():
    mk = Market([[0, 1, 2], [0, 1, 2], [1, 2, 0]], [[2, 0, 1], [1, 2, 0], [2, 0, 1]])
    sm, fair, _ = analyse(mk)
    assert sm == [(0, 1, 2)] and fair
    x, q = (2, -1, 0), [0, 2, 5, 7, 1, 8, 4, 3, 6]
    assert sorted(q) == list(range(9))
    assert run(mk, (-1, -1, -1), [2, 6]) == x and run(mk, x, q) == x
    assert all(not mk.stable(run(mk, x, q[:k])) for k in range(len(q)))
    print("P2 instance: ok")


if __name__ == "__main__":
    test_known()
    test_counts_vs_gs()
    test_c_vs_python()
    test_instance()
