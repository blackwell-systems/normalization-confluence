#!/usr/bin/env python3
"""Strong-fairness counts for every n = 3 profile (robustness check beyond the committed claim).
A profile counts when some set of unstable matchings carries a strongly fair cycle (every pair
that blocks somewhere on the cycle is resolved on it); see strong_fair_sets in p2ref.py."""
from itertools import permutations, product
from collections import Counter
from p2ref import Market, analyse, strong_fair_sets

n = 3
perms = list(permutations(range(n)))
c = Counter()
for mp in product(perms, repeat=n):
    for wp in product(perms, repeat=n):
        mk = Market([list(p) for p in mp], [list(p) for p in wp])
        sm, fair, comps = analyse(mk)
        k = len(sm)
        c[(k, "profiles")] += 1
        c[(k, "fair")] += bool(fair)
        sf = strong_fair_sets(mk)
        c[(k, "strong")] += bool(sf)
        assert not sf or fair  # strong fairness implies pair-fairness
for key in sorted(c):
    print(key, c[key])
