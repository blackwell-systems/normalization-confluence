#!/usr/bin/env python3
"""Run the reference checker on every n = 3 profile (no symmetry reduction). Slow (minutes)."""
import sys
from itertools import permutations, product
from collections import Counter
from p2ref import Market, analyse

n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
perms = list(permutations(range(n)))
stats = Counter()
witnesses = []
for mp in product(perms, repeat=n):
    for wp in product(perms, repeat=n):
        sm, fair, comps = analyse(Market([list(p) for p in mp], [list(p) for p in wp]))
        k = len(sm)
        stats["profiles"] += 1
        stats[f"stable={k}"] += 1
        if comps:
            stats[f"stable={k},cycle"] += 1
        if fair:
            stats[f"stable={k},faircycle"] += 1
            if k == 1 and len(witnesses) < 5:
                witnesses.append((mp, wp))
for key in sorted(stats):
    print(key, stats[key])
print("unique-stable fair witnesses:", witnesses)
