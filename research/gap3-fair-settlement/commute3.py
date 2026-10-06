"""Checks for the rearrangement template on sampled networks (K = 3 tokens).
  C1 (commutation): for consecutive count-preserving moves x -(v1->w1)-> y -(v2->w2)-> z, the
     swapped order (v2 then v1 from x) is a run with 3 tokens throughout iff v2 != w1 and
     w2 != v1. (Same token twice, or the second token moves into the vertex the first one left.)
  C2 (synchronous step by single firings): at every 3-token state some order of U(x) fires each
     token once, each still unstable when fired, so F(x) is reached.
Usage: commute3.py file.json [...]"""
import sys, json, itertools
from collections import Counter
import verify as V
from stats3 import out_nb
C = Counter()
for f in sys.argv[1:]:
    for item in json.load(open(f)):
        tt = item["tt"]; n = len(tt); N = 1 << n
        cnt = lambda x: len(V.unstable(tt, n, x))
        for x in range(N):
            U = V.unstable(tt, n, x)
            if len(U) != 3: continue
            ok2 = False
            for order in itertools.permutations(U):
                y = x; good = True
                for u in order:
                    if u not in V.unstable(tt, n, y): good = False; break
                    y ^= 1 << u
                if good: ok2 = True; break
            C["C2 ok" if ok2 else "C2 FAIL"] += 1
            for v1 in U:
                y = x ^ (1 << v1)
                if cnt(y) != 3: continue
                w1 = out_nb(tt, n, x, v1)
                for v2 in V.unstable(tt, n, y):
                    z = y ^ (1 << v2)
                    if cnt(z) != 3: continue
                    w2 = out_nb(tt, n, y, v2)
                    legal = v2 in U and v1 in V.unstable(tt, n, x ^ (1 << v2)) and cnt(x ^ (1 << v2)) == 3
                    pred = v2 != w1 and w2 != v1
                    C["C1 ok" if legal == pred else "C1 FAIL"] += 1
                    if not pred: C["C1 blocked: " + ("same token" if v2 == w1 else "follow (w2 = v1)")] += 1
for k, c in sorted(C.items()): print(k, c)
