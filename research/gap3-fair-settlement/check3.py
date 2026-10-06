"""Check the k = 3 structural facts stated in K3.md on sampled networks (independent of SAT).
  F1  at a state with exactly 3 tokens, at most one is bad (non-expansiveness at p)
  F2  at a (2,1) state, every vertex j of D(x) points into M = F(x) xor p or nowhere
  F3  along random descending paths x -> p (flipping D), #zero steps + 2 #up steps = g - b
  F4  square rule on every move that passes a token v -> w: the out-arcs of v and of w are kept,
      and any other vertex j changes its out-arc only if w is its old or its new target
  F5  an arc into the fired vertex is kept; an arc into w is never redirected to v
  F6  the out-path of the receiver w is the same at x and at flip v x
  F7  token-to-token arcs at (2,1) states: the bad token points at a good token (the K2 swap
      T-then-H fails), a good token points at the bad one (H-then-T fails)
Usage: check3.py file.json [...]"""
import sys, json, random
from collections import Counter
import verify as V
from stats3 import fixed_points, out_nb, path_from
C = Counter(); rnd = random.Random(1)
for f in sys.argv[1:]:
    for item in json.load(open(f)):
        tt = item["tt"] if isinstance(item, dict) else item; n = len(tt); N = 1 << n
        fp = fixed_points(tt, n)
        if len(fp) != 1: C["no unique fixed point"] += 1; continue
        p = fp[0]
        Fx = lambda x: sum(tt[i][x] << i for i in range(n))
        for x in range(N):
            U = V.unstable(tt, n, x)
            D = x ^ p; Ds = {i for i in range(n) if (D >> i) & 1}
            o = [out_nb(tt, n, x, j) for j in range(n)]
            if len(U) == 3:
                g = sum(1 for u in U if u in Ds); b = 3 - g
                C["F1 ok" if b <= 1 else "F1 FAIL"] += 1
                M = Fx(x) ^ p
                if b == 1:
                    ok = all(o[j] is None or (M >> o[j]) & 1 for j in Ds)
                    C["F2 ok" if ok else "F2 FAIL"] += 1
                    bad = [u for u in U if u not in Ds][0]
                    C["F7 (2,1) states"] += 1
                    if o[bad] in U: C["F7 bad token points at a good token"] += 1
                    if any(o[u] == bad for u in U if u in Ds): C["F7 a good token points at the bad token"] += 1
                # F3 on a few random descending paths
                for _ in range(3):
                    order = list(Ds); rnd.shuffle(order); y = x; zero = up = 0
                    for j in order:
                        t = out_nb(tt, n, y, j); m = Fx(y) ^ p
                        if t is None: zero += 1
                        elif not (m >> t) & 1: up += 1
                        y ^= 1 << j
                    C["F3 ok" if zero + 2 * up == g - b else "F3 FAIL"] += 1
            for v in U:
                w = o[v]
                if w is None or w in U: continue
                y = x ^ (1 << v); o2 = [out_nb(tt, n, y, j) for j in range(n)]
                ok = o2[v] == w and o2[w] == o[w] and all(o2[j] == o[j] or w in (o[j], o2[j]) for j in range(n) if j not in (v, w))
                C["F4 ok" if ok else "F4 FAIL"] += 1
                ok = all(o2[j] == v for j in range(n) if o[j] == v and j != v) and all(o2[j] != v for j in range(n) if o[j] == w and j != v)
                C["F5 ok" if ok else "F5 FAIL"] += 1
                C["F6 ok" if path_from(tt, n, x, w) == path_from(tt, n, y, w) else "F6 FAIL"] += 1
for k, c in sorted(C.items()): print(k, c)
