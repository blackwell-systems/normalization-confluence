"""Abstract forest-token game (a relaxation of a closed K-token run).
Configuration: a forest o (o[j] = out-neighbour of j or -1; acyclic) and a token set U, |U| = K.
Move: fire v in U whose out-neighbour w = o[v] exists and is not in U. Then U' = U - v + w and the
new forest o' satisfies the square rule (derived from (B) at x, flip v x, flip j x, flip j flip v x):
   o'[v] = w, o'[w] = o[w], and for every other j: o'[j] = o[j] or w in {o[j], o'[j]}.
With REFINE (no self-loop at flip j x as well): an arc into v is kept (o[j] = v gives o'[j] = v),
and an arc into w is never redirected to v.
The new forest must be acyclic ((A) at the next run state).
A closed K-token run of a real network projects to a cycle of this graph. If the graph has no
cycle, the relaxation alone proves the claim.
Usage: game.py n K"""
import sys, itertools
from collections import defaultdict

def forests(n):
    out = []
    for o in itertools.product(range(-1, n), repeat=n):
        if any(o[j] == j for j in range(n)): continue
        ok = True
        for j in range(n):
            seen = set(); u = j
            while u != -1:
                if u in seen: ok = False; break
                seen.add(u); u = o[u]
            if not ok: break
        if ok: out.append(o)
    return out

def acyclic(o):
    n = len(o)
    for j in range(n):
        seen = set(); u = j
        while u != -1:
            if u in seen: return False
            seen.add(u); u = o[u]
    return True

REFINE = True

def moves(o, U, n):
    for v in U:
        w = o[v]
        if w == -1 or w in U: continue
        U2 = tuple(sorted(set(U) - {v} | {w}))
        opts = []
        for j in range(n):
            if j == v: opts.append([w]); continue
            if j == w: opts.append([o[w]]); continue
            # square rule with b' = o_{flip j x}(v) != v (no self-loop at flip j x):
            #   o'[j] = o[j] (b' = w); or o[j] = w and o'[j] = b' not in {v, j};
            #   or o'[j] = w and b' = o[j] != v
            if o[j] == w: opts.append([t for t in range(-1, n) if t != j and (t != v or not REFINE)])
            elif o[j] == v and REFINE: opts.append([v])
            else: opts.append(sorted({o[j], w} - {j}))
        for o2 in itertools.product(*opts):
            if acyclic(o2): yield v, o2, U2

if __name__ == "__main__":
    n = int(sys.argv[1]); K = int(sys.argv[2])
    F = forests(n)
    nodes = [(o, U) for o in F for U in itertools.combinations(range(n), K)]
    idx = {nd: i for i, nd in enumerate(nodes)}
    adj = [[] for _ in nodes]
    for i, (o, U) in enumerate(nodes):
        for v, o2, U2 in moves(o, U, n):
            adj[i].append(idx[(o2, U2)])
    # iterative Tarjan
    index = [None] * len(nodes); low = [0] * len(nodes); on = [False] * len(nodes); st = []; c = 0; comps = []
    for s in range(len(nodes)):
        if index[s] is not None: continue
        work = [(s, 0)]
        while work:
            u, k = work.pop()
            if k == 0:
                index[u] = low[u] = c; c += 1; st.append(u); on[u] = True
            rec = False
            for kk in range(k, len(adj[u])):
                w = adj[u][kk]
                if index[w] is None:
                    work.append((u, kk + 1)); work.append((w, 0)); rec = True; break
                elif on[w]: low[u] = min(low[u], index[w])
            if rec: continue
            if low[u] == index[u]:
                comp = []
                while True:
                    w = st.pop(); on[w] = False; comp.append(w)
                    if w == u: break
                comps.append(comp)
            if work:
                p = work[-1][0]; low[p] = min(low[p], low[u])
    big = [cp for cp in comps if len(cp) > 1]
    print("n", n, "K", K, "configs", len(nodes), "edges", sum(map(len, adj)), "cyclic SCCs", len(big))
    if big:
        cp = min(big, key=len); print("smallest cyclic SCC size", len(cp))
        for i in cp[:12]: print("  ", nodes[i])
