#!/usr/bin/env python3
"""Reference checker for prediction P2 (readable, slow).

Model (P2.md): n men, n women, complete strict preferences. A state is a matching (partial
allowed), stored as a tuple wife[m] in {-1, 0..n-1}. Labels are the n^2 pairs (m, w), label
index m*n + w. The update u_(m,w) matches m with w when (m, w) blocks (each is single or prefers
the other to the current partner); their former partners become single. Otherwise it is a no-op.

A bad fair lasso exists from some start iff some strongly connected component S of the state
graph (edges = updates that change the state) with at least one edge satisfies: for every pair j,
j is non-blocking at some state of S, or j labels an edge with both ends in S. Why this is exact:
  * Stable matchings are fixed by every label, so they are sinks; a nontrivial SCC has only
    unstable states, and a loop that visits a stable state never leaves it (not bad).
  * A loop word q that returns to its start traces a closed walk; its states lie in one SCC S.
    Each label j in q is either a no-op step (j non-blocking there) or a real step inside S.
  * Conversely, if S satisfies the condition, a closed walk through S that visits every chosen
    witness state and edge, with the no-op labels inserted at their witness states, is a loop
    word naming every pair, and every state of S is unstable.
  * The condition is monotone in S (fewer states, fewer witnesses), so no Emerson-Lei
    refinement below an SCC is needed: if the SCC fails a pair, every subset fails it too.
Every state is a possible start, so every SCC is reachable from some start.
"""
from itertools import permutations, product


def matchings(n):
    """All partial matchings of n men and n women, as tuples wife[m] (-1 = single)."""
    out = []

    def go(m, used, cur):
        if m == n:
            out.append(tuple(cur))
            return
        go(m + 1, used, cur + [-1])
        for w in range(n):
            if not used & (1 << w):
                go(m + 1, used | (1 << w), cur + [w])

    go(0, 0, [])
    return out


class Market:
    def __init__(self, mp, wp):
        """mp[m]: list of women, best first; wp[w]: list of men, best first."""
        self.n = n = len(mp)
        self.mp, self.wp = mp, wp
        self.rm = [[0] * n for _ in range(n)]
        self.rw = [[0] * n for _ in range(n)]
        for m in range(n):
            for k, w in enumerate(mp[m]):
                self.rm[m][w] = k
        for w in range(n):
            for k, m in enumerate(wp[w]):
                self.rw[w][m] = k

    def husbands(self, mu):
        h = [-1] * self.n
        for m, w in enumerate(mu):
            if w >= 0:
                h[w] = m
        return h

    def blocks(self, mu, m, w):
        h = self.husbands(mu)
        if mu[m] == w:
            return False
        okm = mu[m] < 0 or self.rm[m][w] < self.rm[m][mu[m]]
        okw = h[w] < 0 or self.rw[w][m] < self.rw[w][h[w]]
        return okm and okw

    def update(self, mu, m, w):
        if not self.blocks(mu, m, w):
            return mu
        h = self.husbands(mu)
        new = list(mu)
        if h[w] >= 0:
            new[h[w]] = -1
        new[m] = w
        return tuple(new)

    def stable(self, mu):
        n = self.n
        return all(not self.blocks(mu, m, w) for m in range(n) for w in range(n))


def stable_matchings(mk, states):
    return [s for s in states if mk.stable(s)]


def sccs(nodes, succ):
    """Tarjan's algorithm (iterative). succ[v]: list of (label, target)."""
    index, low, on, stack, comps = {}, {}, set(), [], []
    counter = [0]
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(succ[root]))]
        index[root] = low[root] = counter[0]
        counter[0] += 1
        stack.append(root)
        on.add(root)
        while work:
            v, it = work[-1]
            adv = False
            for _, t in it:
                if t not in index:
                    index[t] = low[t] = counter[0]
                    counter[0] += 1
                    stack.append(t)
                    on.add(t)
                    work.append((t, iter(succ[t])))
                    adv = True
                    break
                elif t in on:
                    low[v] = min(low[v], index[t])
            if adv:
                continue
            work.pop()
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    x = stack.pop()
                    on.discard(x)
                    comp.append(x)
                    if x == v:
                        break
                comps.append(comp)
    return comps


def analyse(mk):
    """Return (stable matchings, list of fair SCCs, list of all nontrivial SCCs)."""
    n = mk.n
    states = matchings(n)
    succ = {}
    for s in states:
        succ[s] = [(m * n + w, mk.update(s, m, w)) for m in range(n) for w in range(n)
                   if mk.blocks(s, m, w)]
    comps = [c for c in sccs(states, succ) if len(c) > 1]
    fair = []
    for c in comps:
        cs = set(c)
        ok = set()
        for s in c:
            for m in range(n):
                for w in range(n):
                    if not mk.blocks(s, m, w):
                        ok.add(m * n + w)
            for j, t in succ[s]:
                if t in cs:
                    ok.add(j)
        if len(ok) == n * n:
            fair.append(c)
    return stable_matchings(mk, states), fair, comps


def lasso(mk, comp):
    """Build a loop word q from comp[0] naming every pair and returning to comp[0]."""
    n = mk.n
    cs = set(comp)
    x0 = comp[0]

    def path(a, b):  # BFS inside comp, returns label list
        if a == b:
            return []
        prev = {a: None}
        q = [a]
        while q:
            v = q.pop(0)
            for m in range(n):
                for w in range(n):
                    if mk.blocks(v, m, w):
                        t = mk.update(v, m, w)
                        if t in cs and t not in prev:
                            prev[t] = (v, m * n + w)
                            if t == b:
                                labs = []
                                while prev[t] is not None:
                                    t, j = prev[t]
                                    labs.append(j)
                                return labs[::-1]
                            q.append(t)
        raise ValueError("not strongly connected")

    word, cur = [], x0
    for j in range(n * n):
        m, w = divmod(j, n)
        # prefer a non-blocking state, else an internal edge
        target = None
        for s in comp:
            if not mk.blocks(s, m, w):
                target = ("noop", s)
                break
        if target is None:
            for s in comp:
                if mk.blocks(s, m, w) and mk.update(s, m, w) in cs:
                    target = ("edge", s)
                    break
        _, s = target
        word += path(cur, s)
        word.append(j)
        cur = mk.update(s, m, w)
    word += path(cur, x0)
    return x0, word


def run(mk, x, word):
    for j in word:
        x = mk.update(x, *divmod(j, mk.n))
    return x


def from_one_based(mp1, wp1):
    return Market([[w - 1 for w in l] for l in mp1], [[m - 1 for m in l] for l in wp1])


def show(name, mk):
    sm, fair, comps = analyse(mk)
    print(f"{name}: n={mk.n}, matchings={len(matchings(mk.n))}, stable={len(sm)}: {sm}")
    print(f"  nontrivial SCCs: {len(comps)} (sizes {sorted(len(c) for c in comps)})")
    print(f"  pair-fair SCCs: {len(fair)}")
    for c in fair:
        x0, q = lasso(mk, c)
        assert run(mk, x0, q) == x0 and set(q) == set(range(mk.n ** 2))
        print(f"    loop from {x0}, |q|={len(q)}, q={q}")
    return sm, fair, comps


if __name__ == "__main__":
    # Ackermann, Goldberg, Mirrokni, Roeglin, Voecking, SIAM J. Comput. 2011, Thm 3.
    # Women are the active side there; here "men" index the first argument. We take the women of
    # the paper as our men (rows) and the men of the paper as our women (columns).
    agmrv = from_one_based(
        [[2, 3, 1], [1, 2, 3], [3, 1, 2]],      # w1, w2, w3 of the paper over m1..m3
        [[1, 3, 2], [2, 1, 3], [1, 2, 3]])      # m1, m2, m3 of the paper over w1..w3
    sm, fair, comps = show("Ackermann et al. Thm 3", agmrv)
    # The printed best-response cycle (x, y, z) = partners of w1, w2, w3 (-1 single).
    cyc = [(-1, 2, 3), (3, 2, -1), (3, 1, -1), (3, -1, 1), (2, -1, 1), (-1, 2, 1), (-1, 2, 3)]
    cyc0 = [tuple(v - 1 if v > 0 else -1 for v in c) for c in cyc]
    for a, b in zip(cyc0, cyc0[1:]):
        assert any(agmrv.update(a, m, w) == b for m in range(3) for w in range(3)), (a, b)
    assert any(set(cyc0) <= set(c) for c in comps)
    print("  printed cycle reproduced as a blocking-pair cycle in this model")

    # Tamura 1993, as Example 2 of Chen, Skowron, Sorge (arXiv 1906.12274).
    tamura = from_one_based(
        [[1, 3, 2, 4], [2, 4, 3, 1], [3, 1, 4, 2], [4, 2, 1, 3]],
        [[2, 4, 1, 3], [3, 1, 2, 4], [4, 2, 3, 1], [1, 3, 4, 2]])
    show("Tamura (Chen et al. Ex 2)", tamura)


def strong_fair_sets(mk):
    """Strong fairness (robustness check beyond the committed claim): every pair that blocks at
    some state of the cycle is resolved on the cycle. Emerson-Lei: in each SCC of the current
    state set, a pair that blocks somewhere in it but labels no internal edge forces removing
    the states where it blocks; recurse on the rest. Returns the maximal surviving sets."""
    n = mk.n
    states = [s for s in matchings(n) if not mk.stable(s)]
    out, work = [], [set(states)]
    while work:
        cur = work.pop()
        succ = {s: [(m * n + w, mk.update(s, m, w)) for m in range(n) for w in range(n)
                    if mk.blocks(s, m, w) and mk.update(s, m, w) in cur] for s in cur}
        for c in sccs(sorted(cur), succ):
            if len(c) < 2:
                continue
            cs = set(c)
            internal = {j for s in c for j, t in succ[s] if t in cs}
            bad = {m * n + w for s in c for m in range(n) for w in range(n)
                   if mk.blocks(s, m, w)} - internal
            if not bad:
                out.append(cs)
            else:
                rest = {s for s in c if not any(mk.blocks(s, *divmod(j, n)) for j in bad)}
                if rest:
                    work.append(rest)
    return out
