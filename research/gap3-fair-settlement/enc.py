"""SAT encodings for gap 3 (LossyNetworks P2): Boolean networks f: {0,1}^n -> {0,1}^n,
local interaction graph G(x) as in coq/LocalSigned.v (larc x j i iff f_i(flip j x) != f_i(x)).

Conditions:
  A : no elementary cycle (length 1..n, self-loops included) in any G(x)   (NoLocalCycle)
  B : every vertex of every G(x) has out-degree <= 1                        (OutDeg1)
Targets:
  cycle : the asynchronous state graph (x -> flip v x for v unstable at x) has a cycle
  fair  : some start state and some fair schedule (every vertex named infinitely often, as in
          DistributedCycles.Fair) never settle. Exact encoding: a nonempty set C of states that is
          strongly connected through state-graph edges (root r; every state of C reachable from r
          inside C and reaching r inside C), with at least one edge inside C, and covering every
          vertex w: some x in C where w is stable (a no-op update) or w is unstable and flip w x is
          in C.
State x is an int; x_v = (x >> v) & 1.
"""
import itertools
from pysat.formula import IDPool, CNF


def elem_cycles(n):
    """Elementary cycles of the complete digraph with loops on 0..n-1, canonical (min first)."""
    out = []
    for k in range(1, n + 1):
        for comb in itertools.combinations(range(n), k):
            m = comb[0]
            rest = comb[1:]
            for perm in itertools.permutations(rest):
                out.append((m,) + perm)
    return out


class Enc:
    def __init__(self, n, A=True, B=True, target="cycle", fixed=None):
        self.n = n
        N = 1 << n
        self.N = N
        self.pool = IDPool()
        self.cnf = CNF()
        P = self.pool
        self.F = [[P.id(("F", i, x)) for x in range(N)] for i in range(n)]
        # arc variables, shared between x and flip j x
        self.arc = {}
        for x in range(N):
            for j in range(n):
                if (x >> j) & 1:
                    continue
                y = x | (1 << j)
                for i in range(n):
                    a = P.id(("arc", x, j, i))
                    f1, f2 = self.F[i][x], self.F[i][y]
                    # a <-> f1 xor f2
                    self.cnf.extend([[-a, f1, f2], [-a, -f1, -f2], [a, -f1, f2], [a, f1, -f2]])
                    self.arc[(x, j, i)] = a
                    self.arc[(y, j, i)] = a
        if fixed is not None:
            for i in range(n):
                for x in range(N):
                    self.cnf.append([self.F[i][x] if fixed[i][x] else -self.F[i][x]])
        if A:
            cyc = elem_cycles(n)
            for x in range(N):
                for c in cyc:
                    k = len(c)
                    self.cnf.append([-self.arc[(x, c[t], c[(t + 1) % k])] for t in range(k)])
        if B:
            for x in range(N):
                for j in range(n):
                    lits = [self.arc[(x, j, i)] for i in range(n)]
                    for p in range(n):
                        for q in range(p + 1, n):
                            self.cnf.append([-lits[p], -lits[q]])
        if target == "cycle":
            self._cycle()
        elif target == "fair":
            self._fair()
        elif target == "none":
            pass
        else:
            raise ValueError(target)

    def u(self, x, v):
        """literal: v unstable at x (f_v(x) != x_v)."""
        return self.F[v][x] if ((x >> v) & 1) == 0 else -self.F[v][x]

    def _cycle(self):
        P, n, N = self.pool, self.n, self.N
        c = [P.id(("c", x)) for x in range(N)]
        self.cnf.append(c[:])
        for x in range(N):
            es = []
            for v in range(n):
                e = P.id(("e", x, v))
                es.append(e)
                self.cnf.extend([[-e, self.u(x, v)], [-e, c[x ^ (1 << v)]]])
            self.cnf.append([-c[x]] + es)
        self.c = c

    def _fair(self):
        P, n, N = self.pool, self.n, self.N
        c = [P.id(("c", x)) for x in range(N)]
        r = [P.id(("r", x)) for x in range(N)]
        cnf = self.cnf
        cnf.append(r[:])
        for p in range(N):
            for q in range(p + 1, N):
                cnf.append([-r[p], -r[q]])
            cnf.append([-r[p], c[p]])
        T = N  # levels 0..T-1
        for kind in ("f", "b"):
            d = [[P.id((kind, x, t)) for t in range(T)] for x in range(N)]
            for x in range(N):
                cnf.append([-d[x][0], r[x]])
                for t in range(T):
                    cnf.append([-d[x][t], c[x]])
                for t in range(T - 1):
                    gs = []
                    for v in range(n):
                        y = x ^ (1 << v)
                        g = P.id((kind + "g", x, t, v))
                        gs.append(g)
                        if kind == "f":   # edge y -> x (flip v at y)
                            cnf.extend([[-g, d[y][t]], [-g, self.u(y, v)]])
                        else:             # edge x -> y
                            cnf.extend([[-g, d[y][t]], [-g, self.u(x, v)]])
                    cnf.append([-d[x][t + 1], d[x][t]] + gs)
                cnf.append([-c[x], d[x][T - 1]])
        # nontrivial: an edge inside C
        ss = []
        for x in range(N):
            for v in range(n):
                s = P.id(("s", x, v))
                ss.append(s)
                cnf.extend([[-s, c[x]], [-s, self.u(x, v)], [-s, c[x ^ (1 << v)]]])
        cnf.append(ss)
        # cover every vertex
        for w in range(n):
            ps = []
            for x in range(N):
                p = P.id(("p", x, w))
                ps.append(p)
                cnf.extend([[-p, c[x]], [-p, -self.u(x, w), c[x ^ (1 << w)]]])
            cnf.append(ps)
        self.c = c

    def decode(self, model):
        pos = set(l for l in model if l > 0)
        return [[1 if self.F[i][x] in pos else 0 for x in range(self.N)] for i in range(self.n)]

    def decode_c(self, model):
        pos = set(l for l in model if l > 0)
        return [x for x in range(self.N) if self.c[x] in pos]
