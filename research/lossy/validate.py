#!/usr/bin/env python3
"""Empirical checks for LOSSY-NETWORKS.md (research note, not a proof).

Every check below compares a claimed equivalence against brute force on random small instances.
Nothing here is mechanized; a passing run is evidence that the constructions in the note are
stated correctly, not a proof that they are.

Model (reading A, the constraint reading). A network is a set of vertices, each with a finite
domain, and a list of directed edges (u, v, f) where f is a total map from dom(u) to dom(v),
given as a dict. A state s is CONSISTENT (a section) when f(s[u]) == s[v] for every edge. This is
CohomologyGeneral.msection with typed fibers.

Model (reading B, the resolver reading). Each vertex v has a list of sources and a local function
F_v reading the sources' values. A state is CONSISTENT when s[v] == F_v(s[src(v)]) for every v
with sources (vertices without sources are free). This is Categorical.Consistent /
FederationOrder.run's fixed points.

Checks:
  1. 3-SAT -> reading A, typed fibers: section exists <=> formula satisfiable, and the number of
     sections equals the number of satisfying assignments of the occurring variables.
  2. Same reduction on a single shared fiber (the msection setting: every vertex takes values in
     one set V), using a filter gadget: same two equalities.
  3. Rooted algorithm (one vertex reaches all others): drive each root value along a BFS
     out-tree, check the remaining edges. Agrees with brute force.
  4. Root-set algorithm (David 1995): one representative per source SCC of the condensation;
     enumerate their joint values, drive, check. Agrees with brute force.
  5. Multicolored k-clique -> reading A with k(k-1)/2 source vertices: section exists <=> the
     graph has a multicolored k-clique (W[1]-hardness in the number of sources).
  6. Readings A and B differ: an acyclic network with no section in reading A (an unbalanced
     undirected cycle) and a unique fixed point in reading B; and the Z/2 loops of
     CoordinatedCycles.v (copy-back, negation) read as Boolean networks.
  7. In-degree <= 1 (every vertex has at most one incoming edge): readings A and B coincide, and
     for Z/2 (copy/negation) labels a section exists iff every directed cycle has an even number
     of negations (positive in Thomas's sense).
  8. Reading B -> reading A by product vertices: #fixed points == #sections.
  9. Reading A -> reading B by an alarm gadget (a Boolean vertex that negates itself exactly when
     an extra in-edge disagrees): a section exists iff a fixed point exists.
 10. Permutation labels on a connected graph: some family of total orders on the fibers makes every
     edge map monotone iff every holonomy is the identity (iff #sections == |X|).
 11. Lossy maps with in-degree <= 1: monotonizable implies a section exists (and the converse
     fails on some instances).

Usage: python3 validate.py [--quick]   (full run about 10 s; the seed is fixed, so output is
deterministic; the recorded output is in validate.out)
"""

import itertools
import random
import sys
from collections import deque

# --------------------------------------------------------------------------------------------
# Reading A: brute-force section search (backtracking; checks an edge once both ends are set).


def sections(domains, edges, limit=None):
    """Yield consistent states (dicts) of a reading-A network, by backtracking."""
    order = list(domains)
    pos = {v: i for i, v in enumerate(order)}
    # edges checked when the later endpoint (in `order`) is assigned
    check_at = {v: [] for v in order}
    for (u, v, f) in edges:
        check_at[order[max(pos[u], pos[v])]].append((u, v, f))
    s = {}
    count = [0]

    def rec(i):
        if limit is not None and count[0] >= limit:
            return
        if i == len(order):
            count[0] += 1
            yield dict(s)
            return
        v = order[i]
        for x in domains[v]:
            s[v] = x
            if all(f[s[a]] == s[b] for (a, b, f) in check_at[v]):
                yield from rec(i + 1)
            del s[v]

    yield from rec(0)


def has_section(domains, edges):
    for _ in sections(domains, edges, limit=1):
        return True
    return False


def count_sections(domains, edges):
    return sum(1 for _ in sections(domains, edges))


def is_section(s, edges):
    return all(f[s[u]] == s[v] for (u, v, f) in edges)


# --------------------------------------------------------------------------------------------
# 3-SAT


def random_3sat(n, m, rng):
    clauses = []
    for _ in range(m):
        vs = rng.sample(range(n), 3)
        clauses.append(tuple((v, rng.random() < 0.5) for v in vs))  # (var, negated?)
    return clauses


def sat_assignments(n, clauses):
    occ = sorted({v for c in clauses for (v, _) in c})
    sols = 0
    for bits in itertools.product((0, 1), repeat=len(occ)):
        a = dict(zip(occ, bits))
        if all(any((a[v] ^ neg) == 1 for (v, neg) in c) for c in clauses):
            sols += 1
    return sols


def clause_sat_values(c):
    """The 7 (of 8) assignments to the clause's three variables that satisfy it, as bit triples."""
    out = []
    for bits in itertools.product((0, 1), repeat=3):
        if any((b ^ neg) == 1 for b, (_, neg) in zip(bits, c)):
            out.append(bits)
    return out


def reduce_typed(clauses):
    """Clause vertex C_j with domain = its 7 satisfying assignments; variable vertex x_i with
    domain {0, 1}; projection edge C_j -> x_i for each variable of C_j. Every clause vertex is a
    source; every variable vertex is a sink with one incoming edge per occurrence."""
    domains, edges = {}, []
    occ = sorted({v for c in clauses for (v, _) in c})
    for i in occ:
        domains[("x", i)] = (0, 1)
    for j, c in enumerate(clauses):
        vals = clause_sat_values(c)
        domains[("C", j)] = tuple(vals)
        for k, (i, _) in enumerate(c):
            edges.append((("C", j), ("x", i), {a: a[k] for a in vals}))
    return domains, edges


def reduce_single_fiber(clauses):
    """The same reduction on ONE shared fiber V = {0..7} u {POISON}, as in msection, where every
    vertex ranges over all of V. A clause value is a 3-bit code; a code that does not satisfy the
    clause projects to POISON. A filter vertex z is pinned to 0 by a constant self-loop, and each
    variable vertex has an edge x_i -> z mapping 0, 1 to 0 and everything else to 1, so variable
    values are forced into {0, 1}, which in turn forces clause values to satisfying codes."""
    POISON = 8
    V = tuple(range(9))
    domains, edges = {}, []
    occ = sorted({v for c in clauses for (v, _) in c})
    domains[("z",)] = V
    edges.append((("z",), ("z",), {x: 0 for x in V}))  # constant self-loop pins z = 0
    filt = {x: (0 if x in (0, 1) else 1) for x in V}
    for i in occ:
        domains[("x", i)] = V
        edges.append((("x", i), ("z",), filt))
    for j, c in enumerate(clauses):
        sat = {(a[0] << 2) | (a[1] << 1) | a[2] for a in clause_sat_values(c)}
        domains[("C", j)] = V
        for k, (i, _) in enumerate(c):
            proj = {}
            for x in V:
                if x in sat:
                    proj[x] = (x >> (2 - k)) & 1
                else:
                    proj[x] = POISON
            edges.append((("C", j), ("x", i), proj))
    return domains, edges


# --------------------------------------------------------------------------------------------
# Random reading-A networks, and the polynomial algorithms of the note


def random_network(nv, ne, dom, rng, rooted=False):
    domains = {v: tuple(range(dom)) for v in range(nv)}
    edges = []
    if rooted:  # a random out-arborescence from vertex 0 guarantees 0 reaches every vertex
        for v in range(1, nv):
            u = rng.randrange(v)
            edges.append((u, v, {x: rng.randrange(dom) for x in range(dom)}))
    while len(edges) < ne:
        u, v = rng.randrange(nv), rng.randrange(nv)
        # bias toward permutations sometimes, so that sections exist often enough to be informative
        if rng.random() < 0.5:
            p = list(range(dom))
            rng.shuffle(p)
            f = dict(enumerate(p))
        else:
            f = {x: rng.randrange(dom) for x in range(dom)}
        edges.append((u, v, f))
    return domains, edges


def out_adj(domains, edges):
    adj = {v: [] for v in domains}
    for (u, v, f) in edges:
        adj[u].append((v, f))
    return adj


def drive(domains, edges, seeds):
    """BFS from the seeded vertices along out-edges; the first edge to reach a vertex sets it.
    Returns the driven partial state (every vertex reachable from a seed is set)."""
    adj = out_adj(domains, edges)
    s = dict(seeds)
    q = deque(seeds)
    while q:
        u = q.popleft()
        for (v, f) in adj[u]:
            if v not in s:
                s[v] = f[s[u]]
                q.append(v)
    return s


def rooted_has_section(domains, edges, r):
    """rooted_criterion as an algorithm: O(|X_r| (|V| + |E|))."""
    for x in domains[r]:
        s = drive(domains, edges, {r: x})
        assert len(s) == len(domains), "root does not reach every vertex"
        if is_section(s, edges):
            return True
    return False


def sccs(vertices, edges):
    """Tarjan's algorithm, iterative. Returns a list of components (lists of vertices)."""
    adj = {v: [] for v in vertices}
    for (u, v, _) in edges:
        adj[u].append(v)
    index, low, on, st, comps = {}, {}, set(), [], []
    counter = [0]
    for root in vertices:
        if root in index:
            continue
        work = [(root, iter(adj[root]))]
        index[root] = low[root] = counter[0]
        counter[0] += 1
        st.append(root)
        on.add(root)
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]
                    counter[0] += 1
                    st.append(w)
                    on.add(w)
                    work.append((w, iter(adj[w])))
                    advanced = True
                    break
                elif w in on:
                    low[v] = min(low[v], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = st.pop()
                    on.discard(w)
                    comp.append(w)
                    if w == v:
                        break
                comps.append(comp)
    return comps


def root_set(domains, edges):
    """One representative per source component of the condensation (David 1995, App. A.1)."""
    comps = sccs(list(domains), edges)
    cid = {v: i for i, c in enumerate(comps) for v in c}
    has_in = set()
    for (u, v, _) in edges:
        if cid[u] != cid[v]:
            has_in.add(cid[v])
    return [comps[i][0] for i in range(len(comps)) if i not in has_in]


def rootset_has_section(domains, edges):
    """Enumerate the joint values of a minimum root set, drive, check: O(prod |X_r| (|V|+|E|))."""
    R = root_set(domains, edges)
    for vals in itertools.product(*(domains[r] for r in R)):
        s = drive(domains, edges, dict(zip(R, vals)))
        assert len(s) == len(domains)
        if is_section(s, edges):
            return True
    return False


# --------------------------------------------------------------------------------------------
# Multicolored clique -> reading A


def random_colored_graph(k, per, p, rng):
    """k color classes of `per` vertices each; each cross-class pair is an edge with prob. p."""
    verts = [(c, i) for c in range(k) for i in range(per)]
    E = set()
    for a, b in itertools.combinations(verts, 2):
        if a[0] != b[0] and rng.random() < p:
            E.add((a, b))
    return verts, E


def has_mc_clique(k, per, E):
    Es = set(E) | {(b, a) for (a, b) in E}
    for pick in itertools.product(range(per), repeat=k):
        vs = [(c, pick[c]) for c in range(k)]
        if all((a, b) in Es for a, b in itertools.combinations(vs, 2)):
            return True
    return False


def reduce_clique(k, per, E):
    """Source vertex P_{ab} (a < b colors) ranges over the edges between classes a and b; sink
    vertex Y_c ranges over the vertices of class c; edges P_{ab} -> Y_a and P_{ab} -> Y_b project
    an edge to its endpoint in that class. Sections = multicolored k-cliques. k(k-1)/2 sources."""
    domains, edges = {}, []
    for c in range(k):
        domains[("Y", c)] = tuple(range(per))
    for a, b in itertools.combinations(range(k), 2):
        dom = []
        for (x, y) in E:
            if {x[0], y[0]} == {a, b}:
                xa, xb = (x, y) if x[0] == a else (y, x)
                dom.append((xa[1], xb[1]))
        domains[("P", a, b)] = tuple(dom)
        edges.append((("P", a, b), ("Y", a), {d: d[0] for d in dom}))
        edges.append((("P", a, b), ("Y", b), {d: d[1] for d in dom}))
    return domains, edges


# --------------------------------------------------------------------------------------------
# Reading B: fixed points and asynchronous dynamics of small networks


def fixed_points(domains, src, F):
    """Fixed points of the resolver reading: s[v] == F[v](tuple(s[u] for u in src[v])) for every
    vertex with sources; vertices without sources are free."""
    order = list(domains)
    out = []
    for vals in itertools.product(*(domains[v] for v in order)):
        s = dict(zip(order, vals))
        if all(s[v] == F[v](tuple(s[u] for u in src[v])) for v in order if src[v]):
            out.append(s)
    return out


def async_attractors(domains, src, F):
    """Attractors (terminal SCCs) of the asynchronous state graph: from x, update one vertex v
    with x[v] != F_v(x). Returns (number of fixed-point attractors, number of cyclic ones)."""
    order = list(domains)
    states = [tuple(vals) for vals in itertools.product(*(domains[v] for v in order))]
    idx = {v: i for i, v in enumerate(order)}

    def succ(x):
        out = []
        for v in order:
            if not src[v]:
                continue
            y = F[v](tuple(x[idx[u]] for u in src[v]))
            if y != x[idx[v]]:
                z = list(x)
                z[idx[v]] = y
                out.append(tuple(z))
        return out

    E = [(x, y, None) for x in states for y in succ(x)]
    comps = sccs(states, E)
    cid = {x: i for i, c in enumerate(comps) for x in c}
    leaves = set(range(len(comps)))
    for (x, y, _) in E:
        if cid[x] != cid[y]:
            leaves.discard(cid[x])
    fp = sum(1 for i in leaves if len(comps[i]) == 1)
    return fp, len(leaves) - fp


def reading_b_to_a(domains, src, F):
    """Reading B -> reading A. For each vertex v with sources u_1..u_k, add a product vertex P_v
    ranging over X_{u_1} x ... x X_{u_k}, projection edges P_v -> u_i, and an edge P_v -> v
    carrying F_v. Sections correspond one-to-one to fixed points."""
    dA, eA = dict(domains), []
    for v in domains:
        if not src[v]:
            continue
        P = ("P", v)
        tuples = tuple(itertools.product(*(domains[u] for u in src[v])))
        dA[P] = tuples
        for i, u in enumerate(src[v]):
            eA.append((P, u, {t: t[i] for t in tuples}))
        eA.append((P, v, {t: F[v](t) for t in tuples}))
    return dA, eA


def reading_a_to_b(domains, edges):
    """Reading A -> reading B. A vertex with in-edges e_1..e_k reads its first in-edge
    (v := f_1(u_1)); each further in-edge e_i gets a Boolean alarm vertex a_i that keeps its value
    when f_i(u_i) == v and negates itself otherwise (a negative self-loop that is active exactly
    on disagreement). Fixed points exist iff sections exist (each alarm doubles the count)."""
    dB, srcB, FB = dict(domains), {v: [] for v in domains}, {}
    inc = {v: [] for v in domains}
    for (u, v, f) in edges:
        inc[v].append((u, f))
    for v, lst in inc.items():
        if not lst:
            continue
        u1, f1 = lst[0]
        srcB[v] = [u1]
        FB[v] = (lambda f: (lambda t: f[t[0]]))(f1)
        for i, (ui, fi) in enumerate(lst[1:]):
            a = ("alarm", v, i)
            dB[a] = (0, 1)
            srcB[a] = [ui, v, a]
            FB[a] = (lambda f: (lambda t: t[2] if f[t[0]] == t[1] else 1 - t[2]))(fi)
    return dB, srcB, FB


def monotonizable(domains, edges):
    """Brute force: is there a total order on every fiber making every edge map monotone
    (x <= y implies f(x) <= f(y))? Orders are permutations of the domain (rank vectors)."""
    order = list(domains)
    choices = [list(itertools.permutations(domains[v])) for v in order]
    for perms in itertools.product(*choices):
        rank = {v: {x: i for i, x in enumerate(p)} for v, p in zip(order, perms)}
        good = True
        for (u, v, f) in edges:
            ru, rv = rank[u], rank[v]
            for x in domains[u]:
                for y in domains[u]:
                    if ru[x] <= ru[y] and rv[f[x]] > rv[f[y]]:
                        good = False
                        break
                if not good:
                    break
            if not good:
                break
        if good:
            return True
    return False


# --------------------------------------------------------------------------------------------


def main():
    quick = "--quick" in sys.argv
    rng = random.Random(20261004)
    ok = True

    def report(name, agree, total, extra=""):
        nonlocal ok
        status = "OK" if agree == total else "MISMATCH"
        ok = ok and agree == total
        print(f"[{status}] {name}: {agree}/{total} agree{extra}")

    # 1 and 2: the 3-SAT reduction
    trials = 150 if quick else 600
    agree1 = agree2 = cnt1 = cnt2 = 0
    sat_count = 0
    for t in range(trials):
        n = rng.randint(4, 8 if quick else 10)
        # clause density around the 3-SAT threshold (4.26) gives a mix of SAT and UNSAT
        m = max(1, int(round(n * rng.uniform(3.0, 6.0))))
        cl = random_3sat(n, m, rng)
        nsat = sat_assignments(n, cl)
        sat_count += nsat > 0
        d, e = reduce_typed(cl)
        agree1 += has_section(d, e) == (nsat > 0)
        cnt1 += count_sections(d, e) == nsat
        if t % 3 == 0:  # the single-fiber variant is slower (9 values per vertex)
            d2, e2 = reduce_single_fiber(cl)
            agree2 += has_section(d2, e2) == (nsat > 0)
            cnt2 += count_sections(d2, e2) == nsat
    n2 = len(range(0, trials, 3))
    report("3-SAT -> reading A (typed fibers): section exists iff satisfiable", agree1, trials,
           f"; {sat_count} satisfiable, {trials - sat_count} unsatisfiable")
    report("3-SAT -> reading A (typed fibers): #sections == #satisfying assignments", cnt1, trials)
    report("3-SAT -> reading A (single shared fiber, filter gadget): existence", agree2, n2)
    report("3-SAT -> reading A (single shared fiber, filter gadget): counts", cnt2, n2)

    # 3: rooted algorithm
    trials = 300 if quick else 1500
    agree = has = 0
    for _ in range(trials):
        nv = rng.randint(2, 6)
        ne = rng.randint(nv - 1, nv + 4)
        d, e = random_network(nv, ne, rng.randint(2, 4), rng, rooted=True)
        b = has_section(d, e)
        has += b
        agree += rooted_has_section(d, e, 0) == b
    report("rooted algorithm vs brute force (one vertex reaches all)", agree, trials,
           f"; {has} with a section")

    # 4: root-set algorithm, general networks
    trials = 300 if quick else 1500
    agree = has = multi = 0
    for _ in range(trials):
        nv = rng.randint(2, 6)
        ne = rng.randint(1, nv + 4)
        d, e = random_network(nv, ne, rng.randint(2, 3), rng)
        b = has_section(d, e)
        has += b
        multi += len(root_set(d, e)) > 1
        agree += rootset_has_section(d, e) == b
    report("root-set algorithm (David 1995) vs brute force", agree, trials,
           f"; {has} with a section, {multi} with more than one source component")

    # 5: multicolored clique
    trials = 120 if quick else 400
    agree = has = 0
    for _ in range(trials):
        k = rng.randint(3, 4)
        per = rng.randint(2, 4)
        _, E = random_colored_graph(k, per, rng.uniform(0.4, 0.8), rng)
        c = has_mc_clique(k, per, E)
        has += c
        d, e = reduce_clique(k, per, E)
        agree += has_section(d, e) == c
    report("multicolored k-clique -> reading A with k(k-1)/2 sources", agree, trials,
           f"; {has} with a clique")

    # 6: readings A and B differ
    print("\nReadings A and B on the same graph and maps:")
    # u -> v copy, u -> w copy, w -> v negation. Acyclic. Reading A: v = u and v = not u.
    dA = {"u": (0, 1), "v": (0, 1), "w": (0, 1)}
    cp, ng = {0: 0, 1: 1}, {0: 1, 1: 0}
    eA = [("u", "v", cp), ("u", "w", cp), ("w", "v", ng)]
    print(f"  diamond u->v copy, u->w copy, w->v negation: reading A sections = "
          f"{count_sections(dA, eA)} (an unbalanced undirected cycle, no directed cycle)")
    srcB = {"u": [], "w": ["u"], "v": ["u", "w"]}
    for name, res in (("AND", lambda t: t[0] & (1 - t[1])), ("first-source", lambda t: t[0])):
        FB = {"w": lambda t: t[0], "v": res}
        print(f"  same graph, reading B with resolver v = {name}: fixed points = "
              f"{len(fixed_points(dA, srcB, FB))} (one per value of the free source u)")
    # c22_cycle_basis_fails: a -> c constant 0, b -> c constant 1
    dC = {"a": (0, 1), "b": (0, 1), "c": (0, 1)}
    eC = [("a", "c", {0: 0, 1: 0}), ("b", "c", {0: 1, 1: 1})]
    srcC = {"a": [], "b": [], "c": ["a", "b"]}
    FC = {"c": lambda t: 0}  # e.g. priority to a: c takes a's constant
    print(f"  c22 (a->c const 0, b->c const 1): reading A sections = {count_sections(dC, eC)};"
          f" reading B with a priority resolver: fixed points = "
          f"{len(fixed_points(dC, srcC, FC))} (4 = free values of the two sources)")

    print("\nThe Z/2 loops of CoordinatedCycles.v as Boolean networks (reading B, in-degree 1):")
    d2 = {"A": (0, 1), "B": (0, 1)}
    for name, fBA in (("copy-back (positive 2-cycle)", lambda t: t[0]),
                      ("negation (negative 2-cycle)", lambda t: 1 - t[0])):
        src = {"A": ["B"], "B": ["A"]}
        F = {"B": lambda t: t[0], "A": fBA}
        fp = fixed_points(d2, src, F)
        a_fp, a_cyc = async_attractors(d2, src, F)
        print(f"  {name}: fixed points = {len(fp)}; asynchronous attractors: {a_fp} fixed, "
              f"{a_cyc} cyclic")

    # 7: in-degree <= 1, Z/2 labels: section iff every directed cycle has an even number of
    # negations, and readings A and B coincide
    trials = 300 if quick else 1000
    agreeAB = agreeSign = 0
    for _ in range(trials):
        nv = rng.randint(1, 7)
        d = {v: (0, 1) for v in range(nv)}
        e, src, F = [], {v: [] for v in range(nv)}, {}
        for v in range(nv):
            if rng.random() < 0.8:  # at most one incoming edge per vertex
                u = rng.randrange(nv)
                neg = rng.random() < 0.5
                e.append((u, v, ng if neg else cp))
                src[v] = [u]
                F[v] = (lambda t: 1 - t[0]) if neg else (lambda t: t[0])
        a = count_sections(d, e)
        b = len(fixed_points(d, src, F))
        agreeAB += a == b
        # every directed cycle of a functional graph: follow parents
        par = {v: (u, f is ng) for (u, v, f) in e}
        neg_cycle = False
        for v0 in range(nv):
            seen, v, parity = [], v0, 0
            while v in par and v not in seen:
                seen.append(v)
                u, isneg = par[v]
                parity ^= isneg
                v = u
            if v == v0 and v in par:
                neg_cycle = neg_cycle or parity == 1
        agreeSign += (a > 0) == (not neg_cycle)
    report("in-degree <= 1: #sections (reading A) == #fixed points (reading B)", agreeAB, trials)
    report("in-degree <= 1, Z/2 labels: section exists iff no negative directed cycle",
           agreeSign, trials)

    # 8: reading B -> reading A (product vertices): #fixed points == #sections
    trials = 200 if quick else 800
    agree = 0
    for _ in range(trials):
        nv = rng.randint(1, 4)
        dom = rng.randint(2, 3)
        d = {v: tuple(range(dom)) for v in range(nv)}
        src, F = {}, {}
        for v in range(nv):
            k = rng.choice([0, 1, 1, 2, 2])
            src[v] = [rng.randrange(nv) for _ in range(k)]
            if k:
                table = {t: rng.randrange(dom) for t in itertools.product(range(dom), repeat=k)}
                F[v] = (lambda tb: (lambda t: tb[t]))(table)
        dA, eA = reading_b_to_a(d, src, F)
        agree += len(fixed_points(d, src, F)) == count_sections(dA, eA)
    report("reading B -> reading A (product vertices): #fixed points == #sections", agree, trials)

    # 9: reading A -> reading B (agreement as a conditional negative self-loop): existence
    trials = 200 if quick else 800
    agree = 0
    for _ in range(trials):
        nv = rng.randint(2, 4)
        d, e = random_network(nv, rng.randint(1, nv + 2), 2, rng)
        dB, srcB, FB = reading_a_to_b(d, e)
        agree += (len(fixed_points(dB, srcB, FB)) > 0) == has_section(d, e)
    report("reading A -> reading B (alarm gadget): section exists iff fixed point exists",
           agree, trials)

    # 10: permutation labels: monotonizable <=> every holonomy is the identity <=> #sections = |X|
    trials = 150 if quick else 500
    agree = mono = 0
    dom = 3
    for _ in range(trials):
        nv = rng.randint(2, 4)
        d = {v: tuple(range(dom)) for v in range(nv)}
        e = []
        for v in range(1, nv):  # a random spanning tree with random orientations: connected
            u = rng.randrange(v)
            p = list(range(dom))
            rng.shuffle(p)
            e.append((u, v, dict(enumerate(p))) if rng.random() < 0.5 else (v, u, dict(enumerate(p))))
        for _ in range(rng.randint(0, 2)):
            u, v = rng.randrange(nv), rng.randrange(nv)
            p = list(range(dom))
            if rng.random() < 0.6:
                rng.shuffle(p)
            e.append((u, v, dict(enumerate(p))))
        m = monotonizable(d, e)
        mono += m
        agree += m == (count_sections(d, e) == dom)
    report("permutation labels: monotonizable iff trivial holonomy (#sections == |X|)", agree,
           trials, f"; {mono} monotonizable")

    # 11: lossy maps, in-degree <= 1: monotonizable => a section exists (sufficient, not necessary)
    trials = 200 if quick else 600
    holds = mono = sec_not_mono = 0
    for _ in range(trials):
        nv = rng.randint(1, 4)
        d = {v: tuple(range(3)) for v in range(nv)}
        e = []
        for v in range(nv):
            if rng.random() < 0.85:
                e.append((rng.randrange(nv), v, {x: rng.randrange(3) for x in range(3)}))
        m = monotonizable(d, e)
        s = has_section(d, e)
        mono += m
        holds += (not m) or s
        sec_not_mono += s and not m
    report("lossy maps, in-degree <= 1: monotonizable implies a section exists", holds, trials,
           f"; {mono} monotonizable, {sec_not_mono} with a section but not monotonizable")

    print("\nALL CHECKS PASSED" if ok else "\nSOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
