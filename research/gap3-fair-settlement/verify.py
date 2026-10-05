"""Plain-Python checker, independent of the SAT encoding.
A network is a list tt with tt[i][x] = f_i(x), x an int, x_v = (x >> v) & 1."""
import sys


def bit(x, v):
    return (x >> v) & 1


def local_graph(tt, n, x):
    """adjacency: arcs[j] = set of i with f_i(flip j x) != f_i(x)."""
    return [set(i for i in range(n) if tt[i][x ^ (1 << j)] != tt[i][x]) for j in range(n)]


def has_cycle(adj, n):
    # DFS three-colour on a digraph (self-loops count)
    col = [0] * n

    def dfs(u):
        col[u] = 1
        for w in adj[u]:
            if col[w] == 1:
                return True
            if col[w] == 0 and dfs(w):
                return True
        col[u] = 2
        return False

    return any(col[u] == 0 and dfs(u) for u in range(n))


def check_A(tt, n):
    return all(not has_cycle(local_graph(tt, n, x), n) for x in range(1 << n))


def check_B(tt, n):
    return all(len(s) <= 1 for x in range(1 << n) for s in local_graph(tt, n, x))


def unstable(tt, n, x):
    return [v for v in range(n) if tt[v][x] != bit(x, v)]


def state_graph(tt, n):
    return {x: [x ^ (1 << v) for v in unstable(tt, n, x)] for x in range(1 << n)}


def sccs(g):
    idx, low, on, st, out, c = {}, {}, set(), [], [], [0]

    def strong(v):
        idx[v] = low[v] = c[0]; c[0] += 1; st.append(v); on.add(v)
        for w in g[v]:
            if w not in idx:
                strong(w); low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = st.pop(); on.discard(w); comp.append(w)
                if w == v:
                    break
            out.append(comp)

    sys.setrecursionlimit(100000)
    for v in g:
        if v not in idx:
            strong(v)
    return out


def async_cyclic(tt, n):
    return any(len(c) > 1 for c in sccs(state_graph(tt, n)))


def fair_witness(tt, n):
    """Return (C, schedule word, start) for a fair non-settling periodic run, or None.
    Exact: a fair non-settling run exists iff some SCC of the state graph with >= 2 states covers
    every vertex (stable somewhere in it, or fired along an edge inside it)."""
    g = state_graph(tt, n)
    for comp in sccs(g):
        if len(comp) < 2:
            continue
        cs = set(comp)
        ok = all(any(tt[w][x] == bit(x, w) or (x ^ (1 << w)) in cs for x in comp) for w in range(n))
        if ok:
            return comp, build_schedule(tt, n, comp)
    return None


def build_schedule(tt, n, comp):
    """A closed walk in comp from comp[0] performing every vertex at least once (as a real move
    inside comp or as a no-op at a stable state), as a word of vertex names."""
    cs = set(comp)
    start = comp[0]

    def path(a, b):  # BFS inside comp, returns list of vertices fired
        from collections import deque
        prev = {a: None}
        q = deque([a])
        while q:
            x = q.popleft()
            if x == b:
                break
            for v in unstable(tt, n, x):
                y = x ^ (1 << v)
                if y in cs and y not in prev:
                    prev[y] = (x, v); q.append(y)
        word, x = [], b
        while prev[x] is not None:
            x0, v = prev[x]; word.append(v); x = x0
        return word[::-1]

    word, cur = [], start
    for w in range(n):
        # where to do w
        site = None
        for x in comp:
            if tt[w][x] == bit(x, w):
                site = (x, False); break
        if site is None:
            for x in comp:
                if (x ^ (1 << w)) in cs and tt[w][x] != bit(x, w):
                    site = (x, True); break
        x, real = site
        word += path(cur, x)
        word.append(w)
        cur = x ^ (1 << w) if real else x
    word += path(cur, start)
    # at least one real move: append a round trip start -> succ -> start inside comp
    if not any(tt[v][s] != bit(s, v) for s, v in trace(tt, n, start, word)):
        v = next(v for v in unstable(tt, n, start) if (start ^ (1 << v)) in cs)
        word += [v] + path(start ^ (1 << v), start)
    return word


def step(tt, n, x, v):
    return x ^ (1 << v) if tt[v][x] != bit(x, v) else x


def replay(tt, n, x, word):
    for v in word:
        x = step(tt, n, x, v)
    return x


def trace(tt, n, x, word):
    out = []
    for v in word:
        out.append((x, v)); x = step(tt, n, x, v)
    return out


def verify_fair_run(tt, n, start, word):
    """Check: the periodic schedule word^omega from start returns to start after one period,
    names every vertex, and changes the state at least once (so it never settles)."""
    end = replay(tt, n, start, word)
    moved = any(tt[v][s] != bit(s, v) for s, v in trace(tt, n, start, word))
    return end == start and set(word) == set(range(n)) and moved


def fmt(x, n):
    return "".join(str(bit(x, v)) for v in range(n))
