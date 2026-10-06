"""Transition statistics for count-preserving moves between K-token states (default K = 3).
Input: walk*.json files from sample3.py (or nets_*.json lists of networks). For every network,
every state x with exactly K unstable vertices and every move x -v-> y = flip v x with exactly K
unstable vertices at y is classified:
  - (good, bad) counts at x and at y (p the unique fixed point, D(x) = x xor p, a token at u is
    good iff u is in D(x));
  - the type of the fired token and of its receiver w (the out-neighbour of v in G(x));
  - token-to-token arcs in G(x) (a token pointing straight at another token) and shared
    receivers (two tokens with the same stable out-neighbour: the collision case);
  - the shape of the token relation at x and at y.
Usage: stats3.py K file.json [file.json ...]"""
import sys, json, itertools
from collections import Counter
import verify as V

def fixed_points(tt, n):
    return [x for x in range(1 << n) if all(tt[i][x] == V.bit(x, i) for i in range(n))]

def out_nb(tt, n, x, j):
    s = [i for i in range(n) if tt[i][x ^ (1 << j)] != tt[i][x]]
    return s[0] if s else None

def path_from(tt, n, x, a):
    out = [a]; seen = {a}
    while True:
        b = out_nb(tt, n, x, out[-1])
        if b is None or b in seen: return out
        out.append(b); seen.add(b)

def shape(tt, n, x, U, D):
    """canonical description of the token relation at x: for each token its type (g/b) and the
    kind of its out-arc (to a token of type g/b, to a stable vertex, none), plus shared receivers
    and ancestor relations in the forest G(x)."""
    o = {u: out_nb(tt, n, x, u) for u in U}
    ty = {u: ("g" if u in D else "b") for u in U}
    parts = []
    for u in sorted(U, key=lambda u: ty[u]):
        t = o[u]
        if t is None: k = "-"
        elif t in U: k = "T" + ty[t]
        else: k = "s"
        parts.append(ty[u] + ">" + k)
    rec = Counter(o[u] for u in U if o[u] is not None and o[u] not in U)
    shared = sum(1 for r, c in rec.items() if c >= 2)
    anc = 0
    for a, b in itertools.permutations(U, 2):
        if b in path_from(tt, n, x, a)[1:]: anc += 1
    return ",".join(sorted(parts)) + "|sh%d|anc%d" % (shared, anc)

def analyse(tt, n, K, C):
    fps = fixed_points(tt, n)
    if len(fps) != 1: C["no-unique-fp"] += 1; return []
    p = fps[0]
    moves = []
    for x in range(1 << n):
        U = V.unstable(tt, n, x)
        if len(U) != K: continue
        D = set(i for i in range(n) if V.bit(x ^ p, i))
        for v in U:
            y = x ^ (1 << v); Uy = V.unstable(tt, n, y)
            w = out_nb(tt, n, x, v)
            if len(Uy) != K:
                C["drop:" + ("noarc" if w is None else "collision")] += 1; continue
            Dy = set(i for i in range(n) if V.bit(y ^ p, i))
            gx = len([u for u in U if u in D]); gy = len([u for u in Uy if u in Dy])
            moves.append(dict(x=x, y=y, v=v, w=w, gx=gx, gy=gy, U=U, Uy=Uy, D=D, Dy=Dy, p=p))
    return moves

if __name__ == "__main__":
    K = int(sys.argv[1]); files = sys.argv[2:]
    C = Counter(); S = Counter(); T = Counter(); TT = Counter(); Sh = Counter(); ShT = Counter()
    nets = 0; nmoves = 0; longest = Counter()
    for f in files:
        data = json.load(open(f))
        for item in data:
            tt = item["tt"] if isinstance(item, dict) else item
            n = len(tt); nets += 1
            ms = analyse(tt, n, K, C)
            # longest K-token walk (DAG longest path; a cycle would be a counterexample)
            succ = {}
            for m in ms: succ.setdefault(m["x"], []).append(m["y"])
            memo = {}; onstack = set()
            def lp(x):
                if x in memo: return memo[x]
                if x in onstack: raise SystemExit("CYCLE FOUND in %s" % f)
                onstack.add(x)
                r = max([1 + lp(y) for y in succ.get(x, [])], default=0)
                onstack.discard(x); memo[x] = r; return r
            sys.setrecursionlimit(10000)
            longest[max([lp(x) for x in succ], default=0)] += 1
            for m in ms:
                nmoves += 1
                x, y, v, w, U, Uy, D, Dy = m["x"], m["y"], m["v"], m["w"], m["U"], m["Uy"], m["D"], m["Dy"]
                fired = "good" if v in D else "bad"
                recv = "good" if w in Dy else "bad"
                S[(m["gx"], K - m["gx"], m["gy"], K - m["gy"], fired, recv)] += 1
                o = {u: out_nb(tt, n, x, u) for u in U}
                t2t = [u for u in U if o[u] in U]
                T["token-to-token arcs at x: %d" % len(t2t)] += 1
                into_v = [u for u in U if u != v and o[u] == v]
                T["another token points at the fired vertex v: %s" % bool(into_v)] += 1
                same_recv = [u for u in U if u != v and o[u] == w]
                T["another token shares the receiver w (collision case): %s" % bool(same_recv)] += 1
                if same_recv:
                    u = same_recv[0]; ou = out_nb(tt, n, y, u)
                    TT["shared receiver; after the move the sharer points at %s" %
                       ("w (token-to-token)" if ou == w else ("v" if ou == v else ("none" if ou is None else "other")))] += 1
                sx = shape(tt, n, x, U, D); sy = shape(tt, n, y, Uy, Dy)
                Sh[sx] += 1; ShT[(sx, sy)] += 1
    print("networks", nets, "count-preserving K-token moves", nmoves)
    print("longest K-token walk per network:", sorted(longest.items()))
    print("dropped moves:", dict(C))
    print("\n(g,b) before -> after, fired, receiver:")
    for k, c in sorted(S.items()): print("  ", k, c)
    print("\nrelations:")
    for k, c in sorted(T.items()): print("  ", k, c)
    for k, c in sorted(TT.items()): print("  ", k, c)
    print("\nshapes at x (top 25):")
    for k, c in Sh.most_common(25): print("  ", c, k)
    print("\nshape transitions (top 30):")
    for k, c in ShT.most_common(30): print("  ", c, k[0], "->", k[1])
