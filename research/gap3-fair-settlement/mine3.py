"""Candidate orders on count-preserving K-token moves (default K = 3).
For each candidate phi (a state function with values compared lexicographically, tuples allowed),
count the moves x -> y with phi(y) < phi(x), = , >. A candidate is a potential if it never rises
and every closed run would force a strict fall; here we just report rises.
Usage: mine3.py K file.json [file.json ...]"""
import sys, json, itertools
from collections import Counter, defaultdict
import verify as V
from stats3 import fixed_points, out_nb, path_from, analyse

def Fs(tt, n, x):
    return sum(tt[i][x] << i for i in range(n))

def pc(x): return bin(x).count("1")

def candidates(tt, n, x, p):
    U = V.unstable(tt, n, x); D = x ^ p
    Dset = set(i for i in range(n) if (D >> i) & 1)
    g = sum(1 for u in U if u in Dset); b = len(U) - g
    d = pc(D)
    # synchronous orbit from x
    orb = [x]
    while orb[-1] != p and len(orb) < 4 * (1 << n):
        orb.append(Fs(tt, n, orb[-1]))
    T = len(orb) - 1
    dist = [pc(z ^ p) for z in orb]
    kap = [pc(orb[j] ^ orb[j + 1]) for j in range(len(orb) - 1)]
    # forest depths (path length to a root of G(x))
    depth = {u: len(path_from(tt, n, x, u)) - 1 for u in range(n)}
    tokd = sorted((depth[u] for u in U), reverse=True)
    reach = set()
    for u in U: reach |= set(path_from(tt, n, x, u))
    # height of tokens = longest in-path (upstream) length
    o = {j: out_nb(tt, n, x, j) for j in range(n)}
    def height(u):
        ins = [j for j in range(n) if o[j] == u]
        return 0 if not ins else 1 + max(height(j) for j in ins)
    toh = sorted((height(u) for u in U), reverse=True)
    bad = [u for u in U if u not in Dset]
    badd = depth[bad[0]] if bad else -1
    goodd = sorted((depth[u] for u in U if u in Dset), reverse=True)
    t2t = sum(1 for u in U if o[u] in U)
    return {
        "d": d, "g": g, "-g": -g, "(g,d)": (g, d), "(-g,d)": (-g, d), "(d,-g)": (d, -g),
        "T sync time": T, "sum sync dist": sum(dist), "dist vector": tuple(dist),
        "kappa lex": tuple(kap), "sum kappa": sum(kap), "d(Fx,p)": dist[1] if len(dist) > 1 else 0,
        "d+d(Fx,p)": d + (dist[1] if len(dist) > 1 else 0),
        "token depths multiset": tuple(tokd), "-token depths": tuple(-a for a in tokd),
        "sum token depth": sum(tokd), "token heights multiset": tuple(toh), "sum token height": sum(toh),
        "reach size": len(reach), "bad depth": badd, "(g,bad depth)": (g, badd),
        "(-g,bad depth,d)": (-g, badd, d), "(-g,-bad depth,d)": (-g, -badd, d),
        "good depths": tuple(goodd), "(-g, sum depth)": (-g, sum(tokd)), "t2t arcs": t2t,
        "(d,t2t)": (d, t2t), "(-g,t2t,d)": (-g, t2t, d),
    }

if __name__ == "__main__":
    K = int(sys.argv[1]); files = sys.argv[2:]
    R = defaultdict(Counter); C = Counter(); nm = 0
    byclass = defaultdict(lambda: defaultdict(Counter))
    for f in files:
        for item in json.load(open(f)):
            tt = item["tt"] if isinstance(item, dict) else item; n = len(tt)
            ms = analyse(tt, n, K, C)
            if not ms: continue
            p = ms[0]["p"]; cache = {}
            def cand(x):
                if x not in cache: cache[x] = candidates(tt, n, x, p)
                return cache[x]
            for m in ms:
                nm += 1
                cx, cy = cand(m["x"]), cand(m["y"])
                cls = ("good" if m["v"] in m["D"] else "bad") + ">" + ("good" if m["w"] in m["Dy"] else "bad")
                for k in cx:
                    r = "<" if cy[k] < cx[k] else ("=" if cy[k] == cx[k] else ">")
                    R[k][r] += 1; byclass[k][cls][r] += 1
    print("moves", nm)
    for k in R:
        rises = R[k][">"]
        cl = {c: dict(v) for c, v in byclass[k].items()}
        print("%-26s down %6d  same %6d  up %6d   %s" % (k, R[k]["<"], R[k]["="], rises,
              "" if rises == 0 else "rises in: " + ", ".join("%s %d" % (c, v.get(">", 0)) for c, v in cl.items() if v.get(">", 0))))
