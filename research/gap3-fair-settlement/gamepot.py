"""Test candidate potentials on every move of the abstract forest-token game (game.py).
Usage: gamepot.py n K"""
import sys, itertools
from collections import Counter
from game import forests, moves

def path(o, u):
    out = [u]
    while o[out[-1]] != -1: out.append(o[out[-1]])
    return out

def free(o, U, u):
    """number of moves token u can make along its current path before meeting a token or a root"""
    p = path(o, u); Us = set(U); c = 0
    for z in p[1:]:
        if z in Us: return c
        c += 1
    return c

def blocked(o, U, u):
    p = path(o, u); Us = set(U)
    return any(z in Us for z in p[1:])

def cands(o, U, n):
    K = len(U)
    Us = set(U)
    fr = sorted((free(o, U, u) for u in U), reverse=True)
    dp = sorted((len(path(o, u)) - 1 for u in U), reverse=True)
    R = set()
    for u in U: R |= set(path(o, u))
    nb = sum(1 for u in U if not blocked(o, U, u))
    Z=set()
    for u in U:
        for z in path(o,u)[1:]:
            if z in Us: break
            Z.add(z)
    nbk = K - nb
    alld = sum(len(path(o,z))-1 for z in range(n))
    roots = sum(1 for z in range(n) if o[z]==-1)
    anc = sum(1 for z in range(n) for u in U if u in path(o,z)[1:])
    ancs = sum(1 for z in range(n) for u in U if u in path(o,z))
    clean = sum(1 for z in range(n) if not any(q in Us for q in path(o,z)))  # no token at or below z
    tokbelow = sum(sum(1 for q in path(o,z) if q in Us) for z in range(n))
    return {
        "sum all depth": alld, "roots": roots, "-roots": -roots, "anc pairs": anc, "-anc pairs": -anc,
        "clean vertices": clean, "-clean": -clean, "token-below count": tokbelow, "-token-below": -tokbelow,
        "(clean, sum free)": (clean, sum(fr)), "(-tokbelow, sum free)": (-tokbelow, sum(fr)),
        "|Z| union of free paths": len(Z), "(|Z|, sum free)": (len(Z), sum(fr)), "(sum free, |Z|)": (sum(fr), len(Z)),
        "|Z|+blocked": len(Z)+nbk, "(|Z|, blocked)": (len(Z), nbk), "(|Z|, -blocked)": (len(Z), -nbk),
        "sum free": sum(fr), "free multiset": tuple(fr), "sum depth": sum(dp), "depth multiset": tuple(dp),
        "reach": len(R), "(sum free, reach)": (sum(fr), len(R)), "unblocked": nb,
        "(sum free, unblocked)": (sum(fr), nb), "(reach, sum free)": (len(R), sum(fr)),
        "reach minus tokens": len(R) - len(U), "max depth": dp[0],
        "sum depth of unblocked": sum(len(path(o, u)) - 1 for u in U if not blocked(o, U, u)),
    }

if __name__ == "__main__":
    n = int(sys.argv[1]); K = int(sys.argv[2])
    R = {}; ex = {}
    for o in forests(n):
        for U in itertools.combinations(range(n), K):
            c0 = cands(o, U, n)
            for v, o2, U2 in moves(o, U, n):
                c1 = cands(o2, U2, n)
                for k in c0:
                    r = "<" if c1[k] < c0[k] else ("=" if c1[k] == c0[k] else ">")
                    R.setdefault(k, Counter())[r] += 1
                    if r == ">" and k not in ex: ex[k] = (o, U, v, o2, U2)
    for k, c in R.items():
        print("%-26s down %7d same %7d up %7d" % (k, c["<"], c["="], c[">"]), "" if k not in ex else "e.g. %s" % (ex[k],))
