#!/usr/bin/env python3
"""SPIKE (spike/go-extraction): differential test of the generated Go checker
against the OCaml-extracted checker_fast (and a direct Python reading of
check_tables' property, TableCheck.v). Usage:
  difftest.py <ocaml checker_fast> <go gocheck> <count> [seed]
Exits non-zero on any disagreement."""
import os, random, subprocess, sys, tempfile

# DIFF_MAXDIM=16 reaches tries of depth 2 (n up to 4096).
MAXDIM = int(os.environ.get("DIFF_MAXDIM", "5"))


def machine(rng):
    # A product of small counters; event e bumps counter e % k (mod its size),
    # so all events commute. Then optionally restrict validity and perturb.
    k = rng.randint(1, 3)
    dims = [rng.randint(1, MAXDIM) for _ in range(k)]
    n = 1
    for d in dims:
        n *= d
    ne = rng.randint(1, 4)

    def dec(s):
        v = []
        for d in dims:
            v.append(s % d); s //= d
        return v

    def enc(v):
        s, m = 0, 1
        for x, d in zip(v, dims):
            s += x * m; m *= d
        return s

    valid = [True] * n
    if rng.random() < 0.5:
        for s in range(1, n):
            valid[s] = rng.random() < 0.7
    vs = [s for s in range(n) if valid[s]]
    nf = [s if valid[s] else rng.choice(vs) for s in range(n)]
    rows = []
    for e in range(ne):
        c = e % k
        row = []
        for s in range(n):
            v = dec(s); v[c] = (v[c] + 1 + e // k) % dims[c]
            row.append(nf[enc(v)])
        rows.append(row)
    for _ in range(rng.choice([0, 0, 1, 2])):
        r = rng.randrange(ne); s = rng.randrange(n)
        rows[r][s] = rng.choice(vs) if rng.random() < 0.8 else rng.randrange(n)
    if rng.random() < 0.1:
        nf[rng.randrange(n)] = rng.randrange(n)
    if rng.random() < 0.5:
        pairs = None
    else:
        pairs = [(rng.randrange(ne), rng.randrange(ne)) for _ in range(rng.randint(0, 4))]
    return n, ne, nf, rows, pairs


def reference(n, ne, nf, rows, pairs):
    """check_tables (TableCheck.v), read directly."""
    inV = lambda x: x < n and nf[x] == x
    inD = lambda s: s < n and (inV(s) or s == 0)
    ps = pairs if pairs is not None else [(i, j) for i in range(ne) for j in range(i + 1, ne)]
    if not all(a < ne and b < ne for a, b in ps):
        return False
    if not all(inV(nf[s]) for s in range(n)):
        return False
    if not all(inV(rows[e][s]) for e in range(ne) for s in range(n)):
        return False
    T = lambda e, s: rows[e][s] if s < n else 0
    return all(T(a, T(b, s)) == T(b, T(a, s)) for a, b in ps for s in range(n) if inD(s))


def write(path, n, ne, nf, rows, pairs):
    with open(path, "w") as f:
        f.write("gsm-tables 2\n%d %d\nnf %s\n" % (n, ne, " ".join(map(str, nf))))
        if pairs is None:
            f.write("pairs all\n")
        else:
            f.write("pairs %d %s\n" % (len(pairs), " ".join("%d %d" % p for p in pairs)))
        for r in rows:
            f.write(" ".join(map(str, r)) + "\n")


def main():
    ocaml, gobin, count = sys.argv[1], sys.argv[2], int(sys.argv[3])
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    bad = acc = 0
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "m.tables")
        for i in range(count):
            m = machine(rng)
            write(p, *m)
            o = subprocess.run([ocaml, p], capture_output=True).returncode
            g = subprocess.run([gobin, p], capture_output=True).returncode
            r = 0 if reference(*m) else 1
            acc += (g == 0)
            if not (o == g == r):
                bad += 1
                print("DISAGREE case %d: ocaml=%d go=%d reference=%d" % (i, o, g, r))
                print(open(p).read())
    print("%d cases, %d accepted, %d disagreements" % (count, acc, bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
