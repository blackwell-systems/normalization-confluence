#!/usr/bin/env python3
"""SPIKE (spike/go-extraction): differential test of the generated Go rules
checker (gocheck_ast) against the OCaml-extracted astchecker. Random machines
(and some malformed ones), with and without a pairs file; the exit code and
stdout must be identical. Usage:
  difftest_ast.py <ocaml astchecker> <go gocheck_ast> <count> [seed]"""
import os, random, subprocess, sys, tempfile


def expr(rng, nv, depth):
    r = rng.random()
    if depth <= 0 or r < 0.4:
        if rng.random() < 0.6:
            return "(var %d)" % rng.randrange(nv)
        lit = rng.randint(-4, 4)
        if rng.random() < 0.03:
            lit = rng.choice([2147483647, -2147483647, 2147483648, 10**12, 1073741824])
        return "(lit %d)" % lit
    return "(%s %s %s)" % (rng.choice(["add", "sub"]), expr(rng, nv, depth - 1), expr(rng, nv, depth - 1))


def pred(rng, nv, depth):
    r = rng.random()
    if depth <= 0 or r < 0.6:
        return "(%s %s %s)" % (rng.choice(["le", "lt", "eq"]), expr(rng, nv, 1), expr(rng, nv, 1))
    if r < 0.75:
        return "(not %s)" % pred(rng, nv, depth - 1)
    op = rng.choice(["and", "or"])
    return "(%s %s)" % (op, " ".join(pred(rng, nv, depth - 1) for _ in range(rng.randint(0, 2))))


def xform(rng, nv):
    return "(do %s)" % " ".join("(set %d %s)" % (rng.randrange(nv), expr(rng, nv, 2))
                                for _ in range(rng.randint(1, 2)))


def machine(rng):
    nv = rng.randint(1, 3)
    doms = [rng.randint(1, 5) for _ in range(nv)]
    lines = ["(doms %s)" % " ".join(map(str, doms))]
    if rng.random() < 0.5:
        lines.append("(mins %s)" % " ".join(str(rng.randint(-3, 2)) for _ in range(nv)))
    for _ in range(rng.randint(0, 2)):
        lines.append("(inv %s %s)" % (pred(rng, nv, 1), xform(rng, nv)))
    ne = rng.randint(1, 4)
    for _ in range(ne):
        if rng.random() < 0.5:
            lines.append("(ev %s)" % xform(rng, nv))
        else:
            lines.append("(evwhen %s %s)" % (pred(rng, nv, 1), xform(rng, nv)))
    text = "\n".join(lines) + "\n"
    if rng.random() < 0.05:  # malformed input: both must reject it the same way
        i = rng.randrange(len(text))
        text = text[:i] + rng.choice([")", "(", "x", "-", "99999999999", ""]) + text[i + 1:]
    pairs = None
    if rng.random() < 0.5:
        if rng.random() < 0.2:
            pairs = "pairs all\n"
        else:
            k = rng.randint(0, 3)
            ps = [(rng.randrange(ne), rng.randrange(ne)) for _ in range(k)]
            pairs = "pairs %d %s\n" % (k, " ".join("%d %d" % p for p in ps))
    return text, pairs


def main():
    ocaml, gobin, count = sys.argv[1], sys.argv[2], int(sys.argv[3])
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    bad = 0
    codes = {}
    with tempfile.TemporaryDirectory() as d:
        mp, pp = os.path.join(d, "m.machine"), os.path.join(d, "m.pairs")
        for i in range(count):
            text, pairs = machine(rng)
            open(mp, "w").write(text)
            args = [mp]
            if pairs is not None:
                open(pp, "w").write(pairs)
                args.append(pp)
            o = subprocess.run([ocaml] + args, capture_output=True)
            g = subprocess.run([gobin] + args, capture_output=True)
            codes[o.returncode] = codes.get(o.returncode, 0) + 1
            if o.returncode != g.returncode or o.stdout != g.stdout:
                bad += 1
                print("DISAGREE case %d: ocaml=%d go=%d" % (i, o.returncode, g.returncode))
                print(text, pairs)
                print(o.stdout.decode(), g.stdout.decode(), g.stderr.decode()[:500])
    print("%d cases, exit codes %s, %d disagreements" % (count, dict(sorted(codes.items())), bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
