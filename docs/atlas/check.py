#!/usr/bin/env python3
"""Check the Convergence Atlas poster against the development.

Run from anywhere: python3 docs/atlas/check.py

Fails (exit 1) if:
  - a theorem name in docs/atlas/regimes.js (a tile's thm, its theorems, its needed counterexamples)
    or on a plate in docs/atlas/poster.html is not declared as a Theorem, Lemma or Corollary in
    coq/*.v, or is not in coq/verify.sh's Print Assumptions list;
  - a name in a tile's theorems is not declared in one of the tile's modules, a module is missing,
    or a module declares none of the tile's theorems;
  - a tile's section anchor (or, for a gap, the open-gaps anchor) is not a heading of REGIME-AUDIT.md;
  - the theorem count on the poster differs from verify.sh's gate threshold.
"""
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
COQ = ROOT / "coq"
AUDIT = ROOT / "REGIME-AUDIT.md"
GAPS_ANCHOR = "the-open-gaps"

NAME = r"[A-Za-z_][A-Za-z0-9_']*"


def load_atlas():
    src = (HERE / "regimes.js").read_text(encoding="utf-8")
    start = src.index("window.ATLAS =") + len("window.ATLAS =")
    return json.loads(src[start:].strip().rstrip(";"))


def coq_declarations():
    decl = {}
    pat = re.compile(r"^\s*(?:Theorem|Lemma|Corollary)\s+(" + NAME + r")\b", re.M)
    for v in sorted(COQ.glob("*.v")):
        for m in pat.finditer(v.read_text(encoding="utf-8")):
            decl.setdefault(m.group(1), set()).add(v.name)
    return decl


def gate():
    text = (COQ / "verify.sh").read_text(encoding="utf-8")
    names = set(re.findall(r"^Print Assumptions (?:NC\.\w+\.)?(" + NAME + r")\.\s*$", text, re.M))
    m = re.search(r'\[ "\$N" -lt (\d+) \]', text)
    return names, int(m.group(1)) if m else None


def slug(heading):
    s = heading.strip().lower()
    s = re.sub(r"[^\w\- ]", "", s)
    return s.replace(" ", "-")


def anchors(path):
    seen, out = {}, set()
    in_fence = False
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("```"):
            in_fence = not in_fence
        if in_fence:
            continue
        m = re.match(r"^#{1,6}\s+(.*)$", line)
        if not m:
            continue
        base = slug(m.group(1))
        n = seen.get(base, 0)
        seen[base] = n + 1
        out.add(base if n == 0 else f"{base}-{n}")
    return out


def main():
    atlas = load_atlas()
    decl = coq_declarations()
    gated, threshold = gate()
    heads = anchors(AUDIT)
    errors = []
    names = {}  # name -> where it is used

    def use(name, where):
        names.setdefault(name, []).append(where)

    tiles = 0
    for fam in atlas["families"]:
        for t in fam["tiles"]:
            tiles += 1
            where = f'{fam["code"]} {t["name"]}'
            if t.get("thm"):
                use(t["thm"], where + " (tile)")
            for n in t.get("theorems", []):
                use(n, where + " (theorems)")
            for pair in t.get("needed", []):
                use(pair[0], where + " (needed)")
            mods = t.get("modules", [])
            for mod in mods:
                if not (COQ / mod).exists():
                    errors.append(f"{where}: module {mod} not found in coq/")
            for n in t.get("theorems", []):
                if n in decl and not (decl[n] & set(mods)):
                    errors.append(f"{where}: {n} is declared in {sorted(decl[n])}, not in {mods}")
            for mod in mods:
                if not any(mod in decl.get(n, ()) for n in t.get("theorems", [])):
                    errors.append(f"{where}: module {mod} declares none of the tile's theorems")
            if t["section"] not in heads:
                errors.append(f'{where}: anchor #{t["section"]} is not a heading of REGIME-AUDIT.md')
            if "gap" in t and GAPS_ANCHOR not in heads:
                errors.append(f"{where}: anchor #{GAPS_ANCHOR} is not a heading of REGIME-AUDIT.md")
            if t["kind"] in ("exact", "hard") and not t.get("thm"):
                errors.append(f"{where}: {t['kind']} tile with no theorem")

    poster = (HERE / "poster.html").read_text(encoding="utf-8")
    plates = re.findall(r'class="plate-thm">(' + NAME + r")<", poster)
    for n in plates:
        use(n, "plate")

    for n, where in sorted(names.items()):
        if n not in decl:
            errors.append(f"{n}: not declared as Theorem/Lemma/Corollary in coq/*.v ({where[0]})")
        if n not in gated:
            errors.append(f"{n}: not in coq/verify.sh's Print Assumptions list ({where[0]})")

    m = re.search(r"([\d,]+) axiom-free theorems", poster)
    shown = int(m.group(1).replace(",", "")) if m else None
    if threshold is None:
        errors.append("verify.sh: gate threshold not found")
    elif shown != threshold:
        errors.append(f"poster.html: theorem count {shown} differs from verify.sh's gate {threshold}")

    print(f"{tiles} tiles, {len(plates)} plates, {len(names)} distinct theorem names, gate {threshold}")
    if errors:
        for e in errors:
            print("FAIL:", e)
        sys.exit(1)
    print("PASS: every name is declared in coq/*.v and gated by verify.sh; every anchor exists")


if __name__ == "__main__":
    main()
