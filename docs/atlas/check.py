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
  - the theorem count on the poster or the front page (docs/site/index.html) differs from verify.sh's
    gate threshold, or the front page's open-problem count differs from the audit's;
  - the front page's open-problem list differs from the audit's open gaps, or a theorem link on the
    front page (class="thm") does not point at the line declaring that name in coq/, or names an
    ungated theorem, or an atlas count on the front page (tiles, families, tiles by kind) differs
    from docs/atlas/regimes.js, or the front page's prediction counts differ from the committed
    predictions table in research/predictions/README.md;
  - a theorem link on the engineer's guide (docs/site/guide/index.html) fails the front page's link
    check above, the guide has no theorem links, or it contains an em dash;
  - a frozen kernel file listed in research/predictions/frozen.sha256 changed;
  - an open tile names a gap REGIME-AUDIT.md lists as closed or as a design exclusion, or an open
    convergence gap in REGIME-AUDIT.md's "Current state" sentence has no open tile;
  - a tile lacks a unique id, its plain answer, a layer (A, B, C, AB, BC or AC), an axis row and
    column from the axes block, or a paper destination from the paper block; a plain answer is too
    long or does not match its kind (open tiles start "Open:", excluded tiles "Excluded:", hard tiles
    name NP), or a plain answer or a tour stop uses a bare research abbreviation (CC1, CC2, XU, XUcR,
    PJC, PCC, ACC, GC, C1, C2), which belong in the detail card;
  - a paper section title in regimes.js differs from the section with that number in docs/paper
    (main.tex input order, appendices lettered), or the layers, framework or tour blocks are
    malformed (a tour stop names a tile id that does not exist); their theorem names are checked
    like the tiles' above;
  - regimes.js, poster.html or the front page contains an em dash.
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


def audit_gaps():
    """Return (open convergence gaps from the Current state sentence, {gap: closed?})."""
    text = AUDIT.read_text(encoding="utf-8")
    m = re.search(r"Open convergence gaps: ([^;.]*)", text)
    current = set()
    if m:
        for a, b in re.findall(r"(\d+) to (\d+)", m.group(1)):
            current.update(range(int(a), int(b) + 1))
        current.update(int(x) for x in re.findall(r"\d+", re.sub(r"\d+ to \d+", "", m.group(1))))
    start = text.index("### The open gaps")
    end = text.find("\n### ", start + 10)
    rows = {}
    for line in text[start:end if end > 0 else None].splitlines():
        r = re.match(r"^\| (\d+) \|[^|]*\| ([^|]*)\|", line)
        if r:
            kind = r.group(2).strip().lower()
            rows[int(r.group(1))] = kind.startswith("**closed**") or kind.startswith("design")
    return current, rows


LAYERS = ("A", "B", "C", "AB", "BC", "AC")
ID = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
PLAIN_MAX = 150
JARGON = re.compile(r"\b(CC1|CC2|XU|XUcR|PJC|PCC|ACC|GC|C1|C2)\b")


def paper_sections():
    """Return {"section.N" or "appendix.X": title} from docs/paper/main.tex and its inputs."""
    paper = ROOT / "docs" / "paper"
    main_tex = paper / "main.tex"
    if not main_tex.exists():
        return None
    out, n, app = {}, 0, None
    files = []
    for line in main_tex.read_text(encoding="utf-8").splitlines():
        m = re.search(r"\\input\{([^}]+)\}", line.split("%", 1)[0])
        if m:
            files.append(paper / (m.group(1) + ("" if m.group(1).endswith(".tex") else ".tex")))
    for f in files:
        if not f.exists():
            continue
        for line in f.read_text(encoding="utf-8").splitlines():
            line = line.split("%", 1)[0]
            if re.match(r"^\s*\\appendix\b", line):
                app = 0
            m = re.match(r"^\s*\\section\{(.*?)\}(?:\\label|\s*$)", line)
            if not m:
                continue
            title = m.group(1).replace("``", '"').replace("''", '"')
            if app is None:
                n += 1
                out[f"section.{n}"] = title
            else:
                out[f"appendix.{chr(ord('A') + app)}"] = title
                app += 1
    return out


def check_theory(atlas, use, errors):
    """Validate the theory views' data: tile fields, layers, framework, axes, paper and tour."""
    paper = atlas.get("paper", {})
    secs = paper.get("sections", {})
    actual = paper_sections()
    if not paper.get("url", "").endswith(".pdf"):
        errors.append("regimes.js: paper.url is not a PDF link")
    for key, title in secs.items():
        if actual is not None and actual.get(key) != title:
            errors.append(f"regimes.js: paper section {key} is titled {title!r}, docs/paper has {actual.get(key)!r}")
    axes = atlas.get("axes", {})
    shapes = [s["id"] for s in axes.get("shapes", [])]
    models = [m["id"] for m in axes.get("models", [])]
    if len(set(shapes)) != len(shapes) or "other" not in shapes:
        errors.append("regimes.js: axes.shapes ids must be unique and include an 'other' lane")
    if len(set(models)) != len(models) or not models:
        errors.append("regimes.js: axes.models ids must be unique and nonempty")
    ids = {}
    for fam in atlas["families"]:
        for t in fam["tiles"]:
            where = f'{fam["code"]} {t["name"]}'
            tid = t.get("id", "")
            if not ID.match(tid):
                errors.append(f"{where}: missing or malformed id {tid!r}")
            elif tid in ids:
                errors.append(f"{where}: id {tid} also used by {ids[tid]}")
            ids[tid] = where
            plain = t.get("plain", "")
            if not plain.strip():
                errors.append(f"{where}: no plain answer")
            elif len(plain) > PLAIN_MAX:
                errors.append(f"{where}: plain answer is {len(plain)} characters (at most {PLAIN_MAX})")
            elif t["kind"] == "open" and not plain.startswith("Open:"):
                errors.append(f'{where}: an open tile\'s plain answer must start "Open:"')
            elif t["kind"] == "excl" and not plain.startswith("Excluded:"):
                errors.append(f'{where}: an excluded tile\'s plain answer must start "Excluded:"')
            elif t["kind"] == "hard" and "NP" not in plain:
                errors.append(f"{where}: a hard tile's plain answer must say what is NP-complete or NP-hard")
            elif t["kind"] in ("exact", "hard") and plain.startswith(("Open:", "Excluded:")):
                errors.append(f"{where}: plain answer does not match the tile's kind")
            if JARGON.search(plain):
                errors.append(f"{where}: plain answer uses {JARGON.search(plain).group(1)}; say it in words")
            if t.get("layer") not in LAYERS:
                errors.append(f"{where}: layer {t.get('layer')!r} is not one of {', '.join(LAYERS)}")
            if t.get("shape") not in shapes:
                errors.append(f"{where}: shape {t.get('shape')!r} is not an axes.shapes id")
            if t.get("model") not in models:
                errors.append(f"{where}: model {t.get('model')!r} is not an axes.models id")
            if t.get("paper") not in secs:
                errors.append(f"{where}: paper {t.get('paper')!r} is not a key of paper.sections")
    layers = atlas.get("layers", [])
    if [l.get("id") for l in layers] != list(LAYERS):
        errors.append(f"regimes.js: layers must be, in order, {', '.join(LAYERS)}")
    for l in layers:
        if l.get("paper") not in secs:
            errors.append(f"regimes.js: layer {l.get('id')} paper {l.get('paper')!r} is not a key of paper.sections")
        if not l.get("asks"):
            errors.append(f"regimes.js: layer {l.get('id')} has no 'asks' line")
        for k in ("thm", "stop"):
            if len(l.get("id", "")) == 2 and not l.get(k):
                errors.append(f"regimes.js: interface {l.get('id')} has no {k}")
            if l.get(k):
                use(l[k], f"layer {l.get('id')}")
    fw = atlas.get("framework", {})
    if len(fw.get("scales", [])) != 3 or len(fw.get("links", [])) != 2:
        errors.append("regimes.js: framework needs three scales and two links")
    for sc in fw.get("scales", []):
        use(sc["thm"], "framework scale")
    for ln in fw.get("links", []) + [fw.get("together", {"thms": []})]:
        for n in ln["thms"]:
            use(n, "framework")
    if fw.get("paper") not in secs:
        errors.append("regimes.js: framework.paper is not a key of paper.sections")
    tour = atlas.get("tour", [])
    if not 5 <= len(tour) <= 6:
        errors.append(f"regimes.js: the tour has {len(tour)} stops (5 or 6)")
    for i, stop in enumerate(tour, 1):
        if stop.get("tile") not in ids:
            errors.append(f"regimes.js: tour stop {i} names tile {stop.get('tile')!r}, which does not exist")
        if not stop.get("title") or not stop.get("text"):
            errors.append(f"regimes.js: tour stop {i} needs a title and a text")
        if JARGON.search(stop.get("text", "")):
            errors.append(f"regimes.js: tour stop {i} uses {JARGON.search(stop['text']).group(1)}; say it in words")
        if stop.get("thm"):
            use(stop["thm"], f"tour stop {i}")
    if "\u2014" in (HERE / "regimes.js").read_text(encoding="utf-8"):
        errors.append("regimes.js: contains an em dash")


def check_thm_links(page, label, gated, errors):
    """Check every theorem link (class="thm") on a page: it points at the line declaring that name
    in coq/, and a Theorem, Lemma or Corollary is gated. Returns the number of links checked."""
    decl_pat = r"^\s*(Definition|Theorem|Lemma|Corollary)\s+"
    links = re.findall(r'<a class="thm" href="[^"]*/coq/(\w+\.v)#L(\d+)">(' + NAME + r")</a>", page)
    for f, line, n in links:
        src = COQ / f
        lines = src.read_text(encoding="utf-8").splitlines() if src.exists() else []
        i = int(line)
        m2 = re.match(decl_pat + re.escape(n) + r"\b", lines[i - 1]) if 0 < i <= len(lines) else None
        if not m2:
            errors.append(f"{label}: {n} is not declared at coq/{f} line {line}")
        elif m2.group(1) != "Definition" and n not in gated:
            errors.append(f"{label}: {n} is not in coq/verify.sh's Print Assumptions list")
    return len(links)


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

    check_theory(atlas, use, errors)

    current, rows = audit_gaps()
    if not current:
        errors.append("REGIME-AUDIT.md: no 'Open convergence gaps:' sentence found")
    shown_open = set()
    for fam in atlas["families"]:
        for t in fam["tiles"]:
            if t["kind"] == "open":
                g = int(t.get("gap", t.get("mark", 0)))
                shown_open.add(g)
                if g not in rows:
                    errors.append(f'{fam["code"]} {t["name"]}: gap {g} has no row in the open gaps tables')
                elif rows[g]:
                    errors.append(f'{fam["code"]} {t["name"]}: gap {g} is closed in REGIME-AUDIT.md but shown open')
    for g in sorted(current - shown_open):
        errors.append(f"gap {g} is open in REGIME-AUDIT.md's Current state but has no open tile")

    poster = (HERE / "poster.html").read_text(encoding="utf-8")
    plates = re.findall(r'class="plate-thm">(' + NAME + r")<", poster)
    for n in plates:
        use(n, "plate")

    for n, where in sorted(names.items()):
        if n not in decl:
            errors.append(f"{n}: not declared as Theorem/Lemma/Corollary in coq/*.v ({where[0]})")
        if n not in gated:
            errors.append(f"{n}: not in coq/verify.sh's Print Assumptions list ({where[0]})")

    site = ROOT / "docs" / "site" / "index.html"
    if site.exists():
        page = site.read_text(encoding="utf-8")
        ms = re.search(r'id="gate-count">([\d,]+)<', page)
        if not ms or threshold is None or int(ms.group(1).replace(",", "")) != threshold:
            errors.append(f"docs/site/index.html: theorem count {ms.group(1) if ms else None} differs from verify.sh's gate {threshold}")
        mo = re.search(r'id="open-count">(\d+)<', page)
        if not mo or int(mo.group(1)) != len(current):
            errors.append(f"docs/site/index.html: open-problem count {mo.group(1) if mo else None} differs from REGIME-AUDIT.md's {len(current)}")
        kinds = {}
        for fam in atlas["families"]:
            for t in fam["tiles"]:
                kinds[t["kind"]] = kinds.get(t["kind"], 0) + 1
        want = {"atlas-tiles": tiles, "atlas-families": len(atlas["families"]), "atlas-exact": kinds.get("exact", 0),
                "atlas-hard": kinds.get("hard", 0), "atlas-open": kinds.get("open", 0), "atlas-excl": kinds.get("excl", 0)}
        for key, n in want.items():
            mk = re.search(r'id="' + key + r'">(\d+)<', page)
            if not mk or int(mk.group(1)) != n:
                errors.append(f"docs/site/index.html: {key} is {mk.group(1) if mk else None}, the atlas has {n}")
        preds = ROOT / "research" / "predictions" / "README.md"
        if preds.exists():
            ptxt = preds.read_text(encoding="utf-8")
            pstart = ptxt.find("## Committed predictions")
            prow = [l for l in ptxt[pstart:].splitlines() if l.startswith("| [")] if pstart >= 0 else []
            pout = [l.rstrip(" |").rsplit("|", 1)[-1].strip() for l in prow]
            want_p = {"pred-total": len(prow), "pred-confirmed": sum(1 for o in pout if o.startswith("PASS"))}
            for key, n in want_p.items():
                mk = re.search(r'id="' + key + r'">(\d+)<', page)
                if mk and int(mk.group(1)) != n:
                    errors.append(f"docs/site/index.html: {key} is {mk.group(1)}, research/predictions/README.md has {n}")
        ol = re.search(r'id="open-list">(.*?)</ol>', page, re.S)
        listed = {int(g) for g in re.findall(r'class="g">Gap (\d+)<', ol.group(1))} if ol else set()
        if listed != current:
            errors.append(f"docs/site/index.html: open-problem list {sorted(listed)} differs from REGIME-AUDIT.md's {sorted(current)}")
        check_thm_links(page, "docs/site/index.html", gated, errors)
        if "\u2014" in page:
            errors.append("docs/site/index.html: contains an em dash")

    guide = ROOT / "docs" / "site" / "guide" / "index.html"
    if guide.exists():
        gpage = guide.read_text(encoding="utf-8")
        if not check_thm_links(gpage, "docs/site/guide/index.html", gated, errors):
            errors.append("docs/site/guide/index.html: no theorem links found")
        if "\u2014" in gpage:
            errors.append("docs/site/guide/index.html: contains an em dash")

    if "\u2014" in poster:
        errors.append("poster.html: contains an em dash")
    m = re.search(r"([\d,]+) axiom-free theorems", poster)
    shown = int(m.group(1).replace(",", "")) if m else None
    if threshold is None:
        errors.append("verify.sh: gate threshold not found")
    elif shown != threshold:
        errors.append(f"poster.html: theorem count {shown} differs from verify.sh's gate {threshold}")

    frozen = ROOT / "research" / "predictions" / "frozen.sha256"
    if frozen.exists():
        import hashlib
        for line in frozen.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            digest, rel = line.split(None, 1)
            f = ROOT / rel.strip()
            got = hashlib.sha256(f.read_bytes()).hexdigest() if f.exists() else None
            if got != digest:
                errors.append(f"{rel.strip()}: frozen kernel file changed or missing (research/predictions/frozen.sha256)")

    print(f"{tiles} tiles, {len(plates)} plates, {len(names)} distinct theorem names, gate {threshold}")
    if errors:
        for e in errors:
            print("FAIL:", e)
        sys.exit(1)
    print("PASS: every name is declared in coq/*.v and gated by verify.sh; every anchor exists")


if __name__ == "__main__":
    main()
