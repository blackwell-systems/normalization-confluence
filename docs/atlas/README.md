# Convergence Atlas: poster draft

A one-page poster of the regime map: eleven families of regimes, one tile per regime, colored by
what the development proves there (blue: an exact condition; orange: a mechanized hardness
reduction; dashed: an open, numbered gap; hatched: excluded by design), and four plates of the
counterexamples that show a condition is needed. A gold ring marks the results closed in #117.
Every tile carries its answer in one plain line on its face, relative to the tile's stated model.

It is a draft of the Convergence Atlas planned in [docs/ROADMAP.md](../ROADMAP.md#planned-artifact-the-convergence-atlas).
It adds no proofs and claims no more than [REGIME-AUDIT.md](../../REGIME-AUDIT.md) does.

## Opening it

Open `docs/atlas/poster.html` in a browser (from disk is fine: the tile data is a plain script,
`regimes.js`, not a fetched file). The page is up to 1800 px wide and reflows down to phone width;
printed, it is 1800 px wide, and the catalog view fits an 1800 x 4000 px page. The IBM Plex fonts
load from Google Fonts, with system fallbacks offline.

Hover, focus (Tab) or tap a tile for its detail card: the plain answer, the setting, the exact
condition (or the hardness result, the open part, or why the regime is outside the map), the
counterexamples showing each conjunct is needed, what gsm checks, the theorem names with their Coq
modules, where the tile sits in the theory (its layer and its axis cell), a link to the audit section
(and the gap row, for open tiles), and a link to the paper section that treats it (the PDF's named
destination, such as `#section.7`; tiles no section treats on its own link to Section 11, the regime
map). Enter or Space opens the card and moves focus into it; Escape closes it. On a narrow screen the
card is a bottom sheet. Cards do not print.

## Views

A switch above the legend shows the same 60 tiles three ways (the choice is kept in the URL:
`#framework`, `#axes`):

- **Catalog**: the eleven families, as before.
- **Framework**: the tiles grouped by the part of the theory that decides them. A header states the
  main result at three scales (state descent, history descent, canonical recurrence) and the proved
  hierarchy, in the wording of the paper's Figure 1 (`docs/paper/sections/03-main-result.tex`):
  state and history descent are independent; together, with terminating repair, they are exactly the
  single-registry theorem; infinite runs read repair only through its result. Below it, one group
  per layer (A: executions; B: consistent states; C: long-run behavior), each with one line saying
  what it asks, then one group per interface (A to B, B to C, A to C) with its theorem and the
  counterexample that marks where it stops, as in the paper's Figure 2.
- **Axes**: the tiles on the model's two main axes from [docs/COVERAGE.md](../COVERAGE.md): network
  shape down (one registry, acyclic federation, monotone cycles, invertible cycles, lossy networks,
  composition, and an "other" lane for tiles whose question spans several shapes), execution and
  delivery model across (static, repair dynamics, events exactly once, other delivery, events with
  propagation, rules changing mid-run). Each row counts its open tiles; the open gaps sit on the cycle
  rows, composition and the other lane.

**Start here** runs a six-stop tour over real tiles (the shelf and the single-registry theorem,
causal delivery, an acyclic federation, a unique consistent state no run reaches, the NP-complete
lossy cell, and an open gap), with one takeaway per stop. Next and Back (or the arrow keys) step
through it; Escape or the close button ends it. It works in every view and on a phone.

## Files

- `poster.html`: the poster and the card behavior.
- `regimes.js`: the tiles and card text (`window.ATLAS`), one entry per tile, each paraphrasing a
  row of [REGIME-AUDIT.md](../../REGIME-AUDIT.md) (and [docs/COVERAGE.md](../COVERAGE.md) for the
  gaps). The theory views add, per tile: `id` (stable, used by the tour), `plain` (the one-line
  answer), `layer` (`A`, `B`, `C`, or the interface `AB`, `BC`, `AC` when the tile's theorems use
  two layers), `shape` and `model` (its row and column in the Axes view) and `paper` (a named
  destination of the paper PDF). Top-level blocks hold the paper link and section titles, the
  framework header, the layers and interfaces, the axes and the tour. The file's header comment
  documents each field.
- `check.py`: verifies the names. Every theorem name on a tile, in a card or on a plate must be
  declared as a Theorem, Lemma or Corollary in `coq/*.v` and be in `coq/verify.sh`'s
  Print Assumptions list; each card's theorems must be declared in the modules it names; every link
  anchor must be a heading of REGIME-AUDIT.md; the theorem count on the poster must equal the
  gate's threshold; and the open tiles must match the open gaps in REGIME-AUDIT.md (no tile shows a
  closed gap as open, and every open convergence gap in its Current state sentence has a tile). It
  also checks the theory views' data: every tile has a unique id, a plain answer that fits its kind
  (open tiles start "Open:", excluded tiles "Excluded:", hard tiles name NP), a layer in the allowed
  set, an axis row and column that exist, and a paper destination whose section title matches the
  section with that number in `docs/paper`; the tour's tile ids exist; and every theorem name in the
  layers, framework and tour blocks is declared and gated like the tiles'.
  CI runs it on every PR (`.github/workflows/atlas.yml`).

```
python3 docs/atlas/check.py
```

Keeping it current: a PR that changes a regime (closes or narrows a gap, adds an exact theorem a
tile should cite) updates the affected entries in `regimes.js` from its audit rows in the same PR,
and runs `check.py`. A closed gap's tile becomes an exact tile with its theorem and card; a narrowed
gap keeps its open tile with the card's open part restated. The merge script keeps the theorem
count in step.

## Published copy

The poster is published to GitHub Pages at
<https://blackwell-systems.github.io/normalization-confluence/> by `.github/workflows/pages.yml`
on every push to main that touches the atlas, the audit or the gate. The workflow runs `check.py`
first, so a poster that disagrees with the audit or the gate is not published.
