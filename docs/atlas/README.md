# Convergence Atlas: poster draft

A one-page poster of the regime map: eleven families of regimes, one tile per regime, colored by
what the development proves there (blue: an exact condition; orange: a mechanized hardness
reduction; dashed: an open, numbered gap; hatched: excluded by design), and four plates of the
counterexamples that show a condition is needed. A gold ring marks the results closed in #117.

It is a draft of the Convergence Atlas planned in [docs/ROADMAP.md](../ROADMAP.md#planned-artifact-the-convergence-atlas).
It adds no proofs and claims no more than [REGIME-AUDIT.md](../../REGIME-AUDIT.md) does.

## Opening it

Open `docs/atlas/poster.html` in a browser (from disk is fine: the tile data is a plain script,
`regimes.js`, not a fetched file). The poster is 1800 x 2800 px and prints at that size; the IBM
Plex fonts load from Google Fonts, with system fallbacks offline.

Hover, focus (Tab) or tap a tile for its detail card: the setting, the exact condition (or the
hardness result, the open part, or why the regime is outside the map), the counterexamples showing
each conjunct is needed, what gsm checks, the theorem names with their Coq modules, and a link to
the audit section (and the gap row, for open tiles). Enter or Space opens the card and moves focus
into it; Escape closes it. On a narrow screen the card is a bottom sheet. Cards do not print.

## Files

- `poster.html`: the poster and the card behavior.
- `regimes.js`: the tiles and card text (`window.ATLAS`), one entry per tile, each paraphrasing a
  row of [REGIME-AUDIT.md](../../REGIME-AUDIT.md) (and [docs/COVERAGE.md](../COVERAGE.md) for the
  gaps).
- `check.py`: verifies the names. Every theorem name on a tile, in a card or on a plate must be
  declared as a Theorem, Lemma or Corollary in `coq/*.v` and be in `coq/verify.sh`'s
  Print Assumptions list; each card's theorems must be declared in the modules it names; every link
  anchor must be a heading of REGIME-AUDIT.md; the theorem count on the poster must equal the
  gate's threshold; and the open tiles must match the open gaps in REGIME-AUDIT.md (no tile shows a
  closed gap as open, and every open convergence gap in its Current state sentence has a tile).
  CI runs it on every PR (`.github/workflows/atlas.yml`).

```
python3 docs/atlas/check.py
```

Keeping it current: a PR that changes a regime (closes or narrows a gap, adds an exact theorem a
tile should cite) updates the affected entries in `regimes.js` from its audit rows in the same PR,
and runs `check.py`. A closed gap's tile becomes an exact tile with its theorem and card; a narrowed
gap keeps its open tile with the card's open part restated. The merge script keeps the theorem
count in step.
