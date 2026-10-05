# Documentation map

Every page in this repository, with its role in one line. The front page is
[../README.md](../README.md): the headline, its precision paragraph, where to start, and the papers.

## Pages

| Page | Role |
|---|---|
| [THEORY.md](THEORY.md) | Theory overview: the third regime, what is new (each item marked mechanized, paper or implemented) and what is not, the key concepts, and how the three convergence regimes nest. |
| [REGIMES.md](REGIMES.md) | A decision table and flowchart for when a given (possibly federated, possibly cyclic) governed network converges. Role: the field guide, how to pick a regime as a user. |
| [../REGIME-AUDIT.md](../REGIME-AUDIT.md) | What is proved, regime by regime: for each question, the exact condition with its Coq theorem, the hardness result, or the gap stated in the open, the cheap sufficient condition, and what gsm checks. The certification of the headline; it stays at the root. |
| [ROADMAP.md](ROADMAP.md) | The caveats removed so far (finite state, exactly-once delivery, sufficiency-only conditions, non-monotone cycles), the qualifiers found, what remains open, and which caveats are fundamental limits. Role: what is next. |
| [LANDSCAPE.md](LANDSCAPE.md) | Where this sits relative to CRDTs, consensus, invariant confluence, and the saga pattern, and what it changes. Role: prior work. |
| [SUBSUMPTION.md](SUBSUMPTION.md) | The machine-checked proof that, under causal delivery, op-based CRDTs are exactly the compensation-free fragment of normalization confluence, that state-based CRDTs embed as the semilattice case, and that the inclusion is strict. |
| [CATEGORICAL-STRUCTURE.md](CATEGORICAL-STRUCTURE.md) | Working notes for the companion paper: the federation as a limit, compositionality, the sheaf structure of certificates, `H^1` and minimal coordination. |
| [LYAPUNOV-EXTENSION.md](LYAPUNOV-EXTENSION.md) | A forward-looking research note (nothing proven) mapping the discrete conditions to a continuous state space, WFC as a Lyapunov function and CC as contraction, with the convex-gradient sweet spot where the collapse survives and the multi-basin boundary where it provably does not. |
| [COMPANION-OUTLINE.md](COMPANION-OUTLINE.md) | Planning artifact for the companion paper: thesis, ranked contributions, framing decisions and related-work positioning, as decided before drafting. |
| [../coq/README.md](../coq/README.md) | The mechanized proof: build, the axiom-free gate, how to read a module, and the module index by regime, with one page of full results per regime in [../coq/docs/](../coq/docs). |
| [../coq/PAPER-MAP.md](../coq/PAPER-MAP.md) | Map from every numbered result in the three papers to its Coq theorem (its status columns predate later merges; current status is in REGIME-AUDIT.md). |
| [../coq/extraction/README.md](../coq/extraction/README.md), [../coq/goextract/README.md](../coq/goextract/README.md) | The two verified oracles: the extracted OCaml checkers, and the Go generated from them that gsm runs in process. |
| [../CHANGELOG.md](../CHANGELOG.md) | Notable changes to the papers, the proofs and these pages. |

The pages that used to sit at the repository root (REGIMES, ROADMAP, LANDSCAPE, SUBSUMPTION,
CATEGORICAL-STRUCTURE, LYAPUNOV-EXTENSION, COMPANION-OUTLINE) keep a stub there that points here,
because gsm, Bide, the blog and the papers link to the old paths.

## Which page answers which question

Four pages talk about regimes; each answers one question:

- **Which regime am I in, and what must my system satisfy?** [REGIMES.md](REGIMES.md). It is
  written for a user choosing a design, and it cites theorems without auditing them.
- **What exactly is proved in each regime, and what is not?**
  [../REGIME-AUDIT.md](../REGIME-AUDIT.md). It is the source of truth for status: exact (with the
  `<->` theorem), hardness, or a numbered open gap. Where another page summarizes status, this one
  wins.
- **What is next, and which caveats are fundamental?** [ROADMAP.md](ROADMAP.md). Its Done table is
  history; its open items carry REGIME-AUDIT.md's gap numbers.
- **What is new against prior work?** [LANDSCAPE.md](LANDSCAPE.md) (and [THEORY.md](THEORY.md)
  for the list of contributions).

## Adding a page or a module

- A new note goes in `docs/` with a row in the table above.
- A new Coq module gets a row in the [module index](../coq/README.md#modules-by-regime) and a section
  in the matching `coq/docs/<regime>.md` page, not an appended section of `coq/README.md`; the
  steps are in [Adding a module](../coq/README.md#adding-a-module).
- A change in what is proved for a regime updates its row of
  [../REGIME-AUDIT.md](../REGIME-AUDIT.md) and adds a [../CHANGELOG.md](../CHANGELOG.md) entry.
