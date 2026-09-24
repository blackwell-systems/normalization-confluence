# Mechanized confluence proof (Coq / Rocq)

A machine-checked proof of the paper's Convergence Theorem: under the paper's stated conditions,
the governance rewrite system is confluent and every configuration has a unique normal form.
Checked by `coqc` (Rocq 9.3; any Coq/Rocq >= 8.18 should work). No `Admitted`, no added axioms.

## What is proven

- **`Newman.v`**: Newman's Lemma, fully self-contained (no external libraries, no axioms): a
  strongly-normalizing, locally confluent abstract rewrite system is confluent (`newman`,
  `confluent_of_SN`) and therefore has unique normal forms (`unique_normal_forms`). This is the
  exact inference the paper invokes to conclude global confluence from termination + local
  confluence.
- **`Governance.v`**: the paper's Governance Rewrite System (Def. "Governance Rewrite System"),
  with its two rules (apply / compensation), and the derivations:
  - `terminating`: Lemma "Termination": the lexicographic measure `(|B|, Phi(sigma))` strictly
    decreases at every step, so the system is strongly normalizing.
  - `locally_confluent_step`: Lemma "Local Confluence": the three critical-pair cases
    (apply/apply, apply/compensation, compensation/compensation) close, using CC1 and CC2.
  - `governance_confluent`, `governance_unique_normal_forms`: Cor. "Unique Normal Forms":
    confluence and unique normal forms, obtained by applying the machine-checked Newman's Lemma.

## What it rests on (and what it does not)

`Print Assumptions governance_confluent` reports **"Closed under the global context"**: the
theorem depends on no axioms and no admitted lemmas. Its only inputs are the paper's own named
conditions, taken as Coq hypotheses (each annotated in `Governance.v`):

| Coq hypothesis | Paper counterpart |
|---|---|
| `wfc` | Axiom WFC (Well-Founded Compensation): compensation strictly decreases the potential |
| `rho_star_valid`, `rho_star_reach` | Def. "Iterated Compensation": rho* reaches validity and is reachable by compensation steps |
| `cc1` | Axiom CC1 (order independence) |
| `cc2` | Axiom CC2 (compensation absorption) |
| `enabled_after_remove`, `enabled_after_comp` | the enabledness-persistence facts used in the Local Confluence proof (Case 1 and Case 2) |

Scope: the registry operators (`apply`, `rho`, `valid`, `Phi`, `enabled`) are abstract,
**exactly at the paper's level of abstraction**: the paper likewise treats them abstractly and
states WFC/CC as conditions a registry must satisfy. So this development mechanizes *the paper's
theorem*: given any registry meeting WFC and CC, confluence and unique normal forms follow, with
no gaps and no hidden assumptions. It does not (and the paper does not) prove that a particular
registry satisfies WFC/CC; that is a per-registry obligation, discharged in the paper's
worked examples and, for the reference implementation, exercised by `gsm`'s `confluence_test.go`.

## Defensibility (`Defensibility.v`)

A mechanized proof that merely compiles can still be weak in ways `coqc` does not catch. This
file rules out the two that matter:

- **Non-vacuity.** If the hypotheses (WFC, CC1, CC2, rho* reachability, enabledness) were jointly
  unsatisfiable, the theorem would be about nothing. `Defensibility.v` exhibits a concrete
  registry (debt counter: `apply = S`, `rho = pred`, valid at zero, `rho*` repairs to zero) that
  discharges *every* hypothesis and yields `example_confluent : confluent step_` and
  `example_unique_nf` with no hypotheses and no axioms. `Print Assumptions example_confluent`
  is "Closed under the global context". `instance_has_a_real_peak` shows the instance genuinely
  branches (two applies + a compensation from one configuration), so this is closing real
  nondeterminism, not a degenerate system.
- **Discrimination.** If `confluent` were provable for every relation, proving it would say
  nothing. `not_confluent_tri` proves a concrete three-element relation is *not* confluent, so
  the predicate is falsifiable.

Together with the axiom-free `Print Assumptions` on the abstract theorem, this is the argument
that the mechanization is strong: correct definitions (standard rewriting theory), satisfiable
hypotheses (a real model), a discriminating conclusion, and no hidden assumptions.

## Build

```
make          # compiles Newman.vo and Governance.vo
make check    # prints the assumption base (expect "Closed under the global context")
```
