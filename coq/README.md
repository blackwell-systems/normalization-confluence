# Mechanized confluence proof (Coq / Rocq)

[![verify](https://github.com/blackwell-systems/normalization-confluence/actions/workflows/verify.yml/badge.svg)](https://github.com/blackwell-systems/normalization-confluence/actions/workflows/verify.yml)

A machine-checked proof of the paper's Convergence Theorem: under the paper's stated conditions,
the governance rewrite system is confluent and every configuration has a unique normal form.
CI compiles it on Coq 8.18 and 8.20 (also builds on Rocq 9.3) and gates on it being **axiom-free**:
every key theorem is "Closed under the global context", no `Admitted`, no added axioms. The badge
is green only when that gate passes.

## Verify it yourself

With Coq/Rocq installed (`coqc` on PATH):

```
cd coq && bash verify.sh      # compiles everything, then prints the axiom-free gate result
```

Or with nothing but Docker (no local Coq), one command reproduces exactly what CI does:

```
docker run --rm -v "$PWD/coq":/src:ro coqorg/coq:8.20 \
  bash -lc "cp -r /src /tmp/c && cd /tmp/c && bash verify.sh"
```

Expected tail: `PASS: all 23 theorems are Closed under the global context (no axioms, no admits)`.
The gate runs `Print Assumptions` on all twenty-three headline results (the single-registry
confluence and unique-normal-form theorems, the defensibility instance, the two gsm
certification-soundness results, the two federated results, the two chaotic-iteration results, the
verified-checker soundness results, the six CRDT-subsumption results, and the four categorical-core
results: image-equals-fixed-points, the idempotent retraction onto the fixed-point set, its
clamp-to-cap non-vacuity instance, and the consistent-set-is-an-equalizer proposition) and fails if
any of them depends on an axiom or an admitted lemma.

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

## Federated convergence (`Federation.v`)

The federated paper's deepest result (Thm. "Monotone Convergence Despite Cycles") says a
monotone federated repair operator on a product of complete lattices has a least fixed point
reached by Kleene iteration from bottom, on any topology including cycles. `Federation.v`
mechanizes the constructive, finite-lattice core the paper relies on ("the ascending chain
stabilizes for a finite lattice"), axiom-free:

- `iter_ascending` / `iter_below_fixed`: Kleene iteration from bottom is an ascending chain
  bounded by every fixed point.
- `kleene_lfp`: once the iteration stabilizes, the stable value **is** the least fixed point
  (the federated normal form) - existence and Kleene-reachability.
- `lfp_unique`: the least fixed point is unique, i.e. the limit is order-independent.

A concrete finite lattice (`bool`) with a monotone operator witnesses non-vacuity, with the
least fixed point computed (`bool_lfp_true`, `bool_lfp_value`). Deliberately avoids the
impredicative arbitrary-meet form of Knaster-Tarski, which would require excluded middle or
propositional extensionality, so the development stays axiom-free.

## Chaotic (asynchronous) iteration (`Chaotic.v`)

The other half of the monotone-cycles theorem: not only does the least fixed point exist, but
every FAIR ASYNCHRONOUS schedule of component updates from bottom converges to it, regardless of
order. That is the classical convergence of chaotic iteration (Cousot 1977), and it is what
"converges regardless of application order" means for a distributed system with no global clock.
`Chaotic.v` mechanizes it constructively, axiom-free, by reframing a chaotic schedule as a
PRODUCTIVE-update rewrite relation (a step that changes the state):

- `chaotic_terminates`: below the least fixed point a monotone update only moves up, so
  productive steps strictly increase a rank and are finite (the relation is strongly normalizing).
- `normal_is_lfp`: a state with no productive step is a fixed point of the whole operator, hence
  the least fixed point.
- `chaotic_reaches_lfp` / `chaotic_from_bot`: from bottom, any sequence of productive updates
  reaches the least fixed point.
- `chaotic_limit_unique`: every reachable normal form is the least fixed point, i.e. the
  destination is schedule-independent. This is the order-independence itself.

A concrete two-value instance (`bool_chaotic_reaches_lfp`) discharges every hypothesis and shows
the iteration from `false` reaches the fixed point `true`, axiom-free. The productive-step
reframing is what makes "every fair schedule" tractable without modeling infinite schedules: any
maximal run of productive updates terminates at the same unique fixed point.

## Implementation soundness (`Gsm.v`)

The theorem is conditional on WFC and CC. `Gsm.v` mechanizes the soundness of the two arguments
the reference implementation (`gsm`) uses to *certify* those conditions at build time, so the
result attaches to how gsm actually establishes its hypotheses, not just to an illustrative
model:

- **CC by footprint disjointness** (`disjoint_events_commute`): over a valuation state model
  mirroring gsm's bitpacked `State` (a write touches only its variable's field),
  `write_comm` proves disjoint-variable writes commute (Leibniz, no funext), from which two
  events with disjoint footprints commute compositionally. This is gsm's `PairsDisjoint`
  certification path (the one that avoids brute-force enumeration).
- **WFC by a well-founded potential** (`repair_terminates`): a repair that strictly decreases a
  natural-number potential whenever the state is invalid is strongly normalizing. This is the
  fact behind gsm's cycle-detection WFC check.

Concrete witnesses (`inc0_inc1_commute`, `ex_repair_terminates`) discharge both with no
hypotheses; `Print Assumptions` on all four results is "Closed under the global context". The
brute-force CC path is a finite decidable enumeration whose soundness is definitional, so it is
not mechanized; the disjointness path is the substantive one.

## Verified checkers: two differential oracles for gsm (`Checker.v`, `AstChecker.v`, `extraction/`)

Two independent, machine-checked checkers re-certify a gsm machine's convergence, each extracted
to a runnable OCaml binary in `extraction/`. Both are proven axiom-free, so a bug in gsm's
hand-written Go verification cannot make a non-convergent machine pass either one. See
`extraction/README.md` for build, demo, and file formats.

### Table oracle (`Checker.v`)

`Checker.v` proves that a governed machine converges (applying the same events in any order
reaches the same state) exactly when its per-event step functions **commute** and stay in range,
and packages that as a boolean `check_commuting` / `closed` proven sound (`check_commuting_sound`,
`checked_converges`), axiom-free. The mathematical core is `run_perm_invariant`: commuting steps
make `fold` over any permutation of an event list give the same result. It is extracted to the
`checker` binary. gsm emits a built machine's step tables (`Machine.WriteConvergenceTables`) and
the extracted checker independently re-certifies that they converge. gsm's
`TestConvergenceTables_WriteAndVerify` runs it on gsm's real output when `GSM_CONVERGENCE_CHECKER`
points at the binary.

### Rules oracle (`AstChecker.v`)

`AstChecker.v` goes one level deeper: instead of checking gsm's output tables, it checks the
**rules** themselves. It models gsm's combinator vocabulary as data (a small grammar of
expressions, predicates, and transforms, and a `machine` record of domains, minimums, invariants,
and guarded events), recomputes each event's step function by **evaluating that AST** (apply the
event, then normalize by iterated repair), and proves:

- `check_sound_commute`: if the boolean `check` passes, the AST-derived step functions commute on
  every valid valuation, axiom-free.
- `check_sound_converges`: from that plus validity preservation, applying the same events in any
  order from a valid valuation yields the same valuation (order-independent convergence),
  axiom-free. The argument mirrors `run_perm_invariant` but carries a validity side-condition,
  since commutation is guaranteed only on valid states.

It is extracted to the `astchecker` binary. gsm serializes a machine's rules
(`Registry.WriteMachineAST`) and the extracted checker re-derives convergence from the
declarations, trusting neither gsm's enumeration nor its normalization. gsm's `TestMachineAST`
tests run it when `GSM_AST_CHECKER` points at the binary. The modeled fragment covers comparison
predicates, `and`/`or`/`not`, `Set`/`Add`/`Sub` transforms, per-variable nonzero minimums, and
guarded events; the serializer refuses anything outside it, so a passing cross-check always
compares like semantics.

### What this does and does not require of you: no continuous porting to Coq

A natural worry is that this design forces you to keep porting your rules into Coq. It does not.
The only thing mirrored in Coq is the **grammar** (the small, fixed combinator vocabulary), and
it is written once here and once in gsm. Your individual machines are **data** in that grammar:
they are never ported, re-expressed, or re-proven in Coq. You author rules in Go, serialize them,
and the already-proven checker consumes them, so a thousand machines cost zero additional Coq
work. You touch this development again only when you add a brand-new grammar **primitive** (a new
expression, predicate, or transform form), which is a rare, deliberate event and the only time the
two mirrors can drift. That drift is caught automatically: the differential test fails the moment
gsm's evaluator and this Coq evaluator disagree on any machine. This is the standard "trusted core
mirrored in a proof assistant" pattern (the way CompCert mirrors C semantics in Coq): the mirror
is small, changes rarely, and is guarded by a test rather than by hand.

## CRDTs as a special case (`CRDT.v`)

`CRDT.v` machine-checks that conflict-free replicated data types are the compensation-free
fragment of this theory: a CRDT buys convergence by restricting to operations that can never
violate an invariant, so no repair is ever needed, and normalization confluence keeps convergence
after dropping that restriction. Four results, all axiom-free:

- `cmrdt_SEC`: an op-based CRDT's strong eventual consistency (replicas that delivered the same
  operations in any order agree) is a one-line instance of `run_perm_invariant`. Its commuting-
  operations requirement is exactly the order-independence hypothesis that lemma already assumes.
- `cmrdt_governed_SEC`: the embedding is faithful. A CmRDT is a governed machine with the trivial
  invariant (every state valid) and identity compensation; then WFC is trivial, the governed step
  equals the raw operation, and convergence follows again.
- `cvrdt_SEC` / `cvrdt_absorbs_duplicates`: a state-based CRDT is the semilattice special case. A
  commutative, associative, idempotent join makes merge order-independent (the same lemma) and
  absorbs duplicate delivery (the extra property a CvRDT bundles in for at-least-once delivery,
  which normalization confluence does not require in general).
- Strict inclusion (`witness_converges`, `witness_not_cmrdt`, `witness_leaves_valid_space`): a
  concrete governed machine that converges yet is neither CRDT. Its raw operations do not commute
  (so it is no CmRDT), and an event drives a valid state to an invalid one (so its operations are
  not the structure-preserving endomaps of a CvRDT). It converges only because compensation repairs
  the violation.

The claim is scoped to the convergence principle, not to CRDT engineering as a whole: version
vectors, causal delivery, and garbage collection are operational concerns this result does not
subsume. See `../SUBSUMPTION.md` for the full statement and caveats.

## Categorical core (`Categorical.v`)

The first structural results of the companion paper's federation-as-limit account, mechanized at the
paper's level of abstraction: the normalizer is an abstract idempotent endomap, exactly as
`Governance.v` treats the registry operators. All axiom-free.

- **Lemma 0 (a registry is an equalizer).** `image_iff_fixed`: for an idempotent `rho`, the image
  and the fixed-point set coincide (`(exists y, rho y = x) <-> rho x = x`), the forward direction
  being idempotence itself. `fixed_is_equalizer`: the fixed-point set is the equalizer of `id` and
  `rho` (its carrier is `{x | id x = rho x}`), a limit in `Set`.
- **Theorem 1 (retraction, abstract skeleton).** `retract_into_fixed` and `retract_fixes_fixed`:
  `rho` lands in the fixed set and fixes it, so it splits the inclusion of the fixed set into the
  state space, i.e. it is a retraction onto that set (the limit `L`). The equalizer universal
  property is given in its axiom-free fragment (`mediator_lands_in_fixed`, `mediator_values_unique`);
  full uniqueness into the subset type needs proof irrelevance of the membership predicate, which
  holds when the state type has decidable equality (gsm's finite states), so it is noted rather than
  assumed.
- **Proposition 1 (the consistent set is a finite limit).** `consistent_iff_equalizer`: the
  federated consistent set (every target's shared component equals its resolver value) is exactly
  the equalizer of the two parallel maps that send a state to the tuple of shared components and the
  tuple of resolver values over the targets. The product over targets is modeled as a list, so the
  equalizer characterization is axiom-free (no functional extensionality). Non-vacuity:
  `ex_consistent_zero` / `ex_inconsistent_one` exhibit a two-target instance where consistency is a
  genuine constraint.
- **Non-vacuity (retraction).** `clamp3` (clamp to a cap at 3, a genuinely collapsing normalizer of
  the shape a real compensation has) discharges idempotence with no hypotheses (`clamp3_idem`), its
  fixed set is exactly `{n | n <= 3}` (`clamp3_fixed_iff`), and the retraction results instantiate at
  it (`clamp3_retracts_into`, `clamp3_image_iff_fixed`). So the section is about something, not a
  vacuous hypothesis.

`Print Assumptions` on `image_iff_fixed`, `retract_into_fixed`, and `clamp3_retracts_into` is
"Closed under the global context"; all three are in the axiom-free gate above.

## Roadmap: mechanizing the categorical layer (companion paper)

The companion paper (categorical structure of federated convergence) rests on a small structural
core that is elementary in `Set` and finite posets, so it mechanizes by leaning on the modules above
rather than pulling in heavy category-theory libraries. Progress, in priority order:

1. **Lemma 0 (a registry is an equalizer).** DONE (`Categorical.v`): `image_iff_fixed`,
   `fixed_is_equalizer`. `Fix(rho) = im(rho) = eq(id, rho)`, axiom-free.
2. **Proposition 1 (the consistent set is a finite limit).** DONE (`Categorical.v`):
   `consistent_iff_equalizer`. The federated consistent set is the equalizer of the shared-component
   and resolver-value maps, axiom-free (product over targets modeled as a list).
3. **Theorem 1 (federation retraction, acyclic).** Retraction skeleton DONE (`Categorical.v`):
   `retract_into_fixed`, `retract_fixes_fixed` establish that the idempotent normalizer is a
   retraction onto its fixed-point set. Still to do: instantiate this at the concrete federated
   operator `rho_F` and mechanize order-independence across topological orders (close in spirit to
   `Chaotic.v`'s schedule-independence result).
4. **Theorem 2 (compositionality).** Planned. The flat federation and the staged
   (sub-federation-collapsed) federation have the same normalizer. The payoff result; follows once
   Theorem 1 is instantiated at `rho_F`.

Kept at paper level (out of scope for the first mechanization pass):

- The cohomological completion (`H^0`/`H^1`, the completion theorem) is proven at paper level in the
  invertible/torsor fragment only; the general case reduces to the loop-composite fixed-point
  condition, which is a dynamical statement rather than group cohomology.
- The operational core of that story is already implemented: the loop-composite fixed-point / orbit
  test is `gsm`'s `Federation.DiagnoseCycle`. A later target is mechanizing that test (finite-space
  fixed-point reachability), for which `Federation.v` and `Chaotic.v` already supply most of the
  machinery.

Status: these are targets for the companion submission, tracked here so the axiom-free gate above
(currently 18 theorems) stays legible. Nothing in this roadmap is claimed proven until it lands in a
module and passes the gate.

## Build

```
make          # compiles every module (Newman, Governance, Defensibility, Gsm, Federation,
              # Chaotic, Checker, AstChecker, CRDT)
make check    # prints the assumption base (expect "Closed under the global context")
```

`bash verify.sh` does the same compile and then runs the full axiom-free gate over all eighteen
headline theorems. To build and run the two extracted oracles, see `extraction/` (`make`,
`make demo`, `make astdemo`).
