# Mechanized confluence proof (Coq / Rocq)

[![verify](https://github.com/blackwell-systems/normalization-confluence/actions/workflows/verify.yml/badge.svg)](https://github.com/blackwell-systems/normalization-confluence/actions/workflows/verify.yml)

A machine-checked proof of the paper's Convergence Theorem: under the paper's stated conditions,
the governance rewrite system is confluent and every configuration has a unique normal form.
CI compiles it on Coq 8.18, Coq 8.20 and Rocq 9.3 and gates on it being **axiom-free**:
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

Expected tail: `PASS: all 715 theorems are Closed under the global context (no axioms, no admits)`.
The gate runs `Print Assumptions` on all 327 headline results (among them the single-registry
confluence and unique-normal-form theorems, the defensibility instance, the two gsm
certification-soundness results, the two federated results, the two chaotic-iteration results, the
verified-checker soundness results (including the Build-aligned table and rules oracles), the six CRDT-subsumption results, and the ten categorical-core
results: image-equals-fixed-points, the idempotent retraction onto the fixed-point set, its
clamp-to-cap non-vacuity instance, the consistent-set-is-an-equalizer proposition, the concrete
federated operator's retraction and image characterization, the order-independence commutation core,
the general acyclic fold operator's retraction and image characterization, the compositionality
fold-append theorem, and the four cohomological-layer results: the gluing counterexample, the
completion theorem's single-cycle essence (a section exists iff the holonomy is trivial), and the
identity-settles and negation-orbits witnesses, plus the ten cross-registry event-interleaving results
of `FederationEvents.v`, the twelve monotone-cycle results of `FederationEventsCycles.v` and the eleven
exactness results of `FederationEventsConverse.v`, the fourteen well-founded-governance results of
`GovernanceWF.v`, the seventeen ACC chaotic-iteration results of `ChaoticACC.v`, the sixteen
at-least-once results of `AtLeastOnce.v`, the twenty-seven converse results of
`GovernanceConverse.v`, the twenty-two coordinated-cycle results of `CoordinatedCycles.v` and the fifty categorical-bridge results of `CategoricalBridge.v`, including eight previously ungated `Categorical.v` names) and fails if any of them depends on an axiom or an

`GovernanceConverse.v`, the twenty-two coordinated-cycle results of `CoordinatedCycles.v` and the ten
per-event cycle-check results of `FederationEventsCyclesCheck.v`) and fails if any of them depends on an axiom or an
admitted lemma.

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

## Verified checkers: two differential oracles for gsm (`Checker.v`, `Trace.v`, `TableCheck.v`, `TableFast.v`, `TableFn.v`, `AstChecker.v`, `AstTables.v`, `AstCompact.v`, `extraction/`)

Two independent, machine-checked checkers re-certify a gsm machine's convergence, each extracted
to a runnable OCaml binary in `extraction/` and generated as Go in `goextract/` (gsm runs the Go
in-process). Both are proven axiom-free, so a bug in gsm's
hand-written Go verification cannot make a non-convergent machine pass either one. See
`extraction/README.md` for build, demo, and file formats.

Both checkers decide exactly the property gsm's `Build` checks, so on every machine they and
`Build` must agree (gsm's differential test fails on any disagreement outside the rules oracle's
arithmetic fragment):

- **WFC over every state.** Repair reaches a valid state from every state in the box, as `Build`
  requires and as the meta-theory assumes (`Governance.wfc`, `Gsm.repair_terminates`). The table
  image of WFC is that the normal-form table lands on valid states.
- **Declared pairs.** Only the event pairs declared independent are checked (every pair when none
  is declared). The guarantee is stated for event sequences that differ by reordering adjacent
  declared-independent events: `Trace.v` defines that trace equivalence (`tequiv`) and proves
  `run_tequiv` (trace-equivalent sequences reach the same state) and `perm_tequiv_total` (with
  every pair declared, it is any permutation).
- **Domain.** Commutation is checked on the valid states plus the zero state that gsm's
  `Machine.NewState` returns, valid or not, under gsm's step, which normalizes even when a guard
  is false.

### Table oracle (`TableCheck.v`, on top of `Checker.v`)

`TableCheck.v` defines `check_tables` over a state count, an event count, the normal-form table,
the step tables and the declared pairs. A state `s` is valid when `NF s = s` (gsm's `IsValid`), so
the domain comes from the tables and gsm cannot shrink it. Theorems, all axiom-free:
`check_tables_nf_valid` (normal forms are valid), `check_tables_step_valid` (every step from every
state is valid), `check_tables_commute` (declared pairs commute on the valid states and the zero
state), `check_tables_converges` (trace-equivalent sequences reach the same state from that
domain) and `check_tables_converges_all` (every permutation, with no pairs declared). Lookups go
through an axiom-free binary trie, proven equal to list lookup (`tget_of_list`), in O(log n);
Rocq's primitive arrays would be O(1) but are specified by axioms.

`TableFn.v` defines `check_fn`, the same check over two accessor functions instead of lists: `nf s`
(the normal form of state `s`) and `st e s` (the state event `e` leads to from `s`). It is what the
`checker` binary runs, over accessors on the arrays it parses, and what a caller that already holds
its tables (gsm holds them as arrays) passes accessors to, so nothing is copied: at 2^20 states and
20 events the `checker` binary peaks at about 320 MB (the file and the arrays) where the list entry
point needed about 1.9 GB. `check_fn_converges` states the guarantee on the accessor functions
themselves: from a valid state or the zero state, trace-equivalent event sequences reach the same
state under `st`. So the theorem is about whatever function the accessor computes; the caller must
pass accessors that are pure and total (the same answer for the same arguments on every call, an
answer for every argument) and return non-negative values that fit the extraction's `int`.
`check_tables_fn` proves `check_tables` equal to `check_fn` on its tries' lookups and `check_fast_fn`
proves `check_fast` equal to `check_fn` on the list accessors, so all three entry points decide the
same property. Every loop is tail-recursive.

`TableFast.v` defines `check_fast`, the list entry point (extracted for callers that pass lists), and proves it
equal to `check_tables` (`check_fast_eq`), so `check_tables_converges` holds for it
(`check_fast_converges`). It computes the same boolean faster. It builds one cell per state: the
state's normal form and its column of steps `T[0][s] ... T[nE-1][s]` in blocks of 16, read by
skipping blocks and four comparisons (proven equal to list lookup by `bget_chunk`); the rows are
transposed 16 states at a time, so the transposition allocates per state only the cell's own
blocks. The cells sit in a 16-ary trie (5 levels at 2^20 keys instead of a 20-level binary tree,
proven equal to list lookup by `vlook_of_listV`) whose digit is found by four comparisons against
thresholds built by addition, with no division and no multiplication. One pass over the cells then
looks up, for each state, the cell of every step target once (nE trie walks per state, whatever
the number of pairs) and answers each declared pair `(a, b)` with four block reads:
`T[a][T[b][s]]` is entry `a` of the column of `T[b][s]`. Every list helper is tail-recursive, so
the extracted code's stack depth does not grow with the number of states, events or declared
pairs (its only non-tail recursion is the trie, at most 8 levels). On 2^20 states and 20 events
(gsm's largest machines) with every pair declared, the `checker` binary takes about 10 s end to
end, parsing the 150 MB tables file included, where the previous `check_fast` (a 16-ary trie per
event row, two row lookups per pair per state) took about 29 s; with 10 declared pairs it takes
about 6 s, most of it parsing (Apple M-series, OCaml 5). `check_tables`' own extraction took
about 60 s on 2^20 states with 10 declared pairs (measured with OCaml 5, whose stacks grow) and
overflowed OCaml 4.14's 8 MiB native stack. No axioms and no extraction directives beyond
`Extract.v`'s. The table path relies on these existing `ExtrOcamlNatInt` mappings: `nat` as OCaml
`int`, `Compare_dec.lt_dec` as `(<)` (inlined), `Nat.eqb` as `(=)`, `Nat.div2` as `n/2`, and
`Init.Nat.add`, `Init.Nat.mul`, `Init.Nat.sub` as `(+)`, `( * )` and subtraction clamped at 0. It
avoids `Nat.pow`, which extracts through the unmapped, unary `Nat.mul` inside the `Nat` module.

`Checker.v`, the original table oracle, proves that a governed machine converges (applying the same events in any order
reaches the same state) exactly when its per-event step functions **commute** and stay in range,
and packages that as a boolean `check_commuting` / `closed` proven sound (`check_commuting_sound`,
`checked_converges`), axiom-free. The mathematical core is `run_perm_invariant`: commuting steps
make `fold` over any permutation of an event list give the same result. It is extracted to the
`checker` binary's version-1 input. That property is stricter than `Build`'s (every pair, every
state), and it is exactly `check_tables` with every state valid and every pair declared, which is
how the front end now reads a version-1 file. gsm emits a built machine's tables
(`Machine.WriteConvergenceTables`, format version 2) and the extracted `check_fast`
(= `check_tables`) independently re-certifies them. gsm's
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
- `check_no_overflow`: if `check` passes, every subexpression of every rule evaluates to a value
  of magnitude at most 2^31-1 on every valuation in the box, axiom-free. Expressions evaluate over
  `Z` with gsm's signed Go semantics (signed `Add`/`Sub` and comparisons; a write clamps into the
  variable's range), and this theorem is why `Z` is exactly gsm's arithmetic: Go's `int` never
  wraps on a certified machine, on 32-bit or 64-bit platforms.
- `check_binary_writes_exact`: if `check` passes, every write to a two-valued variable with
  minimum 0 stores exactly `value != 0`, which is what gsm's Bool write stores, axiom-free. The
  rules format does not say which variables are Bools, so the checker holds every such variable
  to this rule.

It is extracted to the `astchecker` binary. gsm serializes a machine's rules
(`Registry.WriteMachineAST`) and the extracted checker re-derives convergence from the
declarations, trusting neither gsm's enumeration nor its normalization. gsm's `TestMachineAST`
tests run it when `GSM_AST_CHECKER` points at the binary. The modeled fragment covers comparison
predicates, `and`/`or`/`not`, `Set`/`Add`/`Sub` transforms, signed literals and minimums, and
guarded events; the serializer refuses anything outside it, so a
passing cross-check always compares like semantics.

`check` decides a property that differs from `Build`'s in the three ways listed above. The
extracted rules oracle runs `checkBuild` instead, which takes the declared pairs as an input and
decides `Build`'s property. Its theorems, all axiom-free: `checkBuild_wfc_terminates` (no infinite
compensation sequence starts anywhere in the box), `checkBuild_wfc_potential` (each repair of an
invalid state strictly decreases the repair depth: the potential `Governance.wfc` assumes),
`checkBuild_normalize_valid`, `checkBuild_step_valid`, `checkBuild_commute`,
`checkBuild_converges`, `checkBuild_converges_all`, and the fragment guarantees
`checkBuild_no_overflow` and `checkBuild_binary_writes_exact`. `stepG_valid_eq` shows gsm's step
(`stepG`) equals `stepAst` on valid states, so the two differ only at an invalid zero state. The
declared pairs travel in a separate pairs file (`Registry.WriteDeclaredPairs`), so the rules
format and every digest over it are unchanged; without that file every pair is checked.

`checkBuild` checks commutation pair by pair: for every state in the domain and every declared
pair it evaluates the rules four times, each with a normalization, so its time grows with states
times pairs. `checkBuildT` (`AstTables.v`) decides the same
property through step tables computed from the rules: it numbers the valuation box by a
mixed-radix encoding (variable 0 the most significant digit; `boxT` lists the box in that order
with tail-recursive loops), computes `NF[s]` from one normalization per state and `T[e][s]` as
`NF` of the state event `e`'s guarded effect reaches from `s`, builds `check_fast`'s cells state
by state (no table lists, no transposition), and runs `check_fast`'s scan. WFC stays on the rules
side, as in `checkBuild`: a repair cycle whose length divides the fuel can make the normal-form
table look like a retraction while WFC fails. Its theorems, all axiom-free: `scan_cells_fn`
(`TableFn.v`: the scan over any cells holding `x`, `nf x` and the column `st 0 x ... st (nE-1) x`
decides `check_fn` on `nf` and `st`), `boxT_eq`, `enc_box` and `box_enc` (the numbering is a
bijection between the box and `0 .. n-1`), `tables_fn_eq` (under WFC, `check_fn` on these
tables is `pairsOkA && ccA`: a state's number is a fixed point of `NF` exactly when the state is
valid, 0 is the zero state's number, and equal numbers are equal states), `cells_ok`, and
`checkBuildT_eq`: `checkBuildT m P = checkBuild m P` for every machine and declaration, so every
`checkBuild` theorem above holds for it (`checkBuildT_converges` states the runtime guarantee as
an example). It evaluates the rules once per state and event, and its scan costs states times
(events + pairs) table reads. On 20 two-valued variables (2^20 states) with 20 events and every
pair declared (190 pairs), `astchecker` takes about 10 s where `checkBuild` took about 260 s; with 3
events (a capped counter on two 1024-valued variables, or 20 Booleans) about 2 s where `checkBuild`
took about 4 s (Apple M1 Pro, OCaml 5). The tables cost memory: about 280 to 480 MiB at 2^20 states
in OCaml (one cell per state: its record, a list and 16-entry blocks), where `checkBuild` peaks at
90 to 150 MiB.

The extracted rules oracle runs `checkBuildC` (`AstCompact.v`), which decides the same property in
about `checkBuildT`'s time and keeps only the tables, packed. It never lists the valuation box:
`foldB` enumerates it on the fly (`foldD` over the leading variables, in descending order, so every
list it builds comes out ascending; the box of the last variables, at most 4096 states, is listed
once and shared as the valuations' tails). The table entries form one sequence: state `s`'s column
`NF[s], T[0][s], ..., T[nE-1][s]` at positions `s*W .. s*W+W-1` (`W = nE + 1`), held as 16-entry
blocks built 16 states at a time (16 columns are exactly `W` blocks, so only the last block is
padded), and a 16-ary trie over the blocks' suffixes finds a state's column in one lookup. The scan
checks what `ccA` checks: every declared pair commutes at every state that is valid or 0. The
validity parts of the table check are implied by WFC (as `tables_fn_eq` shows), so they are not
rechecked. As in `check_fast`, each step target's column is found once per state; it is realigned
to a block boundary (`realign`, four comparisons against constants), so every pair reads it at a
digit fixed by the pair. Every read compares and adds; nothing subtracts (nat subtraction extracts
through OCaml's polymorphic `max`). Its theorems, all axiom-free: `foldD_eq` and `foldB_eq` (the
enumeration is `fold_right` over `boxR`), `p2_inv` (the blocks read exactly the column sequence),
`rdj_view` and `alignN_rdq` (a view and its realigned column read that sequence), `scanC_spec` (the
scan decides commutation on the valid states and 0, read from the sequence), `checkBuildC_eq`
(`checkBuildC m P = checkBuild m P` for every machine and declaration) and `checkBuildC_converges`.
At 2^20 states (Apple M1 Pro; OCaml 5, and the generated Go with Go 1.26; time and peak RSS,
minimum of interleaved runs on a shared machine):

| machine | OCaml `checkBuildC` | OCaml `checkBuildT` | OCaml `checkBuild` |
|---|---|---|---|
| two 1024-valued variables, 3 events | 2.0 s, 69 MiB | 1.9 s, 281 MiB | 4.0 s, 88 MiB |
| 20 two-valued variables, 3 events | 1.5 s, 128 MiB | 1.6 s, 295 MiB | 3.6 s, 130 MiB |
| 20 two-valued variables, 20 events, every pair (190) | 10.1 s, 443 MiB | 9.7 s, 479 MiB | 261 s, 149 MiB |

| machine | Go `checkBuildC` | Go `checkBuildT` | Go `checkBuild` |
|---|---|---|---|
| two 1024-valued variables, 3 events | 4.9 s, 159 MiB | 4.5 s, 689 MiB | 9.8 s, 156 MiB |
| 20 two-valued variables, 3 events | 5.5 s, 172 MiB | 4.3 s, 658 MiB | 12.6 s, 244 MiB |
| 20 two-valued variables, 20 events, every pair (190) | 20.2 s, 701 MiB | 18.6 s, 1560 MiB | over 600 s (367 MiB when stopped) |

With 3 events `checkBuildC` holds about as much as `checkBuild` or less: below it in OCaml and for
Booleans in Go, at parity for the counter in Go (about 150 to 160 MiB against 156). With 20 events
the table itself is 22M entries (about 168 MiB at 8 bytes each), so it outweighs the box list
`checkBuild` holds: `checkBuildC` peaks at about 2.6 times that floor in OCaml (the blocks, their
list cells and the trie, plus the garbage collector's headroom).

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
vectors, the mechanisms that achieve causal delivery, and garbage collection are operational
concerns this result does not subsume. See `../SUBSUMPTION.md` for the full statement and caveats.

## Causal delivery (`CausalReplay.v`, `GovernanceCausal.v`)

The results above require every pair of events to commute. Under causal delivery only
**concurrent** events (neither happened before the other) can arrive in either order, so only they
need to commute. Axiom-free:

- `causal_convergence`: governed steps that commute for every concurrent pair make any two causally
  consistent delivery orders of the same events reach the same state.
- `causal_cmrdt_SEC`: standard op-based CRDTs (concurrent operations commute) converge.
- `compensation_free_exact`: a compensation-free system satisfies the causal condition iff it is an
  op-based CRDT, so the compensation-free fragment is exactly the op-based CRDTs.
- `witness_causal_not_cmrdt` (strictness) and `witness_beyond_all_pairs` (an add, a causally later
  remove, and an independent counter: not all operations commute, yet the system converges).
- `causal_tequiv`: causally consistent orders are trace-equivalent under concurrency, connecting
  causal delivery to `Trace.v`'s `run_tequiv`.
- `causal_governance_confluent` (`GovernanceCausal.v`): the rewrite-system Convergence Theorem with
  CC1 required only for distinct events enabled together; the witness `cw_confluent` /
  `cw_violates_all_pairs_cc1` meets the weakened hypothesis and violates the original.

Each ordering proof bubbles an event to the front past concurrent events, so the connectivity of
linear extensions is never assumed.

## At-least-once delivery (`AtLeastOnce.v`)

The results above assume each replica sees each event exactly once. Transports usually promise
at-least-once delivery, so an event can be redelivered, possibly much later. `AtLeastOnce.v` makes
exactly-once a checked property: it proves when a duplicate is absorbed and gives a divergence
witness when it is not. A delivery is a list of events with duplicates; its exactly-once projection
`dedup` keeps the first delivery of each event. The governed step (apply, then repair to a normal
form) ranges over an invariant domain `D` it preserves. Axiom-free:

- `alo_absorbed`: the general, local form. A delivery reaches the same state as its exactly-once
  projection when every redelivered event is idempotent (`step a (step a s) = step a s` on `D`) and
  commutes with each event delivered between the redelivery and the previous copy.
- `alo_commuting_exactly_once`, `alo_commuting_converges`: the all-orders case. If all delivered
  events commute and every duplicated event is idempotent, an at-least-once delivery reaches the
  same state as every exactly-once delivery of the same events in any order, and any two
  at-least-once deliveries of the same events agree. Built on `Trace.v`'s `run_tequiv`.
- `causal_alo_exactly_once`, `causal_alo_converges`: the causal case. Only concurrent events need to
  commute (as in `causal_convergence`), happens-before is irreflexive, and redelivery is itself
  causally consistent (`causal_alo`: no copy of a cause is delivered after any copy of its effect).
  Then every duplicate is absorbed and the run equals every causally consistent exactly-once run.
  `causal_alo_absorbs` and `causal_alo_dedup_causal` are the two steps; the order argument reuses
  `causal_tequiv` and `run_tequiv`.
- `non_idempotent_diverges`: for any event whose governed step is not idempotent at some state,
  delivering it twice from that state diverges from delivering it once. `inc_not_idempotent` /
  `inc_duplicate_diverges` instantiate it with a counter increment clamped to a cap: from `0`,
  duplicate delivery ends at `2`, exactly-once at `1`.
- `late_duplicate_diverges`: the naive causal statement (idempotent duplicates are absorbed whenever
  the first deliveries are causal) is false. On `CausalReplay.v`'s flag machine, `Add` and `Remove`
  are idempotent and every concurrent pair commutes, yet redelivering `Add` after its causal
  successor `Remove` leaves the flag set, while exactly-once delivery clears it. That delivery is not
  `causal_alo`, which is why the causal theorem requires it.
- `mx_alo_converges` (a max-register clamped to a cap, all-orders case) and
  `fl_causal_alo_converges` (a flag with add and causally later remove next to a clamped
  max-register; `fl_not_all_commute` shows the all-orders theorem does not apply): non-vacuity
  instances discharging every hypothesis.

In short, deduplication is needed only for an event whose governed step is not idempotent, or whose
redelivered copy can overtake an event it does not commute with. The first always diverges at a
witness state (`non_idempotent_diverges`); the second can (`late_duplicate_diverges`).

## The converse: CC and causal convergence are exact (`GovernanceConverse.v`)

The sections above prove CC (single registry) and commutation of concurrent pairs (causal
delivery) sufficient. `GovernanceConverse.v` proves the converses, in the strongest form that is
true, and records where the naive converse fails. Axiom-free. Write `gov e s = rho_star (apply e s)`
for the governed step.

**Single registry, free delivery** (every buffered event may fire; the rewrite system is
`Governance.v`'s, reused verbatim), with WFC and canonical repair (`rho_star` returns a valid
state):

- `cc1_runs`, `cc2_runs`: the two sides of CC1 at `s` are the normal forms of the runs
  `e1` then `e2` and `e2` then `e1` from `(s, [e1; e2])`; the two sides of CC2 at an invalid `s`
  are the normal forms of apply-then-repair and repair-then-apply from `(s, [e])`. So
  `cc1_fail_diverge` and `cc2_fail_diverge`: a CC failure is two runs with distinct normal forms.
- `reach_run`, `cc1_fail_diverge_from`, `cc2_fail_diverge_from`: every state reachable from `s0`
  (by events and compensation) is reached by delivering some word `w` first, so a CC failure at a
  reachable state is a divergence of two event orders from `(s0, w ++ [e1; e2])` or
  `(s0, w ++ [e])`.
- `cc_exact_from` (headline): every event buffer delivered from `s0` has a unique normal form
  **if and only if** CC1 and CC2 hold on the states reachable from `s0`. `cc_exact`: the same for
  every configuration over a reachable state. `cc_exact_global`: CC everywhere iff unique normal
  forms everywhere.
- Sufficiency only needs CC on reachable states, for any enabledness: `newman_on` (Newman's Lemma
  localized to a step-closed set) gives `cc_reach_unique_normal_forms`, which generalizes
  `governance_unique_normal_forms` and `causal_governance_unique_normal_forms` (CC1 on co-enabled
  pairs and CC2, both only at reachable states).

**Single registry, any enabledness (causal, guarded).** Here CC1 is not necessary, and the exact
condition is CC modulo the rest of the run:

- `jc_exact`: from a start configuration `c0`, the system is confluent iff `JC c0`: at every
  configuration reachable from `c0`, the governed successors of each critical pair are joinable
  (`(gov e1 s, B \ e1)` with `(gov e2 s, B \ e2)` for co-enabled `e1 <> e2`; `(gov e s, B \ e)`
  with `(gov e (rho s), B \ e)` for invalid `s`). CC1 and CC2 are the case where the join is an
  equality (`cc_reach_jc`). `jc_unique_normal_forms`: `JC c0` gives unique normal forms from `c0`.

**Counterexamples to the naive converse.**

- `rho_star_qualifier`: the qualifier "canonical repair" is needed. `Governance.v` only asks that
  `rho_star s` be a reduct of `s`, which the identity satisfies; with it CC1 fails (set-true and
  flip do not commute), yet every configuration has a unique normal form (repair resets to the
  only valid state).
- `masked_cc1`: under causal enabledness, CC1 can fail for two co-enabled events at a reachable
  configuration while every run reaches the same normal form. `M1` writes 1, `M2` writes 2, and a
  reset `MR`, enabled only after both, erases the difference: from `(0, [M1; M2; MR])` every
  normal form is `(0, [])`. So "CC fails at a reachable state, hence two orders diverge" is false
  once the future of the run is constrained; `JC` is the exact condition there.

**Causal delivery** (the run model of `CausalReplay.v`):

- `CCR s0`: for every concurrent pair `a`, `b` and every prefix `p` such that `p ++ [a; b]` is
  causally consistent, the governed steps of `a` and `b` commute at `run p s0`.
- `causal_exact`: causal convergence from `s0` (any two causally consistent permutations reach the
  same state) **if and only if** `CCR s0`. Sufficiency (`ccr_convergence`) goes through
  `causal_tequiv` and the fact that swapping a concurrent adjacent pair preserves causal
  consistency (`causal_swap`, `tequiv_causal`); necessity (`ccr_diverge`) exhibits the two
  causally consistent permutations `p ++ [a; b]` and `p ++ [b; a]` with different results.
- `causal_convergence_exact`: with happens-before irreflexive, causal convergence from every start
  iff governed steps commute on every concurrent pair at every state: the converse of
  `causal_convergence`. Irreflexivity is needed: an event with `hb a a` appears in no causal order.
- `naive_causal_converse_fails`: `NA` and `NB` are concurrent and do not commute at state 1, which
  the causally consistent run `[NC]` reaches from 0, yet causal convergence holds from 0, because
  `NC` is causally after both and neither can be delivered after it. Reachability of the
  non-commuting state is not enough; the pair must be deliverable after the prefix, as in `CCR`.

## Event interleavings across registries (`FederationEvents.v`)

The federated results above fix the order in which the normalizer visits registries. They do not
cover local events on a target registry interleaving with changes propagated from its sources,
and those can diverge even when every registry converges, every morphism satisfies M1 and the
network is acyclic: a target event that reads a variable the morphism overwrites sees a different
value depending on whether a source event was propagated first. `FederationEvents.v` closes this
for acyclic federations (single-source morphisms and multi-source resolvers alike), axiom-free.

Model: a federated state gives every registry its state; `N` is gsm's `FedMachine.Normalize`
(normalize each component, then repair each registry in topological order with its morphism
image), and `applyF e` is `FedMachine.Apply` (component step, then `N`). Write `ow_z x` for the
repair of `x` from source states `z`, and call `x` consistent when its shared part is an image
(`x = ow_z' x` for valid `z'`). Two conditions on each registry's events:

- **C1 (cross-registry CC)**: for every event `e`, all valid source states `z`, `z'` and every
  valid `b` consistent with `z'`: `ow_z (e (ow_z b)) = ow_z (e b)`. The repair is on both sides,
  so an event that only writes a shared variable (overwritten by the source, as
  `FedMachine.Apply` documents) passes. This is the check gsm runs.
- **C2 (repaired CC)**: for declared-independent events `e1`, `e2` of one registry and `b`
  consistent with `z`: `ow_z (e2 (ow_z (e1 b))) = ow_z (e1 (ow_z (e2 b)))`. For a source registry
  this is its own CC; for a target it is not implied by its own CC plus C1.

Results:

- `fed_events_commute`, `fed_interleavings_converge`, `fed_permutations_converge`: under the
  per-registry conditions (`Common`: locality, acyclic order, M1/R2, overwrite absorption from
  well-formedness plus source-determinacy, component steps valid) plus C1 and C2, from any valid
  consistent federated state, `FedMachine.Apply` sequences over the combined event alphabet that
  differ by swapping events of different registries, or declared-independent events of one
  registry, reach the same federated state.
- `propagation_flush`, `dist_interleavings_converge`: with propagation as separate steps (each
  node applies local events and merges its sources' projections whenever they arrive), every
  interleaving reaches, once propagation completes, the `FedMachine` run of its events, so all
  interleavings agree. This needs `XU` (C1 for every valid `b`, not only consistent ones) plus
  each registry's own CC, because a node may apply an event to a state whose shared part a local
  event has just overwritten; `xu_implies_c1_c2` shows these imply C1 and C2.
- `audit_counterexample`: everything but C1 holds (a supplier's `sell` guarded on a flag the
  manufacturer's `recall` drives); the two orders give `sold = 0` and `sold = 1`.
- `c2_counterexample`: C1 and the target's own CC hold, C2 fails (`Swap` exchanges a shared and a
  local slot, `Audit` records their xor), and the federation diverges.
- `supply_instance`, `supply_converges`: a concrete federation discharging every hypothesis of
  both models (non-vacuity), whose target event writes a shared variable, so the stronger form
  without the final repair (`Candidate`) fails there although the federation converges.

Cyclic (`AllowMonotoneCycles`) networks are not covered by this file (the proof uses the
topological order); see the next section.

### Monotone cycles and the exact converse (`FederationEventsCycles.v`, `FederationEventsConverse.v`)

**The global condition.** For any federated normalizer `N`, a governed event step is
`step e = N o (apply e)` (`FedMachine.Apply`). Call two events independent when they are on
different registries or declared independent on one registry. The global condition `GC s0` says:
for every state `s` reachable from `s0` by governed steps and every independent pair `a`, `b`,
`step a (step b s) = step b (step a s)`, i.e. the events commute after full re-normalization on
reachable federated states. `gc_iff`: `GC s0` holds iff every two trace-equivalent event sequences
reach the same state from `s0` (sufficiency is `Trace.run_tequiv` over the reachable set; necessity
takes the one-swap pair at the failing state). So it is the exact condition, not only a sufficient
one. `gc_image` is the variant over the whole image of `N` (every normalized state), for a check
without a fixed start.

**Monotone cycles.** The model follows gsm's `normalizeCyclic`: a federated state is (locals,
shared values); phase 1 normalizes each component; every shared variable is reset to bottom; targets
are repaired in sweeps until a sweep changes nothing, at most `kleeneCap` rounds. The hypotheses are
those of `Chaotic.v` (inflationary and soundness-preserving coordinate updates, no change means
`F`-fixed) plus monotone coordinate updates on a finite-height lattice, i.e. what
`verifyMonotoneVisited` checks over every state the iteration visits (valid locals with any shared
values). Results:

- `cyc_N_lfp`, `cyc_N_unique`, `cyc_sweep_order_independent`: the normalizer returns the least fixed
  point of the repair for the phase-1 locals, the only one, whatever the sweep order; the cap is
  provably never reached when it exceeds the lattice height.
- `cyc_N_idem`: the normalizer is idempotent, given that phase 1 fixes valid states and the least
  fixed point is valid (gsm checks image validity at Build and panics on an invalid fixed point).
- `cyc_events_converge_iff`: on a monotone cyclic federation, event interleavings from `s0`
  converge exactly when `GC s0` holds. Events may read shared values (feedback through the cycle).
- `cyc_instance` (non-vacuity): a two-registry cycle (A's shared flag fed by B, B's by A) with raise
  and clear events on both registries; every hypothesis is discharged, the least fixed point is
  computed, and all interleavings converge from every start. `bottom_matters`: on that cycle a
  non-least fixed point exists, which is why per-edge reasoning (unique solution along a
  topological order) does not transfer and iteration from bottom is required.
- `cyc_counterexample`: the same cycle with `LatchA`, which copies A's shared flag (fed by B) into
  A's local alarm. `GC` fails at the start, and `LatchA; RaiseB` and `RaiseB; LatchA`, one allowed
  swap apart, end in different federated states.

**Acyclic case: C1 and C2 are the exact check.** For the acyclic machine of `FederationEvents.v`:

- `conv_c1_runs`, `conv_c2_runs`: the witness equations are runs. From a reachable state `s`, with
  `w` a sequence of events on registries other than `j = reg e` and `z` the state after `w`,
  `run (e :: w)` leaves `ow_z (e b)` on `j` and `run (w ++ [e])` leaves `ow_z (e (ow_z b))`, the
  two sides of C1 at `(e, z, z' = s, b = s j)`; `run [e1; e2]` leaves the left side of C2 at
  `(z = s, b = s j)`.
- `conv_c1_diverge`, `conv_c2_diverge`: a C1 or C2 failure at a witness realized by a reachable
  state is an observable divergence of trace-equivalent sequences (C2: one allowed swap; C1: moving
  `e` past `w`).
- `reach_commute_iff`: at a reachable state, two independent events commute iff their C1 instances
  (different registries) or C2 instance (same registry) hold there.
- `fed_exact`, `fed_exact_full`, `gc_iff_reach`, `acyclic_gc_iff`: from a valid consistent start
  `s0`, all trace-equivalent sequences converge iff `GC s0` iff C1 and C2 hold at the witnesses
  reachable from `s0` (C1 with one intervening event already suffices; any number is equivalent).
- `static_c1_c2_gc`: static C1 + C2 imply `GC s0` and its reachable restriction, so
  `C1 /\ C2 -> reachable C1 /\ reachable C2 <-> GC <-> convergence`.
- `naive_converse_fails`: "C1 fails, so some interleavings diverge" is false. A manufacturer event
  that only bumps a counter and a supplier `sell` guarded on the shared listed flag violate C1, the
  failing witness's target and source state occur together in a valid consistent start, and still
  every interleaving from every valid consistent start converges: no run moves the source from
  `z'` to `z`. The exact converse must quantify over reachable witnesses. For C2 the witness is a
  single pair `(z, b)`, and the converse applies whenever some valid consistent state realizes it
  (for example in a two-registry federation whose source has no repair).

**Not covered here.** Non-monotone cycles have no coordination-free normal form: their repair has no
unique normal form reached from bottom, so there is nothing for events to commute after; gsm routes
them to coordination. Under a computed coordination they converge, to a normal form unique given an
authority root (`CoordinatedCycles.v`, below). The distributed model (explicit propagation steps) is not extended to cycles. The
global condition is exact but semantic: on a cycle there is no per-edge reduction of it, so checking
it exactly means enumerating reachable normal forms (or the image of `N`) and testing every
independent pair. The per-edge C1/C2 enumeration gsm runs for acyclic networks is nevertheless
sufficient on a monotone cycle (next section). Static C1 and C2 remain over-approximations
(sufficient, and necessary only at reachable witnesses).

### Event order on monotone cycles, checked per event (`FederationEventsCyclesCheck.v`)

The previous section leaves `GC` global on a cycle. This file proves that a per-event condition
implies it, so a cyclic federation's event order can be checked without enumerating normal forms.

**Why it works.** gsm's `normalizeCyclic` resets every shared variable to bottom before the sweeps,
so the shared part of a normal form is a function of the locals alone. An event's writes to shared
variables are erased; only its effect on locals survives (`cyc_check_step`). Events therefore
commute after re-normalization as soon as their local outcomes do not depend on which image value
the shared part holds, and same-registry declared pairs commute on locals.

**Model.** Registries of any type with decidable equality; a federated state is (locals, shared
values) with per-registry lenses; `comp k s` is registry `k`'s component; `sig e` is the component
step (`Machine.Apply`), preserving component validity; `cev e` replaces registry `reg e`'s component
by `sig e` of it (locals and shared values); the normal form is `(fst (rho1 t), Lsh (fst (rho1 t)))`,
which is `Ncyc_with` of `FederationEventsCycles.v` for `Lsh l = kleene l js K bot`. `Hs j` is any set
of shared values for registry `j` containing every normal form's (for gsm: the images of the
morphisms into `j` over valid source states).

- **C1cyc**: for every event `e` of registry `j`, every valid component state `(x, h)` of `j` with
  `h` in `Hs j`, and every `h'` in `Hs j`, the locals of `sig e (x, h')` equal the locals of
  `sig e (x, h)`. This is gsm's C1, `ow(rho_B(e(ow(b, v'))), v') = ow(rho_B(e(b)), v')` for every
  image `v'` and valid consistent `b`: the final overwrite fixes the shared part on both sides, so
  the equation says exactly that the locals agree.
- **C2cyc**: for every declared-independent pair `a`, `b` of registry `j` and every valid `(x, h)`
  with `h` in `Hs j`, the locals of `sig a (locals of sig b (x, h), h)` and of
  `sig b (locals of sig a (x, h), h)` agree. This is the local part of gsm's C2 (both sides
  repaired with the same image `z`).

Results:

- `cyc_check_gc`, `cyc_check_converges` (headline): C1cyc and C2cyc imply `GC s0` and convergence of
  all trace-equivalent sequences, for every `s0` in the image of the normalizer. Hypotheses: phase 1
  fixes valid states, normal forms are valid (gsm checks this at run time), `Hs` contains the
  normal forms' shared values.
- `cyc_check_gc_lfp`: the same for gsm's Kleene normalizer `Ncyc_with` on a monotone cycle (the
  hypotheses of `cyc_N_lfp`), with `Hs j` any set containing the repair's output into `j` from valid
  states; "`Hs` contains the normal forms' values" is discharged from the least-fixed-point property.
- `footprint_c1`: the plain read footprint (an event's local outcome ignores shared values) implies
  C1cyc for every `Hs`. Writing shared variables is never a problem (the reset erases the writes).
- `lfp_commute_gc`: the global variant `N o ev e o N = N o ev e`, plus raw commutation of
  independent events, implies `GC`. Sufficient but not per edge (it quantifies over all raw states
  and runs `N`); the latch fails it.
- `cyc_check_instance` (non-vacuity): the two-registry cycle of `cyc_instance` with raise and clear
  events, plus `PingA`, which also writes A's shared flag, declared independent of `RaiseA`. Every
  hypothesis of `cyc_check_gc_lfp` is discharged, and `PingA; ClearA` from the bottom state ends at
  the bottom state (the shared write is erased).
- `check_rejects_latch`: `cyc_counterexample`'s federation is this model (`cev = xstep`
  pointwise), and for every `Hs` containing the normal-form shared values C1cyc fails at `LatchA`.
  The global variant of `lfp_commute_gc` fails too, and `GC xs0` fails.

Counterexamples to the other natural candidates:

- `monotone_c2_insufficient`: "monotone events plus C2 commutation" is false. `LatchA` is a monotone
  map on the component lattice, C2cyc holds (no declared same-registry pairs), each registry's own
  CC holds, and `GC` fails.
- `c1_localcc_insufficient`: "C1 plus each registry's own CC" is false, so C2cyc cannot be dropped.
  A genuine monotone cycle (A's shared flag fed by B, B's fed by A, every hypothesis of `cyc_N_lfp`
  discharged) where B has a shared slot whose only image is `false`. `Swap` exchanges B's local slot
  with the shared slot, `Audit` records their xor. C1cyc holds, the two events commute on B's full
  state, C2cyc fails, and `Audit; Swap` and `Swap; Audit` (one allowed swap apart) diverge from a
  normal form. Both events read a shared variable, so C1cyc is strictly weaker than the read
  footprint.

So candidate A of roadmap item 6 holds, with the qualification that matters: C1 and C2 must be
evaluated with the shared part ranging over a set that contains every normal form's shared values.
Images over valid source states (what gsm's C1 enumerates) satisfy this. The values the Kleene
iteration visits also contain them, so a check over visited states is sufficient too, but it is
stronger than needed (it adds non-image values such as bottom and can reject federations the image
check accepts). Neither condition is necessary: `GC` remains the exact one.

**What gsm has to check on an `AllowMonotoneCycles` network.** Nothing beyond its acyclic C1/C2
enumeration, with three requirements:

1. `H_j`, the image set of target `j`: for each edge into `j`, the morphism (or resolver) image of
   every valid source component state. Cost: one map evaluation per valid source state per edge.
   On a cycle the source's valid states must be enumerated in full (no topological restriction).
2. C1, per event `e` of `j`: for every local part `x` of a valid component state of `j` whose shared
   part is in `H_j`, the locals of `rho_j(e(x, v'))` are the same for every `v'` in `H_j`. Cost:
   `|E_j| x |X_j| x |H_j|` evaluations, `X_j` the distinct such locals. This is gsm's existing C1
   (`b` times `v'`). A C1 or C2 failure on a cycle means event order is not certified there, and the
   report should say so.
3. C2, per declared-independent pair on `j`: for every valid component state `(x, h)` with `h` in
   `H_j`, the two orders "event, overwrite with `h`, event" agree on locals. Cost: four evaluations
   per state per pair. This is gsm's existing C2.

Per-registry state spaces only, never the product: no normal form is enumerated. The exact
alternative (checking `GC` itself) enumerates the image of `N` (the product of the local spaces)
times every independent pair. Regression test: the `cyc_counterexample` latch federation must fail
C1 (`check_rejects_latch`). For a target with several incoming edges, gsm's per-edge C1 checks
overwrite each edge's variables separately; with M1 (overwrites preserve validity) they compose
into C1cyc for the target's whole shared part, one edge at a time. That composition step is not
mechanized here: the file treats each registry's shared part as one block.

## Finiteness only for checking (`GovernanceWF.v`, `ChaoticACC.v`)

The convergence theorems above never needed a finite state space, but two of them used a
natural-number measure: the WFC potential (`Governance.v`) and the rank of finite height
(`Chaotic.v`). These modules remove both, axiom-free:

- `governance_wf_confluent`, `governance_wf_unique_normal_forms` (`GovernanceWF.v`): the
  Convergence Theorem with WFC over an **arbitrary well-founded order**: the potential
  `Phi : State -> P` takes values in any type `P` with any well-founded strict order `ltP`, and
  compensation lowers it (`ltP (Phi (rho s)) (Phi s)` for invalid `s`). Termination is
  lexicographic on `(|B|, Phi s)` (`wf_lex2`, `governance_wf_terminating`); local confluence is
  `Governance.v`'s lemma unchanged. The causal theorem generalizes the same way
  (`causal_governance_wf_confluent`). Corollaries: the nat-valued theorems of `Governance.v` and
  `GovernanceCausal.v` with identical statements (`governance_confluent_from_wf`,
  `causal_governance_confluent_from_wf`), a potential into a lexicographic product
  (`governance_lex_confluent`), and no potential at all, only well-founded compensation
  (`governance_comp_wf_confluent`).
- Non-vacuity on an infinite domain: a withdrawal registry on `Z` (any balance, overdrafts of any
  depth; repair adds 1 up to the floor 0; potential `-s` under `Zwf 0`) discharges every
  hypothesis (`zw_confluent`, `zw_unique_normal_forms`, `zw_any_overdraft_repairs`).
- `chaotic_acc_reaches_lfp`, `chaotic_acc_terminates` (`ChaoticACC.v`): chaotic iteration reaches
  the least fixed point under the **ascending chain condition below the least fixed point**
  (well-foundedness of the converse of the strict order there), with no rank into `nat`.
  `chaotic_reaches_lfp_from_acc` recovers `Chaotic.chaotic_reaches_lfp` with an identical
  statement.
- Kleene iteration under ACC: `kleene_acc_not_forever` (constructive, no extra assumption: the
  iteration from bottom cannot strictly ascend forever) and `kleene_acc_lfp_nn` (a least fixed
  point cannot fail to exist); with the stabilization test `f x = x` decidable,
  `kleene_acc_stabilizes` and `kleene_acc_lfp` compute the stabilizing index and the least fixed
  point. `finite_height_acc` and `kleene_finite_height_lfp` recover the finite-lattice reading.
- Non-vacuity: `option nat` with `None` at the bottom and `Some n` in reverse order satisfies ACC
  (`ole_acc`) but has ascending chains of every length and admits no strictly increasing rank
  (`ole_no_rank`), so `Chaotic.v`'s hypotheses cannot be met on it. On its square with a monotone
  two-component operator, chaotic iteration and Kleene iteration both reach the least fixed point
  (`ple_acc`, `ple_no_rank`, `pl_chaotic_reaches_lfp`, `pl_chaotic_from_bot`,
  `pl_kleene_lfp_value`).

What still uses finiteness: deciding the hypotheses. Exhaustive checking (gsm, the table and
rules oracles) needs a finite state space to be a decision procedure; the theorems do not.
Computing the Kleene limit needs the stabilization test to be decidable; without it the
development proves only the double-negated existence, which is the constructive limit (deciding
`f x = x` in general is not possible).

## Monotone cycles against the paper's hypotheses (`MonotoneFederation.v`)

Completes the federation paper's "Monotone Cycles" section (PAPER-MAP rows F22, F23, F24, F27,
F31), axiom-free:

- F22, the repair operator built from a network: component states are (shared, local) pairs, a
  source keeps its own shared value, a target applies its resolver to its sources' current states
  (a single-source morphism is a one-source resolver). `fed_def_lattice_shared_cyclic_hyps`: if
  that `Phi` is monotone, every hypothesis of `FederationEventsCycles`' cyclic normalizer holds.
- F23, validity of the least fixed point. FALSE AS STATED: `fed_thm_monotone_cycles_lfp_invalid`
  is a 2-cycle of identity morphisms on `bool` (valid iff the flag is set) meeting every hypothesis
  of `thm:monotone-cycles` (complete lattice, `Phi` monotone, M1/R2, components WFC, CC vacuous),
  whose least fixed point is not federally valid; the cyclic normalizer even moves the valid state
  to it. M1/R2 transport validity but bottom need not be valid. Corrected with "every component is
  valid with bottom shared values": `net_iter_valid`, `net_sweep_valid` (any finite schedule),
  `net_lfp_valid` (under ACC), `net_Ncyc_correct` and `net_Ncyc_idem` (which discharges the
  former assumption `lfp_valid` of `cyc_N_idem`); non-vacuity `fed_valid_corrected_instance`.
- F23, the formula `s* = sup_k Phi^k(bot)`. FALSE without continuity:
  `fed_thm_monotone_cycles_kleene_formula_fails` on the complete chain `0 < 1 < ... < w < w+1`
  (`w_complete_nn`, completeness read classically as a double negation). Corrected:
  `kleene_sup_lfp`, `kleene_sup_valid`, non-vacuity `kleene_sup_instance`.
- F23, "all processors converge": `fed_thm_monotone_cycles_events_refuted` restates
  `cyc_counterexample` with `Phi` built from the network and every paper hypothesis discharged;
  `net_events_converge_iff` and `fed_thm_monotone_cycles_events_corrected` give the exact
  condition (GC).
- F24: `negation_not_monotone`; the corollary holds for the repair normal form only.
- F27, infinite lattices and widening: `kleene_sup_instance` (a continuous operator whose least
  fixed point is never reached in finitely many steps), `widening_sound` (a post-fixed point bounds
  every iterate and the least fixed point), `widening_not_normal_form` (a widened result need not
  be a fixed point, so it is not the federated normal form).
- F31, remark "Convexity and the monotone regime". FALSE AS STATED: `fed_rem_convexity_refuted`
  (a one-registry sub-federation whose repair is trivially monotone, while `rho_Fed^J` is the
  component's non-monotone normalizer). Corrected: `fed_rem_convexity_corrected` (phase 1 monotone
  and `Phi` monotone in the locals too), non-vacuity `convexity_corrected_instance`.

## rho* constructed from WFC (`RhoStar.v`)

The modules above take iterated compensation `rho_star` as a parameter, with the hypotheses
`rho_star_reach` (and `rho_star_valid` in `GovernanceConverse.v`). The paper defines it instead
(Base, Def. "Iterated Compensation"): `rho*(s) = rho^m(s)` for the least `m` with `V(rho^m(s))`.
`RhoStar.v` constructs that operator from WFC (and a decidable validity test, which the paper's
Boolean `V_R` is) and proves every base fact that rests on it, axiom-free (61 gated results):

- Construction: `rho_star` (nat measure, computable by fuel) and `rho_star_wf` (any well-founded
  order, by well-founded recursion). `base_def_rhostar` and `base_def_rhostar_least_unique` are the
  paper's definition exactly (the least `m` exists and determines `rho*`); `rho_star_canonical`
  shows the operator does not depend on the measure. Notation (i) to (iii) of Base section
  "Calculus": `rho_star_valid`, `rho_star_fix`, `rho_star_idem`; `rho_star_rho` (rho(s) lies on
  the chain of an invalid s).
- Headline theorems with no rho* hypothesis: `wfc_governance_confluent`,
  `wfc_governance_unique_normal_forms`, `wfc_causal_governance_confluent`,
  `wfc_causal_governance_unique_normal_forms`, `wfc_governance_wf_confluent`,
  `wfc_causal_governance_wf_confluent`, `wfc_cc_exact_from` (both rho* hypotheses discharged).
- Deps-based enabledness (Base def:config: `e` in `B` is enabled iff `deps(e)` is disjoint from
  `B`) discharges `enabled_after_remove` and `enabled_after_comp` in both rewrite systems
  (`deps_enabled_after_remove`, `deps_enabled_after_comp`, `deps_causal_enabled_after_remove`,
  `deps_causal_enabled_after_comp`), and co-enabled events are causally independent
  (`deps_coenabled_independent`). So Base cor:unique-nf holds in the paper's own terms with only
  WFC, CC1 and CC2 as hypotheses: `paper_causal_governance_confluent`,
  `paper_causal_governance_unique_normal_forms` (CC1 on distinct, independent, co-enabled pairs),
  and the all-pairs versions `paper_governance_confluent`, `paper_governance_unique_normal_forms`.
- Absorption: `base_rem_absorption` (CC2 lifts to `rho*(apply(e, s)) = rho*(apply(e, rho*(s)))`),
  `base_rem_absorption_enabled` (CC2 for enabled events only), `base_thm_strong_absorption` (strong
  absorption implies CC2), and the equivalence `strong_absorption_iff_cc2`.
- UBC: `base_lem_finite_implies_ubc` (a listed state space gives `M = max Phi`, attained when there
  is a state); the step bound of Lemma "Termination", every reduction from `(s, E)` has at most
  `|E| + (|E| + 1) M` steps (`base_lem_termination_bound`, `causal_lem_termination_bound`), attained
  (`lv_termination_bound_tight`); the model-level part of Theorem "Convergence Complexity": at most
  `M` compensation steps per applied event plus `M` before the first
  (`base_thm_complexity_comp_total`, `base_thm_complexity_per_event`, `rho_star_steps_le_measure`).
- Cat section 3 background: WFC makes the normalizer idempotent (`cat_bg_rho_idempotent`), reaches
  a valid state from any state (`cat_bg_valid_from_any_state`), and Lemma 0 holds for it with the
  idempotence hypothesis of `Categorical.v` discharged (`cat_bg_lemma_zero`). The unqualified
  "its valid set is non-empty" needs a state: the empty registry satisfies WFC with an empty valid
  set (`cat_bg_nonempty_needs_a_state`).
- Non-vacuity: a four-level saturating counter (`lv_*`: finite, WFC, UBC with `M = 1`, CC1, CC2,
  strong absorption, deps-based enabledness for any dependency map) discharges every hypothesis
  set; the unbounded withdrawal registry of `GovernanceWF.v` gets its rho* constructed
  (`zw_rho_star_built`, `zw_confluent_built`).

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

- **Theorem 1 (retraction), operator half.** `RetractionOntoConsistent` proves the note's Corollary
  in general: any operator that is sound (its image lands in a consistent set `L`, Lemma A) and
  complete (it fixes `L`, Lemma B) is the idempotent retraction onto `L`, with image and fixed-point
  set both `L` (`rhoL_idempotent`, `rhoL_image_iff_L`, `rhoL_L_iff_fixed`). `FederatedOperator` then
  discharges Lemma A and Lemma B for a concrete federated operator `rhoF` (a root with local
  normalizer, plus a morphism target whose shared component is fixed from the root's normal form),
  so `rhoF` is the idempotent retraction onto its consistent set (`rhoF_retraction`,
  `rhoF_image_iff_L2`).
- **Order-independence, commutation core.** `updates_commute`: updates to two independent registry
  components commute (the local step of Lemma C, incomparable registries having disjoint reads and
  writes). The full result, that all topological orders agree, is mechanized in
  `FederationOrder.v` (below) without assuming the linear-extension connectivity fact.
- **Order-independence for arbitrary acyclic federations (`FederationOrder.v`).** Registries read the
  state only through their sources (`f_local`); an order is topological when it is duplicate-free and
  every in-order source comes earlier. `order_independent`: any two topological orders of the same
  registries give the same final state, from any initial state. The proof bubbles the first registry
  of one order to the front of the other (`bubble`, via the adjacent commutation `step_comm`), so the
  classical connectivity of linear extensions is never assumed. States are compared pointwise (no
  functional extensionality). A three-registry instance (`ex_orders_agree`) discharges every
  hypothesis.
- **Theorem 1 for a general acyclic federation.** `GeneralFederatedFold` models `rho_F` as a
  left-to-right fold over a topological order (state is a positional list; `stepAt` reads the
  finalized prefix and returns a position's finalized value), defines the consistent set `L_F`
  intrinsically (every position fixed by its step given its prefix), and proves Lemma A
  (`rhoFold_sound`, needing `stepAt` idempotent given a fixed prefix) and Lemma B
  (`rhoFold_complete`, needing only the definition). It therefore instantiates the Corollary:
  `rhoFold_retraction` and `rhoFold_image_iff_consistent` give that `rho_F` is the idempotent
  retraction onto `L_F` for every acyclic federation, not just the two-registry instance. The
  supporting `app_split_snoc` (splitting a snoc) is axiom-free.
- **Theorem 2 (compositionality).** `rhoFold_compositional` (via the fold-append law
  `rhoF_from_app`): the flat normalization of a federation split along a topological cut `J ++ K`
  equals the staged one, finalize the upstream block `J`, then continue with `K` on top of the
  collapsed (finalized) `J`. So an upstream sub-federation collapses to its finalized block and the
  combined normalizer factors as (normalize `J`) then (normalize `K`). Axiom-free.

`Print Assumptions` on the categorical-core headline results is "Closed under the global context";
they are in the axiom-free gate above.

## Categorical bridge (`CategoricalBridge.v`)

The companion paper's Proposition 1 and Theorem 1 on one concrete federation model, joining the
three pieces `Categorical.v` and `FederationOrder.v` prove separately: the consistent set with every
conjunct the paper states, the retraction onto it, and order-independence. Registries are indexed
by `nat`; registry `i` has a local normalizer `rho i`, sources `src i`, and (as a target) a shared
component read by `get i`, written by `ovr i`, and a resolver `res i`. `stepN i` overwrites the
shared component with the resolver value and then normalizes locally. All axiom-free.

- **Proposition 1 (`prop:one`), with the component conjunct.** `LF` is the paper's `L_F`: the tuple
  lies in the product of the valid sets `Phi_{R_i} = im(rho_i)` (`ProdPhi`) and every target's shared
  component equals its resolver value. `cat_LF_split`: `LF` is `ProdPhi` plus `Categorical.Consistent`.
  `cat_prop_one`: on the product of the valid sets, `L_F = eq(g, h)`. `cat_prop_one_product`: the
  product of valid sets is the equalizer of the identity and the product normalizer, factorwise
  Lemma 0's `eq(id, rho_i)` (via `fixed_is_equalizer`). `cat_prop_one_limit`: `L_F` is a single
  equalizer of two maps into a finite product, a finite limit in `Set`.
- **The bridge (`thm:one`).** `rhoFold_run`: `Categorical.rhoFold`, instantiated on
  (registry, value) pairs over a topological order, computes `FederationOrder.run` on that order.
  `consistentList_iff_LF`: Categorical's intrinsic `ConsistentList` is exactly the paper's `L_F`,
  given local idempotence, the lens law `putget`, and `sh_fixed` (the local normalizer fixes the
  overwritten shared component). `rhoFold_order_independent` and `rhoFold_order_perm`: the fold
  inherits `order_independent`.
- **Theorem 1 as stated.** `cat_thm_one_sound` (Lemma A, from `rhoFold_sound`),
  `cat_thm_one_complete` (Lemma B, from `rhoFold_complete`), `cat_thm_one_idempotent`,
  `cat_thm_one_image` and `cat_thm_one_fixed` (`im(rho_F) = Fix(rho_F) = L_F`),
  `cat_thm_one_order_independent`, and `cat_thm_one_fold_image` for the positional fold.
- **Corrected hypothesis.** `cat_thm_one_m1_counterexample`: with M1 read as validity preservation
  under overwrite (the paper's Background definition) plus local idempotence, Theorem 1 fails:
  `rho_F` does not land in `L_F` and is not idempotent, because compensation rewrites the shared
  component the morphism wrote. The hypothesis that makes Theorem 1 true is `sh_fixed`, the paper's
  own Section 3.3 reading of M1/R2.
- **Non-vacuity.** `nv_*`: three registries (2 reads 0 and 1), clamping normalizers and a summing
  resolver discharge `idem`, `putget` and `sh_fixed`; `nv_sound`, `nv_s0_not_LF` (L_F is a genuine
  constraint), `nv_orders_agree` (two topological orders) and `nv_prop_one`.

The gate also covers the Cat-cited `Categorical.v` names that were not in it: `fixed_is_equalizer`,
`retract_fixes_fixed`, `rhoL_idempotent`, `rhoL_image_iff_L`, `rhoL_L_iff_fixed`, `rhoFold_sound`,
`rhoFold_complete`, `rhoF_from_app`.

## Cohomological layer (`Cohomology.v`)

The operational core of the companion's cohomological layer (paper Sections 5-6), mechanized
axiom-free. `Cohomology.v` mechanizes the per-cycle content the diagnostic computes; the general-graph
completion, the cycle-basis generation, and `H^1` as a quotient with its rank are in
`CohomologyGraph.v` (below).

- **Gluing is not naive (Section 5).** `gluing_order_dependent`: two confluent normalizers on
  `{0,1,2}` with the same valid set `{0,2}` but different maps on the shared state
  (`disagree_as_normalizers`) glue to an order-dependent union, so agreement on valid values is not
  enough. `rA_idem`, `rB_idem`, and `agree_on_valid` supply the setup.
- **Completion theorem, single-cycle essence (Section 6).** `fixed_point_iff_trivial_holonomy`: in
  the invertible fragment each edge acts as a group translation, the loop composite is translation
  by the holonomy, and it has a fixed point (a global section closes) iff the holonomy is the
  identity. So a section exists iff `H^1` vanishes on that cycle. `loop_composite` and `has_section`
  frame the general model.
- **The minimal obstruction.** `identity_holonomy_has_section` (trivial holonomy settles) and
  `flip_no_section` (the negation on `{0,1}`, as `Z/2` under xor, has no fixed point, so the loop
  orbits) instantiate it, the negation being the minimal nonzero obstruction.
- **Multi-loop / non-abelian.** `simultaneous_section_iff`: for a bouquet of loops sharing one value,
  a simultaneous section exists iff every loop's holonomy is trivial. The proof uses no commutativity,
  so it holds for a non-abelian `G`. This is the necessary-and-sufficient content behind the
  minimal-coordination reading (coordinate exactly the non-trivial loops), and it settles the
  edge-disjoint regime: the minimum is the number of obstructing cycles, for any `G`. The general
  minimum is the group feedback edge set number of the labeled nerve: NP-hard even in the abelian
  case (it is edge bipartization / Max Cut), fixed-parameter tractable in the coordinated-core size,
  and polynomial on planar or edge-disjoint nerves. See `CATEGORICAL-STRUCTURE.md` section 10.3.
- **The `S_3` separating instance (`S3Sep`).** Machine-checks the finite crux that the non-abelian
  minimum can be strictly ABOVE the abelian count (so never below): on the theta graph with generator
  holonomies `a = (0 1 2)` and `b = (0 1)` in `S_3`, every single-edge deletion leaves a non-trivial
  residual (`del_e1/e2/e3_nontrivial`, so `min_G = 2`), while `a` is even (`a_even`, invisible to the
  sign / abelian invariant, so `min_{G^ab} = 1`). `a_inv` confirms `a` is a genuine relabeling.
- **The graph-level minimum counts (`CohomologyMin.v`).** Closes the wrapping around those crux facts,
  stated directly in terms of global sections over the `S_3` torsor (each section decider is proven
  equivalent to the section Prop, so the theorems are about sections, not about a checker).
  `min_G_lower` / `min_G_attained`: every coordination leaving a section deletes at least two edges,
  and keeping only the spanning edge leaves one, so `min_G = 2`. `min_ab_lower` / `min_ab_attained`:
  the abelianized problem needs one deletion and deleting `e3` suffices, so `min_{G^ab} = 1`.
  `sign_hom` proves the sign map is a homomorphism (the true abelianization), and
  `section_G_implies_ab` proves every `S_3` section induces an abelian one, the
  "never below the abelian count" direction. `theta_separation` packages the strict gap
  `1 = min_{G^ab} < min_G = 2`.

- **The completion on an arbitrary graph (`CohomologyGraph.v`).** Any finite graph, any group (abstract
  group laws as section hypotheses). `section_iff_coboundary`: a global section exists iff the edge
  labeling is a coboundary (Thm 7.2 in general). `tree_has_section`: a spanning tree always carries a
  section, so coordinating every non-tree edge restores convergence (Prop 9.1). `tree_unique`: tree
  sections are unique up to one right constant. `cycle_basis_criterion`: for a spanning tree plus
  extra edges, the whole graph has a section iff every fundamental cycle has trivial holonomy
  (`sat_iff_trivial_holonomy`), so the obstruction is generated by the fundamental cycles.
  `keep_balanced_suffices` / `unbalanced_blocks`: relative to a fixed spanning tree, the edges that
  must be coordinated are exactly the unbalanced fundamental edges. A Z/2 triangle
  (`tri_identity_has_section`, `tri_flip_no_section`) discharges every hypothesis and shows the
  criterion firing both ways.

- **`H^1` as a quotient, and its rank (`CohomologyGraph.v`).** A gauge acts on a labeling by
  `g -> h(v) g h(u)^-1`; labelings are `cohomologous` when one is a gauge transform of the other.
  `gauge_fix`: every labeling is cohomologous to one that is the identity on a spanning tree, and
  `gauge_fixed_holonomy`: the remaining labels are exactly the fundamental-cycle holonomies.
  `H1_classification`: two tree-fixed labelings are cohomologous iff their non-tree labels are
  simultaneously conjugate by one group element, for any group, abelian or not. So `H^1` is the
  tuples of fundamental holonomies modulo simultaneous conjugation. `tree_vertex_count` and
  `betti_number`: the number of those generators is `|E| - |V| + 1`, the first Betti number.
  `tri_flip_not_cohomologous_to_identity` discharges every hypothesis on the Z/2 triangle.
  Scope: this is `H^1` of the graph (the nerve's 1-skeleton, where every labeling is a cocycle). The
  nerve's triangles (2-cells) impose further relations that can lower the rank; those are not
  modeled.

Paper-level (not mechanized): the rank on the nerve as a 2-complex (the triangle relations), and the
complexity of choosing the spanning tree that minimizes the coordinated set (the group feedback edge
set results, cited from the literature).

## Non-monotone cycles under a computed coordination (`CoordinatedCycles.v`)

Soundness of the holonomy-minimal plan in gsm's `HOLONOMY-COORDINATION-DESIGN.md`, mechanized
axiom-free by composing the acyclic federation results (`FederationOrder.v`, `FederationEvents.v`)
with `CohomologyGraph.v`.

**Model of the plan.** The network is a group-labeled graph as in `CohomologyGraph.v` (the
invertible fragment: the shared fiber of every registry is the group `G`, an edge `(u, v, g)`
transports `s(u)` to `g * s(u)`). Relative to a designated authority root `r`, a plan splits the
edges into three lists:

- `T`, a spanning tree grown from `r` (`tree r T`). Tree edges **drive** values: the root keeps its
  own value, and every other tree registry reads only its tree parent and takes the transported
  value (`g * s(p)`, or `g^-1 * s(p)` when the tree edge points toward the root). The network
  (`dsrc`, `dfun`) is computed from `T`; it is acyclic, so it is an acyclic federation in the sense
  of `FederationOrder.v` and `FederationEvents.v` (`drive_common` discharges `Common`).
- `B`, balanced non-tree edges. They are **demoted to checked constraints**: they never write, and
  a state is accepted only if it satisfies them.
- `C`, coordinated non-tree edges. They are **removed from the federation**: neither a writer nor a
  constraint inside it. Whatever the external coordinator does with them (serialize them through a
  single authority, or reject the writes they would make) happens outside the propagation graph,
  and the normal form is not required to satisfy them.

**Results.**

- `drive_order_exists`: the driving network has a topological order over exactly the tree's
  vertices, so a normal form exists. `drive_consistent`: running any such order leaves every tree
  registry equal to its driven value, keeps the authority value at the root, and leaves off-tree
  registries untouched (through `FederationEvents.frun_solves`; `topo_topoF` and `frun_run` bridge
  the two acyclic-federation files). `cons_section`: such a state is a section of the tree.
- `balanced_any_section`: balance against one tree section implies balance against every tree
  section (the right constant of `tree_unique` cancels), so "balanced" is a static property of the
  edge.
- **`coordinated_sound` (the soundness theorem).** If `T` is a spanning tree from `r` and every edge
  of `B` (among the tree's vertices) is balanced, then for every initial state `s0` and every
  topological order `o` of the driving network, the normal form `drive r T o s0` satisfies every
  edge of `T ++ B`, has the authority value `s0 r` at the root, leaves off-tree registries at `s0`,
  is the **unique** state satisfying `T ++ B` with root value `s0 r` on the tree (`tree_unique`: the
  root fixes the constant), and every other topological order reaches the same state pointwise
  (`FederationOrder.order_independent`). `coordinated_unique_nf` states the same as existence and
  uniqueness.
- `coordination_needed` (via `unbalanced_blocks`): keeping any unbalanced edge of `C`, as a writer
  or as a constraint, leaves no consistent state at all, so the normal form is lost.
  `plan_exact` (via `cycle_basis_criterion`): with `B` balanced and `C` unbalanced, a set of
  non-tree edges can be kept with a consistent state iff it avoids `C`. The coordinated set is
  exactly the unbalanced edges, relative to the tree.
- `coordinated_events_converge`: composed with `fed_permutations_converge`, any two permutations of
  local events (on any tree registries) converge under the plan when the authority root's own
  events commute, and the result satisfies `T ++ B`. Events on non-root registries are overwritten
  by the drive: a demoted edge no longer propagates a local write backward, as the design note
  warns.

**Instances** (Z/2 as `(bool, xor)`, gsm's two 2-cycles from `diagnose_test.go`, every hypothesis
discharged). `copyback_zero_coordination`: A -> B copy and B -> A copy, rooted at A; the back edge
is balanced and kept as a constraint, nothing is coordinated, and the normal form is `A = B = s0(A)`.
`negation_one_coordinated`: A -> B copy and B -> A `1 - x`, rooted at A; one edge is coordinated, the
rest has a unique normal form, and keeping the coordinated edge leaves no consistent state.

**Where the naive statement fails** (recorded as theorems).

- `copyback_without_authority`: with no root (both copy-back edges kept as writers), two
  propagation orders from `A = 0, B = 1` reach `(1, 1)` and `(0, 0)`, both consistent. Trivial
  holonomy gives existence, not uniqueness; the authority root is what makes the normal form unique.
- `root_choice_matters`: the normal form is unique given the root, but depends on the root. Rooted
  at A versus at B, the same edges and the same initial state reach `(0, 0)` versus `(1, 1)`. The
  plan must report its root ("coordination-free given the reported authority root").
- `noninvertible_balance_not_static`: with a non-invertible transport (B -> A the constant 0), the
  back edge holds at the normal form from authority value 0 and fails from 1. Without the group
  laws, whether an edge needs coordination depends on the authority value, not on the cycle.
- `nonfree_holonomy_counterexample`: with bijections acting on a fiber that is not the group itself
  (a swap of `{0, 1}` acting on `{0, 1, 2}`), a non-identity holonomy still admits a consistent state
  (value 2), so "keeping an unbalanced edge destroys every consistent state" needs the regular
  action. The edge is still violated from authority value 0, so a plan that must be sound for every
  root value still coordinates it.

Scope: the fiber is the group itself (the regular action). Choosing the spanning tree (and root)
that minimizes the coordinated set is the group feedback edge set problem, cited at the paper level.

## The federated theorems in corrected form (`FederationGRS.v`)

ROADMAP item 7, work package WP5 (rows F6 to F10 and F17 to F19 of `PAPER-MAP.md`). The federation
paper's Section "Federated Convergence" states its results for the federated rewrite system
`G_Fed`: apply steps run an event on its registry, and the compensation step is `rho_Fed` (phase 1:
`rho^*` on every component; phase 2: in topological order, overwrite each target's shared component
with its morphism image or resolver value). `FederationGRS.v` builds `G_Fed` as an instance of
`Governance.step` (federated states as lists, so Leibniz equality is the paper's state equality),
states the paper's hypotheses as a record, and mechanizes each result by label. Axiom-free.

The model:

- `PaperNet` (Part B) is the hypothesis set of `thm:resolved-convergence`: a shared/local
  decomposition of every state space (`mk`, `sh`, `lc`, Def. "Registry Morphism"), an acyclic network
  with a resolver `Gam j` per target reading only its sources (R1) and preserving validity (R2; M1
  for a single source), component WFC (`cj`, `Phij`, with `rho j` the iterate to validity) and
  component CC (CC1 on every same-registry pair, CC2 with the one-step compensation).
  `PaperTree` adds "each non-source has one incoming edge" (`thm:fed-cc`, `thm:fed-convergence`).
  `paper_common` derives the `Common` conditions of `FederationEvents.v` from them.
- `gapply`, `grho`, `gvalid` (Part A) are the apply step, `rho_Fed` and federal validity on list
  states; `gov e = grho o gapply e` is the governed step, and `gov_eq` shows it is
  `FedMachine.Apply`. The GUARDED system (`genab`: an event fires only at a federally valid state,
  compensation first) is `FedMachine.Apply` semantics as a rewrite system.
- `XU` is C1 for every valid target state, not only consistent ones (`FederationEvents.v`).

Results, by paper label:

| Label | Status | Coq |
|---|---|---|
| `lem:authority` (a) | exact (at every normal form) | `fed_lem_authority_a` (non-vacuity `fed_lem_authority_a_instance`); generic `source_projection`, `fed_authority_a_gen` |
| `lem:authority` (b) | exact | `fed_lem_authority_b` |
| `lem:authority` (c) | first clause exact; convergence clause refuted, corrected | `fed_lem_authority_c_local`; `fed_lem_authority_c_refuted`; `fed_lem_authority_c_corrected` |
| `lem:fed-termination` | exact, from ANY state | `fed_lem_fed_termination`, `single_round`, `phase2_invariant`, `fed_phase1_bound`, `grho_valid` |
| `lem:resolved-termination` | exact, from ANY state | `fed_lem_resolved_termination` |
| `thm:fed-cc` | refuted; corrected | `fed_thm_fed_cc_refuted`; `fed_thm_fed_cc_corrected` (XU), `fed_thm_fed_cc_corrected_machine` (C1 + C2, at valid states) |
| `thm:fed-convergence` | refuted; corrected; exact | `fed_thm_fed_convergence_refuted`, `fed_c2_paper_counterexample`; `fed_thm_fed_convergence_corrected` (XU), `fed_thm_fed_convergence_guarded` (C1 + C2); `fed_thm_fed_convergence_exact` |
| `thm:resolved-convergence` | refuted; corrected; exact | `fed_thm_resolved_convergence_refuted`; `fed_thm_resolved_convergence_corrected`, `fed_thm_resolved_convergence_guarded`; `fed_thm_resolved_convergence_exact` |
| `cor:fed-nf` | refuted; corrected | `fed_cor_fed_nf_refuted`; `fed_cor_fed_nf_corrected` (generic `fed_nf_constructive`, `fed_nf_recipe_xu`) |
| `cor:resolved-nf` | corrected (refuted by the tree case) | `fed_cor_resolved_nf_corrected` |

The bridge to `Governance.step`: `fed_grs_exact` (an instance of `cc_exact_from`: `G_Fed` has unique
normal forms from `s0` for every buffer iff its CC1 and CC2 hold on the states reachable from
`s0`), `fed_grs_un_c1_c2` (unique normal forms imply C1 and C2 at the reachable witnesses of
`fed_exact`), `grs_unique_nf` (XU and component CC give CC1 and CC2 everywhere, then
`governance_unique_normal_forms`, the paper's proof route), and `fed_guarded_exact` (the guarded
system has unique normal forms from a federally valid `s0` for every buffer iff C1 and C2 hold at
the reachable witnesses, via `jc_unique_normal_forms` and `fed_exact`).

Corrected statements (the network hypotheses H are those of the paper: a tree, or an acyclic
resolved network, with M1 or R1 and R2, component WFC and component CC):

- `thm:fed-cc`: H and XU imply that `G_Fed` satisfies CC1 and CC2 at every federated state. H, C1
  and C2 imply CC1 at every federally valid state. H, C1 and C2 do not imply CC2 of `G_Fed`
  (`fed_grs_c1_c2_insufficient`).
- `thm:fed-convergence`, `thm:resolved-convergence`: H and XU imply unique normal forms of `G_Fed`
  from every configuration, and every configuration reaches a federally valid one. H, C1 and C2
  imply unique normal forms of the guarded system from every federally valid start. Exactly: the
  guarded system converges from `s0` iff C1 and C2 hold at the witnesses reachable from `s0`.
- `cor:fed-nf`, `cor:resolved-nf`: under C1 and C2, the normal form `Z` of any event sequence from a
  federally valid start is the unique solution, in topological order, of
  `Z_j = ow_Z(x_m)`, `x_0 = ow_Z(s_j)`, `x_t = ow_Z(sig_{e_t}(x_{t-1}))` over the events of `j`
  in order, where `ow_Z` overwrites the shared component from the FINALIZED sources. Under XU this
  collapses to the paper's recipe `Z_j = ow_Z(sig_{e_m}(...sig_{e_1}(s_j)))`.

Counterexamples, each discharging every paper hypothesis (`au_paper`, `cw_paper`, `gg_paper`):

- `fed_thm_fed_cc_refuted`, `fed_thm_fed_convergence_refuted`, `fed_thm_resolved_convergence_refuted`,
  `fed_lem_authority_c_refuted`: the audit federation (`audit_counterexample` as a paper network).
  From one federally valid state and the buffer `[recall; sell]`, `G_Fed` reaches two federally
  valid normal forms; they agree on the source and on the target's shared flag and differ in the
  target's local `sold` (0 versus 1).
- `fed_c2_paper_counterexample`: C1 holds as well (the `c2_counterexample` as a paper network,
  with the source's compensation made WFC); `G_Fed` still diverges.
- `fed_grs_c1_c2_insufficient`: C1 and C2 hold, every FedMachine permutation converges and the
  guarded system has unique normal forms, but the unrestricted `G_Fed` has two normal forms: two
  target events applied before compensation, the second reading the shared value the first wrote.
- `fed_cor_fed_nf_refuted`: in the same federation the paper's recipe gives `(false, true)`, every
  event order gives `(false, false)`, and the corrected recipe `Gc` gives `(false, false)`.

Non-vacuity: `fed_supply_paper_instance` (the supply chain as a paper network: H, XU, C1, C2, and
the unique-normal-form conclusion instantiated) and `fed_grs_c1_c2_insufficient` (H, C1 and C2
without XU). The list encoding adds bookkeeping hypotheses only: registries are `0 .. n-1`, indices
outside the network are unconstrained, validity and state equality are decidable (the paper's state
spaces are finite).

## Verification calculus for CC (`Calculus.v`)

The Base paper's section "Verification Calculus for CC" (`sec:calculus`), its "Practical import"
remark, pattern 1 of section 8.2 and product composition (PAPER-MAP rows B31, B33, B35 to B40).
A registry has invariants `psi i` indexed by a list `all`, validity is their conjunction, `rho`
fixes valid states and decreases a measure on invalid ones, and `N = rho*` (`IsRegistry`).
Per-invariant repairs (`PerInv`: R1 to R3), `Decomposable`, `IsFootprint`, `RepairLocal` and
`DisjointFP` are the paper's definitions.

Exact: `base_lem_repair_commute` (`lem:repair-commute`), `base_lem_repair_idempotent`
(`lem:repair-idempotent`), `calc_decomp_normalizer` (the Notation facts (i) to (iii) for a
decomposable normalizer), `base_thm_product` (`thm:product`: WFC, `rho*`, CC1 and CC2 lift; CC1
for a product pair holds iff it holds in both components) and `base_thm_product_decomposable`
(repairs, footprints composed by union, repair locality and disjointness lift).

Refuted. `thm:footprint-cc1` is false as stated: `base_thm_footprint_cc1_refuted` (no
invariants, `x := 1` and `x := 2`) and `base_thm_footprint_cc1_raw_refuted` (four states, raw
events commute, CC1 fails at an invalid state). The "Practical import" remark is false:
`base_rem_practical_import_refuted` (every footprint of approve and of credit contains the one
invariant); its other half is true (`calc_order_credit_repair_commute`). Pattern 1 ("canonical
state gives CC1 and CC2 trivially") fails for both conditions: `base_pattern1_cc1_refuted`,
`base_pattern1_cc2_refuted`.

Corrected footprint theorem. Under the paper's hypotheses (H1) disjoint footprints and (H2)
repair locality:

- `calc_footprint_cc1_iff`: CC1 at `s` iff
  `N(A_e2(A_e1(R_F(e2) s))) = N(A_e1(A_e2(R_F(e1) s)))` (exact, every state).
- `calc_footprint_cc1_valid_iff`, `calc_footprint_cc1_valid`: at a valid state, CC1 iff the two
  events commute up to `N` (`N(A_e2(A_e1 s)) = N(A_e1(A_e2 s))`). This is the form gsm checks
  (CC1 on valid states).
- `calc_footprint_cc1`: at every state, CC1 follows from (H2), footprint absorption
  (`FPAbsorb`: `N(A_e(R_F(e) s)) = N(A_e s)`, a per-event check on the event's own footprint
  repairs) and commutation up to `N`. Disjointness is not needed.
- `calc_fp_absorb_iff_sa`, `calc_cc2_strong_absorption`, `calc_cc1_iff_commute_under_cc2`:
  footprint absorption is strong absorption for a repair-local event, CC2 implies strong
  absorption, and under CC2 the CC1 of a pair is exactly commutation up to `N`.
- `calc_components_cc1_valid`, `calc_components_cc1_iff`: gsm's footprint components (state
  `S1 * S2`, normalizer componentwise, each event inside one component) satisfy CC1 at every valid
  state with no further hypothesis; at an invalid state CC1 holds iff each event absorbs `N` in
  its own component.

Each added hypothesis is needed: `calc_valid_needs_commute`, `calc_valid_needs_disjoint`,
`calc_valid_needs_repair_local`, `calc_all_needs_commute`, `calc_all_needs_absorb`,
`calc_all_needs_repair_local` (every other hypothesis holds, CC1 fails). Non-vacuity:
`calc_clamp_instance` (two clamped counters, disjoint footprints), `calc_order_cc1` (the paper's
order-fulfillment registry: overlapping footprints, CC1 at every state by `calc_footprint_cc1`,
CC2 for both events), `calc_components_instance`, `calc_product_instance`.

Corrected pattern 1: `calc_canonical_cc2_iff` (with canonical compensation to `bot`, CC2 for `e`
iff `N(A_e s) = N(A_e bot)` for every invalid `s`) and `calc_canonical_pattern` (with that check
for both events, CC1 iff commutation up to `N`); non-vacuity `calc_canonical_instance`.

## General transport maps: the obstruction, the diagnostic, and coordination bounds (`CohomologyGeneral.v`)

The general-map content of the companion paper's sections 6 to 8 (work package WP9 of
`PAPER-MAP.md`), axiom-free. Where a paper statement is false or imprecise, the counterexample is a
theorem and the strongest true form is proven next to it.

**The obstruction theorem (`thm:obstruction`).** A cycle carries edge maps `f_0, ..., f_{n-1}`
(any maps on any fiber `V`, no invertibility); a section is `s 0, ..., s n` with
`s (i+1) = f_i (s i)` and `s n = s 0` (`cycle_section`). "Reachable fixed point", which the paper
does not define, is made precise as `reaches_fixed g x0`: some iterate `g^n x0` is fixed by `g`.

- `thm_obstruction_general`: a section exists iff the loop composite has a fixed point.
  `sections_are_fixed_points`: restriction to vertex 0 is a bijection from sections onto `Fix(g)`,
  so the witness lives on the shared fiber alone.
- `reaches_fixed_iff_section`: a fixed point is reachable from `x0` iff some section has its vertex-0
  value on the forward orbit of `x0`. `thm_obstruction_reachable`: the paper's statement, with
  "reachable" meaning "reachable from some seed".
- gsm's `DiagnoseCycle`, on a finite fiber with decidable equality (`N` = its size):
  `diagnose_bounded` (the seed reaches a fixed point iff `g^N x0` is fixed), `diagnose_orbit_witness`
  (the orbit repeats within `N` steps), `diagnose_dichotomy` (exactly one of the two outcomes).

**Reading the diagnostic (section 7).** "A non-convergent result is definitive" is false:
`c15_definitive_claim_false`, with the loop copy-then-swap on `{t0, t1, t2}` (swap `t0, t1`, fix
`t2`): seed `t0` orbits (`c15_seed_orbits`) while `t2` is a section (`c15_tri_section`). Corrected
forms: `c15_exact_refuter` (no section iff no seed reaches a fixed point), `c15_free_definitive`
(one seed is definitive when the fixed points of `g` are all-or-nothing),
`c15_injective_reaches_iff_fixed` (for an invertible composite a seed reaches a fixed point iff it
is fixed), `c15_regular_definitive` and `c15_regular_is_free` (translation by the holonomy: from any
seed, reaches iff `h = e`). `c15_convergent_result_sound`: a settling seed proves a section exists;
`c15_convergent_result_not_global`: it does not prove every seed settles.

**Minimal coordination with its qualifiers (`prop:minimal`).** `prop_minimal_qualified_iff`: in the
regular action with an authority root `r` and spanning tree `T`, the labeling `T ++ X` is a
coboundary (`H^1 = 0`) iff for every authority value the uncoordinated network (tree drives, every
non-tree edge kept as a checked constraint) has a consistent state that is the unique one with that
root value and that every propagation order reaches. `prop_minimal_qualifiers_needed`: Z/2 acting on
`{t0, t1, t2}` by the swap gives a non-coboundary with a section (the regular action is needed), and
`nonfree_holonomy_counterexample`, `copyback_without_authority` (the authority root is needed).

**Coordination as edge deletion (section 8).** `feasible Es D`: some state satisfies every edge of
`Es` outside `D`.

- Edge-disjoint obstructions: `edge_disjoint_lower_bound` (`k` pairwise edge-disjoint cycles with no
  section force at least `k` deleted edges, for any labels) and `edge_disjoint_min` (with a spanning
  tree whose unbalanced non-tree edges number `k`, the minimum is exactly `k`); instance
  `bowtie_min_two`.
- `min_G >= min_{G^ab}` in general: `section_pushforward`, `feasible_pushforward` and
  `min_G_ge_min_image` push sections and feasible coordinations along any homomorphism, any graph;
  instance `klein_min_ge_1`.
- The non-invertible case, "a cycle basis still suffices", is false: `c22_cycle_basis_fails` is a
  tree (empty cycle basis) with constant maps 0 and 1 into one vertex, which has no section; one
  deletion restores one. Corrected for root-oriented trees (`otree`, every edge pointing away from the
  authority root): `out_tree_section`, `out_tree_unique`, `rooted_criterion` (a section with the
  tree-driven root value exists iff the driven state satisfies every non-tree edge),
  `rooted_coordination_suffices`; instance `c22_rooted_instance`.

**Two regimes, not exhaustive (section 6).** `c13_two_ways_not_exhaustive`: a cyclic loop of two
negations (trivial holonomy, non-monotone edges) and copy-then-swap on `nat` (non-trivial holonomy,
non-monotone composite) both have sections, so acyclicity and monotonicity are two sufficient
conditions, not the only ones.

## Stream processors and Stream Convergence (`Stream.v`)

The base paper's headline theorem (Thm. "Stream Convergence", `thm:convergence`) is about stream
processors that receive events over time, not about one rewrite system. `Stream.v` formalizes
Def. "Stream Processor" (`def:processor`) on top of the causal GRS with the well-founded WFC of
`GovernanceWF.v`, so every result is domain-independent, and proves the stream-level results
axiom-free. `rho*` is taken as in `Governance.v` (specified by `rho_star_reach`).

- Model: `prstep` is the processor discipline inside the GRS (compensate while invalid; apply an
  enabled event only from a valid state); every `prstep` is a GRS step and a `prstep` normal form is
  a GRS normal form (`prstep_cstep`, `nf_prstep_cstep`). A `processor` has received sets
  `recv : nat -> list Event` and configurations `conf : nat -> State * list Event`, with
  `psi p t = fst (conf p t)`. `is_processor` asks for duplicate-free received sets drawn from the
  stream, growth by appending, eventual delivery, and the paper's "the computation on `E_P(t)` is a
  reduction sequence from `(sigma0, E_P(t))`". `settled p t` says the processor has finished
  processing `E_P(t)`; `fair p` says it keeps reducing while nothing new arrives.
  `incremental_computes`: a processor that carries its configuration across arrivals is a
  processor.
- (a) `stream_validity`, `comp_phase_terminates`, `comp_phase_done_valid`,
  `settled_empty_buffer` (with a progress hypothesis the finished configuration has an empty
  buffer). (b) `stream_order_independence` (finished reductions from the same received set end in
  the same state) and `stream_orders_agree` (any two feasible application orders, each followed by
  `rho*`, agree). (c) `stream_agreement` (also across different times) and
  `base_thm_convergence_c`. Bundled: `stream_convergence` (any well-founded potential) and
  `base_thm_convergence` (the paper's `Phi : Sigma -> nat`).
- `base_rem_set_function` (`rem:set-function`): `F(E)` exists and depends only on the set `E`.
- `base_cor_quiescent`, `base_cor_quiescent_nat` (`cor:quiescent`): on a finite stream two fair
  processors eventually hold the same valid state forever. The proof derives "eventually settled"
  from termination and fairness.
- `base_cor_infinite`, `base_cor_infinite_quiescent` (`cor:infinite` at stream level).
- Corrections. Part (c) as written (no "settled" qualifier) is false:
  `base_thm_convergence_c_counterexample` (two fair processors with the same received set, one
  of which has not yet applied it). The closing sentence of the theorem ("disagreements are
  transient ... restoring agreement") and `rem:infinite-streams` are false for infinite streams:
  `base_thm_convergence_transient_counterexample` (one processor a tick behind the other on an
  infinite stream; both settled at every time, they disagree at every time).
- Non-vacuity: the `Z` withdrawal registry with two processors that receive withdrawals 1 and 2 in
  different orders and at different times (`zw_stream_registry`, `zw_processors`,
  `zw_stream_agree`, `zw_stream_quiescent`, `zw_stream_quiescent_nat`,
  `zw_stream_convergence_nat`, `zw_incremental`); the counter registry of the counterexamples
  meets every registry hypothesis (`ct_registry`).

## The papers' concrete examples (`PaperInstances.v`)

Every worked example and counterexample in the two normalization-confluence papers, on the paper's
own data, with every property the paper claims for it as a theorem (work package WP2 of
`PAPER-MAP.md`). Where the paper's text is wrong, a theorem refutes it and a second one proves the
corrected claim.

- **Order fulfillment (Base section 4, row B17).** `of_registry` (rho fixes valid states, WFC, UBC
  with `M = 1`, the invalid states are exactly `(approved, 0)` and `(approved, 1)`),
  `of_valid_paper`, `of_rho_star_iterated` (`rho* = rho` is the iterated compensation of the
  paper's definition), `of_cc1` (CC1 for every pair of events at all 12 states), `of_cc2`,
  `of_paper_traces` (the displayed CC1 and CC2 traces, state by state), `of_unique_normal_forms`
  (through `cc_exact_global`), `of_processors` (P1 and P2 are runs of the rewrite system to
  `((approved, 2), [])`, and every normal form of the paper's stream is that one).
  The naive revert `rho(approved, b) = (pending, b)`: `naive_registry` (WFC, UBC),
  `naive_paper_witness_fails` (the paper's witness is wrong: at `(pending, 0)` both orders give
  `(pending, 1)`), `naive_cc1_fails` (the corrected witness `(pending, 1)`: `(pending, 2)` versus
  `(approved, 2)`), `naive_stream_diverges` (the paper's own stream reaches two normal forms),
  `naive_cc2_fails` (it also violates CC2, at `(approved, 1)` with credit).
- **`R_infinity` (Base `thm:necessity` and the remark "What Fails", rows B25, B26).** On `Z` with
  `apply(e_n, s) = s - n`. `thm_necessity` (for every `M`, a reduction to normal form with more than
  `M` compensation steps, counted by the relation `cred`), `ri_depth_exact` (every reduction from
  `(0, [e_n])` to a normal form has exactly `n`), `ri_no_ubc` (no WFC measure is bounded),
  `ri_cc_any_extension` (CC1 at every state for every pair and CC2 hold for every total extension
  of `apply(e_n, -)`: `rho*` is constant 0), `ri_what_fails` (WFC, CC, unique normal forms, not
  UBC), `ri_rho_star_iterated`.
- **Four-state CC counterexample (Base `prop:cc-necessary`, row B27).** `four_registry`,
  `four_paths`, `prop_cc_necessary`: two runs from `(A, [e1; e2])` reach the distinct valid normal
  forms `(B, [])` and `(A, [])`.
- **Cyclic network (Fed `prop:cycle-necessary`, row F13).** `cycle_paper_trace` (the paper's four
  repairs back to `(0, 0)`), `prop_cycle_necessary` (components valid everywhere, both morphisms
  M1, federated compensation deterministic, no federally valid state, no state terminates).
- **M1 counterexample (Fed `prop:m1-necessary`, row F14).** `m1_paper_trace`, `prop_m1_necessary`
  (M1 fails, deterministic oscillation, never terminates), `m1_single_round_fails` (one application
  of `rho_Fed` returns a federally invalid state: single-round termination needs M1).
- **Resolution conditions (Fed remark after `thm:resolved-convergence`, row F21).**
  `r2_necessary` (a two-source resolver with R1 and without R2 oscillates forever), `r1_necessary`
  (a resolver that reads the target's local component, with R2 and component WFC, on an acyclic
  network: two federally valid normal forms whose shared components differ).
- **Manufacturer-supplier federation (Fed section 6, row F32)**, in `FederationEvents.v`'s model:
  `ms_instance` (`Common`, C1, C2, each registry's own CC, the paper's M1, the supplier's WFC, a
  valid consistent start), `ms_paper_traces` (both orders, state by state, end in
  `(active, listed)`), `ms_converges` (every permutation of any event list converges, through
  `fed_permutations_converge`).

Encodings: the federated examples' `{0, 1}` is `bool`; events in these examples have no causal
dependencies, so enabledness is `free_enabled`.

## Compositional collapse: sub-federations as effective registries (`Collapse.v`)

ROADMAP item 7, work package WP8 (rows F28 to F30, C4 and C5 of `PAPER-MAP.md`): the federation
paper's `thm:collapse` and `cor:modular`, the categorical paper's Theorem 2 collapse claim and its
port refinement. Built on `FederationEvents.v` and `FederationGRS.v` (WP5): the primary corrected
form is the GUARDED federation (events fire only at federally valid states) under C1 and C2.
Axiom-free.

The model. A sub-federation `J` is a membership predicate `inJ`; the data-flow graph has an edge
`k -> j` when `k` is a source of `j` (`path`). `Convex` is `def:subfed`'s convexity. The effective
registry `R_J` (`def:effreg`) has compensation `rhoJ` (phase 1 on the members, then the internal
repairs along `blk`, the members in topological order), member validity `InvJ` and internal
morphism invariants `ConsJ`; its events are the events of the members, `applyJ e = rhoJ o e`. The
contracted network `N'` is `srcC` / `orderC` (graph: `J` replaced by one vertex `c`) and `Ncol`
(normalizer: `J` run as one node), with `grhoC`, `gvalidC`, `genabC` its federated GRS on lists.

| Label | Status | Coq |
|---|---|---|
| proof of `thm:collapse` (c): "a topological order visits a convex `J` as a contiguous block" | refuted ("every order"); corrected ("some order") | `collapse_every_order_refuted`; `collapse_block_order` |
| `thm:collapse` (c): `N'` acyclic if `N` is | exact | `collapse_contract_topo`, `collapse_contract_acyclic` (`topoF_acyclic`); convexity needed: `collapse_convexity_needed` |
| `thm:collapse` (a), WFC | exact (one round) | `collapse_a_wfc` |
| `thm:collapse` (a), CC | refuted; corrected (C1 + C2 on `J`'s events); exact | `collapse_a_refuted`; `collapse_a_guarded`, `collapse_a_guarded_perm`; `collapse_a_guarded_exact` |
| `thm:collapse` (b) | exact with M1 against member validities; refuted with M1 against `R_J`'s federal validity; corrected | `collapse_b_import_iff`, `collapse_b_export_iff`; `collapse_b_import_refuted`, `collapse_b_export_refuted`; `collapse_b_import_corrected`, `collapse_b_export_corrected` |
| `thm:collapse` (c): normal forms agree | exact | `collapse_nf_agree`, `collapse_nf_factor` |
| `thm:collapse` (c): `N` converges iff `N'` does | exact (FedMachine runs, guarded and unguarded GRS) | `collapse_c_runs_agree`, `collapse_c_traceconv`, `collapse_c_exact`; `collapse_c_guarded_iff`, `collapse_c_unguarded_iff`, `collapse_c_guarded_exact`, `collapse_c_guarded_c1_c2` |
| `cor:modular` | exact (corrected hypotheses) | `collapse_modular_c1`, `collapse_modular_c2`, `collapse_modular_converges`; nesting `collapse_regroup`, `collapse_hierarchical`; product case `collapse_product_convex` |
| categorical `thm:two`, "collapses to an effective registry" | exact | `collapse_nf_agree`, `collapse_a_wfc`, `collapse_c_guarded_iff` |
| categorical Section 4, port refinement | mechanized; sealed write refuted | `port_c1_transfer`, `port_c2_transfer`, `port_interior_certificate`, `port_interior_invariant`; `port_sealed_write_refuted` |

Corrected statements (H: `J` convex, its members' morphisms satisfy M1/R2, its components WFC and
CC, the network acyclic):

- (a) `rho_J` reaches `R_J`-validity in one application from any state with valid import ports,
  leaves every non-member unchanged and fixes every `R_J`-valid state (WFC). H does not give `R_J`
  CC: the audit federation (`J` = all of it) satisfies H and two of its events do not commute
  through `R_J` at an `R_J`-valid state. With C1 and C2 for the events of `J`'s members,
  federally independent events commute through `R_J` at every `R_J`-valid state, and (every
  same-registry pair declared independent) every two orders of `J`'s events agree; exactly, `R_J` converges from an `R_J`-valid state iff C1 and C2
  hold at the witnesses reachable inside `J`.
- (b) With M1 posed against the product of the members' validities, an import into a member (or
  an export out of `J`) satisfies M1 for `R_J` iff it does in `N`. With M1 posed against `R_J`'s
  federal validity (member validities and internal invariants), the import direction fails (an
  import overwrites a port and breaks an internal copy) and so does the export converse (an export
  that is M1 on internally consistent sources only). What holds: an import followed by `rho_J`
  lands in `R_J`'s federal validity; M1 of an export in `N` implies it for `R_J`.
- (c) Contracting a convex `J` keeps the network acyclic (convexity is needed); `N'`'s normalizer
  equals `N`'s, and factors as "registries before `J`, then `rho_J`, then the rest"; every event run
  of `N'` equals the run of `N`, so `N'` converges iff `N` does, for the guarded and the unguarded
  GRS. Under C1 and C2 (checked per block) `N'` converges; exactly, iff C1 and C2 hold at the
  reachable witnesses.
- `cor:modular`: C1 and C2 split by the event's registry (`J` and the rest), so verifying `J`'s
  certificate once and the rest once gives `R_J`'s guarded CC and the convergence of `N'`; any
  block decomposition whose flattening is a topological order computes `rho_Fed`, and regrouping
  consecutive nodes changes nothing, so the construction nests. A `J` with no edge leaving it
  (the product case) is convex.
- Port refinement: if the embedding changes the sources and repair only of ports (sealed members
  keep theirs), C1 and C2 at sealed members transfer verbatim, the subsystem's certificate plus the
  seam re-check at the ports is `J`'s full certificate in the embedding, and every federally valid
  state of the embedding satisfies the sealed members' certified repair equations. A write to a
  sealed member breaks that guarantee (`port_sealed_write_refuted`).

Not covered: the cyclic-with-monotone-repair variant of `thm:collapse`'s hypothesis and the remark
"Convexity and the monotone regime" (the monotone cycle model is `FederationEventsCycles.v` /
WP6's). Non-vacuity: `chain_collapse_instance` (a chain `0 -> 1 -> 2`, `J = {0, 1}`: Common, C1, C2,
convexity, the block order, the contracted network, and the guarded convergence of `N'`
instantiated); the counterexamples `collapse_b_import_refuted` and `port_sealed_write_refuted`
satisfy `Common`.

## Roadmap: mechanizing the categorical layer (companion paper)

The companion paper (categorical structure of federated convergence) rests on a small structural
core that is elementary in `Set` and finite posets, so it mechanizes by leaning on the modules above
rather than pulling in heavy category-theory libraries. Progress, in priority order:

1. **Lemma 0 (a registry is an equalizer).** DONE (`Categorical.v`): `image_iff_fixed`,
   `fixed_is_equalizer`. `Fix(rho) = im(rho) = eq(id, rho)`, axiom-free.
2. **Proposition 1 (the consistent set is a finite limit).** DONE (`Categorical.v`):
   `consistent_iff_equalizer`. The federated consistent set is the equalizer of the shared-component
   and resolver-value maps, axiom-free (product over targets modeled as a list).
3. **Theorem 1 (federation retraction, acyclic).** DONE (`Categorical.v`) for the operator content:
   the general Corollary (`RetractionOntoConsistent`), a concrete two-registry operator
   (`FederatedOperator`), and the general acyclic fold `rho_F` over a topological order
   (`GeneralFederatedFold`: `rhoFold_retraction`, `rhoFold_image_iff_consistent`) discharging Lemma A
   and Lemma B, so `rho_F` is the idempotent retraction onto `L_F` for every acyclic federation.
   Full order-independence is DONE (`FederationOrder.v`: `order_independent`), proved by bubbling
   rather than through linear-extension connectivity.
4. **Theorem 2 (compositionality).** DONE (`Categorical.v`): `rhoFold_compositional` (via
   `rhoF_from_app`). The flat normalization over a topological cut `J ++ K` equals finalizing `J`
   then continuing with `K`, so an upstream sub-federation collapses to its finalized block.

With Lemma 0, Proposition 1, Theorem 1 (retraction, general acyclic fold), and Theorem 2
(compositionality) mechanized axiom-free, the structural core of the companion is complete. The development
was then extended past the structural core: full order-independence (`FederationOrder.v`) and the
cohomological completion through `H^1` as a quotient (`Cohomology.v`, `CohomologyMin.v`,
`CohomologyGraph.v`). The loop-composite fixed-point diagnostic is implemented in gsm as
`Federation.DiagnoseCycle`.

Kept at paper level (out of scope for the first mechanization pass):

- The cohomological completion is mechanized in the invertible/torsor fragment (above). The general
  non-invertible case reduces to the loop-composite fixed-point condition, a dynamical statement
  rather than group cohomology, and is not mechanized.
- The operational core of that story is already implemented: the loop-composite fixed-point / orbit
  test is `gsm`'s `Federation.DiagnoseCycle`. A later target is mechanizing that test (finite-space
  fixed-point reachability), for which `Federation.v` and `Chaotic.v` already supply most of the
  machinery.

Status: these are targets for the companion submission, tracked here so the axiom-free gate above
(currently 669 theorems) stays legible. Nothing in this roadmap is claimed proven until it lands in a
module and passes the gate.

## Build

```
make          # compiles every module (Newman, Governance, Defensibility, Gsm, Federation,
              # Chaotic, Checker, Trace, TableCheck, TableFast, TableFn, AstChecker,
              # AstTables, AstCompact, CRDT, ...)
make check    # prints the assumption base (expect "Closed under the global context")
```

`bash verify.sh` does the same compile and then runs the full axiom-free gate over all 327
headline theorems. To build and run the two extracted oracles, see `extraction/` (`make`,
`make demo`, `make astdemo`). The same two checkers are also generated as Go, for gsm to run
in-process: see `goextract/` (`make test`).
