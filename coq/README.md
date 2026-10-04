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

Expected tail: `PASS: all 232 theorems are Closed under the global context (no axioms, no admits)`.
The gate runs `Print Assumptions` on all 158 headline results (among them the single-registry
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
exactness results of `FederationEventsConverse.v`) and fails if any of them depends on an axiom or an
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

**Not covered.** Non-monotone cycles remain excluded by design: their repair has no unique normal
form reached from bottom, so there is nothing for events to commute after; gsm routes them to
coordination. The distributed model (explicit propagation steps) is not extended to cycles. The
global condition is exact but semantic: on a cycle there is no per-edge reduction, so checking it
means enumerating reachable normal forms (or the image of `N`) and testing every independent pair,
not the per-edge C1/C2 enumeration gsm runs for acyclic networks. Static C1 and C2 remain
over-approximations (sufficient, and necessary only at reachable witnesses).

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
(currently 232 theorems) stays legible. Nothing in this roadmap is claimed proven until it lands in a
module and passes the gate.

## Build

```
make          # compiles every module (Newman, Governance, Defensibility, Gsm, Federation,
              # Chaotic, Checker, Trace, TableCheck, TableFast, TableFn, AstChecker,
              # AstTables, AstCompact, CRDT, ...)
make check    # prints the assumption base (expect "Closed under the global context")
```

`bash verify.sh` does the same compile and then runs the full axiom-free gate over all 158
headline theorems. To build and run the two extracted oracles, see `extraction/` (`make`,
`make demo`, `make astdemo`). The same two checkers are also generated as Go, for gsm to run
in-process: see `goextract/` (`make test`).
