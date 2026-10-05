# Infrastructure: verified checkers and paper instances

Detailed results for the infrastructure modules: the two verified oracles gsm runs (table and
rules), the trace equivalence behind them, and the papers' concrete examples. Each module's one-line
summary is in the [module index](../README.md#modules-by-regime).

## Verified checkers: two differential oracles for gsm (`Checker.v`, `Trace.v`, `TableCheck.v`, `TableFast.v`, `TableFn.v`, `AstChecker.v`, `AstTables.v`, `AstCompact.v`, `extraction/`)

Two independent, machine-checked checkers re-certify a gsm machine's convergence, each extracted
to a runnable OCaml binary in `extraction/` and generated as Go in `goextract/` (gsm runs the Go
in-process). Both are proven axiom-free, so a bug in gsm's
hand-written Go verification cannot make a non-convergent machine pass either one. See
[`extraction/README.md`](../extraction/README.md) for build, demo, and file formats.

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
