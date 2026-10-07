# Layer C: canonical recurrence (`CanonicalRecurrence.v`)

Layer C of the three-layer framework ([THEORY.md](../../docs/THEORY.md#layer-c-settlement-dynamics-as-fair-recurrence))
asks whether runs reach a consistent state and which one: settlement, fidelity, fair schedules.
`CanonicalRecurrence.v` is a preregistered experiment on that layer, run the way layer A was run in
`PresentedExecution.v`: state one generic kernel, then try to recover the existing settlement
results as short bridges through it, and report every leak. Axiom-free, in the `coq/verify.sh`
gate. No REGIME-AUDIT status changes.

## The hypothesis under test

> Fair convergence is exactly the absence of a bad fair recurrent behavior, made concrete as a
> finite lasso.

Preregistered criterion: PASS if one generic kernel gives short bridges for at least
`chaotic_reaches_lfp`, `signed_settlement`, `signed_fidelity`, `FairFlushR` / fair settlement and
the ghost failure, and the lasso language classifies oscillation, livelock and ghosts. FAIL if
regimes need different long-run obstruction notions that are not fair lassos.

## Setting

- A state type `X` with decidable equality; finiteness (a list `xs` containing every state) is a
  hypothesis of the sections that need it, not of the definitions.
- Scheduler labels are `nat`, with the label list `js`; an asynchronous update `u : nat -> X -> X`.
- Runs and fairness are the existing ones: `prs X u sg n x` (`DistributedCycles.prs`,
  `x_{t+1} = u (sg t) x_t`) and `Fair js sg` (`DistributedCycles.Fair`: every step names a label of
  `js`, every label of `js` is named infinitely often), exactly as `DistributedCycles.v` and
  `SignedResolver.v` use them.
- `FairLasso s0 x p q`: `p` and `q` are `js`-words, `wrun p s0 = x`, `q` is nonempty,
  `wrun q x = x`, and every label of `js` occurs in `q`. `OnLoop x q y`: `y = wrun (firstn k q) x`
  for some `k < length q`. `BadLasso G s0`: a fair lasso from `s0` with a loop state outside `G`.
- `EvAlways G sg s0`: `exists N, forall n >= N, G (prs sg n s0)`. `FairSettles G s0`: every fair
  schedule's run is eventually always in `G`. `FairSettlesNN`: the same, double negated.
- Canonical layer: an observation `N : X -> C` (decidable equality on `C`) and a target `c`.
  `CanonSettles s0 c := FairSettles (fun x => N x = c) s0`,
  `BadCanonLasso s0 c := BadLasso (fun x => N x = c) s0`. Raw settlement: `Settled x := Stable X u js x`
  (every label of `js` fixes `x`).

## The kernel

Plain statements, `X` finite where marked:

- `bad_lasso_witness`, `bad_lasso_refutes` (no finiteness): a bad fair lasso gives the fair
  schedule `p` then `q` forever (`lsg p q`, `lasso_fair`), whose run leaves `G` infinitely often
  (`lasso_visits`); so `FairSettles G s0` and `FairSettlesNN G s0` both fail.
- `recurrence_nn_exact` (finite): `PDec G -> (FairSettlesNN G s0 <-> ~ BadLasso G s0)`. Proof: a
  state outside `G` that recurs with a full window in between is a bad loop state
  (`state_finitely_often`), and finitely many states give one bound (`nn_bound`).
- `recurrence_closed_exact` (finite): for `G` closed under the steps,
  `FairSettles G s0 <-> ~ BadLasso G s0`. Proof: pigeonhole on fairness-window boundaries finds a
  fair loop after any time, its base point is in `G` (`nobad_hits`), and `G` is absorbing.
- `recurrence_classical` (finite): with `forall P, P \/ ~ P` as a premise (not an axiom),
  `FairSettles G s0 <-> ~ BadLasso G s0` for every `G`.

**C1, canonical recurrence.** On a finite `X`:

- `C1_nn`: `CanonSettlesNN s0 c <-> ~ BadCanonLasso s0 c` (axiom-free, every fiber).
- `C1_closed`: if the fiber of `c` is closed under the steps,
  `CanonSettles s0 c <-> ~ BadCanonLasso s0 c`.
- `C1_classical`: `(forall P, P \/ ~ P) -> (CanonSettles s0 c <-> ~ BadCanonLasso s0 c)`.
- `C1_refutes` (no finiteness): `BadCanonLasso s0 c -> ~ CanonSettles s0 c`.

**C2, raw settlement.** On a finite `X`, constructive (settled states are absorbing):

- `C2`: `FairSettles Settled s0 <-> ~ BadLasso Settled s0`.
- `C2_loops`: `FairSettles Settled s0` iff for every fair lasso `(x, p, q)` from `s0`, every loop
  state is `x` and `x` is settled: every fair recurrent loop is a singleton fixed point.
- `C2_reach` (no finiteness): `FairSettles Settled s0` iff every fair run reaches a settled state.

### The constructive leak

The strong form `~ BadLasso G s0 -> FairSettles G s0` is classical. `lpo_leak` mechanizes why: on
a four-state instance (states `g0, h, b, g1`; label 0 moves `g0 -> h -> b`, label 1 moves
`h -> g0`, `b` goes to the absorbing `g1`), there is no bad fair lasso for `G = (not b)` and
`FairSettlesNN` holds, but `FairSettles` implies LPO for boolean sequences: whether a fair run
ever visits `b` depends on whether the schedule ever names 0 twice in a row, which a schedule can
encode from any boolean sequence. So the axiom-free kernel states C1 in the double-negated form,
the closed-fiber form, or with excluded middle as a premise. Every recovery below targets a fixed
point, whose fiber is closed, so all of them use the strong, constructive `recurrence_closed_exact`.

## The bridges

Shared, regime-independent toolkit (Part 4): `pigeon` (on a finite type every sequence repeats),
`infl_wrun`, `infl_loop_fixed` (an inflationary loop fixes every label it uses), `mono_wrun`,
`loop_floor` (from a sound start `b <= z` with `wrun q z = z`, the iterates of `q` from `b`
stabilize at a state below `z` that every label of `q` fixes). About 60 proof lines in all.

Each recovery proves `~ BadLasso` and reads the settlement off the kernel. Bridge sizes are proof
lines of the regime-specific lemmas, not counting the toolkit.

| Existing result | Recovered as | Bridge | Route | Extra hypotheses (leaks) |
|---|---|---|---|---|
| `Chaotic.chaotic_reaches_lfp` | `chaotic_reaches_lfp_lasso` (also `chaotic_settles_lasso`: every fair run from a reachable state settles at lfp) | 36 lines (`ch_nobad` 11) | a fair loop at a reachable state is inflationary, hence a singleton at a normal form (`infl_loop_fixed`); `Chaotic.normal_is_lfp` names it; `recurrence_closed_exact`; any fair run then gives the productive-step path | `L` listed; the index type is `nat` with a finite list `js`, updates outside `js` inert. Not used: `rank`, `bot`, `step_dec` |
| `SignedResolver.signed_settlement` (all four conjuncts) | `signed_settlement_lasso` | about 75 lines: `sr_floor` 8, `sr_below_nobad` 5, `sr_sound_nobad` 6, assembly 32, bindings 14 | below `slfp`: the bottom run under the loop word stabilizes at a fixed point below the loop, so the loop is `slfp` (C1); from a sound start: every fair loop is a singleton fixed point (C2), and the settled point is the least fixed point above `h0` by monotonicity; the E conjunct is `kernel_E` / `kernel_esh` on the lasso-derived settlement | `Sh` listed (the module assumes finite height, not a finite state type) |
| `SignedResolver.signed_fidelity` | `signed_fidelity_lasso` | 28 lines: `sr_ceiling` 9, `sr_unique_nobad` 5, assembly 14 | dually, the top run bounds every fair loop by a fixed point, which is `slfp` by uniqueness, so every fair recurrent class from every start is `{slfp}` (C1) | `Sh` listed |
| `DistributedCyclesExact.FairFlushAt`, `FairFlushR` | `fairflush_lasso`, `fairflushR_lasso` | 3 and 4 lines | `FairFlushAt` is `C2_reach`, so C2 | `Sh` listed |
| `flip2_fair_livelock` (its `~ FairFlushR` conjunct) | `flip2_fair_lasso` | 13 lines (`bad_lasso_no_fairflush` 3) | the explicit bad fair lasso `fa -0-> fb -1-> fb -0-> fa` refutes C2, with the repair's unique fixed point (`f2_unique`) | none (refutation needs no finiteness) |
| `copyback_ghost` | `copyback_ghost_lasso` | 14 lines | from `(1, 1)` every fair loop is the settled singleton `(1, 1)` (C2 holds); `(1, 1) <> slfp = (0, 0)` gives a bad canonical lasso (C1 fails) | `SS2` is finite already |

The fairness encoding test, `nonfair_cycle_not_refuting`: in the drop network on `{fz, fa, fb}`
(label 0 swaps `fa` and `fb`, label 1 drops every value to `fz`), the cycle `fa -> fb -> fa` under
`0, 0` returns, visits an unquiescent state and never names 1. It is not a fair lasso, and C1 and
C2 hold from every start (`fud_loops`: every fair loop is at `fz`). A merely non-fair cycle does not
refute either side; the fairness clause of `FairLasso` carries the weight.

## Classification by lasso witnesses

`lasso_classification` collects the instances; each row is also its own theorem.

| Instance | Lasso witness | Raw (C2) | Canonical (C1) | Theorem |
|---|---|---|---|---|
| Negation cycle `x0 := not x1, x1 := x0` | bad non-singleton fair lasso, four distinct states; no settled state anywhere | fails | fails for every target | `class_negation_cycle` |
| flip2 fair livelock | bad fair lasso `fa, fb, fb` with one fixed point `fz` | fails | fails | `flip2_fair_lasso` |
| Copyback ghost from `(1, 1)` | settled singleton lasso in the wrong fiber | holds | fails at `slfp` | `copyback_ghost_lasso` |
| Good monotone resolver (`neg_chain_settles`) | no bad fair lasso for `slfp = (1, 0)`, from every start | holds | holds | `class_good_resolver` |
| Several fixed points (copyback from `(0, 1)`) | two reachable singleton classes `{(1, 1)}`, `{(0, 0)}` | holds | fails for every target | `class_multiple_fixed_points` |
| Semantic oscillation (new) | bad raw lasso `a -> b -> a`, no bad canonical lasso | fails | holds | `semantic_oscillation` |

**The semantic-oscillation example.** States `a, b, z`, one label: `a -> b`, `b -> a`, `z -> a`;
`N a = N b = true`, `N z = false`. From `z` the only fair run is `z, a, b, a, b, ...`. The fair lasso
`(a, [0], [0; 0])` has the unsettled loop state `a`, so raw settlement fails (`~ FairSettles
Settled z`). No fair loop visits `z` (nothing maps to `z`), so there is no bad canonical lasso for
`true` and `CanonSettles z true` holds by `C1_closed` (the fiber `{a, b}` is closed). Raw oscillation
with constant meaning: C2 false, C1 true.

## Outcome

**PASS, qualified by a finiteness leak.** One kernel (`recurrence_closed_exact` and its C1 and C2
instances) recovers all five targets; every regime's long-run obstruction was
expressible as a fair lasso (non-singleton bad loops, bad fair livelocks, wrong singletons, several
singleton classes), and the fairness clause is what separates `flip2` from the drop network. The
no-bad-lasso arguments are short (5 to 11 lines each over a 60-line shared toolkit); the longest
bridge, `signed_settlement_lasso`, is long because it reassembles four conjuncts, two of which (the
static `slfp` facts and the E packaging) are not dynamics.

Leaks, reported rather than hidden:

1. **Finiteness.** Every recovery needs a listed state type that the original does not assume:
   `Chaotic.v`, `SignedResolver.v` and `DistributedCycles.v` assume finite height (a bounded rank),
   not finitely many states. The recoveries are of the finite fragments. The rank arguments of the
   originals do not need finiteness; the lasso kernel does (a finite height lattice can have
   infinitely many states, and a fair run on an infinite state space need not repeat a state).
2. **Finite components for `Chaotic.v`.** Its index type is arbitrary; the bridge takes labels in
   `nat` with a finite list `js` and inert updates outside it.
3. **Constructive logic.** The strong `~ BadLasso -> FairSettles` is classical in general
   (`lpo_leak`). Not a leak for the recoveries (their fibers are closed), but C1 for an arbitrary
   fiber is stated in the double-negated or classical-premise form.
4. **No new generic concept** was needed beyond the kernel and the toolkit; no regime-specific
   premise entered the kernel.

Not done: a decision procedure for `BadLasso` on finite instances (reachability plus a fair
strongly connected component, as in the literature below); the instances are classified by explicit
witnesses and short proofs instead.

## Literature

The kernel is the classical fair-cycle characterization and is not claimed as new. On a finite
state graph, a fairness-constrained property fails iff a reachable fair strongly connected
component, equivalently a reachable fair cycle (a lasso), witnesses it: Clarke, Emerson and Sistla,
"Automatic verification of finite-state concurrent systems using temporal logic specifications",
ACM TOPLAS 8(2), 1986 (fairness handled through strongly connected components); Emerson and Lei,
"Efficient model checking in fragments of the propositional mu-calculus", LICS 1986 (the standard
fair-cycle detection procedure); Vardi and Wolper, "An automata-theoretic approach to automatic
program verification", LICS 1986 (verification as automata nonemptiness, decided by finding a
reachable accepting cycle). What the experiment tests is compression: whether this development's
settlement results are short instances of that one characterization.
