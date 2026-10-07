# Reconfiguration inside a run

Detailed results for `Reconfiguration.v` and `ReconfigurationClosure.v`: a run that switches from one configuration to another
while events are in flight, at a quiescent barrier or live, for a single registry and for
federations. The module's one-line summary is in the [module index](../README.md#modules-by-regime);
the status of the question is gap 20 of [REGIME-AUDIT.md](../../REGIME-AUDIT.md#the-open-gaps).

Every other module fixes the topology and the rules for a whole run. Real deployments add services,
migrate schemas and change rules while events are in flight. Here a run starts under a
configuration A, switches once to a configuration B, and finishes under B. The switch may transform
the state (a migration map `m`), and events submitted under A that are still buffered at the switch
are applied under B's rules through a translation `tau`.

## The single-registry model

A and B are two registries of the Governance Rewrite System (`Governance.v`) under free delivery,
the setting of `cc_exact_from`: `A = (applyA, rhoA, rhoA_star, validA)` on states `SA` and events
`EA`, `B` likewise on `SB` and `EB`, with `m : SA -> SB` and `tau : EA -> EB`. Both repairs are
canonical (WFC, `rho_star` reachable by compensation, `rho_star` valid). A configuration of the run
is `InA s Ba Bb` (under A, with A-events `Ba` buffered and B-events `Bb` waiting for the switch) or
`InB c` (under B). The steps (`lstep sw`):

- an A step on `(s, Ba)`: apply a buffered A-event, or compensate;
- the switch, when `sw s Ba` holds: `InA s Ba Bb -> InB (m s, map tau Ba ++ Bb)`; the A-events still
  in `Ba` are in flight and become B-events;
- a B step on `c`.

The **live** switch may happen anywhere (`live_sw`); the **barrier** switch only at an A normal form,
that is with no event in flight and the state repaired (`barrier_sw`). `LiveConv s0` and
`BarConv s0` say that every pair of buffers has a unique normal form from `InA s0 Ba Bb`.

Notation: `gov e x := rho_star (apply e x)`; `f := rhoB_star o m` (migrate, then repair under B);
`CCB x` is CC1 and CC2 of B on the states B reaches from `x` (the condition of `cc_exact_from`);
`CCA s0` the same for A from `s0`.

## The barrier theorem

- `barrier_exact`: `BarConv s0 <-> BarCond s0`, where `BarCond s0` is `CCB (m t)` for every quiescent
  state `t` reachable from `s0` (B converges after the switch), and `AmodF s0`: the A normal forms of
  one buffer agree after `f` (A converges modulo the migration).
- `barrier_exact_faithful`: when `f` is injective on the quiescent states reachable from `s0`
  (`Faithful s0`), `AmodF s0` is A's own condition, so
  `BarConv s0 <-> CCA s0 /\ (CCB (m t) for every quiescent reachable t)`. This is the audit's claim
  (a change at a quiescent barrier reduces to two runs of existing cells), with the qualifier it
  needs: `forgetful_migration` has a migration that is not faithful and hides a divergence of A.
- `barrier_sufficient`: without the qualifier, `CCA s0` and the B part still suffice.

## The live theorem

`live_exact`: `LiveConv s0 <-> LiveCond s0`, where `LiveCond s0` is

- **(B)** `CCB (m s)` for **every** `s` reachable from `s0` under A, quiescent or not (a switch can
  migrate a state between an event and its repair);
- **(S1)** `rhoB_star (m (applyA e s)) = rhoB_star (applyB (tau e) (m s))` for every reachable `s`
  and every A-event `e`: an in-flight event commutes with the switch (apply under A then migrate,
  or migrate then apply its B version);
- **(S2)** `rhoB_star (m (rhoA s)) = rhoB_star (m s)` for every reachable invalid `s`: the switch
  absorbs A's compensation.

(S1) and (S2) are the cross-configuration critical pairs, an A step against the switch, in the
style of C1 and C2 across a morphism. The proof of sufficiency shows that, under the condition, B's
normal form from `(m s, map tau Ba ++ Bb)` is a fold of governed B-steps (`GB`), invariant under
permutation of the buffer (`GB_perm`) and under every A step (`live_step_inv`).

A's own condition is **not** a conjunct. Every live run passes through the switch, so A is only
observed through `f`: `live_implies_barrier` gives it modulo `f`, and `live_exact_faithful` gives
it outright when the migration is faithful, `LiveConv s0 <-> CCA s0 /\ LiveCond s0`, the expected
shape (A's condition, B's condition, the cross pairs). `forgetful_migration` has A diverging and
every live run converging.

`live_no_change`: with `B = A`, `m` and `tau` identities, `LiveConv s0 <-> CCA s0`, which is
`cc_exact_from`.

Witnesses. Each failing conjunct is a divergence from one start, built from runs: `s1_runs`
(apply-then-switch against switch-then-apply from `w ++ [e]`), `s2_runs` (switch an invalid state
against compensate-then-switch), `live_b_runs` and `live_b2_runs` (a CC1 or CC2 failure of B at a
state reachable from a migrated `m s`), `barrier_b_runs`, `amodf_runs`.

## Counterexamples and non-vacuity

In each of the first three, A converges from the start and B from the migrated start (in the first
two, B converges from every state), the barrier switch converges, and the live switch diverges;
each fails exactly one conjunct of `LiveCond`.

- `cap_raise`: a cap of 5 raised to 10, with in-flight adds. An add applied under A from 5 gives 6,
  repaired to 5, and stays 5 after the switch; switched first, the add is applied under B and gives
  6. (S2) fails at 6: `f (rhoA 6) = 5`, `f 6 = 6`.
- `doubling_migration`: `m` doubles the state, the event adds 1 on both sides. (S1) fails at 0: 2
  against 1.
- `migrated_transient`: A's event moves 0 to the invalid state 1, repaired to 0; B also treats 1 as
  invalid, but a B-event moves 1 to 2. (S1), (S2) and `CCB (m 0)` hold; `CCB (m 1)` fails, at a
  state only a live switch can migrate.
- `forgetful_migration`: A is last-writer-wins on a number (it diverges), B has one state.
  Every live run converges, so A's condition is not necessary, and `BarConv` holds without `CCA`.
- `rescaled_cap` (non-vacuity): a cap of 5 becomes a cap of 10 with `m` doubling the state and each
  A add becoming an add of 2, next to native B adds of 1. Online-safe from every start, with every
  conjunct and `Faithful` holding.
- `lww_target`: B is last-writer-wins: unsafe.

## Classification (gsm's planned `CheckMigration`)

`Classified A B m tau s0 o` for `o` in `Online` (`LiveConv`), `BarrierOnly` (`BarConv` and not
`LiveConv`), `Unsafe` (not `BarConv`), over registries packaged as records (`Reg`).

- `classified_unique`: at most one outcome holds.
- `classify`: given decisions of `LiveCond` and `BarCond`, the outcome.
- Finite instances (finite lists of states and events, decidable validity and equality):
  reachability is decidable (`reach_dec`, from a generic closure computation `star_fin_dec`), so
  `LiveConv` is decidable (`live_dec`) and so is `Faithful` (`faithful_dec`); under a faithful
  migration `BarConv` is decidable (`barrier_dec_faithful`) and `classify_finite` returns the
  outcome. `finite_instance` discharges its hypotheses. `instances_classified` classifies the
  instances above (three `BarrierOnly`, two `Online`, one `Unsafe`).
- In the deterministic model (section `Det`, gsm's runtime), the outcome is decided on finite
  instances with no faithfulness hypothesis: `det_classify_complete`, below.

## Federations: topology changes

Under FedMachine semantics (`FederationEvents.v`: every Apply repairs and propagates), what is in
flight at the switch is the buffered events. Section `Det` states the result for any deterministic
steps `stepA`, `stepB`, an equivalence on B-states that `stepB` respects, a migration `M` and a
translation `tau`, under free delivery: a live run applies a permutation `u` of part of the
A-events under A, migrates, then applies a permutation of the translated rest together with the
B-events.

- `det_live_exact`: `DLive s0 <-> PermB (M s0) /\ DS1 s0`, where `PermB x` says every permutation of
  B-events from `x` agrees and `DS1 s0` says `M (stepA e t) ~ stepB (tau e) (M t)` at every reachable
  `t`. B's condition is needed only at the migrated **start**: `DS1` carries it to every reachable
  A-state (`M_run`). Unlike the rewriting model, there is no transient state to migrate.
- `det_barrier_exact`, `det_barrier_faithful`, `det_live_implies_barrier`: the barrier form, with
  B's condition at every migrated reachable state and A's condition modulo `M` (exactly A's own when
  `M` reflects and preserves the equivalences).
- `fed_live_exact`, `fed_barrier_exact` (section `FedSwitch`): A and B are two acyclic federations
  with their own topology (`src`, `f`, `o`), validity, repair and events; `M` is the migration (for
  instance B's normalizer: new edges propagate once, a new registry is initialized). With every
  same-registry pair declared (free delivery), `PermB` is `TraceConv`, so by `fed_exact`
  (`permB_traceconv`):
  - live: `FLive s0 <-> (C1R1_B (M s0) /\ C2R_B (M s0)) /\ FS1 s0`, given `M s0` valid and
    consistent;
  - barrier: `FBar s0 <-> (C1R1_A s0 /\ C2R_A s0) /\ forall u, C1R1_B /\ C2R_B at M (runF_A u s0)`,
    given `M` maps valid consistent states to valid consistent states and reflects and preserves
    `feq`.
- `late_edge`: adding the edge `0 -> 1` to a two-registry federation whose target event adds the
  shared part to the local part. A and B each converge and the barrier change converges from every
  start, but from a start where the target's shared part is stale, an event submitted before the
  edge and applied after it reads the new source value: `FS1` fails and the live change diverges.
  `late_edge_fresh`: from a start whose target already agrees with the new image, the same change is
  online-safe, and every hypothesis of `fed_live_exact` holds there (non-vacuity).

## The barrier without injectivity (`ReconfigurationClosure.v`)

`det_barrier_exact` splits the barrier condition into B's part at every migrated reachable state and
A's part, **A converges modulo M** (`AmodM s0`): for every two permutations `u`, `u'` of one list of
A-events, `M (runA u s0) ~ M (runA u' s0)`. `det_barrier_faithful` replaces it by A's own
convergence when `M` reflects and preserves the equivalences; without that, `AmodM` quantifies over
every pair of permutations. This module gives it a local and a finite exact form, and closes
residue (c) for the deterministic model.

- `amodm_swap_exact`: `AmodM s0` iff for every word `u` (the reachable state `t = runA u s0`), events
  `a`, `b` and continuation `w`, `M (runA w (stepA b (stepA a t))) ~ M (runA w (stepA a (stepA b t)))`.
  Necessity: `u a b w` and `u b a w` are permutations of each other. Sufficiency: two permutations
  are joined by a chain of adjacent transpositions (induction on `Permutation`), and `~` is
  transitive along the chain. The continuation `w` cannot be dropped: `M` need not respect the
  steps, so two states with one image can separate later.
- The **pair closure** `PC s0` is the least relation containing the seeds
  `(stepA b (stepA a t), stepA a (stepA b t))` for every reachable `t` and events `a`, `b`, and closed
  under applying one event to both components (`pc_iff`: its pairs are exactly the pairs of the
  swap form). `amodm_closure_exact`: `AmodM s0` iff `M x ~ M y` on every pair of `PC s0`
  (`ClosureOK`).
- `det_barrier_closure_exact`: `DBar s0 <-> (forall u, PermB (M (runA u s0))) /\ ClosureOK s0`.
  `permB_local_exact` makes B's part local (stepB respects `~`, so there the continuation drops):
  `det_barrier_local_exact` and `det_live_local_exact` state both outcomes as commutation at
  reachable states plus, for the barrier, the closure, which is what gsm's `CheckMigration`
  evaluates; `permA_eq_local_exact` does the same for A's own convergence with equality.
- Finite instances (finite lists of states and events on both sides, decidable state equality,
  decidable `~`): reachability and `PC` are computed by the closure of `star_fin_dec`
  (`run_star_iff`, `pc_star_iff`), so `ClosureOK` is decidable (`closure_dec`). `amodm_witness_exact`:
  `AmodM s0` fails iff the closure has a pair `M` separates; a search that enumerates the closure
  finds a witness iff there is one, and an exhausted search is a certificate.
- **Complete classification.** `DClassified s0 o` for `o` in `Online` (`DLive`), `BarrierOnly`
  (`DBar` and not `DLive`), `Unsafe` (not `DBar`); at most one holds (`det_classified_unique`).
  `det_live_dec`, `det_barrier_dec` and `det_classify_complete` decide the outcome on every finite
  instance, with no faithfulness hypothesis and no unknown case. `det_unsafe_exact`: the barrier
  diverges iff B diverges after a barrier switch at some reachable state or the closure has a pair
  `M` separates.
- **The faithful case recovered.** `det_barrier_faithful_closure`: when `M` reflects and preserves
  the equivalences, `ClosureOK` is A's own convergence, and `det_barrier_closure_faithful` gives
  `det_barrier_faithful` back. `det_closure_of_permA`: when `M` preserves them (always, with
  equality on A), A's convergence implies `ClosureOK`.
- **gsm's pruned search.** `PCg` seeds only for one orientation `sel a b` of each pair of distinct
  events and only where the two states differ, and does not expand a pair of equal states.
  `gsm_closure_exact`: given decidable state equality and `sel` covering every pair
  (`a = b \/ sel a b \/ sel b a`), `ClosureOK` on `PCg` is `ClosureOK` on `PC`: equal pairs stay
  equal under common events, and a pair and its mirror are separated together.

Generic forms (section `Swap`, any deterministic `step`, observation `obs` and equivalence):
`perm_swap_exact`, `closure_perm_exact`, `closure_swap_exact`, `perm_local_exact` (for an
observation compatible with the steps), `closure_witness_exact`.

Instances. A is last-writer-wins on `option bool` (`None` the start, `Some b` the last write); it
diverges (`lww_diverges`). Each migration is not injective on the states A reaches
(`merge_not_injective`, `partial_not_injective`), the case the classification under `Faithful`
left open.

- `merged_online`: `mergeM` sends both writes to one B-state; B sets a flag and every A-event becomes
  the flag event: `Online`.
- `merged_barrier`: `mergeM` again, B ignores the translated events, so an in-flight write is lost
  (`DS1` fails): `BarrierOnly`, certified by the closure (`merged_barrier_closure`), with A
  diverging and `M` not injective.
- `partial_merge`: `partialM` sends `None` and `Some true` to one state and `Some false` to another.
  The seed at the start with events `true`, `false` is a pair it separates
  (`partial_merge_witness`): `Unsafe`.
- `closure_nonvacuous` (the closure condition holds for one migration and fails for the other),
  `gsm_search_instances` (the same for the pruned closure, with `sel_tf` covering every pair), and
  `merged_classified_outcomes` (`det_classify_complete` runs on the three instances, its finite
  hypotheses all hold, and returns `Online`, `BarrierOnly`, `Unsafe`).

### gsm design input

For an exhausted search to certify the barrier, `CheckMigration`'s AmodM search must compute
`PCg` from each start `s0`, with `stepA` the old registry's `Apply` and `M` its migration followed by
normalization under the new registry:

- **Seeds:** for every state `t` reachable from `s0` by `stepA` (the whole reachable set, not a
  sample) and every pair of events `e1 < e2`, the pair `(stepA e2 (stepA e1 t), stepA e1 (stepA e2 t))`
  when its two states differ.
- **Closure:** apply each event of A to both components; skip a pair of equal states.
- **Test:** compare `M` on both components of every pair, seeds included.
- **Outcome:** if no pair is separated and the search was exhaustive, `AmodM` holds
  (`amodm_witness_exact`, `gsm_closure_exact`), and with `PermB-every` the change is safe behind a
  barrier (`det_barrier_closure_exact`). If a pair is separated, the two orders
  `l e1 e2 r` and `l e2 e1 r` (with `l` the path to `t` and `r` the closure path) are the witness
  (`amodm_swap_exact`, necessity). Only a search stopped by a resource limit leaves the outcome
  undecided.

gsm `main` `2d90eea` (`migration.go`, `fromStart`) computes exactly this closure: its seeds are
`runAll(t, [e1, e2])` against `runAll(t, [e2, e1])` at every reachable `t` for `e1 < e2`, kept only
when different; it closes under every event applied to both sides, skipping equal pairs, and
deduplicates. The differences are in the conclusion only: it reports `Unknown` when the exhausted
search finds no witness, where `ClosureOK` holds and the outcome is `SafeBehindBarrier`, and its
`AmodM` condition is reported as not decided in that case.

## Delivery classes across the switch (`ReconfigurationDelivery.v`)

Residue (b), closed in the deterministic model (section `Det`, gsm's runtime). A run is a delivery
sequence `w` of the combined alphabet `X = EA + EB`: `inl a` is an A-event, submitted before the
switch, `inr b` a B-event, submitted after it. It splits as `w = map inl p ++ q`: `p` delivered under
A, the switch, then `q` under B, where an in-flight `inl a` is applied as `stepB (tau a)`, so the
outcome is `runX q (M (runA p s0))` with `runX` the run of `stepX x = stepB (trX x)`. A **delivery
class** is a set `Adm` of admissible sequences of `X`, closed under prefixes, compared by a relation
`Rel` reflexive on it, as in `dist_delivery_exact`: free delivery is every sequence up to
`Permutation`; declared independence is `tequiv IX` for a symmetric `IX` on `X` (a pair of A-events,
of B-events, or an in-flight A-event with a B-event); causal delivery is `causal hbX` up to
`Permutation`; at-least-once delivery is `causal_alo hbX` (every sequence when `hbX` is empty) up to
the same set of events.

- **Live** (`LiveD`: every two splits of related admissible sequences agree; the switch may fall
  anywhere before the first B-event). `live_delivery_exact`: `LiveD s0` iff `ConvXD (M s0)` (B's
  class condition over the combined alphabet, translated in-flight events included) and `S1D s0`
  (`M (stepA a (runA u s0)) ~ stepB (tau a) (M (runA u s0))` at every A-prefix `u ++ [a]` the class
  admits, with duplicates under at-least-once delivery). Necessity: switching at the start gives
  `ConvXD`; the same sequence split before and after its last A-event gives `S1D`. Sufficiency:
  `S1D` carries the migrated state along the A-prefix (`M_runD`), so every split equals a run of the
  combined alphabet from `M s0`.
- **Barrier** (`BarD`: only the splits `Q p q` allows: B-events only after the switch, or for
  at-least-once delivery also redeliveries of A-events delivered before it).
  `barrier_delivery_exact`: given `Glue` (the A parts and the B parts of two related barrier runs
  can be compared separately), `BarD s0` iff `BarBD s0` (B's class condition after the switch at
  every migrated reachable state) and `AmodMD s0` (A converges under the class modulo `M`).
  `live_implies_barrier_d`; `ClassD`, `classD_unique`, `classD_decide`.
- **Free delivery recovered**: `free_live_exact` (the generic live outcome is `det_live_exact`'s
  `DLive`), `free_barrier_exact`, `free_barrier_closure_exact` (`det_barrier_closure_exact`).
- **Declared pairs** (Rel `tequiv IX`, `Adm` closed under prefixes and declared swaps).
  `trace_conv_s_exact` (generic, up to an equivalence): trace convergence iff declared pairs commute
  after every admissible prefix (`CommS`). `live_trace_exact`: every declared pair of the combined
  alphabet commutes after every admissible prefix from `M s0`, and `S1D`; the cross pairs count
  exactly as the class declares them. `barrier_trace_exact` (admissibility of `map inl p ++ map inr
  v` splitting): B's declared pairs from every migrated reachable state, and `AmodT` (declared-trace
  equivalent A-histories migrate to equivalent states), generated by adjacent declared swaps
  (`amodt_swap_exact`). With every sequence admissible (gsm's `Independent`):
  `live_declared_exact` (declared pairs of the combined alphabet commute at every state reached from
  `M s0`, and `DS1`) and `barrier_declared_exact` (B's declared pairs at every state reached from
  every migrated reachable state, and `ClosureI`: the pair closure seeded with A's declared pairs
  only, `closureI_swap_exact`, `closureI_witness_exact`).
- **Causal** (`hbX` irreflexive; for the barrier, no B-event before an A-event):
  `live_causal_exact` (`CCRonS` of the combined alphabet at `M s0`, and S1 at the causal A-prefixes)
  and `barrier_causal_exact` (`CCRonS` of B at every migrated causal state, and `AmodC`, A's causal
  convergence modulo `M`).
- **At-least-once**: `live_alo_exact` (`CCRonS` and idempotence `IdemAtS` of the combined alphabet at
  `M s0`, and S1 at every causally consistent at-least-once A-prefix). `barrier_alo_exact`: B's
  `CCRonS` and `IdemAtS` at every migrated state, `AmodA` (A-runs with the same set of events
  migrate to equivalent states), and `AbsorbS`, the duplicate straddling the switch: an A-event
  delivered before the switch and redelivered after B-events `v` is absorbed,
  `stepB (tau a) (runB v (M (runA p s0))) ~ runB v (M (runA p s0))` for `a` in `p`. Live, the
  straddling duplicate needs no conjunct of its own: S1 at the duplicate prefix and the idempotence of
  `tau a` cover it. Free forms: `live_free_alo_exact`, `barrier_free_alo_exact`.
- **No switch** (B = A, `M` and `tau` identities, only A-events): `no_switch_exact`, and the gap 15
  theorems as corollaries, `causal_no_switch` (`causal_exact`), `declared_no_switch`
  (`tconv_exact`), `alo_no_switch` (`alo_exact`), `dalo_no_switch` (`dalo_exact`).
- **Finite instances**: `classify_declared_complete` (every sequence admissible),
  `classify_causal_complete`, `classify_alo_complete` decide the outcome with no unknown case.
  Causal and at-least-once admissibility depend on the delivered set, so the search runs over pairs
  of a state and a canonical delivered set (sections `Monitor` and `FiniteClass`: `mreach_iff`,
  `mforall_dec`, `ccr_s_dec`, `idem_s_dec`, `causal_pairs_dec`, `alo_pairs_dec`; reachability on a
  closed finite universe, `star_in_dec`).

Instances (each fails one conjunct with the others holding, or is non-vacuity):

- `cross_declared_online`, `cross_declared_barrier`: A sets a flag, B has set (the image) and toggle,
  `M` the identity, `DS1` holds. Declaring nothing, `Online`; declaring only the pair (in-flight
  set, toggle), the live switch diverges and the barrier converges, `BarrierOnly`. The causal forms
  `cross_causal_online` (the in-flight event ordered before the toggle) and `cross_causal_barrier`
  (concurrent with it).
- `count_dup_prefix`: A counts, B's image saturates at 1. Every pair commutes and every event is
  idempotent after the switch, and the exactly-once live switch is online; S1 fails at the prefix
  `[a]` delivered twice, so the at-least-once live switch diverges.
- `reset_straddle`: A and B set a flag, `M` resets it. Exactly once, `BarrierOnly`; at least once,
  `Unsafe` by `AbsorbS` alone.
- `barrier_b_needed`, `barrier_a_needed`: the barrier's B part and A part under causal delivery.
- `rescaled_max`: max-registers, `M` and `tau` doubling, every condition of every class holding.
- `instances_classified`: the three decision procedures run on the finite instances.

### gsm design input

`CheckMigration` refuses a registry with `Independent` pairs. Under declared pairs with every
sequence admissible, the check is `classify_declared_complete`: take `IX` on the combined alphabet
from the two registries' declarations (A's pairs, B's pairs, and a declaration for an in-flight
A-event with a B-event, for instance B's declaration of `tau a` with `b`); `PermB-start` checks only
the declared pairs, translated, at every state B reaches from `M s0` (`live_declared_exact`, with
`DS1` unchanged); `PermB-every` checks only B's declared pairs (`barrier_declared_exact`); and the
AmodM search seeds only A's declared pairs (`ClosureI`; `closureI_witness_exact` makes an exhausted
search a certificate). Causal and at-least-once delivery need the delivered set in the search state
(`classify_causal_complete`, `classify_alo_complete`); under at-least-once delivery the barrier adds
the straddle check `AbsorbS`, and `DS1` is already checked at every reachable state, duplicate
prefixes included.

## Scope and residue

Exact here: the single registry under free delivery (rewriting model, compensation as steps), at a
barrier and live; federations under FedMachine semantics, at a barrier and live; and, in the
deterministic model, the barrier's A part without injectivity, in local and finite form, so the
classification is decided on finite instances with no unknown case. Not covered (the residue of gap
20): (a) a live switch in the distributed model (`DistributedExact.v`), where propagation is itself
in flight, so projections sent under A can be merged under B. Residue (b), declared independence,
causal or at-least-once delivery across the switch, is closed for the deterministic model
(`ReconfigurationDelivery.v`); in the rewriting model these classes, and declared pairs combined
with at-least-once delivery across a switch, are not covered. Residue (c), a local form of the
barrier's A part when the migration is not faithful, is closed for the deterministic model, the
model of gsm's runtime (`ReconfigurationClosure.v`). In the rewriting model with compensation as separate steps,
`barrier_exact` remains exact but its `AmodF` has no local form here: its runs interleave optional
compensation steps, which adjacent swaps of events do not connect.
