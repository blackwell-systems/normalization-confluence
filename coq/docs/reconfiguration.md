# Reconfiguration inside a run

Detailed results for `Reconfiguration.v`: a run that switches from one configuration to another
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

## Scope and residue

Exact here: the single registry under free delivery (rewriting model, compensation as steps), at a
barrier and live; federations under FedMachine semantics, at a barrier and live. Not covered (the
residue of gap 20): (a) a live switch in the distributed model (`DistributedExact.v`), where
propagation is itself in flight, so projections sent under A can be merged under B; (b) declared
independence, causal or at-least-once delivery across the switch; (c) a local form of the barrier's
A part (`AmodF`) when the migration is not faithful (`barrier_exact` is exact there, but `AmodF`
quantifies over all buffers).
