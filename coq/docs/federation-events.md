# Federation: event order

Detailed results for event interleavings across registries: the acyclic model, its exact converse,
and the global condition `GC` with gsm's cyclic normalizer. Each module's one-line summary is in the
[module index](../README.md#modules-by-regime); the status of each question in this regime is in
[REGIME-AUDIT.md](../../REGIME-AUDIT.md#7-acyclic-federation-event-order), section 7 (and section 10
for `GC` on monotone cycles).

## Event interleavings across registries (`FederationEvents.v`)

The federated repair results ([federation-repair.md](federation-repair.md),
[monotone-cycles.md](monotone-cycles.md)) fix the order in which the normalizer visits registries. They do not
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
authority root (`CoordinatedCycles.v`, in [non-monotone-invertible.md](non-monotone-invertible.md)). The distributed model
(explicit propagation steps) on cycles is in `DistributedCycles.v` ([distributed.md](distributed.md)). The
global condition is exact but semantic: on a cycle there is no per-edge reduction of it, so checking
it exactly means enumerating reachable normal forms (or the image of `N`) and testing every
independent pair. The per-edge C1/C2 enumeration gsm runs for acyclic networks is nevertheless
sufficient on a monotone cycle (`FederationEventsCyclesCheck.v`, in [monotone-cycles.md](monotone-cycles.md)). Static C1 and C2 remain over-approximations
(sufficient, and necessary only at reachable witnesses).

## Buffered guards (`FederatedGuards.v`)

`FederationGRS.v` presents the federated rewrite system as a `Governance.step` instance with an
enabledness parameter, but its exact theorems fix it: free delivery (`fed_grs_exact`) and the
federal guard (`fed_guarded_exact`). `FederatedGuards.v` lets events wait: a buffered event fires
only when its guard holds, and a normal form may hold stuck events. It closes audit gap 15 (d).

- Any enabledness: `fed_jcg_exact`, confluence from `c0` iff JC' (`EnabledAfterComp.JCg`), for
  guards on the federated state and the buffer, evaluated at any state, possibly disabled or
  enabled by compensation. This is `jcg_exact` on the federated system; termination is discharged
  (`fed_terminating`), so there is no termination premise.
- Under the federal guard. A guard `g e l` is a decidable predicate on the federated state;
  `benab e l B := In e B /\ gvalid l /\ g e l`. A word is guard-feasible (`feas`) when each
  event's guard holds where it is applied. `GCR s0`: at every state `lrun p s0` with `p`
  guard-feasible, two distinct events whose guards both hold stay enabled after each other and
  commute. `fed_buffered_exact`: from a federally valid `s0`,
  `(forall B, UN Gb (s0, B)) <-> GCR s0`; `fed_buffered_cr`, the same with confluence. Necessity
  runs the feasible word with the pair appended to the buffer (`bg_run_feas`) and compares the
  normal forms of the two branches (`bg_branch`, `bg_branch'`): a stranded event leaves a
  different residual buffer. Sufficiency is JC on the reachable configurations (`bg_form`,
  `bg_jc`) through `jc_unique_normal_forms` and `jc_exact`.
- Per edge: `fed_buffered_edge` (with `gcr_edge_iff`), the commutation clause read through
  `reach_commute_iff`: C1 in both directions for co-enabled events on different registries, C2 for
  co-enabled events of one registry, at the federated states guard-feasible runs reach.
- Recovered: with the trivial guard every word is feasible, `GCR` is commutation at every run
  state (`gcr_true_iff`), and `fed_buffered_recovers` gives `GCR s0 <-> C1R1 /\ C2R`, the condition
  of `fed_guarded_exact`.
- Counterexamples and non-vacuity (registry 0 holds a value, registry 1 copies it).
  `bg_persistence_needed`: `Raise` and `Lift` both set the value to 1, so every pair commutes and
  `C1R1 /\ C2R` holds; `Lift` waits for 0. From `([0; 0], [Raise; Lift])` one run strands `Lift`
  and another ends with an empty buffer: two normal forms, `GCR` fails. `bg_commute_needed`: two
  overwrites with no guard, `GCR` and unique normal forms fail. `bg_wait_exact`: `WRaise` waits for
  0 and `WBump` for 1, so no two distinct events are ever co-enabled: `GCR`, unique normal forms,
  confluence and JC' hold from every valid start, `WBump` waits for `WRaise`, and `C1R1 /\ C2R`
  fails (the two events do not commute): the unguarded condition is neither sufficient nor
  necessary once events wait.
