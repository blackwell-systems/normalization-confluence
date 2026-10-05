# Distributed model with propagation steps

Detailed results for the distributed propagation model: the exact condition on acyclic federations,
and the model on monotone cycles. Each module's one-line summary is in the [module
index](../README.md#modules-by-regime); the status of each question in this regime is in
[REGIME-AUDIT.md](../../REGIME-AUDIT.md#8-distributed-model-with-propagation-steps), section 8.

## The distributed model: the exact condition (`DistributedExact.v`)

`FederationEvents.v` proves the distributed model (local events `DEv e` on a registry's own state,
propagation steps `DProp j` that overwrite `j`'s shared part with the image of its sources'
*current* states) convergent under `XU` plus each registry's own CC, and nothing more. This file
gives the exact condition for an acyclic federation, from a fixed valid start `s0` (55 gated
results, axiom-free). Runs are compared after a final flush `N`, as `dist_interleavings_converge`
does: `DistConv s0` says every two words of events and propagation steps whose event sequences are
federated-trace-equivalent give the same `N (drun w s0)`.

**Reachable stale combinations.** A state `t = drun p s0` reached by a distributed run can hold a
target value `t j` whose shared part is stale: the image of an earlier source state, a value a
local event wrote, or the start's own value. It will be repaired to the image of the flushed
sources, `N t`. The pair `(t j, N t)` is a reachable (target state, image) combination.

- `XUat t e`: `ow (sig e (ow (t j))) = ow (sig e (t j))` with `j = reg e`, `ow = f j (N t)`: the
  XU equation at that combination. `XUR s0`: `XUat t e` at every reachable `t`, every event `e`.
- `LCCat t e1 e2`: `ow (sig e2 (sig e1 (t j))) = ow (sig e1 (sig e2 (t j)))`, each registry's own
  CC up to the repair. `LCCR s0`: at every reachable `t`, every declared same-registry pair.

**The exact condition.**

- **`dist_exact`**: `DistConv s0 <-> XUR s0 /\ C2R (N s0)`, where `C2R` is the FedMachine's C2 at
  states reachable from the flushed start (`FederationEventsConverse.v`).
- **`dist_exact_local`**: `DistConv s0 <-> XUR s0 /\ LCCR s0`, the reachable forms of the two
  hypotheses of `dist_interleavings_converge`.
- `dist_exact_tc`: `DistConv s0 <-> XUR s0 /\ TraceConv (N s0)`: distributed convergence is
  reachable XU plus FedMachine convergence from the flushed start.
- The converse is constructive from a failure witness. `dist_xu_runs` computes the runs "event at
  `t`" (`p ++ [DEv e]`) and "flush, then event" (`p ++ map DProp o ++ [DEv e]`): the same events,
  and their flushes at `reg e` are the two sides of `XUat t e`, so they differ exactly when it fails
  (`dist_xu_diverge`). `lcc_runs` does the same for two same-registry events one swap apart.
- `flush_ev_at`: flushing commutes with an event at `t` iff `XUat t e`; `dist_flush` is
  `propagation_flush` under reachable XU only. `xur_c1r1`: reachable XU already contains the
  FedMachine's C1 at reachable witnesses, so the only extra piece is C2.

**(a) XU is sufficient, recovered.** `dist_interleavings_converge_recovered` (XU + LocalCC),
`xu_exact_condition` (they imply `XUR`, `C2R`, `LCCR` from every valid start), and the weaker
pair **`dist_xu_c2_converge`**: XU + C2 suffice, without LocalCC.

**(b) Strictly weaker than XU: `levels_exact_not_xu`.** gsm's `levels` federation (the test
`TestProjection_StaticWitnessUnreachable`): a source flag `on`, a target `(level, count)` with
`level <= 3`, the morphism writes `level := min on 1`, and `Bump` increments `count` only at
`level = 3`, which no image produces and no event writes. C1 and C2 hold, XU fails at the valid
stale state `(3, 0)`, and from every valid start whose target is not at level 3 (every consistent
start among them) `XUR`, `C2R` and `DistConv` hold. From the stale start `lv_stale` (target at
level 3) two runs with the same events diverge, so the reachability qualifier is needed.

**(c) Distributed convergence implies FedMachine convergence, not conversely.**
`dist_implies_fed`: from a valid consistent start, `DistConv s0` gives `TraceConv s0`, hence
`C1R1 s0 /\ C2R s0` (`fed_exact`); `dist_implies_fed_flush` for any valid start, at `N s0`.
`dist_strictly_stronger_than_fed`: the federation of `fed_grs_c1_c2_insufficient` (both target
events flip the shared flag and add it into the local bit; the only image is `false`) has C1 and
C2, so every FedMachine order converges from every consistent start, but `XUR` fails at the
consistent start `(false, false)`, and the runs `G1; G2` and `G1; propagate; G2` (the same event
sequence) flush to `(false, true)` and `(false, false)`.

**Quantifying the start.**

- `dist_exact_global`: convergence from every valid start iff `XUG /\ C2G`, where `XUG` is XU at
  every valid target state with the image of the *flushed* sources and `C2G` is C2 at every
  consistent state.
- `dist_exact_consistent`: convergence from every valid consistent start iff reachable XU from
  every such start and `C2G`.
- **`dist_global_exact_roots`**: when every target's sources are roots (their repair is the
  identity: any two-registry federation, any star), convergence from every valid start iff
  static `XU /\ C2` (`xug_iff_xu`, `c2g_iff_c2`).

Non-vacuity: `supply_dist_exact` (the `supply_instance` federation satisfies every form from every
valid start), `levels_exact_not_xu` (the exact condition without XU), and the instance of (c).

**What gsm would check.** gsm's projection check (gsm PR #34, `verifyProjectionMerge`) evaluates
the XU equation for every target event, every valid target state, and every image in `Img` (the
images over every valid source state), and Build checks C2.

- *Sound.* For a single-source target that is the Coq `XU` on that target, and Build's C2 is the
  Coq `C2`, so `dist_xu_c2_converge` certifies convergence from every valid start. It does not
  need each component's CC, which `dist_interleavings_converge` used.
- *Exact for every valid start, root sources.* When the target's sources are roots (the common
  single-edge case), `dist_global_exact_roots` says XU + C2 is exactly "every interleaving
  converges from every valid start, stale ones included". There it never over-rejects for that
  question. For a target whose source is itself a target, the exact global condition `XUG` needs
  only images of flushed (consistent) source states, while `Img` also holds images of
  inconsistent source states, so XU can over-reject there.
- *Over-rejection for a deployment that starts consistent* (`Normalize(NewState())`, or any
  FedMachine state). The exact condition is `dist_exact_consistent`: the XU equation only at the
  reachable stale combinations `(t j, N t)` from consistent starts, plus C2 (Build's). XU
  over-rejects exactly when every failing `(b, v)` pair is unreachable: `levels_exact_not_xu` is
  such a case (a shared value no image produces and no local event writes).
- *An exact check, and its cost.* For a target `j` whose sources are roots, `XUat t e` depends only
  on `t` on `src j` and `j` (the roots' flushed states are their own states), and only source
  events, `j`'s events and `DProp j` change them. So the reachable combinations from consistent
  starts are a breadth-first search over `valid(sources) x valid(j)` from the consistent pairs
  `(a, b)` with `b = ow_a(b)`, with moves: a source event, a target event, a propagation
  `b := ow_a(b)`. At each reached `(a, b)` and each event `e` of `j`, check the XU equation with
  image `ow_a`; together with Build's C2 this is exact for "every consistent start" (from
  `dist_exact_consistent`; the enumeration itself is not mechanized). Its pairs are a subset of
  XU's grid `valid(j) x Img`, so it evaluates no equation XU does not; the extra cost is the
  search, `|valid(sources)| x |valid(j)|` states with `|events(sources)| + |events(j)| + 1` moves
  each, against XU's `|events(j)| x |valid(j)| x |Img|` (with `|Img| <= |valid(sources)|`): the
  same order. For a target below another target, stale images of stale sources make the exact
  set depend on the whole ancestor cone (a search over the product of their state spaces);
  treating the source as free (any valid source state at any time) gives a sound relaxation that
  still lies inside XU's grid and still accepts `levels`.

The model's `DProp j` is the resolver merge over all of `j`'s sources; gsm's `SharedProjection`
sends one edge's image, which is why gsm reports multi-source targets as not certified.

## The distributed model on monotone cycles (`DistributedCycles.v`)

`DistributedExact.v` settles the distributed model on acyclic federations. On a cycle the repair
equations have several solutions (`bottom_matters`), and gsm's FedMachine picks the least one
because `normalizeCyclic` resets every shared value to bottom before its Kleene sweeps. Distributed
nodes have no such reset: a propagation step overwrites a target's shared part with the image of
its sources' current states, which may be stale or mid-iteration. This file answers what that
model computes (117 gated results, axiom-free).

**Model.** A state is `(l, h)`: the locals of every node and every shared value, in a finite
lattice. `F l` is the synchronous repair and `u l j` the repair of target `j` alone, with the
hypotheses of `FederationEventsCycles.v`. `Lfp l` is the least fixed point of `F l` (gsm's Kleene
loop from bottom) and `Nc (l, h) = (l, Lfp l)` is `FedMachine.Normalize`; the FedMachine step is
`Nc o ev e`. Actions: a local event `AEv e` (any function of the state, so it may read and write
shared values), a propagation step `AProp j` (`h := u l j h`), and, only in the protocol of Q3, a
reset `AReset` (`h := bot`). A schedule is fair when it names every target infinitely often; a
state is quiescent when no propagation step changes it (equivalently `F l h = h`).

**Q1. Repair without events.** Locals fixed, shared part `h0` at the start.

- `q1_from_bot`: from bottom, every fair schedule settles at `Lfp l` (Chaotic.v, in fair-schedule
  form). **`q1_below`**: the same from any `h0 <= Lfp l`, sound or not (the run is squeezed between
  the run from bottom and `Lfp l`).
- **`q1_sound_settles`**: from a sound start (`h0 <= F l h0`: bottom, or any fixed point), every
  fair schedule settles at the least fixed point above `h0`. **`q1_sound_iff`**: for a sound start
  and a fair schedule, the run reaches `Lfp l` iff `h0 <= Lfp l`.
- `q1_stuck`: if `h0 >= p` for a fixed point `p <> Lfp l`, no schedule ever reaches `Lfp l`.
- **`q1_unique_iff`**: given a top element and the dual step laws (which coordinate updates
  satisfy), every fair schedule from every start settles at `Lfp l` iff `F l` has exactly one fixed
  point. Instance: `dist_unique_fixed_point` (one fixed point with alarm A raised; two with both
  alarms clear).
- Arbitrary stale starts: `dist_schedule_dependence` (on the flag cycle, the start `(true, false)`
  settles at the least fixed point under one fair schedule and at the ghost `(true, true)` under
  another) and **`dist_ring_livelock`** (a monotone 3-cycle `a := b, b := c, c := a`, every
  hypothesis discharged: from `(true, false, false)` the fair schedule `c, a, b, c, a, b, ...`
  moves the set flag around the ring forever and never reaches a quiescent state).

So distributed nodes reach gsm's least fixed point exactly from below it. Above a non-least fixed
point they stay there (a ghost); from an arbitrary stale start the outcome can depend on the
schedule, or never arrive.

**Q2. Events, no resets.** For a start `s0`, over the words of events and propagation steps:

- `XUc t e`: `fst (ev e t) = fst (ev e (Nc t))`, the event's local outcome does not depend on
  whether the node's shared part is stale or at the least fixed point. `XUcR s0`: at every
  reachable `t` (the cyclic reachable XU).
- `DAgreeQ`: every reachable quiescent state is the FedMachine state for the same events.
  `DConvQ`: reachable quiescent states of words with trace-equivalent events are equal.
- `NoGhostR`: every reachable quiescent state holds `Lfp` of its locals. `FlushR`: every
  reachable state can be flushed to quiescence by propagation. `LowR`: every reachable state is
  at or below `Lfp` of its locals.

Results:

- `track`: under `XUcR`, `Nc (crun w s0) = FM (events of w) (Nc s0)` for every reachable word.
  `quiet_ghost_only`: so a quiescent state has the FedMachine's locals and a shared part that is a
  fixed point at or above the FedMachine's. Ghosts are the only way to disagree.
- **`quiet_agree_iff`**: `FlushR -> (DAgreeQ <-> XUcR /\ NoGhostR)`.
- **`quiet_conv_iff`**: `FlushR -> NoGhostR -> (DConvQ <-> XUcR /\ FMConv (Nc s0))`.
- **`low_agree_iff`, `low_conv_iff`**: `LowR` gives `FlushR` and `NoGhostR`, so under `LowR`,
  `DAgreeQ <-> XUcR` and `DConvQ <-> XUcR /\ FMConv (Nc s0)`.
- `evlow_lowr`: `LowR` follows from `EvLow` (events keep a state below the least fixed point of
  its locals), and `infl_evlow`: inflationary events satisfy it (they raise locals in an order the
  repair is monotone in and never raise shared values). `uniq_noghost`, `uniq_agree`: when `F l`
  has one fixed point for every `l`, there is no ghost and `XUcR` alone gives `DAgreeQ`.
- `lens_quiet`: gsm's per-target `C1cyc + C2cyc` (`FederationEventsCyclesCheck.v`), over a set
  `Hs` covering every reachable shared value, plus `LowR`, give `DConvQ` and `DAgreeQ`.

The counterexample, **`dist_cyc_ghost`**: the flag cycle of `cyc_instance` with raise and clear
events. `C1cyc` and `C2cyc` hold, `XUcR` holds from every start (the events' local outcomes ignore
shared values), and the FedMachine converges from every normal form: the cyclic analog of the
acyclic exact condition and gsm's per-target checks all pass. Yet `RaiseA; propagate B; propagate
A; ClearA` is quiescent at `((false, false), (true, true))`: the alarm is clear and the two shared
flags keep each other set. The FedMachine, and the same two events flushed later, give `((false,
false), (false, false))`, and no propagation schedule leaves the ghost. `DAgreeQ`, `DConvQ`,
`NoGhostR` and `LowR` fail. Positive instances: `dist_cyc_raise_only` (raise-only events on the
same cycle: `LowR`, `DConvQ`, `DAgreeQ` hold) and `dist_cyc_unique_no_reset` (a registry cycle
without shared-value feedback, `sa := lb`, `sb := la || sa`, with the same raise and clear events).

The gap left in Q2: without `LowR`, the exact statements keep the reachable hypotheses `FlushR`
(and `NoGhostR` for `DConvQ`). `FlushR` can fail on a general lattice, and the only per-event check
offered for `NoGhostR` is `EvLow` (or a unique fixed point).

**Q3. Reset epochs.** An epoch is `AReset` followed by `K` sweeps of every target (`EP_run`:
it computes `Nc t`; `epoch_flush`: any reset followed by propagation to quiescence ends at `Nc t`,
and by `q1_from_bot` every fair schedule after the reset gets there). Compare after a final epoch:
`DistAgreeE`: `Nc (crun w s0) = FM (events of w) (Nc s0)`; `DistConvE`: trace-equivalent events give
the same `Nc (crun w s0)`. Words may contain resets anywhere.

- **`epoch_agree_iff`**: `DistAgreeE s0 <-> XUcR s0`.
- **`epoch_conv_iff`**: `DistConvE s0 <-> XUcR s0 /\ FMConv (Nc s0)`, the cyclic form of
  `dist_exact_tc`. The converse is constructive: "event at `t`" against "epoch, then event"
  (`xu_runs`) have the same events and differ exactly when `XUc t e` fails.
- **`lens_epoch`**: `C1cyc + C2cyc` over `Hs` covering the reachable shared values give
  `DistConvE` and `DistAgreeE` (`lens_xucr`, `lens_fmconv`). `hs_reach`: it suffices that `Hs`
  contains the start's values, bottom, what propagation writes (the morphism images), and what
  events write.
- `dist_cyc_epoch_fix`: on the ghost federation every run agrees with the FedMachine after a final
  epoch, from every start, and the ghost run followed by an epoch is cleared. A staggered reset is
  not enough: if A resets its flag while B still holds the ghost, one propagation step of A
  restores it. The reset must be a barrier (no propagation reads a pre-reset value after the
  first node resets).

**Consequence for gsm.** gsm's projection API (`SharedProjection` + `MergeProjection`) reports
cyclic networks "not certified" (gsm PR #34). `dist_cyc_ghost` shows that is required, not
conservative: on a monotone cycle that passes every check gsm runs (C1 and C2 read on the cycle,
monotonicity, FedMachine convergence), projection nodes can settle at a ghost the FedMachine never
produces. Two ways to certify a cyclic projection deployment:

- *With reset epochs* (`lens_epoch`, exact form `epoch_conv_iff`). The deployment runs epochs:
  a barrier at which every node resets its shared part to bottom, then propagation until
  quiescence (at most `K` sweeps of every target; gsm's `kleeneCap`), with no event applied inside
  the epoch (events between epochs are unrestricted). After the epoch every node holds the
  FedMachine state for the events applied so far, whatever their interleaving. The
  check is gsm's cyclic C1 and C2 with the image set widened to `Hs`: the morphism images (what gsm
  enumerates now), the bottom value of each shared slot, and the shared values events write (or,
  most simply, every valid shared value, which makes C1 say "an event's local outcome ignores its
  shared part", the cyclic XU). Cost: the same enumeration as today's cyclic C1/C2 (events x valid
  component states x `Hs`), with `Hs` larger by one bottom value per slot plus the event-written
  values; at run time one barrier per epoch and at most `K` propagation sweeps. Between epochs
  nodes may hold ghosts; only post-epoch states are certified.
- *Without resets* (`lens_quiet`). Certify only when no ghost can arise: every event is
  inflationary (`infl_evlow`: locals only rise, in an order the morphisms are monotone in, and no
  event raises a shared value), or the repair has one fixed point for every locals assignment
  (`uniq_agree`). The first is a per-event check over valid component states (events x valid
  states, plus a monotonicity check of the morphisms in their source locals, alongside the
  existing check in shared values); the second is a global check over locals x shared lattice. A
  network with a clear event on a feedback loop (the `alarms` shape) fails both, and needs epochs.
