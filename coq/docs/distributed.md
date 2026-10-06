# Distributed model with propagation steps

Detailed results for the distributed propagation model: the exact condition on acyclic federations,
the model on monotone cycles, that model without resets made exact, convergence alone in it, and
propagation over channels that deliver projections late, reordered or duplicated. Each module's one-line summary is in the [module
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
offered for `NoGhostR` is `EvLow` (or a unique fixed point). `DistributedCyclesExact.v` (#64)
closes this gap: see [the no-reset model, exactly](#the-no-reset-model-on-monotone-cycles-exactly-distributedcyclesexactv).

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

## The no-reset model on monotone cycles, exactly (`DistributedCyclesExact.v`)

`DistributedCycles.v` proves the no-reset model exact only relative to reachable hypotheses:
`quiet_agree_iff` and `quiet_conv_iff` assume `FlushR` (and `NoGhostR`), and `low_agree_iff` and
`low_conv_iff` assume `LowR`. This file moves those hypotheses to the right-hand side, proves
each conjunct necessary, and characterizes `FlushR` and `NoGhostR` (129 gated results,
axiom-free). New notions: `FlushAt t` (some propagation word from `t` reaches quiescence),
`FairFlushAt t` (every fair schedule from `t` does), `FairFlushR` (at every reachable state; the
operational reading: nodes propagate asynchronously and fairly), `SoundR` (every reachable state
satisfies `h <= F l h`), `Sand l h` (`s <= h <= ` every fixed point above `s`, for a sound `s`),
`GhostFree t` (every quiescent state propagation reaches from `t` holds `Lfp`), `UniqueFP l`.

**1. Unconditional iffs.**

- **`flush_agree_iff`**: `FlushR /\ DAgreeQ <-> XUcR /\ FlushR /\ NoGhostR`.
- **`fair_agree_iff`**: `FairFlushR /\ DAgreeQ <-> XUcR /\ FairFlushR /\ NoGhostR`.
- **`flush_fed_iff`**: `FlushR /\ DAgreeQ /\ DConvQ <-> XUcR /\ FMConv (Nc s0) /\ FlushR /\
  NoGhostR`; **`fair_fed_iff`** with `FairFlushR`.

Each right-hand conjunct is necessary: an instance where it alone fails.

| Conjunct | Instance | What holds, what fails |
|---|---|---|
| `XUcR` | `copy_xu_fails` | registry cycle with one fixed point, event `la := sa` from a low stale start: `FairFlushR`, `NoGhostR`, `FMConv` hold; the event reads A's unpropagated flag and the quiescent state differs from the FedMachine |
| `FMConv` | `fm_conv_fails` | the same cycle, `SetA` and `ClrA` declared independent: `FairFlushR`, `XUcR`, `NoGhostR` hold, the FedMachine does not converge |
| `FlushR` | `flip_noflush` | shared values `{fz < fa, fb}`, repair swaps `fa` and `fb`: one fixed point, no ghost, `XUcR` and `FMConv` hold; from `fa` no propagation word ever reaches quiescence |
| `FairFlushR` | `flip2_fair_livelock`, `ring_exact` | flip2 adds a target dropping `fa` to `fz`: every state has a flushing word, one fixed point, no ghost, but the fair schedule `0, 1, 0, 0, 1, 0, ...` never quiesces. The 3-ring of `dist_ring_livelock` also has `FlushR` without `FairFlushR` (and a reachable ghost) |
| `NoGhostR` | `ghost_exact` | `dist_cyc_ghost`: `FairFlushR`, `FlushR`, `XUcR`, `FMConv` hold, agreement fails |

`conv_ghost_normal`: `NoGhostR` is not necessary for `DConvQ` alone. On a cycle where A's flag also
keeps itself (`sa := lb || sa || sb`), from the FedMachine normal form, every quiescent
interleaving of the same events agrees, yet each one after an event is a ghost. Convergence among
interleavings is weaker than agreement with the FedMachine; the exact condition for convergence
alone is `conv_quiet_exact` ([below](#convergence-alone-on-monotone-cycles-distributedconvergenceexactv);
[REGIME-AUDIT.md](../../REGIME-AUDIT.md) gap 14, closed).

**2. `FlushR` exactly.**

- **`fair_flush_sound_iff`**: under a fair schedule, the run reaches a quiescent state iff it
  reaches a sound state (from a sound state every step is inflationary, and a quiescent state is a
  fixed point). **`flushat_sound_iff`**: some word reaches quiescence iff some word reaches a sound
  state. Reachable forms: `fairflushR_sound_iff`, `flushR_sound_iff`. `fairflushR_flushR`,
  `fairflush_flushat` (via the round-robin schedule `rrs`, `rrs_fair`).
- **`sand_settles`**: if `s` is sound and `s <= h <=` every fixed point above `s`, every fair
  schedule from `h` settles at the least fixed point above `s`. It contains `q1_below` (`s = bot`;
  `sand_recovers` rederives it) and `q1_sound_settles` (`h = s`).
- Sufficient: `sandr_fairflush`, `soundr_fairflush`, `lowr_fairflush`. Per event: `evsand_sandr`,
  `evsound_soundr` (events keep states sandwiched, or sound); `infl_evsound` (inflationary events
  that do not write shared values keep soundness); `evlow_fairflush` (`EvLow`, which
  `infl_evlow`'s events satisfy, keeps `LowR`); `nc_sound_low` (gsm starts `Nc t` are sound and
  low). Per network: `step_sound_fairflush` (every single propagation step yields a sound state;
  the 2-flag cycle satisfies it, `cu_step_sound`, the 3-ring does not).
- Necessity status: none of `SoundR`, `SandR`, `LowR` is necessary. In `ghost_exact` the reachable
  state after `PingA; ClearA` is neither sound nor sandwiched, and `FairFlushR` holds.

**3. `NoGhostR` exactly.**

- **`noghost_event_iff`**: `NoGhostR <->` the start and every post-event state (an event applied
  at a reachable state) are `GhostFree`. **`ghost_witness`**: every reachable quiescent ghost is
  reached by propagation from the start or from the output of a last event, and that state is not
  below the least fixed point of its locals: an event moved shared values above it and the cycle
  sustained them.
- `ghostfree_low`: a low state is ghost-free. **`ghostfree_sound_iff`**: a sound state is
  ghost-free iff it is low. So **`noghost_soundr_iff`**: `SoundR -> (NoGhostR <-> LowR)`, and
  **`lowr_post_iff`**: `LowR <->` the start is low and every event, applied at a reachable state,
  leaves the shared values below the least fixed point of the new locals. Under `SoundR`:
  **`soundr_agree_iff`** `DAgreeQ <-> XUcR /\ LowR`, **`soundr_fed_iff`** `DAgreeQ /\ DConvQ <->
  XUcR /\ LowR /\ FMConv (Nc s0)` (no flush hypothesis: `SoundR` gives `FairFlushR`).
- Without soundness the post-event condition stays `GhostFree`, which can depend on the schedule
  (`dist_schedule_dependence`), and lowness is not necessary for it: `ghostfree_unsound` is an
  unsound start above the least fixed point with no ghost (one fixed point), so `LowR` is not
  necessary without `SoundR`.
- **`noghost_inv_iff`** (certificate form): `NoGhostR <->` some invariant `P` (holding at the
  start, closed under events, propagation steps and resets) contains no quiescent ghost.
  **`unique_or_low_noghost`**: it suffices that every `P`-state has locals with one fixed point or
  is low; `unique_or_low_recovers` gives `uniq_noghost` (`P` = everything) and the `EvLow` route
  (`P` = low states) as the two extremes.
- `latched_exact`: beyond both. On the flag cycle with B's alarm latched (no event clears it),
  clearing A's alarm is safe: every reachable locals assignment has one fixed point. `EvLow` fails
  and `F l` does not have one fixed point for every `l`, yet `NoGhostR`, `FairFlushR`, `DAgreeQ`
  and `DConvQ` hold (through `lens_noreset_fair_iff`).
- `local_reset_ghost`: a clear that also resets its own shared slot to bottom still leaves a
  ghost (`RaiseA; propagate B; propagate A; ClearA-and-reset-sa; propagate A` is quiescent at
  `((false, false), (true, true))`): B's flag holds A's back up. A reset on a cycle has to cover
  the cycle, which is the barrier of `lens_epoch`.

**4. What gsm would check without resets.** **`lens_noreset_iff`**, **`lens_noreset_fair_iff`**:
given gsm's per-target `C1cyc` and `C2cyc` over a set `Hs` covering the reachable shared values,
a cyclic projection deployment without resets is certified (`FlushR /\ DAgreeQ /\ DConvQ`, or
the fair form) exactly when it flushes and has no reachable ghost. C1 and C2 discharge `XUcR` and
`FMConv`; the two remaining conditions are reachability properties of the global state space,
and gsm has these ways to discharge them:

- *Inflationary events* (`infl_evlow` with `evlow_fairflush` and `unique_or_low_recovers`): a
  per-event check over valid component states (each event raises its local and does not raise a
  shared value) plus monotonicity of the morphisms in their source locals. Cost: events x valid
  component states, and morphisms x pairs of source local states; no global enumeration. It gives
  `LowR`, hence `FairFlushR` and `NoGhostR`. A clear on a feedback loop fails it.
- *An invariant with pinned fixed points* (`unique_or_low_noghost`, as in `latched_exact`): find
  a set of global states closed under events and propagation in which every state's locals have
  one fixed point (compare the least fixed point from bottom with the greatest from top: two Kleene
  runs of at most `K` sweeps per locals assignment) or the state is low; flushing from
  `step_sound_fairflush` (a check over locals x shared values x targets) or from `SoundR`. Cost:
  global, the product of the registries' state spaces, like any reachability check.
- *A unique fixed point everywhere* (`uniq_noghost`): a global check over locals x shared values,
  plus a flush argument (with a top element and the dual step laws, `q1_unique_iff` gives
  `FairFlushR`; without them `flip_noflush` shows uniqueness alone does not flush).

The reset-epoch route (`lens_epoch`, exact form `epoch_conv_iff`) needs only the C1/C2
enumeration (events x valid component states x `Hs`, with `Hs` widened by each slot's bottom value
and the event-written values) and pays at run time: one barrier and at most `K` sweeps per epoch,
certifying post-epoch states only. Without resets the deployment is certified at every quiescent
point and needs no barrier, but unless events are inflationary the extra check is a global
reachability argument. For gsm's `alarms` shape (a clear on a feedback loop, nothing pinning the
loop) no-reset certification is impossible (`ghost_exact`), and epochs are required.

## Convergence alone on monotone cycles (`DistributedConvergenceExact.v`)

`flush_fed_iff` is exact for convergence *together with* agreement with the FedMachine, whose
canonical state is the least fixed point `Lfp`. Convergence among quiescent interleavings alone,
`FlushR /\ DConvQ` (no resets), had only the sufficient condition `quiet_conv_suff` (`XUcR`,
`FMConv`, `NoGhostR`), and `conv_ghost_normal` showed `NoGhostR` is not necessary. This file gives
the exact condition (55 gated results, axiom-free). The idea: replace the FedMachine's canonical
state (reset, then Kleene) by the canonical state the propagation dynamics produces itself, the
quiescent state a reachable state flushes to, which may be a ghost. The canonical-execution
decomposition then goes through with that canonicalizer, read as a relation (no choice function, so
nothing leaves the axiom-free gate).

New notions (all without resets):

- `Flushes t q`: some propagation word takes `t` to the quiescent state `q`.
- `FlushDetR` (E, canonical fidelity with the dynamics' own canonicalizer): every reachable state
  flushes to at most one quiescent state. A ghost is allowed; it must be determined.
- `FlushXUR` (S, state descent for the flush): for every reachable `t`, event `e` and flush `q` of
  `t`, `ev e t` and `ev e q` flush to a common state.
- `QM s es q`, the quiescent machine: flush `s`, then for each event apply it and flush again,
  ending at `q`. It is the FedMachine with `Normalize` (reset, then Kleene) replaced by propagation
  to quiescence, which keeps ghosts.
- `QMConv s0` (H, history descent for the flush): trace-equivalent event sequences have the same
  quiescent-machine outcomes.

**1. The exact condition.** No lattice hypothesis is used: the proof needs only the action
structure of the model.

- **`conv_quiet_exact`**: `FlushR /\ DConvQ <-> FlushR /\ FlushDetR /\ FlushXUR /\ QMConv`.
  The forward direction holds with resets too (`conv_flushdet`, `conv_flushxu`, `conv_qmconv`); the
  backward direction (`conv_quiet_suff`, through `qm_track`: under the three layers every flush of a
  reachable state is the quiescent machine's outcome for the same events) is for the no-reset
  model: a reset moves a state's flush to `Lfp` without an event, which the epoch theorems handle.
- **`fair_conv_exact`**: the same with `FairFlushR`.
- **`flushdet_event_iff`**: `FlushDetR <->` the start and every post-event state flush to at most
  one quiescent state (the analog of `noghost_event_iff`).

Each right-hand conjunct is necessary: an instance where it alone fails.

| Conjunct | Instance | What holds, what fails |
|---|---|---|
| `FlushR` | `flip_conv_noflush` | flip1 from `fa`: no reachable state quiesces, so `FlushDetR`, `FlushXUR` and `QMConv` hold vacuously; `FlushR` fails |
| `FlushDetR` | `fork_conv_nodet` | the flag cycle with both alarms clear, from the stale start `(sa, sb) = (true, false)`, identity events: propagating A first reaches `Lfp`, propagating B first reaches the ghost `(true, true)`; `FlushR`, `FlushXUR`, `QMConv` hold |
| `FlushXUR` | `copy_conv_noxu` | `copy_xu_fails` (one fixed point): `FlushR`, `FlushDetR`, `QMConv` hold; `CopyA` reads A's stale flag |
| `QMConv` | `fm_conv_noqm` | `fm_conv_fails` (one fixed point): `FlushR`, `FlushDetR`, `FlushXUR` hold; `SetA` and `ClrA` are declared independent and do not commute |

**2. The ghost-free case recovers the earlier results.** Under `FlushR /\ NoGhostR` every flush is
the FedMachine normal form (`noghost_flushes`), so `FlushDetR` holds (`noghost_flushdet`), `FlushXUR`
is `XUcR` (`noghost_flushxu_iff`) and `QMConv` is `FMConv (Nc s0)` (`noghost_qmconv_iff`; by
`noghost_qm` the quiescent machine is the FedMachine).

- **`quiet_conv_recovered`**: `FlushR -> NoGhostR -> (DConvQ <-> XUcR /\ FMConv (Nc s0))`, which is
  `quiet_conv_iff` at `r = false`.
- **`agree_conv_noghost`**: `FlushR -> (DAgreeQ /\ DConvQ <-> DConvQ /\ NoGhostR)`. Agreement with
  the FedMachine is convergence plus canonical fidelity to `Lfp`.
- **`flush_fed_recovered`**: `flush_fed_iff` at `r = false`, rederived through `conv_quiet_exact`.
- `quiet_conv_suff` stays the sufficient condition that needs no `FlushR`.

**3. When the ghost is determined for free.** With the lattice hypotheses of `DistributedCycles.v`:
**`sand_flushdet`**: a sandwiched state (`s <= h <=` every fixed point above `s`, `s` sound) flushes
only to the least fixed point above `s`. So `SandR` or `SoundR` gives `FlushDetR`
(`sandr_flushdet`, `soundr_flushdet`), and **`soundr_conv_iff`**: `SoundR -> (DConvQ <-> FlushXUR /\
QMConv)`; `FlushR` and `FlushDetR` come free. Only unsound reachable states can fork
(`fork_conv_nodet`, the start of `dist_schedule_dependence`).

**4. Instances.**

- **`conv_ghost_instance`**: `conv_ghost_normal` is an instance. All four conjuncts hold, `NoGhostR`
  and `DAgreeQ` fail, and the quiescent machine sends `SetSA` to the ghost
  `((false, false), (true, true))` while the FedMachine sends it to `((false, false), (false,
  false))`: the interleavings agree, on the quiescent machine's state rather than the FedMachine's.
- **`ghost_conv_not_fed`**: none of the three conditions of `quiet_conv_suff` is necessary. On the
  same network, from the ghost start `((false, false), (true, true))` (a fixed point above `Lfp`),
  with `XCopyA` (A's alarm := A's flag) and `XRaiseB` (B's alarm := true), declared independent as
  events of different registries: A's flag stays set, so `XCopyA` always raises A's alarm and the
  quiescent state depends only on which events occurred. `FairFlushR` and `DConvQ` hold, so all four
  conjuncts hold; `XUcR`, `FMConv (Nc s0)`, `NoGhostR` and `DAgreeQ` all fail (the FedMachine resets
  A's flag, so `XCopyA` before `XRaiseB` leaves A's alarm down there, and after it raises it).
- **`raise_only_conv`**: non-vacuity without a ghost, and of `SoundR`: raise-only events from a
  FedMachine normal form.

Reading. The ghost is not the obstacle to convergence; it is the obstacle to agreement with the
FedMachine. Convergence alone asks the same three layers as `flush_fed_iff`, each relative to the
state propagation settles in instead of `Lfp`. All conditions are reachable properties (as in
`flush_fed_iff`); `SoundR` removes the fidelity layer. No per-target check for `FlushXUR` or
`QMConv` is given: gsm's `C1cyc` and `C2cyc` are stated against `Lfp`, so they discharge the
ghost-free forms (`XUcR`, `FMConv`) only.

## Propagation over channels (`ProjectionChannels.v`)

The modules above have a propagation step that reads the sources' *current* states. gsm's nodes
send projections (`SharedProjection`) over a transport and merge what arrives: `MergeProjection`
applies every projection, `MergeProjectionAfter` refuses one whose `Version` is not newer than the
last one applied from that edge. This file models the transport (audit gap 21, a new axis; 90 gated
results, axiom-free).

**Model.** A configuration holds every registry's state `cs`, the projections in flight to each
target `cb j` (a version and a snapshot of the state when it was sent), the last applied version
`cl j` and the last sent version `cv j`. Actions: `CEv e` (a local event), `CSend j v` (send `j`
the projection of the current state with version `v`), `CDel j i` (deliver the `i`-th projection
in flight to `j` and remove it: any `i`, so any order and any delay), `CDup j i` (deliver it and
keep it, so it can arrive again later). A delivery merges `t j := f j z (t j)` with the snapshot
`z`. `vm = false` is `MergeProjection`; `vm = true` is `MergeProjectionAfter`. `disc` is gsm's
version contract: each send to `j` has a version above every earlier one. The channel is per
target: for a single-source target it is gsm's per-edge channel; a multi-source target's channel
carries all its sources at one snapshot, which gsm's per-edge projections do not provide (gsm
reports those targets as not certified). `fround c` is the final round: in topological order each
target is sent the projection of the current state with the next version, and that projection is
delivered. A drain is any word of deliveries.

- `ChanConv vm s0`: disciplined channel runs whose event sequences are federated-trace-equivalent
  agree after a final flush `N` (as `DistConv` does).
- `CXUR vm s0`: `XUat` at every state a disciplined channel run reaches.
- `SettleConv s0`: versioned runs, each completed by its final round and any drain, agree **with no
  outside flush**.

**After a flush, either mode.**

- `emb_run`: the current-value model is the channel model with every send delivered at once, in
  either mode, with no hypothesis on the federation (so also on cycles).
- **`chan_exact`**: `ChanConv vm s0 <-> CXUR vm s0 /\ C2R (N s0)`. `CXUR` contains `XUR` (by
  `emb_run`), so a channel deployment needs XU at its own reachable states.
- `chan_exact_global`: every valid start iff `XUG /\ C2G`, the current-value condition;
  `chan_global_exact_roots`: when every target's sources are roots, iff static `XU /\ C2` (gsm's
  check); `chan_xu_c2`: `XU` and `C2` suffice. `chan_flush`: under `CXUR`, every channel run flushes
  to the FedMachine run of its events.

**Versioned merge: the channels deliver the flush.**

- **`vsettle`**: after the final round every projection still in flight is refused, so every drain
  ends at `frun o (cs c)`, the current-value flush of the state reached; `vsettle_settled`: that
  state is a fixed point of every repair.
- **`vsettle_exact`** and **`vsettle_exact_cond`**: `SettleConv s0 <-> ChanConv true s0 <-> CXUR true
  s0 /\ C2R (N s0)`.
- `vsettle_cv`: the drained state is the state of the current-value run "the same events, then a
  flush". `vsettle_xu_c2`: gsm's `XU` (`FedReport.ProjectionSafe`) and `C2` give `SettleConv`.
- Two-level networks (`TwoLevel rt`: every registry is a pure root, whose repair is the identity,
  or a sink nobody reads; any two-registry federation, any star). **`vchan_emulate`**: every state a
  versioned channel run reaches is, at any target and at every root, the state of a current-value
  run. The emulating word keeps the root events in order, appends the target's events since its
  last merge, and places each applied projection where its snapshot was taken; the version check
  is what makes those places move forward. **`vchan_twolevel_exact`**: `ChanConv true s0`,
  `SettleConv s0` and `DistConv s0` are each equivalent to `XUR s0 /\ C2R (N s0)`, `dist_exact`'s
  condition.

**Plain merge: the channels cannot deliver the flush.**

- **`plain_settle_iff`**: after the final round, every drain settles iff every projection still in
  flight to `j` carries the image of the flushed state at `j`.
- **`plain_stale_counterexample`**: the supply federation (Common, XU, LocalCC). The source is
  projected, then recalls; the final round sends and delivers the fresh projection; a stale copy of
  the first projection arrives after it. The drained state lists a recalled product (not a fixed
  point), and the same events with the old projection delivered first end elsewhere. `ChanConv
  false` holds there (the failure is the stale overwrite, not XU), and the versioned merge refuses
  the stale copy (`SettleConv` holds). `plain_stale_in_flight` names the stale image in flight.

**Hypotheses.**

- `version_order_counterexample`: versions out of send order (a newer version on an older
  snapshot: a retry restamped with a new version, or a version read off a value the source
  revisits) let the versioned merge apply a stale projection last. A source that revisits a value
  is harmless when versions follow the send order: the newer projection carries the current value.
- `no_final_send_counterexample`: drained channels with no send after the last source change leave
  the target stale, in either mode.
- `late_delivery_instance`: non-vacuity, a projection snapshot before a sale and a recall, delivered
  after both; the final round settles at the current-value run's state.

**Cycles.** **`vchan_cyc_ghost`**: on the flag cycle of `dist_cyc_ghost`, a disciplined versioned
run with in-order fresh deliveries and a final round is drained and settled at the ghost
`((false, true), (false, true))`, while the same events, with no propagation between them, settle
at the least fixed point. By `emb_run` every cyclic current-value run is a versioned channel run, so
the cyclic counterexamples transfer; flush and reset epochs over channels have no theorem (an
in-flight projection from before a reset is a hazard the current-value epoch theorems do not see).

Not covered (the residue of gap 21): whether versioned channels reach new stale combinations beyond
two-level networks (chains, multi-source targets), that is whether `CXUR true` equals `XUR` there;
channels on cycles. Loss without redelivery is outside the model (the eventual-delivery limit).

## Causal and at-least-once event delivery (`DistributedDelivery.v`)

`DistributedExact.v` compares words whose event sequences are federated-trace-equivalent. Under
causal or at-least-once delivery only a sufficient condition followed, by restricting `dist_exact`.
`DistributedDelivery.v` states the exact condition for any delivery class and closes audit gap
15 (c).

- A delivery class is a set `Adm` of admissible event sequences closed under prefixes, with a
  comparison `Rel` reflexive on them. `XURD Adm s0`: XU (`XUat`) at every state `drun p s0` with
  `evs p ++ [e]` admissible. `DistConvD Adm Rel s0`: admissible words with related event sequences
  agree after the final flush. `FedConvD Adm Rel s`: the FedMachine runs of related admissible
  sequences agree (pointwise).
- `dist_delivery_exact`: `Inv s0 -> (DistConvD s0 <-> XURD s0 /\ FedConvD (N s0))`. The first
  conjunct is the propagation layer (an event at a stale state against the event at its flush:
  `dist_xu_runs` gives two words with the same events), the second the event-order layer on the
  FedMachine; `dist_flush_d` is `dist_flush` for the class. `dist_exact_tc_recovered`: every
  sequence, compared by federated trace equivalence, gives `dist_exact_tc`.
- The FedMachine compares states pointwise, so its conditions are stated up to an equivalence:
  `causal_conv_s_exact` (`CConvS <-> CCRonS`) and `causal_alo_s_exact`
  (`CALOConvS <-> CCRonS /\ forall a, IdemAtS a`) for a step respecting any equivalence; at `eq`
  they give `GovernanceConverse.causal_exact` and `AtLeastOnceExact.causal_alo_exact_idem` back
  (`causal_exact_recovered`, `causal_alo_exact_recovered`).
- Instances. Causal (`Adm = causal hb`, `Rel = Permutation`): `dist_causal_exact`,
  `DistCausal s0 <-> XURC s0 /\ CCRF (N s0)` (concurrent pairs commute on the FedMachine after
  every causal prefix). Free at-least-once (every sequence, compared by its set of events):
  `dist_alo_exact`, `DistALO s0 <-> XUR s0 /\ CommRF (N s0) /\ forall a, IdemRF (N s0) a`, with
  `XUR` exactly `dist_exact`'s propagation condition. Causal at-least-once (`causal_alo hb`):
  `dist_causal_alo_exact`, `DistCALO s0 <-> XURCA s0 /\ CCRF (N s0) /\ forall a, IdemF (N s0) a`.
- gsm: `xu_xurd`, static XU (what `FedReport.ProjectionSafe` checks) gives `XURD` for every class
  from every valid start, and `xur_xurd` the same from reachable XU; the delivery class changes
  only the FedMachine conjunct.
- Counterexamples (two registries over `nat * nat`, registry 1's shared part copies registry 0's).
  `tr_causal_instance`: `TRead` (registry 1 adds its shared value to its local part) happens before
  `RSet` (registry 0 sets its value to 1), from the zero start. `XURC`, `XURCA`, `CCRF` and `IdemF`
  hold, so causal and causal at-least-once delivery converge, while `XUR` fails (`RSet` then
  `TRead` with no propagation reads a stale value), so `DistConv` and free at-least-once delivery
  fail: restricting `dist_exact` is not exact for causal delivery. `snap_xu_needed`: every
  FedMachine condition holds, a stale start makes every class diverge. `set_comm_needed`: XU and
  idempotence hold, commutation fails. `inc_idem_needed`: `DistConv` holds (`dist_exact`) and
  at-least-once delivery fails. Non-vacuity: `mk_alo_holds` (a max-register and a mark, events on
  both registries, every class from every valid start).
