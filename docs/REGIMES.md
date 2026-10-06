# When does a governed network converge? A field guide to the regimes

The papers prove convergence under several different conditions, tuned to the shape of your
network and the nature of your repair. This page is the practitioner's map: find your situation,
read off whether it converges and why. It is a companion to the papers, not a replacement; each
row points at the theorem that proves it. Where an original paper statement was corrected, this
guide follows the mechanized theorem; each paper's version 2 lists the corrections in its appendix
"Errata and corrections" ([base](../normalization_confluence_2026.pdf),
[federation](../normalization_confluence_in_federated_registry_networks.pdf),
[categorical](../categorical_structure_of_federated_convergence.pdf)).

Role of this page: how to pick a regime as a user. What is proved in each regime (an exact
condition, a hardness result or an open gap, each with its Coq theorem) is
[REGIME-AUDIT.md](../REGIME-AUDIT.md); what is next is [ROADMAP.md](ROADMAP.md); prior work is
[LANDSCAPE.md](LANDSCAPE.md). The map of all pages is [README.md](README.md).

## The one-sentence idea

A governed system **converges** when every processor that sees the same events reaches the same
valid state under every admissible delivery order: any order for free delivery, causally
consistent orders under causal delivery, orders that fire events only at valid states in the
guarded model. Tolerating duplicate deliveries is a separate property (at-least-once delivery,
below), not part of this definition.

Normalization confluence reaches that state **through repair**: it allows operations that
individually break invariants, and asks that (a) compensation always terminates (WFC) and (b) the
*repaired* results are order-independent (CC). CRDTs are the special case where no repair is ever
needed (see the CRDT paragraph under "Why the boundaries are where they are").

**Related regimes.** CRDT conditions characterize replica convergence under particular state- or
operation-delivery models: for op-based CRDTs (CmRDTs), concurrent operations commute under causal
delivery; for state-based CRDTs (CvRDTs), states form a monotone semilattice and merge is the least
upper bound. Invariant confluence (I-confluence; Bailis et al., arXiv 1402.2237) characterizes when
application invariants are preserved under coordination-free merging of independently reached
valid states. Normalization confluence is about convergence through repair. The three are related,
not points on one ordered axis; the precise relationship (the compensation-free fragment) is
stated in [SUBSUMPTION.md](SUBSUMPTION.md).

## The main map: execution semantics first, topology second

Which condition applies depends first on **how events execute** (one registry or many; free or
causal delivery; events fired only at valid states or at any time; repair to a fixed point on a
cycle) and only then on the network's **topology**. "Exact" is a mechanized iff; "sufficient" is
the cheap condition, usually what gsm checks.

| Execution semantics | Topology | Exact condition | Sufficient (and gsm) | Refutations and qualifiers |
|---|---|---|---|---|
| **Single registry, free delivery** | one registry | With canonical repair (`rho_star` returns a valid state): CC1 and CC2 at the states reachable from `s0` (`cc_exact_from`); for causal or guarded enabledness that persists under compensation, joinability of critical pairs at reachable configurations, JC (`jc_exact`) | Static WFC plus CC at every state: `governance_unique_normal_forms` (the Convergence Theorem, `cor:unique-nf`); gsm's `Registry.Build` | Canonical repair is needed (`rho_star_qualifier`); CC1 is not necessary under guarded enabledness (`masked_cc1`) |
| **Single registry, causal delivery** | one registry | CCR: concurrent pairs commute after every causally consistent prefix (`causal_exact`); globally, for every start: concurrent pairs commute at every state, with irreflexive happens-before (`causal_convergence_exact`) | WFC, CC2, and CC1 only for concurrent pairs: `causal_governance_confluent`, `causal_convergence`; gsm's declared `Independent` pairs | Reachability of the state is not enough (`naive_causal_converse_fails`) |
| **Federation, repair normal form** (no events) | acyclic: trees (one incoming morphism per registry, M1) and resolved multi-source networks (R1, R2); a tree is the single-source special case of a resolved acyclic network | Unconditional inside the regime: unique repair normal form, reached in every order (`frun_solves`, `solve_unique`, `order_independent`, `fed_lem_resolved_termination`) | M1 per morphism; R1 (source determinacy) and R2 (validity preservation) per resolver; gsm's `Federation` (`verifyEdge`, `verifyResolved`) | Each hypothesis is needed: `prop_cycle_necessary` (acyclicity), `prop_m1_necessary`, `r1_necessary`, `r2_necessary` |
| **Federation, FedMachine (guarded) execution**: events fire only at federally valid states | acyclic (trees as the single-source case) | C1 and C2 at reachable witnesses (`C1R1`, `C2R`): `fed_thm_fed_convergence_exact` (trees), `fed_thm_resolved_convergence_exact` (resolved networks); `fed_exact` | Static C1 and C2: `static_c1_c2_gc`; gsm's cross-order check (C1) and repaired-CC check (C2) | Static C1 is not necessary (`naive_converse_fails`) |
| **Federation, unrestricted rewrite system**: events may fire before compensation finishes | acyclic | CC1 and CC2 of the governed steps at reachable states: `fed_grs_exact` (first clause of `fed_thm_fed_convergence_exact`); no per-edge form | XU: `fed_thm_fed_convergence_corrected`, `fed_thm_resolved_convergence_corrected` | The paper's original statements, with component CC and M1 only, are false (`fed_thm_fed_convergence_refuted`, `fed_thm_resolved_convergence_refuted`); C1 and C2 do not suffice here (`fed_grs_c1_c2_insufficient`). gsm runs the guarded model and has no XU check for it |
| **Federation, buffered guards**: an event waits in the buffer until the state is federally valid and its guard holds | acyclic | Co-enabled events stay enabled after each other and commute at every state a guard-feasible word reaches (`GCR`): `fed_buffered_exact`, `fed_buffered_cr`; per edge, C1 both ways and C2 at those states: `fed_buffered_edge`; with no guard this is `fed_guarded_exact`'s condition (`fed_buffered_recovers`). Any enabledness (guards on the buffer, at invalid states, disabled by compensation): JC', `fed_jcg_exact` | | Commutation alone is neither sufficient (`bg_persistence_needed`: a guard strands an event) nor necessary (`bg_wait_exact`) (`FederatedGuards.v`) |
| **Cyclic repair network**: repair iterated to a common fixed point | any topology, cycles included; repair **monotone** on a lattice | A valid least fixed point: valid **iff** some Kleene iterate is valid (`lfp_valid_iff_reached`; under ACC `lfp_valid_exact`; gsm's normalizer `Ncyc_valid_exact`). Reaching it: at a finite stage **iff** the Kleene chain is eventually constant (`kleene_reach_exact`); chaotic schedules iff Kleene does (`chaotic_reach_exact`) | Bottom validity (`net_lfp_valid`); ACC or finite height (`kleene_reach_of_acc`, `kleene_reach_of_finite_height`), or continuity at the Kleene chain (`kleene_sup_lfp`); gsm's image-validity check (`gsm_check_Ncyc_valid`); every repair schedule reaches the same fixed point (`cyc_N_lfp`, `chaotic_reaches_lfp`) | Without bottom validity the least fixed point can be reached and invalid (`fed_thm_monotone_cycles_lfp_invalid`); without continuity the supremum formula fails (`fed_thm_monotone_cycles_kleene_formula_fails`); bottom validity and ACC are not necessary (`bottom_validity_not_necessary`, `acc_not_necessary`), nor is gsm's check (`gsm_check_not_necessary`) |
| **Cyclic event execution**: events interleave with repair to the fixed point | monotone cycles | GC: independent governed steps commute at every reachable federated state (`gc_iff`, `net_events_converge_iff`, `cyc_events_converge_iff`) | gsm's per-target C1cyc and C2cyc over image sets: `cyc_check_gc`, `cyc_check_gc_lfp`; multi-edge and resolver targets through the joint image (`multi_edge_c1`, `resolver_joint_c1`) | Monotone repair with a valid least fixed point does not give event-order convergence (`fed_thm_monotone_cycles_events_refuted`); GC has no per-edge reduction |
| **Collapsed sub-federation**: a convex block `J` replaced by one effective registry | acyclic, convex `J` | Collapse preserves semantics; it does not manufacture convergence. Every run of the collapsed network equals the same run of the original (`collapse_c_runs_agree`), so one converges **iff** the other does (`collapse_c_traceconv`), exactly when C1 and C2 hold at reachable witnesses (`collapse_c_exact`); the effective registry's guarded CC: `collapse_a_guarded_exact` | Modular route: C1 and C2 on `J`'s events and on the rest (`collapse_modular_converges`); gsm's `Federation.Embed` and certificates | CC is not inherited by the effective registry (`collapse_a_refuted`). All in `Collapse.v`; cyclic monotone blocks are paper only |

### Monotone cycles: three separate questions

The monotone rows above answer three different questions, and each has its own condition.

1. **Does a valid least fixed point exist?** On a lattice with ACC the least fixed point of the
   federated repair operator exists; it is federally valid if every component is valid with bottom
   shared values and the resolvers preserve validity (`net_lfp_valid`), and exactly when some Kleene iterate is valid (`lfp_valid_iff_reached`,
   `coq/MonotoneExact.v`). Without bottom validity it can be invalid even though a valid fixed point
   exists (`fed_thm_monotone_cycles_lfp_invalid`).
2. **Does iteration reach it?** Kleene iteration reaches it at a finite stage **iff** the Kleene
   chain is eventually constant (`kleene_reach_exact`); ACC or finite height suffice
   (`kleene_reach_of_acc`, `kleene_reach_of_finite_height`) and are not necessary
   (`acc_not_necessary`); on a complete lattice without ACC, continuity at the chain gives the
   supremum formula (`kleene_sup_lfp`), which fails without it
   (`fed_thm_monotone_cycles_kleene_formula_fails`). When it is reached, **every repair schedule
   reaches the same one** (`cyc_N_lfp`, `cyc_sweep_order_independent`, `chaotic_reaches_lfp`). This
   is a statement about the order of repair steps, not about the order of events.
3. **Do event interleavings converge?** Exactly under GC (`gc_iff`), for which gsm's per-target
   checks suffice (`cyc_check_gc_lfp`). Questions 1 and 2 do not imply it
   (`fed_thm_monotone_cycles_events_refuted`).

The constructive finite-lattice core is mechanized in `coq/Federation.v` (axiom-free), and
`coq/ChaoticACC.v` extends it to lattices with no infinite ascending chain (ACC). gsm's
image-validity check is proved sound (`gsm_check_Ncyc_valid`) but is not necessary
(`gsm_check_not_necessary`). On a complete lattice without ACC, existence of the least fixed point
is classical Knaster-Tarski, outside the axiom-free gate; this is a design exclusion, and gsm's
finite domains satisfy ACC.

## Single registry: other delivery models

| You have | You need | Converges? | Proof |
|---|---|---|---|
| One registry, **at-least-once delivery** (duplicates) | exactly-once commutation at reachable states + each event idempotent at every reachable state where it is first delivered (under causal delivery: CCR + the same per event, with causally consistent redelivery) | **Yes, if and only if**, same state as exactly-once | `alo_exact`, `causal_alo_exact_idem`; sufficient forms `alo_commuting_converges`, `causal_alo_converges` |
| One registry, **at-least-once delivery under declared independence** `I` (gsm's `Independent` pairs) | declared pairs commute after every reachable exactly-once prefix + each event idempotent at every reachable state where it is first delivered, with redelivery that reorders only declared pairs; if retries may cross undeclared partners, absorption after every history containing the event instead of idempotence | **Yes, if and only if**, same state as the history | `dalo_exact`, `dalo_r_exact`; free and causal recovered: `alo_exact_declared`, `causal_alo_exact_declared` |
| One registry, a duplicated **non-idempotent** event | | **No** (diverges) when the failure is at a reachable state; an event needs deduplication iff its duplicate is not absorbed (`safe_free_exact`) | `non_idempotent_diverges`, `notidem_needs_dedup`, `late_duplicate_diverges` |
| One registry, **guarded enabledness that a compensation step can disable** (a buffered event stops being enabled after repair) | termination from the start + **JC'**: JC's event/event clause, and for each event enabled at an invalid state, repairing after it joins with repairing first; JC alone is neither sufficient nor necessary here | **Yes, if and only if**; normal forms may leave disabled events in the buffer | `jcg_exact`, `jcsplit_exact`, `gnf_iff`; `dc_jc_insufficient`, `nv_jc_not_necessary` (`EnabledAfterComp.v`) |
| **State-based CRDT** merges (payload states as events, merge as the action, no repair) | merges commute and are idempotent at every state reachable from the start; equivalently, on the reachable states a join-semilattice for which each merge is the join with its payload | **Yes, if and only if**, under every order and any duplication | `merge_action_exact`, `merge_conv_alo_exact`, `cvrdt_on_iff`; `naive_cvrdt_iff_fails`, `clamp_reach_qualifier` (`CvRDTExact.v`) |
| **Stream processors** (incremental, time-indexed received sets) | under `Progress`: PJC at every duplicate-free event set (free delivery: PCC) | **Yes, if and only if**: settled processors with the same received set agree | `stream_exact`, `stream_exact_free` |
| **Stream processors, at-least-once delivery** (received lists may repeat events) | free delivery: PCC + each event idempotent at every state where a processor first applies it; any enabledness under `Progress`: PJC at every received list + absorption of one redelivered copy | **Yes, if and only if**: settled processors with the same received set agree, whatever the multiplicities | `stream_alo_exact_free`, `stream_alo_free_split`, `stream_alo_exact`; `ct_alo_fails` (exactly-once agreement holds, at-least-once fails) (`StreamAtLeastOnce.v`) |

WFC = every compensation chain is finite. CC = two independent events, each followed by repair,
commute (CC1), and repairing before vs after an event gives the same result (CC2). This is the
core theorem for a single registry. Mechanized in `coq/Governance.v` (axiom-free), and
in `coq/GovernanceWF.v` with the WFC potential in any well-founded order (ordinals, lexicographic
products), not only the natural numbers, so the state space need not be finite.

**Exact, not only sufficient.** `coq/GovernanceConverse.v` proves the converses. With canonical
repair (`rho_star` returns a valid state) and free delivery, every configuration from `s0` has a
unique normal form **iff** CC holds on the states reachable from `s0` (`cc_exact_from`). For
causal or guarded enabledness that persists under compensation, the exact condition is JC: the
critical pairs are joinable at every reachable configuration (`jc_exact`); CC is the case where the
join is an equality. When a compensation step can disable a buffered event, `coq/EnabledAfterComp.v`
gives the exact condition JC' (`jcg_exact`), which is JC when enabledness persists
(`jcsplit_iff_jc`); JC alone is then neither sufficient (`dc_jc_insufficient`) nor necessary
(`nv_jc_not_necessary`). Under causal
delivery the exact condition is CCR: concurrent pairs commute after every causally consistent prefix
(`causal_exact`). The naive converses are false (`rho_star_qualifier`, `masked_cc1`,
`naive_causal_converse_fails`). `coq/GovernanceWFConverse.v` states the same converses over any
well-founded potential (`wf_jc_exact`, `wf_cc_exact_from`, `canonical_cc_exact_from`) and shows that
termination itself is exact: the system terminates iff compensation is well-founded iff some
well-founded potential exists (`terminating_iff_comp_wf`, `comp_wf_iff_wfc`). At-least-once delivery
(`coq/AtLeastOnceExact.v`: `alo_exact`, `causal_alo_exact`; under declared independence
`coq/AtLeastOnceDeclared.v`: `dalo_exact`) and stream processors
(`coq/StreamExact.v`: `stream_exact`; under at-least-once delivery `coq/StreamAtLeastOnce.v`:
`stream_alo_exact_free`, `stream_alo_exact`) have exact conditions too; for streams the natural iff
with JC is false (`jc_not_necessary`).

**Exact versus checked.** JC, CCR and the reachable form of CC quantify over reachable states, so
checking them means exploring the reachable state space. CC checked at every state (and CC1 on the
declared-independent pairs) implies them and is what gsm's `Build` checks: sufficient, cheap to
enumerate, and necessary only at reachable states.

**Causal variant.** The base theorem asks CC1 of every pair of events, so every replay order must
agree. Real replicated systems usually promise only causal delivery, under which two causally
ordered events are never enabled at the same time and only *concurrent* events can arrive in
either order. CC1 is then needed only for those concurrent pairs. `coq/GovernanceCausal.v` proves
the full rewrite-system Convergence Theorem under that weaker hypothesis
(`causal_governance_confluent`; the witness `cw_confluent` / `cw_violates_all_pairs_cc1` meets it
while violating all-pairs CC1). `coq/CausalReplay.v` proves the replay form for governed steps
(apply, then normalize): if they commute on every concurrent pair, any two causally consistent
delivery orders reach the same state (`causal_convergence`). This is also how gsm's declared
`Independent` pairs read: `causal_tequiv` shows any two causally consistent orders are
trace-equivalent under concurrency, and `Trace.v`'s `run_tequiv` shows trace-equivalent sequences
reach the same state. So when the declared-independent pairs cover the concurrent ones, gsm's check
of only those pairs is the causal-delivery form of CC1. All axiom-free.

## Networks: coordination, lossy transports and distributed deployments

The main map covers acyclic federations, monotone cycles and collapse. The rows below cover
non-monotone cycles (with and without coordination), lossy transports, and deployments in which
propagation runs as separate steps.

| Topology | Repair | You need | Converges? | Proof |
|---|---|---|---|---|
| **Single cycle**, invertible transports, coherently oriented | **non-monotone**, coordination-free, no authority root | a consistent state exists **iff** the holonomy is trivial | Unique **iff** the group is trivial; otherwise there is no unique normal form (two orders reach different consistent states, or none exists) | `rootless_nf_exists_iff`, `rootless_unique_normal_form_iff` (`RootlessCycles.v`) |
| **Any network**, invertible transports, several cycles or mixed orientation | **non-monotone**, coordination-free, no authority root | a consistent state exists **iff** `H^1 = 0` (whole underlying graph); every start reaches one **iff** also each weakly connected component has a registry upstream of all of it (or the group is trivial) | Given `H^1 = 0`: the reached state is unique **iff** each component contains a registry no other registry writes (a de facto root), or the group is trivial; a unique normal form from every start **iff** each component has such a root upstream of all of it (an authority root), or the group is trivial | `net_nf_exists_iff`, `net_unique_iff`, `net_unique_normal_form_iff`, `net_reachable_iff` (`RootlessNetworks.v`); holonomy inside strongly connected components is not enough (`rootless_global_holonomy`) |
| **Cyclic**, non-invertible or otherwise non-monotone, without a root | **non-monotone**, coordination-free | no exact condition yet for lossy transports (open; see `REGIME-AUDIT.md`, gap 3; sufficient certificates for Boolean resolver networks are mechanized, including fair settlement under no local cycle plus out-degree at most one from starts with at most two unstable vertices) | **May diverge** | counterexample `prop_cycle_necessary`; a consistent state can still exist (`c13_two_ways_not_exhaustive`) |
| **Cyclic**, invertible transports | **non-monotone**, with a computed coordination | values driven along a spanning tree from an **authority root**; balanced non-tree edges kept as checked constraints; unbalanced edges coordinated | **Yes**, unique **given the root**; event order converges **iff** independent root events commute at the reachable root values | `coordinated_sound`, `coordinated_unique_nf` (`CoordinatedCycles.v`); `coordinated_events_exact` (`CoordinatedExact.v`) |
| **Any graph**, non-invertible (lossy) transports | coordination from a **root set** (every registry reachable from some root) | some root assignment drives a state satisfying every edge | A consistent state exists **iff** that holds (deciding it is NP-complete in general: the 3-SAT reduction is mechanized, NP-completeness by the standard argument); unique given the root values | `root_set_criterion_graph`, `root_set_count`, `root_set_bijection` (`RootSet.v`); `net_section_iff_sat`, `net_size`, `np_certificate` (`LossyHardness.v`) |
| **Any graph**, non-invertible transports, **event order** under root-set coordination | values driven along an outward spanning forest from the root set | for each root, its independent events commute at every value reachable from its start value by its own events | **Yes, if and only if**: one condition per root, roots never interact | `forest_events_exact`, `forest_perm_exact`, `forest_events_exact_global` (`RootSetEvents.v`) |
| **Acyclic**, **distributed** deployment (local events and propagation steps interleave; a target may read stale sources) | any | XU at every reachable stale combination plus C2 at reachable states (equivalently, plus FedMachine convergence); static XU plus C2 suffices, and is exact for every valid start when every target's sources are roots | **Yes, if and only if**, after the final flush; strictly weaker than XU, strictly stronger than FedMachine convergence | `dist_exact`, `dist_exact_tc`, `dist_exact_global`, `dist_global_exact_roots`, `dist_xu_c2_converge`; `levels_exact_not_xu`, `dist_strictly_stronger_than_fed` (`DistributedExact.v`) |
| **Acyclic**, **distributed**, propagation under **any fair schedule** (every target updated infinitely often, in any order, reading its sources' current values) | any (a later overwrite absorbs an earlier one, as gsm's shared-only writes give) | nothing beyond acyclicity: Robert's theorem | **Yes**, from every valid start, at the run of one topological order, within depth plus one rounds; fewer than `2^n` steps of any propagation word change the state. With finitely many events first, the FedMachine run of the events under XU, and the limits agree **iff** `dist_exact`'s condition. On a cycle it can fail (no fixed point, or two) | `rb_robert_fair`, `rb_rounds`, `rb_effective`, `rb_closed`, `rb_events`, `rb_fair_dist_exact`; resolver model `rb_lens_robert`; Boolean networks with an acyclic global interaction graph `rb_robert_boolean`; `rb_neg2_cycle`, `rb_copyback_cycle`, `rb_converse_fails` (`RobertFair.v`) |
| **Acyclic**, **distributed**, **causal or at-least-once event delivery** (any delivery class closed under prefixes) | any | XU at every state the class reaches plus FedMachine convergence over the class from the flushed start; causal: CCR on the FedMachine; at-least-once: commutation after duplicate-free prefixes and idempotence where an event is first delivered (causal redelivery: CCR and the same idempotence); static XU covers the first conjunct for every class | **Yes, if and only if**, after the final flush; restricting `dist_exact` is not exact for causal delivery | `dist_delivery_exact`, `dist_causal_exact`, `dist_alo_exact`, `dist_causal_alo_exact`, `xu_xurd`; `tr_causal_instance`, `inc_idem_needed` (`DistributedDelivery.v`) |
| **Acyclic**, **distributed** over **channels** that deliver projections late, reordered or duplicated, **versioned** merge (gsm's `MergeProjectionAfter`, versions strictly increasing per edge in send order) | any | XU at every state a channel run reaches plus C2 at reachable states; static XU plus C2 (gsm's check) suffices; on two-level networks (every target's sources are roots: any two-registry federation, any star) the condition is exactly the current-value model's (XU at reachable stale combinations plus C2) | **Yes, if and only if**, once the channels drain after a final round (each target sent the current projection with the next version, and that projection delivered), with no outside flush; the drained state is that of the current-value run with the same events then a flush. Versions out of send order, or no send after the last source change, break it | `vsettle_exact_cond`, `vsettle_xu_c2`, `vsettle_cv`, `chan_exact`, `vchan_twolevel_exact`, `vchan_emulate`; `version_order_counterexample`, `no_final_send_counterexample` (`ProjectionChannels.v`) |
| **Acyclic**, **distributed** over channels that can reorder or redeliver, **plain** merge (gsm's `MergeProjection`) | any | after a final flush: the same condition as the versioned row (`chan_exact`); at drain: every drain settles **iff** no projection still in flight carries a stale image | **No** in general, even under XU: a stale projection delivered after the fresh one leaves the target out of date and two drained runs of the same events disagree; converges only after an outside flush | `plain_settle_iff`, `plain_stale_counterexample`, `chan_xu_c2` (`ProjectionChannels.v`) |
| **Monotone cycles**, **distributed**, with **reset epochs** (a barrier resets every shared value to bottom, then propagation to quiescence) | monotone | each event's local outcome is the same at every reachable stale state as at its flushed form (`XUcR`), plus FedMachine convergence; gsm's per-target C1cyc and C2cyc over a set covering the reachable shared values suffice | **Yes, if and only if**, after a final epoch; the reset must be a barrier (a staggered reset re-creates a ghost) | `epoch_agree_iff`, `epoch_conv_iff`, `lens_epoch`, `dist_cyc_epoch_fix` (`DistributedCycles.v`) |
| **Monotone cycles**, **distributed**, **no resets** | monotone | the deployment flushes, every reachable quiescent state is the FedMachine state, and quiescent interleavings agree **iff** `XUcR`, FedMachine convergence, `FlushR` (every reachable state has a propagation word to quiescence; or `FairFlushR`, every fair schedule gets there) and `NoGhostR` (every reachable quiescent state holds the least fixed point of its locals); each conjunct is necessary. Under `LowR` (every reachable state at or below the least fixed point of its locals; inflationary events from such a start give it) the last two hold and the condition is `XUcR` plus FedMachine convergence | **Yes, if and only if**, with no reachable hypothesis; convergence among interleavings alone, when they may agree on a ghost, is exact too: the deployment flushes and quiescent interleavings agree **iff** it flushes, every reachable state flushes to one quiescent state, an event at a stale state and at its flush flush alike, and the flush-then-event machine converges (`conv_quiet_exact`) | `flush_agree_iff`, `flush_fed_iff`, `fair_agree_iff`, `fair_fed_iff`, `lens_noreset_iff` (`DistributedCyclesExact.v`); `conv_quiet_exact`, `fair_conv_exact` (`DistributedConvergenceExact.v`); `low_agree_iff`, `low_conv_iff`, `infl_evlow`, `evlow_lowr`, `lens_quiet` (`DistributedCycles.v`) |
| **Monotone cycles**, **distributed**, no resets: checking `FlushR` and `NoGhostR` | monotone | `FlushR` exactly: a fair run reaches quiescence iff it reaches a sound state (`h <= F l h`). Checkable routes: events that keep states sound or sandwiched (inflationary events that write no shared value), `EvLow` events, or every single propagation step yielding a sound state; gsm starts are sound and low. `NoGhostR` exactly: the start and every post-event state are ghost-free, or some invariant has no quiescent ghost; under `SoundR` it is `LowR`, checked per event; an invariant whose states have a unique fixed point or are low suffices (a unique fixed point for every locals assignment: `uniq_agree`) | exact characterizations; the cheap checks are sufficient, not necessary (`ghost_exact` flushes fairly from a state that is neither sound nor sandwiched) | `fair_flush_sound_iff`, `flushat_sound_iff`, `sand_settles`, `evsand_sandr`, `evsound_soundr`, `infl_evsound`, `evlow_fairflush`, `step_sound_fairflush`, `nc_sound_low`; `noghost_event_iff`, `ghost_witness`, `noghost_inv_iff`, `noghost_soundr_iff`, `lowr_post_iff`, `soundr_fed_iff`, `unique_or_low_noghost`, `latched_exact` (`DistributedCyclesExact.v`) |
| **Monotone cycles**, **distributed**, no resets, a clear event on a feedback loop (the ghost) | monotone | every check gsm runs passes: C1cyc, C2cyc, `XUcR` from every start, FedMachine convergence | **No**: nodes can settle at a fixed point above the least one (a ghost) that the FedMachine never produces, and no schedule leaves it; reset epochs fix it | `dist_cyc_ghost`, `q1_stuck`, `dist_cyc_epoch_fix` (`DistributedCycles.v`) |

**Events across registries, by regime.** Repair normal forms and event order are separate
questions; this list collects the event-order results, including those in the tables above:

- *Acyclic.* In the guarded execution (the FedMachine: events fire only at federally valid
  states), per-registry conditions plus C1 (cross-registry CC) and C2 (repaired CC) give
  convergence of every interleaving (`fed_interleavings_converge`, `coq/FederationEvents.v`). C1 and
  C2 at witnesses realized by reachable states are also necessary (`fed_exact`, `fed_exact_full`,
  `coq/FederationEventsConverse.v`); static C1 and C2, which gsm checks, are sufficient but not
  necessary (`naive_converse_fails`). In the unrestricted rewrite system (an event may fire before
  compensation finishes) C1 and C2 do not suffice (`fed_grs_c1_c2_insufficient`); the exact
  condition is reachable governed CC (`fed_grs_exact`), and XU suffices
  (`fed_thm_fed_convergence_corrected`). When events wait in the buffer until their guard holds
  (buffered guards, `coq/FederatedGuards.v`), the exact condition is that co-enabled events stay
  enabled after each other and commute at the states guard-feasible runs reach
  (`fed_buffered_exact`); commutation alone is neither sufficient nor necessary
  (`bg_persistence_needed`, `bg_wait_exact`). With propagation as separate steps (the distributed model),
  every interleaving converges after the final flush **iff** XU holds at every reachable stale
  combination and C2 at reachable states (`dist_exact`, `coq/DistributedExact.v`). Static XU plus
  C2 suffices (`dist_xu_c2_converge`; gsm checks static XU, gsm PR #34) and is exact for every
  valid start when the sources are roots (`dist_global_exact_roots`); the exact condition is
  strictly weaker than XU (`levels_exact_not_xu`) and strictly stronger than FedMachine
  convergence (`dist_strictly_stronger_than_fed`). Under causal or at-least-once event delivery
  (`coq/DistributedDelivery.v`) the same split holds for every delivery class: XU at the states the
  class reaches plus the FedMachine's condition for the class (`dist_delivery_exact`; causal
  `dist_causal_exact`, at-least-once `dist_alo_exact`, `dist_causal_alo_exact`). Over channels that deliver projections late,
  reordered or duplicated (`coq/ProjectionChannels.v`), the exact condition is XU at every
  channel-reachable state plus C2 in either merge mode (`chan_exact`); with versioned merging the
  channels deliver the flush themselves once they drain after a final round (`vsettle_exact_cond`,
  `vsettle_xu_c2`), and on two-level networks the condition is `dist_exact`'s
  (`vchan_twolevel_exact`); plain merging can end a drained run stale even under XU
  (`plain_stale_counterexample`). On monotone cycles the ghost survives versioned channels
  (`vchan_cyc_ghost`).
- *Distributed model on monotone cycles* (`coq/DistributedCycles.v`). Repair alone reaches the
  FedMachine's least fixed point exactly from below it (`q1_sound_iff`, `q1_below`); above another
  fixed point it stays there (`q1_stuck`), and from an arbitrary stale start the result can depend
  on the schedule (`dist_schedule_dependence`) or never settle (`dist_ring_livelock`). With events,
  reset epochs make the model exact: every run agrees with the FedMachine after a final epoch **iff**
  `XUcR` (`epoch_agree_iff`, `epoch_conv_iff`), and gsm's cyclic C1 and C2 over a widened value set
  give it (`lens_epoch`). Without resets the model is exact under `LowR` (`low_agree_iff`,
  `low_conv_iff`), and in general with no reachable hypothesis (`coq/DistributedCyclesExact.v`): the
  deployment flushes, agrees with the FedMachine at quiescence and converges **iff** `XUcR`,
  FedMachine convergence, `FlushR` and `NoGhostR` (`flush_fed_iff`, `fair_fed_iff`), each necessary.
  `FlushR` is exactly reaching a sound state (`fair_flush_sound_iff`); `NoGhostR` is exactly
  ghost-freedom after every event (`noghost_event_iff`), or an invariant with no quiescent ghost
  (`noghost_inv_iff`). With gsm's cyclic C1 and C2, certification reduces to `FlushR` and
  `NoGhostR` (`lens_noreset_iff`). The ghost `dist_cyc_ghost` passes every check gsm runs and still
  settles away from the FedMachine (`ghost_exact`), which is why gsm reports cyclic projection
  deployments not certified. Convergence among interleavings alone does not need `NoGhostR`
  (`conv_ghost_normal`), nor `XUcR` or FedMachine convergence (`ghost_conv_not_fed`); it is exact
  with the quiescent state propagation settles in as the canonical state, ghost allowed
  (`conv_quiet_exact`), and agreement with the FedMachine is that convergence plus `NoGhostR`
  (`agree_conv_noghost`).
- *Monotone cycles.* Interleavings converge **iff** the global condition GC holds: independent
  governed steps commute at every reachable federated state (`gc_iff`,
  `coq/FederationEventsCycles.v`). GC has no per-edge reduction on a cycle; gsm's per-target C1 and
  C2 over image sets imply it (`cyc_check_gc_lfp`, `coq/FederationEventsCyclesCheck.v`). Monotone
  repair alone does not give it: `fed_thm_monotone_cycles_events_refuted` has a valid least fixed
  point and no per-registry conflict, and two trace-equivalent event sequences still diverge.
- *Coordinated non-monotone cycles.* Event order converges **iff** independent events at the
  authority root commute at every root value reachable from the start (`coordinated_events_exact`,
  `coq/CoordinatedExact.v`).
- *Root-set coordination on lossy networks.* The same, one root at a time: event order converges
  **iff** each root's independent events commute at every value that root's own events reach
  (`forest_events_exact`, `coq/RootSetEvents.v`). Events on different roots commute
  (`forest_cross_commute`), and events on driven registries are overwritten
  (`forest_driven_noop`).

**Non-monotone cycles under coordination.** A non-monotone cycle has no coordination-free unique
normal form in general: on a single coherently oriented invertible cycle without a root, a unique
one exists from every start iff the group is trivial (`rootless_unique_normal_form_iff`), although a
consistent state exists whenever the holonomy is trivial (`rootless_nf_exists_iff`). On any
finite invertible network without a root, the same question is exact: a unique normal form from
every start iff, given `H^1 = 0`, each weakly connected component already has an authority root (a
registry no other registry writes, upstream of the whole component), or the group is trivial
(`net_unique_normal_form_iff`, `coq/RootlessNetworks.v`). A source feeding a cycle is enough
(`rootless_source_feeds_cycle`); two sources in one component break existence from some start
(`rootless_mixed_square`). With the
holonomy-minimal plan (an authority root, a spanning tree that drives values, balanced
non-tree edges as checks, unbalanced edges coordinated), it has one, unique given the root
(`coordinated_sound`); keeping an unbalanced edge leaves no consistent state
(`coordination_needed`). The root matters (`root_choice_matters`), and without one two orders reach
different consistent states (`copyback_without_authority`, `rootless_two_orders`). How few edges to
coordinate: the best plan over rooted spanning trees coordinates exactly the minimum number of
edges any feasible coordination needs (the group feedback edge set number), for every root
(`plan_min_exact`, `coq/CoordinationMinimum.v`); finding it is NP-hard (a mechanized Max-Cut
reduction, `maxcut_reduction`). gsm's `CoordinationPlan` cuts every cycle, which is sound and can
coordinate more than the minimum. For
non-invertible (lossy) transports the authority root generalizes to a root set: a consistent state
exists iff some assignment of root values drives a state satisfying every edge
(`root_set_criterion_graph`, `coq/RootSet.v`), and sections correspond one to one with consistent
root assignments (`root_set_count`). Deciding existence is NP-complete in general: the 3-SAT
reduction of the research note [LOSSY-NETWORKS.md](LOSSY-NETWORKS.md) is mechanized (`net_section_iff_sat`, parsimonious by
`net_count`, linear by `net_size`, with the certificate `np_certificate`; `coq/LossyHardness.v`), and
NP-completeness follows by the standard argument, so no efficient exact criterion exists unless
P = NP. Event order under root-set coordination is exact (`forest_events_exact`,
`coq/RootSetEvents.v`). The fewest edges to coordinate on a lossy network is the least deletion
whose residual passes the root-set criterion (`lmin_root_set`, decided by `lmin_decide`,
`coq/LossyMinimum.v`); even telling 0 from 1 is NP-hard (`lmin_reduction`).

## The decision, as a flowchart

```mermaid
flowchart TD
  A[Governed system] --> B{How do events execute?}
  B -- one registry --> S{Delivery?}
  S -- free --> S1[Exact: reachable CC1 and CC2 with canonical repair, or JC<br/>sufficient: WFC and CC at every state]
  S -- causal --> S2[Exact: CCR<br/>sufficient: WFC, CC2, CC1 on concurrent pairs]
  S -- with duplicates --> S3[At-least-once: exactly-once commutation<br/>plus idempotence at reachable first deliveries]
  B -- a network --> T{Acyclic?}
  T -- yes --> G{Events fire only at federally valid states?}
  G -- yes, FedMachine --> G1[Repair normal form: M1, or R1 and R2<br/>events: C1 and C2 at reachable witnesses<br/>sufficient: static C1 and C2]
  G -- no, unrestricted --> G2[Events: reachable governed CC<br/>sufficient: XU; C1 and C2 do not suffice]
  T -- no, cyclic --> M{Repair monotone on a lattice?}
  M -- yes --> M1[(1) valid least fixed point: bottom validity, or a valid Kleene iterate<br/>(2) reached: Kleene chain eventually constant; ACC suffices<br/>(3) events: GC; per-target C1cyc and C2cyc suffice]
  M -- no --> R{Coordinate from an authority root or a root set?}
  R -- yes --> R1[Unique given the root values<br/>events: each root's events commute at its reachable values]
  R -- no --> R0[May diverge; a single invertible cycle is unique only for the trivial group]
```

Deployments that run propagation as separate steps (the distributed rows) add a further
condition on top of these: XU at reachable stale states, and on cycles reset epochs or the
no-reset conditions `FlushR` and `NoGhostR`.

## Why the boundaries are where they are

- **What acyclicity gives.** On an acyclic network propagation has a finite direction: a
  topological order of the registries is a normalization order, so repair settles in one round
  (`fed_lem_fed_termination`, `fed_lem_resolved_termination`), and every fair asynchronous
  schedule of propagation steps settles at the same state (`rb_robert_fair`, Robert's theorem). A cycle lets two registries constrain each other in opposite
  directions; with the negation morphism `phi(x) = 1 - x`, repair keeps flipping the shared value
  and compensation never settles (`prop_cycle_necessary`).
- **What monotonicity gives.** If repair only moves shared values **up** a lattice order, even a
  cycle cannot flip them back and forth: cyclic propagation has fixed-point structure, and every
  repair schedule climbs to the same least fixed point when one is reached (the three questions
  above). Acyclicity and monotonicity are two independent routes to a unique **repair** normal form.
- **What neither gives.** Neither acyclicity nor monotonicity by itself establishes that event
  interleavings converge. Event interactions need their own conditions: C1 and C2 at reachable
  witnesses in the guarded acyclic model (`fed_exact`), reachable governed CC or XU in the
  unrestricted model (`fed_grs_exact`, `fed_thm_fed_convergence_corrected`), and GC or the
  per-target checks on cycles (`gc_iff`, `cyc_check_gc_lfp`). The refutations show each gap:
  `fed_thm_fed_convergence_refuted` (a tree), `fed_thm_monotone_cycles_events_refuted` (a monotone
  cycle).

Topology constrains which interactions are possible; it does not replace the interaction
conditions.

**Where CRDTs sit.** For unordered at-least-once delivery, convergence of a compensation-free
system (merges as events, no repair) is exactly a commutative and idempotent action on the
reachable states (`merge_action_exact`), and with a finite event range and decidable equality,
exactly a join-semilattice representation on the reachable states in which each merge is the join
with its payload (`cvrdt_on_iff`). CvRDTs occupy that compensation-free monotone corner. The
federated monotone-cycle results address a different problem: a common network repair fixed point
when constraints between registries form cycles. Under causal delivery, convergence for every start
is exactly commutation of concurrent pairs at every state (`causal_convergence_exact`), and standard
op-based CRDTs converge as an instance (`causal_cmrdt_SEC`); `compensation_free_exact` is the
structural statement that, with normalization the identity, that commutation condition is the
op-based CRDT condition. Normalization confluence adds business invariants on top, and that is
strictly more: `witness_causal_not_cmrdt` converges causally although its raw transitions are
not an op-based CRDT (its governed behavior is itself trivially a CRDT,
`witness_governed_constant`, so the separation is on the transition representation), and
`witness_beyond_all_pairs` (an add, a causally later remove, an independent counter) converges
although its operations do not all commute. The precise relationship is in
[SUBSUMPTION.md](SUBSUMPTION.md).

## Where each regime lives in the code and proofs

| Regime | gsm API | Mechanized |
|---|---|---|
| Single registry | `Registry.Build` (verifies WFC + CC) | `coq/Governance.v`, `coq/Gsm.v` |
| Single registry, causal delivery | declared `Independent` pairs (CC1 checked only on those) | `coq/GovernanceCausal.v`, `coq/CausalReplay.v`, `coq/Trace.v` (`run_tequiv`, bridged by `causal_tequiv`) |
| Single registry, exact condition | (`Build` checks the sufficient form) | `coq/GovernanceConverse.v`, `coq/GovernanceWFConverse.v` (any well-founded potential), `coq/EnabledAfterComp.v` (enabledness a compensation step can disable) |
| State-based CRDTs | n/a | `coq/CRDT.v`, `coq/CvRDTExact.v` (exact condition), `coq/CRDTBoundary.v` (the boundary: without compensation the CRDT algebra is exactly the convergence condition) |
| At-least-once delivery | non-idempotent events reported (`Report.NotIdempotent`: under free or causal delivery, sound at reachable witnesses, complete when exactly-once delivery converges, may over-report at unreachable states; with declared `Independent` pairs, sound at reachable witnesses and complete when the declared pairs commute at reachable states (Build's check, with reachable states valid) and retries respect the declared order, `dalo_notidem_needs_dedup`, `dalo_gsm_unlisted_safe`, `fl_retry_order_needed`) | `coq/AtLeastOnce.v`, `coq/AtLeastOnceExact.v`, `coq/AtLeastOnceDeclared.v` |
| Stream processors | n/a | `coq/Stream.v`, `coq/StreamExact.v`, `coq/StreamAtLeastOnce.v` (at-least-once) |
| Tree / DAG federation | `Federation` with directed morphisms; `Resolver` for multi-source | `coq/FederationOrder.v`, `coq/Categorical.v`, `coq/CategoricalBridge.v` (order-independence, retraction); `coq/FederationGRS.v` (the authority and resolution theorems in corrected form); `coq/SheafGluing.v` (when local consistency on sub-federations glues: R1 and a cover that refines the constraints) |
| Events across registries (acyclic) | cross-registry order check (C1, C2) | `coq/FederationEvents.v`, `coq/FederationEventsConverse.v`, `coq/FederatedGuards.v` (buffered guards) |
| Distributed deployment (propagation steps) | XU check for projection merging (`FedReport.ProjectionSafe`, opt-in `RequireProjectionSafe`; cyclic and multi-source targets reported not certified); `MergeProjectionAfter`'s version check over reordering channels | `coq/DistributedDelivery.v` (causal and at-least-once event delivery), `coq/DistributedExact.v` (acyclic, exact), `coq/ProjectionChannels.v` (channels: plain and versioned merge, exact; versioned converges at drain), `coq/DistributedCycles.v` (monotone cycles: repair alone, reset epochs, no resets), `coq/DistributedCyclesExact.v` (monotone cycles without resets, exactly; `FlushR`, `NoGhostR`) |
| Monotone cycles | `Federation.AllowMonotoneCycles()` | `coq/Federation.v` (least-fixed-point core), `coq/Chaotic.v`, `coq/ChaoticACC.v`, `coq/MonotoneFederation.v`, `coq/MonotoneExact.v` (validity, reachability, gsm's check), `coq/FederationEventsCycles.v`, `coq/FederationEventsCyclesCheck.v`, `coq/FederationEventsCyclesMulti.v` |
| Non-monotone cycles, coordinated | `CoordinationPlan` (cuts every cycle; each `CoordinationPoint` names its `Authority`) | `coq/CoordinatedCycles.v` (soundness of the holonomy-minimal plan in gsm's `HOLONOMY-COORDINATION-DESIGN.md`), `coq/CoordinatedExact.v` (event order), `coq/CoordinationMinimum.v` (the minimum number of coordinated edges, attained by a plan) |
| Non-monotone cycles, no root | (rejected by `Build`) | `coq/RootlessCycles.v` (single invertible cycles), `coq/RootlessNetworks.v` (any finite invertible network) |
| Non-invertible transports | `Federation.DiagnoseCycle` | `coq/CohomologyGeneral.v` (single cycle, rooted), `coq/RootSet.v` (root sets), `coq/LossyHardness.v` (the 3-SAT reduction), `coq/RootSetEvents.v` (event order), `coq/LossyMinimum.v` (minimum coordination); with no root, sufficient signed certificates only (`coq/SignedCycles.v`, `coq/SignedResolver.v`, `coq/LocalSigned.v`, `coq/LocalFairSettlement.v`, `coq/LocalTwoToken.v`; audit gap 3, open) |
| Compositional collapse | `Federation.Embed` | `coq/Collapse.v` (acyclic blocks); cyclic monotone blocks are paper only |

Regime by regime status, including the gaps still open, is in [REGIME-AUDIT.md](../REGIME-AUDIT.md).

See the papers for the full statements and proofs, and `coq/README.md` for what is machine-checked.

## Two verified oracles re-certify the single-registry result

The single-registry row is not only proven in the abstract; a built gsm machine's convergence is
re-certified by two independent checkers extracted from the axiom-free Coq development, so a bug in
gsm's hand-written Go verification cannot pass a non-convergent machine.

| Oracle | Certifies | Source | Trusts gsm's tables? |
|---|---|---|---|
| **Table oracle** (`checker`) | the emitted step tables commute and stay in range | `coq/Checker.v` | yes (checks what gsm emitted) |
| **Rules oracle** (`astchecker`) | the rules themselves converge, by re-evaluating the combinator AST | `coq/AstChecker.v`, `coq/AstTables.v`, `coq/AstCompact.v` | no (recomputes from declarations) |

Both are extracted OCaml binaries (`coq/extraction/`); gsm's differential tests run them on real
machines. The rules oracle is the stronger check: it re-derives convergence straight from the
declared invariants and events, trusting neither gsm's enumeration nor its normalization.
