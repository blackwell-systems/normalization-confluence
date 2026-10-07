# Regime audit of the headline claim

The claim this audit certifies (the README's headline):

> **An exact regime map of governed concurrent state: in every regime, a machine-checked exact
> condition, a hardness result showing no efficient one exists, or a gap stated in the open, with a
> checker for the practical ones.**

This page checks that sentence against the development, regime by regime and question by question.
It adds no proofs. Current at `main` `226ef2d` with #92 and #93 (gate: `coq/verify.sh`, 2241 axiom-free
results; the fifth revision was audited at `70646f6`, gate 1783, the rows #80 and #81 changed were
read at `dc610a9`, the rows #83 changed at `69ef03a`, the rows #90 changed at `a0d4713`, and the
rows #91 changed against #91's `RootlessNetworks.v`, the rows #92 changed against #92's
`LocalFairSettlement.v`, and the rows #93 changed against #93's `LocalTwoToken.v`, and the rows the closing of gap 15 changed against `StreamAtLeastOnce.v`,
`DistributedDelivery.v` and `FederatedGuards.v`, gate 2467, the rows the closing of gap 16 (d)
changed against `RobertFair.v`, gate 2569, and the rows the narrowing of gap 20 changed against
`Reconfiguration.v`, gate 2693, and the gap 20 rows the closing of its residue (c) changed against
`ReconfigurationClosure.v`, gate 3243, and the rows the closing of gap 5 and the narrowing of
gap 19 changed against `CompositionBlocks.v`, gate 3513) and gsm `main` `a4c18e4` (gsm #34 adds the XU check read in section 8; gsm #36 to #39
since then are documentation only). Every Coq name cited was read as a statement in `coq/*.v`, not
matched by name; a name in an "exact" cell is an `<->` theorem (or a conjunction containing one).

Current state. Open convergence gaps: 3, and 16 to 21; gaps 8 and 9 are design exclusions.
Gaps 15 to 21 came from a systematic coverage pass ([docs/COVERAGE.md](docs/COVERAGE.md)): the
regime space was derived from the model's axes, every meaningful combination was mapped to this
audit, and the combinations no row covered (gaps 15 to 19) and two dimensions the model does not
represent at all (gaps 20 and 21, new axes) are now listed; the same pass states five new design
exclusions (X1 to X5). Gap 15 (delivery and enabledness off the replay model) is closed in all
four parts: (a), at-least-once delivery under declared independence, by `AtLeastOnceDeclared.v`
(`dalo_exact`); (b), at-least-once stream processors, by `StreamAtLeastOnce.v`
(`stream_alo_exact_free`; any enabledness `stream_alo_exact`); (c), causal and at-least-once event
delivery in the distributed model, by `DistributedDelivery.v` (`dist_delivery_exact` for any
prefix-closed delivery class: `dist_causal_exact`, `dist_alo_exact`, `dist_causal_alo_exact`);
(d), buffered guards in federations, by `FederatedGuards.v` (`fed_buffered_exact`; any
enabledness `fed_jcg_exact`). Gap 21 (propagation
over channels) is narrowed by `ProjectionChannels.v`: on acyclic networks the exact condition over
channels is stated in either merge mode (`chan_exact`), versioned merging converges at drain exactly
when it does after a flush (`vsettle_exact_cond`), plain merging cannot be settled by its channels
(`plain_settle_iff`, `plain_stale_counterexample`), and on two-level networks the versioned condition
is `dist_exact`'s own (`vchan_twolevel_exact`); open beyond two-level networks (the current-value
form) and on cycles. Gap 20 (reconfiguration inside a run) is narrowed by `Reconfiguration.v`: for a
single registry under free delivery, a switch at a quiescent barrier is exact (`barrier_exact`;
each side's own condition when the migration is faithful, `barrier_exact_faithful`), and so is a
live switch with events in flight (`live_exact`: B's condition from every migrated reachable state
plus two cross-configuration critical pairs; A's own condition is not necessary,
`forgetful_migration`), with the outcome (online, behind a barrier only, unsafe) decidable on finite
instances (`classify_finite`); federation topology changes are exact under FedMachine semantics
(`fed_live_exact`, `fed_barrier_exact`). Its residue (c) is closed in the deterministic model (gsm's
runtime) by `ReconfigurationClosure.v`: A converges modulo the migration iff every pair of the
closure of adjacent swaps under common continuations has equal images (`amodm_closure_exact`), a
finite search on finite instances, so the outcome is decided with no faithfulness hypothesis
(`det_classify_complete`). Open: a live switch while propagation is in flight (the distributed
model) and other delivery classes across the switch. Gap 14
(convergence alone in the no-reset cyclic distributed model) is closed by #90
(`conv_quiet_exact`), and gap 2 (rootless invertible networks beyond a single coherently oriented
cycle) is closed by #91 (`net_nf_exists_iff`, `net_unique_iff`, `net_unique_normal_form_iff`). Gap 5
(a cyclic monotone `J` under collapse) is closed in the FedMachine model by `CompositionBlocks.v`:
the repair is triangular across the condensation, blockwise least fixed points are the least fixed
point (`bekic_lfp`), so `N'` and `N` have the same normal form (`mono_collapse_nf`) and converge
together, exactly under GC (`mono_collapse_exact`). Gap 19 is narrowed by the same module: (a) is
closed for blocks of any engines (`compose_exact`: the composite converges iff the upstream
converges, the block settles at every quiet input, and its settled states are not separated by its
steps at the transient inputs; each block converging in isolation is not enough,
`compose_isolated_refuted`, and with real engines `mixed_ghost_refuted`), with the rootless and
monotone engines plugged in (`mixed_rootless_exact`, `mixed_mono_iff`) and the black-box interface
closed under composition (`interface_closed`); (b) is closed for an acyclic `J`: `N` converges iff
`N'` (`J` propagating as one atom) converges and XU holds at every state `N` reaches
(`dist_collapse_iff`), `collapse_c`'s plain statement fails (`dist_collapse_refuted`), and static XU
restores it (`dist_collapse_xu`). Open: a cyclic `J` in the distributed model. The
optimization and counting gaps 10, 11 and 12 are closed with exact theorems and mechanized hardness
reductions, and gap 13 is closed on the registry-level site with two residues at paper level (the
variable-level and monotone-overlap site, and a sheaf condition for relative certificates on covers
not closed under sources). Gap 3 has progress, not closure: sufficient signed certificates for E on
the global interaction graph (`signed_settlement`, `signed_fidelity`), with Harary's balance
theorem proved for finite signed graphs (`harary_balance`) and the loop-versus-merge separation
(`obstruction_loop_vs_merge`); and, for Boolean networks of every size, sufficient certificates on
the local (state-dependent) interaction graphs (#83, `LocalSigned.v`): CanonicalFidelity from no
local positive cycle (`local_fidelity_canon`), E's Settlement from Richard's Theorems 3 and 4
(`richard_t3`, `richard_t4`), and all of E from no local cycle (`shih_dong_E`). Settlement here is
E's existential (flush) form, some update word reaching a fixed point from every reachable state.
Fair-schedule settlement, the analogue of `FairFlushR`, fails under each of these local conditions
(`shih_dong_not_fair`, `ring_local_conditions`). #92 (`LocalFairSettlement.v`) adds progress on it
under no local cycle (A) plus out-degree at most one (B): the synchronous form (`sync_simple`, the
conclusion of Shih and Ho 1999, Theorem 3.1, with (A) needed only at one orbit state:
`sync_orbit_fixed`), and fair settlement from every start with at most one unstable vertex
(`one_token_fair_settlement`); #93 (`LocalTwoToken.v`) extends this to every start with at most two
unstable vertices (`two_token_closed`, `two_token_fair_settlement`). Runs whose states all have three
or more unstable vertices are the open part. Gap 3 is cyclic, and
[the cyclic frontier](#the-cyclic-frontier) states it, with gap 13's monotone-overlap part, as one
question: what additional structure makes P, the composition layer of the canonical-execution
framework, exact on cycles. Of the gaps
the coverage pass added, 17 and 18 are cyclic and 16, 19 and 21 are in part; 15 (closed) and 20 are not (the
frontier table classifies each).

History. The first version of this audit (at `bb8ea95`, gate 729) checked the earlier headline,
which called the map "complete" with "exact conditions in every regime", and found both words
inaccurate; its conclusion listed the convergence regimes that had a sufficient condition only, or none. Since then seven mechanization PRs
closed most of those gaps: #47 (`CoordinatedExact.v`), #48 (`RootlessCycles.v`), #49
(`GovernanceWFConverse.v`), #50 (`MonotoneExact.v`), #51 (`StreamExact.v`), #54 (`RootSet.v`) and
#55 (`AtLeastOnceExact.v`). The second revision (at the 989 gate) listed gaps 1 to 13 below; a second
wave closed gaps 4, 6 and 7 (#59 `RootSetEvents.v`, #56 `EnabledAfterComp.v`, #58 `CvRDTExact.v`)
and mechanized the 3-SAT reduction behind the lossy-network hardness result (#57 `LossyHardness.v`).
A third wave settled most of gap 1: the acyclic distributed model is exact (#60
`DistributedExact.v`), and on monotone cycles the distributed model is exact under reset epochs and
under `LowR` (#62 `DistributedCycles.v`); gap 1 was restated as the residual. A fourth step closed
that residual: without reset epochs the model is exact with no reachable hypothesis left outside
the iff (#64 `DistributedCyclesExact.v`). The distributed model is now exact in every form the
development covers (acyclic; monotone cycles with reset epochs; monotone cycles without resets),
for convergence together with agreement with the FedMachine. #64 also showed that convergence among
quiescent interleavings alone, without that agreement, is not characterized; that is recorded as
gap 14. A fifth wave took up the optimization and counting gaps, 10 to 13. Minimum coordination on
invertible networks is tied to the plan model exactly, with a mechanized Max-Cut reduction (#72
`CoordinationMinimum.v`, gap 10 closed); minimum coordination on lossy networks has an exact
characterization, a decision procedure, a mechanized 3-SAT reduction and an NP certificate (#70
`LossyMinimum.v`, gap 11 closed); `H^1` on the nerve as a 2-complex is classified for any group and
counted over Z/2 (#71 `CohomologyNerve.v`, gap 12 closed); and sheaf gluing is exact on the
registry-level site for consistent states, with certificates gluing on covers closed under sources
(#73 `SheafGluing.v`, gap 13 narrowed to the paper's variable-level and monotone-overlap site). The
research note on lossy networks (#52) is now [docs/LOSSY-NETWORKS.md](docs/LOSSY-NETWORKS.md). Since
then #80 (`SignedCycles.v`, `SignedResolver.v`) and its statement review (#81) brought the gate to
1968: section 12 gains a loops-versus-merges row and sufficient signed certificates for E on the
rootless resolver row, and gap 3 records them as progress; no gap closes and no status changes.
Then #83 (`LocalSigned.v`) brought the gate to 2012: the rootless resolver row gains sufficient
certificates on local interaction graphs, with counterexamples marking what they do not give, and
gap 3 records them as progress; again no gap closes and no status changes. Then #90
(`DistributedConvergenceExact.v`) brought the gate to 2067 and closed gap 14: convergence among
quiescent interleavings alone is exact (`conv_quiet_exact`), with the quiescent state propagation
settles in, ghost allowed, as the canonical state in place of the FedMachine's least fixed point.
Then #91 (`RootlessNetworks.v`) brought the gate to 2160 and closed gap 2: rootless propagation on
any finite invertible network is exact, for the reachable set, existence from every start,
uniqueness, and the two together, with the single-cycle theorems of #48 recovered as corollaries.
Then #92 (`LocalFairSettlement.v`) brought the gate to 2189: the rootless resolver row gains
fair-schedule settlement under no local cycle plus out-degree at most one, in the synchronous form
and from starts with at most one unstable vertex, and gap 3 records it as progress; no gap closes
and no status changes.
Then #93 (`LocalTwoToken.v`) brought the gate to 2241: under the same two conditions no closed
asynchronous run with two unstable vertices changes the state, so fair schedules from starts with
at most two unstable vertices settle; gap 3 records it as progress; no gap closes and no status
changes.
Then a coverage pass ([docs/COVERAGE.md](docs/COVERAGE.md)) checked the audit from the other side:
completeness here had been relative to the rows listed. It derived thirteen axes from the Coq
premises and the audit's vocabulary, pruned the product by ten axis dependences, and mapped 179
cells: 58 covered, 12 excluded, 19 open under existing gaps, 55 degenerate, 14 ill-formed, and 21
with no row at all (12 distinct questions). Those became gaps 15 to 19; two dimensions the model
does not represent (reconfiguration inside a run, propagation over channels) became gaps 20 and
21, and five became design exclusions X1 to X5. It adds no proofs; no existing gap's status
changes. Since then gap 15 has closed: part (a) with `AtLeastOnceDeclared.v` (#97), parts (b) to (d)
with `StreamAtLeastOnce.v`, `DistributedDelivery.v` and `FederatedGuards.v` (gate 2467); gap 21 is
narrowed (#98); gap 16 is narrowed, (d) closed with `RobertFair.v` (gate 2569); gap 20 is narrowed (`Reconfiguration.v`, gate 2693), and its residue (c) is closed in the deterministic model (`ReconfigurationClosure.v`, gate 3243); gap 5 is closed and gap 19 narrowed (`CompositionBlocks.v`, gate 3513).
The tables below are the current state; the conclusion re-answers the old questions and confirms
the wording.

## How to read the tables

Each row is one question asked of one regime. Columns:

- **Exact (N and S).** A mechanized necessary-and-sufficient condition, with its theorem, or
  "none mechanized", or "none known".
- **Cheap sufficient, and the link.** The condition gsm-style checking can afford (per state, per
  pair, per edge), and the theorem that makes it imply the exact one.
- **gsm.** Whether gsm `main` implements a check (file or API named).
- **Gap.** `paper` (proved in a paper, not mechanized), `open` (not proved anywhere, or listed open
  by the development itself), `design` (excluded by the model or the axiom-free constraint),
  `hardness` (a complexity result says no efficient exact condition exists; each row says whether it
  is mechanized or cited), or `-`.

Three kinds of question are kept apart, because the convergence claim is about the first:

1. **Convergence**: does a unique normal form exist; do all event orders reach it.
2. **Optimization**: what is the minimum coordination.
3. **Counting**: the rank of `H^1`.

## 1. Single registry

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Free delivery: unique normal form for every buffer from `s0` | CC1 and CC2 on states reachable from `s0`, with canonical repair: `cc_exact_from`, `cc_exact`, `cc_exact_global`; with `rho*` built from WFC: `wfc_cc_exact_from`; with no termination hypothesis: `canonical_cc_exact_from` | CC1 and CC2 at every state: `governance_unique_normal_forms`, `paper_governance_unique_normal_forms`; reachable form implies JC: `cc_reach_jc` | `Registry.Build` (exhaustive CC; footprint path `disjoint_events_commute`); re-certified by the table and rules oracles | Qualifier: canonical repair needed (`rho_star_qualifier`). - |
| Causal or guarded enabledness: confluence from `c0` | For any enabledness, including enabledness a compensation step can disable, with termination from `c0`: JC' (JC's event/event clause, and for each `e` enabled at an invalid `sigma`, `(rho* (apply e sigma), B - e)` joinable with `(rho sigma, B)`) at configurations reachable from `c0`: `jcg_exact`; JC' is exactly joinability of every critical pair at every reachable configuration: `jcg_iff_critical`, `cr_iff_critical`; split form (JC's clause where `e` stays enabled, the direct join where compensation disables it): `jcsplit_exact`. When enabledness persists under compensation (`enabled_after_comp`), JC' is JC (`jcsplit_iff_jc`, `jcg_iff_jc`) and the earlier theorems are recovered: `jc_exact_recovered`, `sn_jc_exact_recovered` (types checked against `jc_exact`, `sn_jc_exact`) | CC1 on co-enabled pairs plus CC2, on reachable states: `cc_reach_jc`, `cc_reach_unique_normal_forms`; deps-based enabledness: `paper_causal_governance_unique_normal_forms` | CC1 checked on declared `Independent` pairs only | Without `enabled_after_comp`, JC is neither sufficient (`dc_jc_insufficient`: JC holds, yet `(Pending, [Settle])` has two normal forms, one stuck) nor necessary (`nv_jc_not_necessary`: a compensation disables an event, JC' holds and every configuration is confluent, JC fails). Normal forms are (state, residual buffer) pairs: `gnf_iff`; the buffer may be non-empty (`stuck_nf_iff`). CC1 not necessary: `masked_cc1`. - (closed by #56) |
| Any well-founded potential (infinite state, ordinal or lexicographic `Phi`): unique normal form | `wf_jc_exact`, `lex_jc_exact`, `comp_wf_jc_exact` (no potential), `canonical_jc_exact`; free delivery `wf_cc_exact_from`, `canonical_cc_exact_from`; with `rho*` constructed: `wf_cc_exact_from_built`, `comp_wf_cc_exact_from_built`. The `nat` statements are recovered: `jc_exact_from_wf`, `cc_exact_from_from_wf` | `governance_wf_confluent`, `causal_governance_wf_confluent`, `governance_lex_confluent`, instance `zw_confluent` | n/a (gsm needs finite state to decide) | - (closed by #49) |
| WFC itself (termination) | The system terminates from every configuration iff compensation is well-founded: `terminating_iff_comp_wf`; iff some potential into some well-founded order exists: `comp_wf_iff_wfc`. Canonical repair implies it: `canonical_comp_wf`; with decidable validity a `nat` potential exists: `comp_wf_nat_potential` | `repair_terminates`; `base_lem_finite_implies_ubc` | WFC cycle detection in `Build` | - (closed by #49) |

## 2. Causal delivery (replay model)

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Do all causally consistent orders of the same events reach one state from `s0` | CCR: concurrent pairs commute after every causally consistent prefix: `causal_exact` | Governed steps commute on every concurrent pair at every state: `causal_convergence`; the global iff `causal_convergence_exact` (needs `hb` irreflexive) | Declared `Independent` pairs read as the concurrent ones (`causal_tequiv`, `run_tequiv`) | Qualifier: reachability of the state is not enough (`naive_causal_converse_fails`). - |

## 3. At-least-once delivery

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Free delivery: does every delivery with duplicates reach the exactly-once result | Exactly-once commutation at reachable states plus idempotence of each event at every reachable state where it is first delivered: `alo_exact`; equivalently with absorption after every exactly-once run containing the event: `alo_exact_absorb`. Convergence forces idempotence at every state any at-least-once delivery reaches: `alo_idem_reachable` | `alo_absorbed`, `alo_commuting_exactly_once`, `alo_commuting_converges`; placed under the iff by `old_free_implies`, `alo_commuting_recovered` | `Report.NotIdempotent` (see the next row) | - (closed by #55) |
| Per event: which events need deduplication | An event needs none iff its duplicate is absorbed after every exactly-once run containing it: `safe_free_exact`, `needs_dedup_exact`, `needs_dedup_witness`; under reachable commutation, iff idempotent at reachable first deliveries: `safe_free_iff_idem` | A non-idempotent step at a reachable witness: `notidem_needs_dedup` | `Report.NotIdempotent` is sound at reachable witnesses (`notidem_needs_dedup`) and complete when exactly-once delivery converges and reachable states are valid (`gsm_unlisted_safe`). It can over-report: a step not idempotent only at an unreachable state is listed though every delivery converges (`jmp_unreachable`). Idempotence alone is not enough without commutation (`flag_idem_needs_dedup`, `fw_alo_fails`). Both placements are for free delivery (and, by the causal forms, causal delivery); for a registry that declares `Independent` pairs see the next rows | - |
| Causal delivery (`causal_alo` redelivery) | CCR on the event set plus absorption: `causal_alo_exact`; plus idempotence: `causal_alo_exact_idem`; per event `safe_at_exact`, `safe_at_iff_idem` | `causal_alo_exactly_once`, `causal_alo_converges`, placed by `old_causal_implies`, `causal_alo_recovered`; `late_duplicate_diverges` shows the redelivery qualifier is needed | as above (`causal_notidem_needs_dedup`, `causal_gsm_unlisted_safe`) | Qualifier: absorption at every causal run containing the event is not necessary (`causal_absorb_qualifier`). - (closed by #55) |
| Declared independence `I` (`ALOI` redelivery: every pair some copy delivers out of the history's order is declared) | Declared pairs commute after every reachable exactly-once prefix (`CommI`, equivalently exactly-once trace convergence, `tconv_exact`) plus idempotence of each event at every reachable state where it is first delivered: `dalo_exact`; with absorption after every history whose later events are declared independent of the event: `dalo_exact_absorb`; `dalo_exact_trace`; per event `safe_i_exact`, `safe_i_iff_idem`. On exactly-once deliveries the model is trace equivalence (`aloi_nodup_iff`). Free and causal recovered: `alo_exact_declared`, `causal_alo_exact_declared` | Build's check on declared pairs at valid states gives `CommI` when reachable states are valid (`build_comm_i`); with `NotIdempotent` empty, every delivery converges (`dalo_gsm_build`) | `Report.NotIdempotent` with `Independent` pairs: sound at reachable witnesses (`dalo_notidem_needs_dedup`, `dalo_notidem_needs_dedup_once`); complete when `CommI` holds and reachable states are valid (`dalo_gsm_unlisted_safe`), and then deduplicating exactly the listed events suffices (`dalo_unlisted_converge`); over-reports at unreachable witnesses (`jmp_declared_unreachable`). Completeness needs `CommI`: `fl_partner_overtakes` (Add and Remove declared, both idempotent everywhere, the redelivered Add overtakes its declared partner). It needs retries to respect the declared order too: `fl_retry_order_needed` | Instances: `fl_declared_exact` (free delivery fails there, `fl_retry_order_needed`), `fl_gsm_build`; `inc_declared_fails` (the idempotence clause is needed). The FedMachine with declared `I` by P1 ([COVERAGE.md](docs/COVERAGE.md)). - (closed, gap 15 (a)) |
| Declared independence, retries unordered (only first copies respect the declared order) | `CommI` plus absorption after EVERY history containing the event: `dalo_r_exact`; per event `safe_r_exact`; strictly stronger than the `ALOI` condition (`dalo_r_implies`, strict by `fl_retry_order_needed`) | | `NotIdempotent` is not complete here even with `CommI` (`fl_retry_order_needed`: `Add` unlisted, needs deduplication) | Instance `mx_declared_r`. - (closed, gap 15 (a)) |
| Off the replay model: stream processors and the distributed model | Streams under free delivery: `PCC` plus idempotence at every state where a processor first applies the event: `stream_alo_exact_free` (section 5). Distributed model: XU at the states at-least-once words reach (that is `XUR`, `dist_exact`'s own) plus, on the FedMachine from the flushed start, commutation after duplicate-free prefixes and idempotence where an event is first delivered: `dist_alo_exact`; causal redelivery: `dist_causal_alo_exact` (section 8). Both are `alo_exact` and `causal_alo_exact_idem` applied to the governed step each model reaches (from `rho* s0` for streams, `stream_alo_aloconv`; the FedMachine up to pointwise equality, `causal_alo_s_exact`) | | `NotIdempotent` is per registry; the distributed condition asks for idempotence of the FedMachine step, which no gsm check targets | Counterexamples: `ct_alo_fails` (streams: exactly-once agreement holds, at-least-once fails), `inc_idem_needed` (distributed: `DistConv` holds, at-least-once fails). - (closed, gap 15 (b) and (c)) |

## 4. CRDT fragment

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Op-based, causal delivery: convergence of a compensation-free system | `compensation_free_exact` (causal condition iff op-based CRDT) composed with `causal_convergence_exact` | `cmrdt_SEC`, `causal_cmrdt_SEC` | Rules oracle certifies the compensation-free classification | - |
| State-based: convergence of merges | Merges as events of a compensation-free registry (identity repair): deliveries over the event set with the same set of events, in any order and with any duplication, reach one state from `s0` iff the merges commute and are idempotent at every state reachable from `s0`: `merge_action_exact`; equivalently `alo_exact`'s conditions: `merge_conv_alo_exact`. With finitely many payloads and decidable state equality, iff the reachable states carry a join-semilattice for which each merge is the join with its payload: `cvrdt_on_iff` (backward direction `cvrdt_on_conv`, unqualified; `cvrdt_on_exact` as exported also takes `MergeConv s0` as a premise, so it is not the iff). Free delivery through the registry's exact theorems: `cf_cc_exact_from`, `cf_cc_exact_from_wfc` | `cvrdt_SEC`, `cvrdt_absorbs_duplicates` (commutative, associative, idempotent join), recovered as `cvrdt_SEC_recovered`, `cvrdt_absorbs_duplicates_recovered`; monotone case: `cvrdt_lfp` (the delivered state is the least upper bound of `s0` and the payloads) | n/a | Qualifiers: the naive iff with a join-semilattice on all of S is false (`naive_cvrdt_iff_fails`); reachability is needed (`clamp_reach_qualifier`); both clauses are needed (`add_cc_not_alo`, `lww_not_conv`). Not proved as an instance of `thm:monotone-cycles` (Fed remark says so); the exact condition is stated directly. - (closed by #58) |
| Strictness of the inclusion | The boundary, one theorem: `crdt_boundary`. Compensation-free, causal convergence from every start iff concurrent raw operations commute (`cf_causal_boundary`), convergence under every order and duplication iff the raw actions are commutative and idempotent at reachable states (`cf_merge_boundary`), and with a finite range and decidable state equality iff a semilattice representation on reachable states (`cf_cvrdt_boundary`). With compensation, the witness (raw `settrue`, `flip`; repair to `false`) converges under both delivery models from every start while its raw transitions fail each condition: `witness_ops_not_commute` (the specific pair, at every state), `witness_raw_not_causal`, `witness_not_cvrdt_order` (no partial order on `bool` makes both inflationary), `witness_not_cvrdt_exact` (not commutative, not idempotent, no `MergeConv`, no `CvRDTOn`, from every start) | `witness_not_cmrdt`, `witness_leaves_valid_space`, `witness_causal_not_cmrdt` (kept; the older `witness_not_cmrdt` quantifies over all functions `bool -> bool`) | n/a | Qualifier: strictness is relative to the raw transition representation; the governed composite is itself a CmRDT and a CvRDT on `bool` (`witness_governed_constant`), so the claim is about representations, not observable behavior. Non-vacuity: `boundary_nonvacuous`. - |

## 5. Stream processors

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Settled processors with the same received set agree | Under `Progress`: PJC at every duplicate-free `(s0, E)`: `stream_exact`, with `pjc_exact` for the processor rewrite system; free delivery: PCC: `stream_exact_free`; with no qualifier, agreement iff finished reductions are a set function: `stream_agree_set_function` | `stream_convergence`, `stream_order_independence`, `base_cor_quiescent`; `pjc_stream_agreement`, `jc_stream_agreement`, `stream_agreement_recovered` | n/a | Qualifiers: the natural iff with the rewrite-system JC is false (`jc_not_necessary`); `Progress` is needed (`progress_needed`). - (closed by #51) |
| At-least-once delivery: settled processors whose received lists may repeat events, compared by their set of events (`StreamAgreeA`) | Free delivery: `PCC` plus `PIdem` (each event idempotent at every state `grun (rho* s0) u` where a processor first applies it): `stream_alo_exact_free`; equivalently exactly-once agreement plus `PIdem`: `stream_alo_free_split`; the property is `ALOConv` of the governed step from `rho* s0` (`stream_alo_aloconv`). Any enabledness, under `Progress`: PJC at every received list, duplicates allowed, plus `DupAbsorb` (for `a` in `E`, some finished reduction from `a :: E` ends where one from `E` does): `stream_alo_exact`, a reduction to one redelivered copy, local only under free delivery. Duplicate-free lists recover `stream_exact` (`stream_exact_recovered`, `stream_agree_nodup_iff`) | `PCC` plus idempotence at every state | n/a | Qualifiers: `stream_exact`'s condition is not sufficient (`ct_alo_fails`: the counter; PJC and exactly-once agreement hold, `[0]` and `[0; 0]` settle at 1 and 2); idempotence alone is not (`ow_alo_fails`); the two conjuncts of `stream_alo_exact` are independent (`ct_general`, `ow_general`). Non-vacuity `mx_alo_holds`. - (closed, gap 15 (b)) |
| Infinite streams: eventual agreement | None; the naive claim is false (`base_thm_convergence_transient_counterexample`) | Agreement at settled times with equal received sets (`stream_agreement`) | n/a | design (a lagging processor need never agree) |

## 6. Acyclic federation: the repair normal form

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Single source (M1): unique federated repair normal form | **No iff needed.** Under the network hypotheses the normal form is unconditional: `frun_solves`, `solve_unique`, `order_independent`, `cat_thm_one_order_independent`, one round from any state `fed_lem_fed_termination`. Each hypothesis is shown needed existentially: acyclicity `prop_cycle_necessary`, M1 `prop_m1_necessary` | M1 per morphism | M1, shared-only writes, source determinacy (`verifyEdge`) | The regime is defined by its hypotheses; inside it the answer is unconditional. - |
| Multi-source (R1, R2) | **No iff needed**, same shape: `fed_lem_resolved_termination`; R1 `r1_necessary`, R2 `r2_necessary` | R1 and R2 per resolver | `verifyResolved`, every combination of valid source states | Decidability remark for R1, R2 is paper-only (Fed `rem:fed-mechanized`; ROADMAP item 5). - |
| Every fair asynchronous schedule of propagation steps, from every valid start (Robert's asynchronous half; the distributed model's step: a target overwrites its shared part with the image of its sources' current states) | **No iff needed**, unconditional in the regime (`RobertFair.v`): every fair schedule settles at the run of one topological order (`rb_robert_fair`), which is quiescent (`rb_limit_quiet`) and the only quiescent state a propagation word reaches (`rb_unique`); every topological order reaches it (`rb_topo_runs`; `order_independent` recovered as `rb_order_independent`). Bound: with levels increasing along source arcs (the depth), a target is final from the end of round level plus one (`rb_rounds`, `rb_rounds_all`; with the position, after `\|o\|` rounds, `rb_rounds_pos`); along any propagation word, fair or not, fewer than `2^\|o\|` steps change the state and a closed word changes nothing (`rb_effective`, `rb_closed`). Resolver model: resolvers that read only their sources along an acyclic graph have a unique fixed point that every fair schedule reaches (`rb_lens_robert`, with `rb_lens_closed`); Boolean networks whose global interaction graph has no cycle: acyclic asynchronous state graph, unique fixed point, fair settlement from every start (`rb_robert_boolean`; Robert 1986 and 1995, as restated in Richard 2019, Theorem 1). Each hypothesis is needed: acyclicity (`rb_dist_cycle_needed`, `rb_neg2_cycle`, `rb_copyback_cycle`), absorption of a later overwrite (`rb_absorb_needed`); acyclicity is not necessary (`rb_converse_fails`, Shih and Ho's network) | n/a (the regime's hypotheses) | n/a | - (closed, gap 16 (d)) |

## 7. Acyclic federation: event order

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Guarded (events at federally valid states, `FedMachine.Apply`): all trace-equivalent sequences converge from a valid consistent `s0` | C1 and C2 at witnesses reachable from `s0`: `fed_exact`, `fed_exact_full`, `acyclic_gc_iff`; as a rewrite system `fed_guarded_exact`; by paper label `fed_thm_fed_convergence_exact`, `fed_thm_resolved_convergence_exact` | Static C1 and C2: `static_c1_c2_gc`, `fed_permutations_converge`, `fed_thm_fed_convergence_guarded` | C1 and C2 (`verifyCrossOrder`, `verifyRepairedCC`) | Qualifier: static C1 not necessary (`naive_converse_fails`). A C2 converse quantifying over all valid starts is a different quantification (ROADMAP, lower value); the reachable-witness iff stands. Not oracle-certified (ROADMAP item 5). - |
| Unguarded `G_Fed` (events may fire before compensation) | CC1 and CC2 of `G_Fed` on reachable states: `fed_grs_exact` (no per-edge form) | XU plus component CC: `grs_unique_nf`, `fed_thm_fed_convergence_corrected`; C1 and C2 do not suffice (`fed_grs_c1_c2_insufficient`) | No XU check; gsm's runtime is the guarded model | - (exact, in global form) |
| Buffered guards: an event waits in the buffer until the state is federally valid and its guard `g` (decidable, on the federated state) holds; normal forms may hold stuck events | From a valid consistent `s0`, unique normal forms for every buffer iff `GCR s0`: at every state a guard-feasible word reaches, co-enabled distinct events stay enabled after each other and commute: `fed_buffered_exact`; with confluence `fed_buffered_cr`; per edge (C1 both ways across registries, C2 within one, at those states): `fed_buffered_edge`. The trivial guard recovers `fed_guarded_exact`'s condition (`fed_buffered_recovers`, `gcr_true_iff`). Any enabledness (guards on the buffer, evaluated at invalid states, disabled by compensation): JC', `fed_jcg_exact` (`jcg_exact` on the federated GRS, termination discharged by `fed_terminating`) | | No buffered guard in gsm's runtime (`DeclEventGuarded` is a no-op when false) | Qualifiers: commutation (the unguarded condition, `C1R1 /\ C2R`) is not sufficient (`bg_persistence_needed`: every pair commutes, a guard strands an event, two normal forms) and not necessary (`bg_wait_exact`: two events never enabled together, not commuting, unique normal forms and JC'); `bg_commute_needed`. - (closed, gap 15 (d)) |

## 8. Distributed model with propagation steps

The model of `FederationEvents.v`: a run is a word of local events (a registry applies an event to
its own state) and propagation steps (a target overwrites its shared part from its sources' current,
possibly stale, states). Acyclic: `DistributedExact.v` (#60). Monotone cycles: `DistributedCycles.v`
(#62) and, without resets, `DistributedCyclesExact.v` (#64), where a state is the locals of every node and every shared value, a propagation step repairs
one target from its sources' current values, `Lfp l` is the FedMachine's least fixed point for the
locals `l`, and a quiescent state is one no propagation step changes. The no-reset properties are
read at quiescent states: `DAgreeQ` (every reachable quiescent state is the FedMachine state for the
same events), `DConvQ` (two reachable quiescent states reached by federated-trace-equivalent event
sequences are equal), `FlushR` (every reachable state has a propagation word to quiescence),
`FairFlushR` (every fair schedule from every reachable state reaches quiescence), `NoGhostR` (every
reachable quiescent state holds `Lfp` of its locals), `XUcR` (an event's local outcome is the same at
every reachable stale state as at its flushed form), `FMConv` (the FedMachine converges from the
flushed start).

Channels (`ProjectionChannels.v`, gap 21): projections are sent with a version and a snapshot of the
state, and delivered later, in any order, and possibly more than once; a delivery merges the
snapshot's image. Plain merging (gsm's `MergeProjection`) applies every delivery; versioned merging
(`MergeProjectionAfter`) applies only a version above the last applied one. Versions sent to a
target strictly increase in send order (gsm's contract). `ChanConv vm` compares runs after a final
flush (as `DistConv` does); `CXUR vm` is XU at every state a channel run reaches; `SettleConv`
compares versioned runs at drain, after a final round (each target, in topological order, sent the
current projection with the next version, and that projection delivered) and any drain, with no
outside flush.

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Acyclic: from a valid start `s0`, any two words whose event sequences are federated-trace-equivalent give the same state after the final flush (`DistConv`) | XU at every reachable stale combination (`XUR`: the target's possibly stale shared part against the image of its flushed sources) plus C2 at states reachable from the flushed start: `dist_exact`; equivalently `XUR` plus reachable LocalCC: `dist_exact_local`; `XUR` plus FedMachine convergence from the flushed start: `dist_exact_tc`. Quantified starts: every valid start iff `XUG` and `C2G`: `dist_exact_global`; every consistent start: `dist_exact_consistent`; when every target's sources are roots, every valid start iff static XU and C2: `dist_global_exact_roots` | Static XU plus C2, no LocalCC needed: `dist_xu_c2_converge`; XU plus each registry's own CC: `dist_interleavings_converge` (recovered as `dist_interleavings_converge_recovered`), `propagation_flush`; `xu_implies_c1_c2` | `verifyProjectionMerge` (gsm #34) checks static XU per single-source target and reports it (`FedReport.ProjectionSafe`; opt-in `RequireProjectionSafe`); with `Build`'s C2 it is sound by `dist_xu_c2_converge`, exact for every valid start when the sources are roots (`dist_global_exact_roots`), and can over-reject for deployments that start consistent (`levels_exact_not_xu`). Multi-source targets are reported not certified (gsm sends one edge's image; the model's propagation step is the resolver merge) | The exact condition is strictly weaker than XU (`levels_exact_not_xu`: C1 and C2 hold and XU fails, yet every consistent start converges; from the stale start at the failing level two runs diverge, so the reachability qualifier is needed) and strictly stronger than FedMachine convergence (`dist_implies_fed`; `dist_strictly_stronger_than_fed`: every FedMachine order converges from every consistent start, two propagation timings of the same events diverge). - (closed by #60) |
| Acyclic, fair schedules with finitely many events: a word of events and propagation steps followed by any fair propagation schedule, or an infinite schedule with finitely many events in which every target propagates infinitely often; limits compared | Every such run settles at the FedMachine run of its events, under Common and XU (`rb_events`, `rb_event_schedule`); from a valid start `s0`, the limits of fair schedules after words with federated-trace-equivalent events agree iff `XUR s0` and C2 at states reachable from the flushed start, `dist_exact`'s condition (`rb_fair_dist_exact`, through `rb_fair_conv_iff`: agreement of the limits is `DistConv`) | XU and C2 (`dist_xu_c2_converge`, transferred by `rb_fair_conv_iff`) | as the row above | Non-vacuity: `rb_supply_events`, `rb_supply_fair_conv`; the condition fails on `rb_gg_not_fair_conv`. Infinitely many events give no settlement in general and are not stated. - (gap 16 (d), closed) |
| Acyclic, any event-delivery class: admissible event sequences closed under prefixes, compared by a relation reflexive on them (causal orders by permutation; at-least-once deliveries, free or causal, by their set of events) | `XURD` (XU at every state reached by a word whose events, extended by the event, are admissible) plus convergence of the FedMachine over the class from the flushed start: `dist_delivery_exact`; `dist_exact_tc` recovered (`dist_exact_tc_recovered`). Causal: `XURC` plus CCR on the FedMachine (concurrent pairs, after every causal prefix): `dist_causal_exact`. At-least-once, free: `XUR` (unchanged) plus FedMachine commutation after duplicate-free prefixes and idempotence where an event is first delivered: `dist_alo_exact`; causal redelivery: `XURCA`, CCR and idempotence: `dist_causal_alo_exact`. The FedMachine conditions are `causal_exact` and `causal_alo_exact_idem` up to pointwise equality (`causal_conv_s_exact`, `causal_alo_s_exact`, which give the Leibniz theorems back: `causal_exact_recovered`, `causal_alo_exact_recovered`) | Static XU gives the propagation conjunct of every class from every valid start (`xu_xurd`; reachable XU too, `xur_xurd`) | `verifyProjectionMerge` (static XU) covers the propagation layer for every delivery class; the event-order layer is the FedMachine's condition for the class: under causal delivery, the pairs `hb` leaves concurrent commute after causal prefixes, in place of C2 on declared pairs; under at-least-once delivery the FedMachine step must also be idempotent where an event is first delivered, which no gsm check targets | Qualifiers: restricting `dist_exact` is not exact for causal delivery (`tr_causal_instance`: causal and causal at-least-once delivery converge while `XUR`, `DistConv` and free at-least-once delivery fail; the class's own reachability is needed). Each conjunct necessary: `snap_xu_needed` (every FedMachine condition holds, a stale start diverges), `set_comm_needed`, `inc_idem_needed` (`DistConv` holds, at-least-once fails). Non-vacuity `mk_alo_holds`. - (closed, gap 15 (c)) |
| Acyclic, over channels (projections delivered late, reordered or duplicated; either merge mode), compared after a final flush (`ChanConv vm`) | `CXUR vm` (XU at every channel-reachable state) plus C2 at states reachable from the flushed start: `chan_exact`; every valid start iff `XUG` and `C2G`, the current-value model's own condition: `chan_exact_global`; when every target's sources are roots, iff static XU and C2: `chan_global_exact_roots`. The current-value model is the case of immediate delivery (`emb_run`), so `CXUR` contains `XUR` | XU and C2: `chan_xu_c2`; `chan_flush` | gsm's static XU check (`FedReport.ProjectionSafe`) with `Build`'s C2 is sound for both `MergeProjection` and `MergeProjectionAfter` after a flush, and exact for every valid start when the sources are roots | The comparison is after a flush the channels do not deliver; the next two rows compare at drain. - (gap 21, narrowed) |
| Acyclic, versioned merge (`MergeProjectionAfter`), at drain: a final round, then any drain (`SettleConv`) | After the final round every projection in flight is refused, so every drain ends at the current-value flush of the state reached: `vsettle`, `vsettle_settled`; converging at drain is converging after a flush: `vsettle_exact`, so `SettleConv <-> CXUR true /\ C2R`: `vsettle_exact_cond`; the drained state is the state of the current-value run "the same events, then a flush": `vsettle_cv`. Two-level networks (every registry a root, whose repair is the identity, or a sink; any two-registry federation, any star): every versioned channel state is, at any target and every root, a current-value state (`vchan_emulate`), so `SettleConv <-> XUR /\ C2R <-> DistConv`: `vchan_twolevel_exact` | XU and C2 give convergence at drain: `vsettle_xu_c2` | `MergeProjectionAfter`'s version check is proved: with versions strictly increasing per edge in send order, gsm's XU and C2 give convergence once the channels drain after a final round, with no outside flush (`vsettle_xu_c2`), at the state of the current-value run (`vsettle_cv`) | Hypotheses necessary: versions out of send order (a newer version on an older snapshot) apply a stale projection last (`version_order_counterexample`); drained channels with no send after the last source change leave the target stale (`no_final_send_counterexample`); `CXUR` and C2 by `chan_exact`. Non-vacuity, a projection delivered after later local events: `late_delivery_instance`. - (gap 21, narrowed: whether `CXUR true` equals `XUR` beyond two-level networks is open) |
| Acyclic, plain merge (`MergeProjection`), at drain | After the final round, every drain settles iff every projection still in flight to a target carries the image of the flushed state there: `plain_settle_iff` | Nothing in flight at the final round (every earlier projection delivered first, as a per-edge FIFO channel without redelivery does), by `plain_settle_iff` | `MergeProjection` over a channel that can reorder or redeliver is not settled by its channels, even under XU: `plain_stale_counterexample` (the supply federation: Common, XU and LocalCC hold, a drained run whose last send to the target came after the source's last change ends with a recalled product still listed, another drained run of the same events does not; `ChanConv false` holds, so only an outside flush repairs it, and versioned merging refuses the stale projection) | - (gap 21, narrowed) |
| Monotone cycles, over versioned channels | Not stated | | n/a (cyclic projection deployments are reported not certified) | The ghost survives versioned channels: `vchan_cyc_ghost` (the `dist_cyc_ghost` flag cycle; a disciplined versioned run with in-order fresh deliveries and a final round is drained and settled at the ghost, the same events give the least fixed point); every cyclic current-value run is a versioned channel run (`emb_run`, no hypothesis). Flush and reset epochs over channels are open (a pre-reset projection still in flight is a hazard the current-value epoch theorems do not see). - (gap 21, open on cycles) |
| Monotone cycles, repair alone (no events): does every fair propagation schedule from a stale start settle at `Lfp l` | From a sound start (`h0 <= F l h0`) and a fair schedule, the run reaches `Lfp l` iff `h0 <= Lfp l`: `q1_sound_iff` (from a sound start every fair schedule settles at the least fixed point above `h0`: `q1_sound_settles`); every fair schedule from every start settles at `Lfp l` iff `F l` has exactly one fixed point (with a top element and the dual step laws): `q1_unique_iff` | Any start at or below `Lfp l`: `q1_below` (bottom: `q1_from_bot`) | n/a (gsm reports cyclic projection deployments not certified, gsm #34) | Qualifiers: at or above a fixed point other than `Lfp l` no schedule reaches `Lfp l` (`q1_stuck`, a ghost); from an arbitrary stale start the fixed point reached depends on the schedule (`dist_schedule_dependence`), and a fair schedule on a monotone 3-cycle never reaches a quiescent state (`dist_ring_livelock`). - (closed by #62) |
| Monotone cycles, events, with reset epochs (a barrier resets every shared value to bottom, then propagation to quiescence, no event inside the epoch); compared after a final epoch | Every run agrees with the FedMachine iff the event's local outcome is the same at every reachable stale state as at its flushed form (`XUcR`): `epoch_agree_iff`; all interleavings agree iff `XUcR` and the FedMachine converges from the flushed start: `epoch_conv_iff` (the cyclic form of `dist_exact_tc`) | gsm's per-target C1cyc and C2cyc over a set covering the reachable shared values (the start's values, bottom, the morphism images and what events write: `hs_reach`) give both: `lens_epoch`; an epoch computes the flushed state: `EP_run`, `epoch_flush` | No epoch mode; cyclic projection deployments are reported not certified (gsm #34) | Qualifier: the reset must be a barrier; a staggered reset re-creates the ghost in one propagation step (`dist_cyc_epoch_fix`, which also shows epochs repair the `dist_cyc_ghost` federation from every start). - (closed by #62) |
| Monotone cycles, events, no resets, every reachable state at or below `Lfp` of its locals (`LowR`); compared at quiescent states | Every reachable quiescent state is the FedMachine state iff `XUcR`: `low_agree_iff`; all quiescent interleavings agree iff `XUcR` and FedMachine convergence from the flushed start: `low_conv_iff` (`LowR` gives `FlushR` and `NoGhostR`: `low_flush`, `low_noghost`) | Per event: inflationary events (locals only rise, no shared value raised) give `EvLow` (`infl_evlow`), and `EvLow` from a start at or below `Lfp` gives `LowR` (`evlow_lowr`); gsm's C1cyc and C2cyc over a covering set plus `LowR`: `lens_quiet` | n/a (as above) | - (closed by #62) |
| Monotone cycles, events, no resets, general (no `LowR`); compared at quiescent states. The certified property is that the deployment flushes, every reachable quiescent state agrees with the FedMachine, and quiescent interleavings agree (`FlushR /\ DAgreeQ /\ DConvQ`, or with `FairFlushR`) | Unconditional (nothing on the left of the iff but the property): `FlushR /\ DAgreeQ <-> XUcR /\ FlushR /\ NoGhostR` (`flush_agree_iff`); `FlushR /\ DAgreeQ /\ DConvQ <-> XUcR /\ FMConv /\ FlushR /\ NoGhostR` (`flush_fed_iff`); the same with `FairFlushR` (`fair_agree_iff`, `fair_fed_iff`). Each right-hand conjunct is necessary, by an instance where it alone fails: `XUcR` (`copy_xu_fails`), `FMConv` (`fm_conv_fails`), `FlushR` (`flip_noflush`), `FairFlushR` (`flip2_fair_livelock`; `ring_exact`, the ring of `dist_ring_livelock`, has `FlushR` without `FairFlushR`), `NoGhostR` (`ghost_exact`, the `dist_cyc_ghost` federation). `FlushR` exactly: a fair run reaches quiescence iff it reaches a sound state (`h <= F l h`): `fair_flush_sound_iff`; for words `flushat_sound_iff`; reachable forms `fairflushR_sound_iff`, `flushR_sound_iff`. `NoGhostR` exactly: iff the start and every post-event state (an event applied at a reachable state) are ghost-free: `noghost_event_iff` (every reachable ghost comes from the start or a last event whose output is not below `Lfp` of its locals: `ghost_witness`); iff some invariant closed under events and propagation contains no quiescent ghost: `noghost_inv_iff`; a sound state is ghost-free iff it is low: `ghostfree_sound_iff`, so under `SoundR` (every reachable state sound) `NoGhostR <-> LowR` (`noghost_soundr_iff`), `LowR` is checked per event (`lowr_post_iff`), and `DAgreeQ <-> XUcR /\ LowR`, `DAgreeQ /\ DConvQ <-> XUcR /\ LowR /\ FMConv` (`soundr_agree_iff`, `soundr_fed_iff`) | `FlushR` (as `FairFlushR`, which implies it: `fairflushR_flushR`): sandwiched, sound or low reachable states (`sandr_fairflush`, `soundr_fairflush`, `lowr_fairflush`; `sand_settles`, which recovers `q1_below` and `q1_sound_settles`); per event `evsand_sandr`, `evsound_soundr`, `evlow_fairflush`, and inflationary events that write no shared value keep soundness (`infl_evsound`); gsm starts `Nc t` are sound and low (`nc_sound_low`); per network, every single propagation step yields a sound state (`step_sound_fairflush`). `NoGhostR`: an invariant whose states have one-fixed-point locals or are low (`unique_or_low_noghost`, recovering `uniq_noghost` and the `EvLow` route: `unique_or_low_recovers`); `EvLow` (`infl_evlow`). gsm's C1cyc and C2cyc over a covering set reduce the certified property to `FlushR /\ NoGhostR` (or `FairFlushR /\ NoGhostR`): `lens_noreset_iff`, `lens_noreset_fair_iff` | n/a (gsm reports cyclic projection deployments not certified, gsm #34 and #36; no check for `FlushR` or `NoGhostR`) | Qualifiers: flushability is part of the certified property, not a hypothesis on it: `DAgreeQ` and `DConvQ` speak only of quiescent states, so they say nothing about a deployment that never quiesces (`flip_noflush`: one fixed point, `XUcR`, `FMConv` and `NoGhostR` hold, and no propagation word from the start reaches quiescence). None of `SoundR`, `SandR`, `LowR` is necessary for `FairFlushR` (`ghost_exact` reaches a state that is neither sound nor sandwiched, and `FairFlushR` holds), and `LowR` is not necessary for `NoGhostR` without `SoundR` (`ghostfree_unsound`). Non-vacuity beyond `EvLow` and global uniqueness: `latched_exact`; a clear that resets only its own shared slot still ghosts (`local_reset_ghost`: the reset must cover the cycle, as in `lens_epoch`). `NoGhostR` is not necessary for `DConvQ` alone: from a FedMachine normal form, `FairFlushR`, `XUcR`, `FMConv` and `DConvQ` hold, every quiescent interleaving agrees, and each sits on a ghost, so `NoGhostR` and `DAgreeQ` fail (`conv_ghost_normal`). Convergence is exact jointly with agreement here; convergence alone is the next row. - (closed by #64; was gap 1) |
| Monotone cycles, events, no resets: convergence among quiescent interleavings alone, without agreement with the FedMachine (`FlushR /\ DConvQ`, a common ghost allowed) | Unconditional: `FlushR /\ DConvQ <-> FlushR /\ FlushDetR /\ FlushXUR /\ QMConv` (`conv_quiet_exact`; with `FairFlushR`: `fair_conv_exact`). The canonical state is the one propagation settles in, read as a relation (`Flushes t q`: a propagation word takes `t` to the quiescent `q`), in place of `Lfp`: `FlushDetR` (E: every reachable state flushes to at most one quiescent state; checked at the start and each post-event state, `flushdet_event_iff`), `FlushXUR` (S: an event at a reachable stale state and at its flush flush to a common state), `QMConv` (H: the quiescent machine, flush then event then flush, gives trace-equivalent event sequences the same outcomes). No lattice hypothesis is used. Each conjunct is necessary, by an instance where it alone fails: `FlushR` (`flip_conv_noflush`), `FlushDetR` (`fork_conv_nodet`: from a stale start one word reaches `Lfp`, another the ghost), `FlushXUR` (`copy_conv_noxu`), `QMConv` (`fm_conv_noqm`). Ghost-free case: under `FlushR /\ NoGhostR`, `FlushDetR` holds, `FlushXUR <-> XUcR`, `QMConv <-> FMConv (Nc s0)` (`noghost_flushdet`, `noghost_flushxu_iff`, `noghost_qmconv_iff`), recovering `quiet_conv_iff` (`quiet_conv_recovered`) and `flush_fed_iff` (`flush_fed_recovered`); agreement is convergence plus fidelity to `Lfp`: `FlushR -> (DAgreeQ /\ DConvQ <-> DConvQ /\ NoGhostR)` (`agree_conv_noghost`) | `XUcR`, `FMConv` and `NoGhostR` give `DConvQ` with no `FlushR` (`quiet_conv_suff`); under `SoundR`, `FlushR` and `FlushDetR` are free and `DConvQ <-> FlushXUR /\ QMConv` (`soundr_conv_iff`; a sandwiched state flushes only to the least fixed point above its sound lower bound, `sand_flushdet`) | n/a (gsm's C1cyc and C2cyc are stated against `Lfp`; they discharge `XUcR` and `FMConv`, the ghost-free forms, and nothing is given for `FlushXUR` or `QMConv` when a ghost is reachable) | Qualifiers: no resets (the backward direction fails with resets: a reset moves a state's flush to `Lfp` without an event; the forward direction holds for every `r`). None of `XUcR`, `FMConv`, `NoGhostR` is necessary for convergence alone: `ghost_conv_not_fed` (from a ghost start, a copy event on A and a raise on B: `FairFlushR` and `DConvQ` hold, `XUcR`, `FMConv (Nc s0)`, `NoGhostR` and `DAgreeQ` fail). `conv_ghost_normal` is an instance (`conv_ghost_instance`: the interleavings agree on the quiescent machine's ghost). The conditions are reachable properties, as in `flush_fed_iff`. - (closed by #90; was gap 14) |

## 9. Monotone cycles: the repair normal form

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Unique repair normal form, finite height or ACC | Unconditional inside the regime: `cyc_N_lfp`, `cyc_N_unique`, `cyc_sweep_order_independent`, `kleene_lfp`, `lfp_unique`, `chaotic_reaches_lfp`, `chaotic_limit_unique`, `chaotic_acc_reaches_lfp`, `kleene_acc_lfp` | Monotone `Phi` (`fed_def_lattice_shared_cyclic_hyps`) | `verifyMonotone`, `verifyMonotoneVisited` (cover-step monotonicity over visited states) | - |
| Same on a complete lattice without ACC | Existence of the lfp is classical Knaster-Tarski: paper only (`thm:monotone-cycles` (a)). Mechanized: double-negated existence under ACC (`kleene_acc_lfp_nn`), the Kleene supremum when `Phi` preserves it (`kleene_sup_lfp`), and, on any partial order with bottom, the exact condition for the lfp to be reached by iteration (next row) | Continuity at the Kleene chain | n/a: gsm's lattices are finite, so they satisfy ACC | **design** (the axiom-free gate excludes classical Knaster-Tarski; the constructive scope is ACC, or an lfp reached by iteration) |
| Finite reachability of the lfp by iteration | The lfp is reached at a finite stage iff the Kleene chain is eventually constant iff productive Kleene steps from bottom are strongly normalizing iff there is no infinite strict ascent along the chain: `kleene_reach_exact` (any partial order with bottom, monotone `f`, decidable stabilization), `kleene_reaches_iff`, constructive `kleene_reach_nn`; chaotic schedules and gsm's round-robin reach it iff Kleene does: `chaotic_reach_exact`, `rounds_reach_by_kleene` | ACC (`kleene_reach_of_acc`, `kleene_reach_of_acc_below`); finite height (`kleene_reach_of_finite_height`). ACC is not necessary (`acc_not_necessary`); "every schedule terminates" is strictly stronger (`chaotic_sn_strictly_stronger`) | `kleeneCap` from the lattice bound | - (closed by #50) |
| Validity of the lfp | For a reached lfp: valid iff some Kleene iterate is valid: `lfp_valid_iff_reached`; under ACC with no reachability hypothesis: `lfp_valid_exact`; for gsm's normalizer: `Ncyc_valid_exact`; any fixed point is valid iff the images are valid at it: `fixed_valid_iff_images`. Bottom validity is the case `k = 0` (`net_lfp_valid_recovered`) and is not necessary (`bottom_validity_not_necessary`); the reachability qualifier is needed (`lfp_valid_iff_needs_reach`) | Every component valid with bottom shared values (`net_lfp_valid`); gsm's visited-image check (next column) | Image validity over visited states (`verifyMonotoneVisited`), now proved sound: it makes every fixed point valid (`gsm_check_fixed_valid`), hence the lfp (`gsm_check_lfp_valid`) and gsm's cyclic normal form (`gsm_check_Ncyc_valid`), with no bottom-validity hypothesis. Sufficient, not necessary (`gsm_check_not_necessary`); incomparable with bottom validity | - (closed by #50; the earlier caveat that gsm's check was not the one Coq proves sufficient is resolved) |
| The paper's monotone repair inside the non-monotone engine (non-monotone `rho_Fed^J` of a sub-federation) | n/a | `fed_rem_convexity_corrected` (phase 1 and `Phi` monotone in locals) | n/a | - (`fed_rem_convexity_refuted` corrects the paper) |

## 10. Monotone cycles: event order

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| All trace-equivalent sequences converge from `s0` | GC at reachable federated states: `gc_iff`, `cyc_events_converge_iff`, `net_events_converge_iff`, `fed_thm_monotone_cycles_events_corrected` | C1cyc and C2cyc over a set containing every normal form's shared values: `cyc_check_gc`, `cyc_check_converges`, `cyc_check_gc_lfp` (image sets over valid sources suffice); read footprint `footprint_c1`; global variant `lfp_commute_gc` | Per-target C1 and C2 with image sets over every valid source state (`FedReport.Checks`, citing `cyc_check_gc_lfp`) | GC has no per-edge reduction; neither cheap condition is necessary. Not oracle-certified. - |
| Multi-edge targets | Same GC | Per-edge C1 plus M1 compose: `multi_edge_c1`, `multi_edge_gc`, `multi_edge_converges`; M1 needed: `m1_necessary`; without M1, check every local part: `multi_edge_c1_free` | gsm checks C1 against the joint image of all incoming edges (C1cyc directly), not the per-edge route | - |
| Resolver targets on a cycle | Same GC | C1 over the resolver image `R`: `resolver_joint_c1`; per-source images insufficient: `resolver_edge_insufficient` | Joint image `R` over every combination of valid source states | - |

## 11. Non-monotone cycles, invertible transports

Model: the shared fiber is the group `G` acting on itself (regular action); edges are transports by
group elements.

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Does a consistent state exist (`H^0` non-empty) | The labeling is a coboundary (`H^1 = 0`): `section_iff_coboundary`; per fundamental cycle: `cycle_basis_criterion`, `sat_iff_trivial_holonomy`; single cycle: `fixed_point_iff_trivial_holonomy` | Trivial holonomy of each fundamental cycle of a spanning tree | `DiagnoseCycle` on one cycle (sound refuter on the regular action: `c15_regular_definitive`) | Regular action needed (`nonfree_holonomy_counterexample`). - |
| Coordination-free convergence to a unique normal form, given an authority root | `H^1 = 0` iff, for every root value, the root-driven implementation has a unique consistent state reached by every propagation order: `prop_minimal_qualified_iff` | as above | Not implemented: gsm has no root-driven coordination-free mode for cycles; a non-monotone cycle fails `Build` | - for the theory; gsm gap (holonomy-minimal plan "proposed, not implemented", `HOLONOMY-COORDINATION-DESIGN.md`) |
| No authority root (every edge a writer), single coherently oriented cycle (`n >= 1`) | A consistent state exists, and every state reaches one by a fair round, iff the holonomy is trivial: `rootless_section_iff_holonomy`, `rootless_nf_exists_iff`; with trivial holonomy, the reachable consistent state is unique iff `\|G\| = 1`, for all schedules and for fair ones: `rootless_unique_iff`, `rootless_unique_iff_general`; existence and uniqueness from every initial state iff `\|G\| = 1`: `rootless_unique_normal_form_iff` | none needed (the iff is decidable from the labels) | n/a | Corners: `n = 0` is unique over Z/2 (`rootless_selfloop_unique`); a non-coherently oriented triangle is unique (`rootless_orientation_matters`: a registry with no in-edge is a de facto root). Both corners are instances of the network theorems below: each has a de facto root (`selfloop_recovered`, `orientation_matters_recovered`). - (closed by #48) |
| No authority root, any finite invertible network (several cycles, mixed orientation, sources feeding cycles): which consistent states a start reaches | A section `sg` is reached from `t0` (by some schedule, equivalently by some fair one) iff every registry has an upstream registry, possibly itself, where `sg` and `t0` agree: `net_reachable_iff`, `net_reachable_fair_iff`; a consistent state is reachable from `t0` iff such a section exists: `net_nf_from_iff`. The mechanism: relative to any section, firing an edge copies the offset `sg(u)^-1 t(u)` downstream unchanged (`net_origin`) | none needed | n/a | - (closed by #91; was gap 2) |
| No authority root, any finite invertible network: existence from every start; uniqueness; both | Existence from every start (by a fair schedule) iff `H^1 = 0` (a section exists) and (every weakly connected component has a registry upstream of all of it, `co_rooted`, or `\|G\| = 1`): `net_nf_exists_iff` (`co_rooted_iff_roots`). Uniqueness of the reached consistent state, for all schedules and for fair ones, iff (`H^1 = 0` implies every component contains a de facto root, a registry with no in-edge from another registry, or `\|G\| = 1`): `net_unique_iff`, `net_unique_fair_iff`. Both iff `H^1 = 0` and (every component has a de facto root upstream of all of it, that is an authority root, or `\|G\| = 1`): `net_unique_normal_form_iff`, with `authority_cover_iff`. Forms without the `\|G\| = 1` disjunct over a nontrivial group: `net_nf_exists_iff_nontrivial`, `net_unique_iff_nontrivial`, `net_unique_normal_form_iff_nontrivial`. Strongly connected with an edge between distinct registries: existence iff `H^1 = 0`, uniqueness iff (`H^1 = 0` implies `\|G\| = 1`): `net_strong_iff`. The single-cycle row is recovered: `cycle_nf_exists_recovered`, `cycle_unique_recovered`, `cycle_unique_general_recovered`, `cycle_unique_normal_form_recovered` | The structural conditions are reachability conditions on the edge list (decidability proved: `closure`, `reach_dec`; no complexity bound mechanized); `H^1 = 0` as in the first row | n/a | Qualifiers, proved over Z/2: the existence obstruction is `H^1` of the whole underlying graph, not holonomy inside strongly connected components (`rootless_global_holonomy`: an authority root, no directed cycle, no consistent state); a coboundary does not give existence from every start (`rootless_mixed_square`: mixed orientation, two sources, unique but some start reaches nothing); a coherently oriented cycle with `\|G\| = 2` still has a unique normal form when a source feeds it (`rootless_source_feeds_cycle`); several cycles: `rootless_figure_eight` (two cycles sharing a registry), `rootless_cycle_feeds_cycle` (only the source component is free). - (closed by #91; was gap 2) |
| What must be coordinated, relative to a spanning tree | Exactly the unbalanced non-tree edges: `plan_exact`, `coordination_needed`; soundness `coordinated_sound`, `coordinated_unique_nf`; balance is static `balanced_any_section`; root dependence `root_choice_matters` | Coordinate all unbalanced edges | `CoordinationPlan` cuts a feedback edge set by DFS (every cycle, not only unbalanced ones) and names the authority; `BuildCoordinated` | gsm's plan is sound but not the holonomy-minimal one. - |
| Event order under the coordination | From a start consistent with the driving network, J-trace-equivalent sequences all converge iff independent root events commute at every root value reachable by root events: `coordinated_events_exact`, `coordinated_perm_exact`, `coordinated_events_exact_plan`; from every start iff they commute at every value: `coordinated_events_exact_global` | Root events commute at every value: `coordinated_events_converge` (recovered as `coordinated_events_converge_recovered`; not necessary for a fixed start: `old_condition_not_necessary`) | `BuildCoordinated` runs the acyclic C1 and C2 on the residual (on the driving network C1 holds unconditionally, `coordinated_c1_static`, and C2 is the root-event condition, `coordinated_c2at_iff`) | - (closed by #47) |
| **Optimization:** minimum coordination over all trees and roots | For a connected network (some plan rooted at `r` exists), any group with decidable equality, regular action: some plan rooted at `r` coordinates at most `k` edges iff some feasible coordination deletes at most `k` edges, so the minimum plan cost over rooted spanning trees is the group feedback edge set number: `plan_min_exact` (lower bounds `plan_min_lower_iff`; attained, `plan_min_attained`; the same for every root, `plan_min_root_independent`; with membership deletion on a duplicate-free network, `plan_min_exact_set`). Each plan's coordinated set is feasible (`plan_coord_feasible`), and every feasible set yields a plan no costlier (`feasible_plan`; the residual need not be connected). Earlier pieces: `edge_disjoint_lower_bound` (per plan: `plan_cost_ge_disjoint`), `edge_disjoint_min`, `min_G_ge_min_image`, `theta_separation` (`S_3`: `min_G = 2 > 1 = min_{G^ab}`); over `S_3` the tree choice matters (`s3_tree_choice`) | Unbalanced edges of any rooted tree: size at most `betti_number` (`plan_cost_le_betti`) | `CoordinationPlan` (upper bound, "not necessarily the minimum"; it cuts every cycle, not the minimum-cost plan) | Qualifiers: connectivity is needed (`plan_min_connected_needed`; on a disconnected network the theorem applies per component), and `NoDup` for the set form (`plan_min_nodup_needed`). **hardness** (mechanized reduction): a graph `H` with every edge labeled by the Z/2 flip has a feasible coordination with `\|F\| + k <= \|H\|` iff `H` has a cut of at least `k` edges (`maxcut_reduction`; plans: `maxcut_plan_reduction`; same size: `signed_size`), so minimum coordination is NP-hard already over Z/2 and in the plan model, with NP-completeness of Max-Cut cited (Karp 1972); a plan is the NP certificate (`section_decide`). - (closed by #72; was gap 10) |

## 12. Non-invertible transports

Reading A (the constraint reading) in the terms of the research note
[docs/LOSSY-NETWORKS.md](docs/LOSSY-NETWORKS.md): each
edge is an equation and the consistent states are the sections (`msection`).

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Single cycle: does a consistent state exist | Loop composite has a fixed point: `thm_obstruction_general`, `sections_are_fixed_points`; "some seed reaches a fixed point": `thm_obstruction_reachable`, `reaches_fixed_iff_section` | Finite fiber: `g^N x0` fixed for some seed (`diagnose_bounded`, `diagnose_dichotomy`) | `DiagnoseCycle` | - |
| Reading the diagnostic | No section iff no seed reaches a fixed point: `c15_exact_refuter`; one seed is definitive only when fixed points are all-or-nothing (`c15_free_definitive`) | A settling seed proves existence: `c15_convergent_result_sound` | `DiagnoseCycle` tests one representative seed | gsm's one-seed result is not a refuter off the regular action (`c15_definitive_claim_false`); documented. - |
| Graph with an out-arborescence from a root: consistent state with a given root value | Driven state satisfies every non-tree edge: `rooted_criterion` (recovered from the root-set form: `rooted_criterion_recovered`); uniqueness `out_tree_unique` | Delete every non-tree edge: `rooted_coordination_suffices` | n/a | Edge need depends on the root value (`noninvertible_balance_not_static`). - |
| General graph (no spanning root): does a consistent state exist | Root sets are exactly the sets with an outward spanning forest: `root_set_iff_forest`. For any root set and spanning forest, a section exists iff some root assignment drives a state satisfying every edge: `root_set_criterion_graph`; with root values fixed: `root_set_criterion_values`; agreement form (two roots agree wherever both reach): `root_set_agreement`; decided by search over the product of root domains: `root_set_decide`. Existence is NP-complete in general: the 3-SAT reduction of [LOSSY-NETWORKS.md](docs/LOSSY-NETWORKS.md#32-the-reduction-from-3-sat) section 3.2 is mechanized in `LossyHardness.v` (#57): a network `net f` built from a 3-CNF `f` has a section iff `f` is satisfiable (`net_section_iff_sat`), sections and satisfying assignments correspond one to one and have equal counts (`net_bijection`, `net_count`, a parsimonious reduction), the construction is linear (`net_size`: `6\|f\| + 1` edges, each a 9-entry table), and a section is certified by an edge-by-edge check of one value per vertex (`np_certificate`, membership in NP). NP-completeness follows from these by the standard argument; the gadget is needed (`no_filter_trivial`, `no_pin_trivial`) | One root (`rooted_criterion`) is polynomial | n/a | **hardness** (mechanized reduction): no efficient exact criterion unless P = NP; the exact one is mechanized. - (closed by #54; reduction #57) |
| Counting and uniqueness given root values | Sections correspond bijectively to consistent root assignments: `root_set_bijection`, counted by `root_set_count`; sections are determined by their root values (`out_forest_unique`) | n/a | n/a | - (closed by #54) |
| Event order under root-set coordination (non-invertible driving forest) | From a start consistent with the forest's driving network, J-trace-equivalent sequences all converge iff, for each root `r`, `r`'s independent events commute at every value reachable from `s0 r` by `r`'s own events: `forest_events_exact`; permutation form `forest_perm_exact`; from every consistent start iff they commute at every value, iff static C1 and C2: `forest_events_exact_global`, `forest_global_iff_static`. One condition per root: roots never interact (`forest_runs_by_root`, `forest_cross_commute`, `forest_run_single_root`; events on driven registries are overwritten, `forest_driven_noop`), and the only coupling is through constraints (`forest_runs_kept`). The group case is recovered (`coordinated_events_exact_recovered`) | Every root's events commute at every value (`forest_events_exact_global`); C1 holds unconditionally on the forest (`forest_c1_static`) | n/a | Qualifier: commuting at the start value is not enough (`tw_reachable_matters`). - (closed by #59) |
| Loops versus merges: what an obstruction to a section looks like | Invertible (group labels, regular action), on any finite edge list with no spanning-tree or connectivity premise: a section exists iff every closed walk (edges crossed in either direction) has trivial holonomy, iff walk labels are path-independent, iff the labeling is a coboundary; two directed paths with different labels close into a closed walk with non-trivial holonomy and rule out a section (`invertible_merge_is_holonomy`, `holonomy_free_section`, `section_transport`; per fundamental cycle `fundamental_cycles_holonomy`). Harary's balance theorem, proved for every finite signed graph (parallel edges and self-loops allowed) as the Z/2 instance: a switching to all-positive exists iff no closed walk carries an odd number of negative edges (`harary_balance`). Lossy: the theorem pair `obstruction_loop_vs_merge`: every invertible tree has a section and trivial holonomy, while the C22 tree has no section although each of its two edges alone has one, with minimum coordination 1 | n/a | n/a | Qualifier: `harary_balance` is stated for closed walks; the classical form with simple cycles (every odd closed walk contains a negative cycle) is not mechanized. "Tree" in `obstruction_loop_vs_merge` is `CohomologyGraph.tree` (grown leaf by leaf from a root, either orientation); forests are covered by `holonomy_free_section`. - (#80) |
| Rootless propagation (resolver reading B): does every fair order reach one consistent state | **No exact condition mechanized** for non-invertible labels. The Boolean instances `copyback_without_authority` and the negation loop are invertible (section 11). Sufficient certificates for E (#80, `SignedResolver.v`), under an explicit resolver semantics: one value set with a least and a greatest element and finite height, per-vertex resolvers on a lens-structured state, fair asynchronous schedules, and a signed **global** interaction graph certifying the resolvers (`Resp`: each resolver reads only its in-neighbors, `resp_reads_in_neighbors`, monotone in positive and antitone in negative inputs, signs fixed across all states). With a switching (balance): from every start at or below the switched least fixed point, every fair schedule settles there and E (`EffectiveCanon`: Settlement and CanonicalFidelity, canonicalizer the constant least fixed point) holds (`signed_settlement`, `signed_settlement_harary`); with at most one fixed point as well, from every start (`signed_fidelity`, `signed_fidelity_harary`). Each hypothesis is shown needed: balance (`neg2_no_fixed_point`, `unbalanced_unique_oscillates`), the start condition (`copyback_ghost`, `toggle_ghost`: fidelity; `ring_needs_low_start`, `ring_low_start_E`: fair settlement and fidelity), the greatest element (`flip_needs_top_resolver`), signability (`xor_no_certificate`, `cyc3_unsignable`). Local (state-dependent) interaction graphs, Boolean value set, every `n` (#83, `LocalSigned.v`; `G(x)` is the discrete Jacobian at `x`, cycles elementary): no positive cycle in any `G(x)` gives at most one fixed point (`rrt_sub`, `local_fidelity`, Remy, Ruet and Thieffry 2008) and CanonicalFidelity from every start with no global sign hypothesis (`local_fidelity_canon`), and replaces the uniqueness hypothesis of `signed_fidelity` (`local_signed_fidelity`); no negative cycle in any `G(x)` plus out-degree at most one, which is non-expansiveness (`outdeg_nonexpansive`), or plus one vertex on every local positive cycle, gives from every state an update word reaching a fixed point, hence E's Settlement from every start (`richard_t3`, `richard_t4`, Richard 2011, Theorems 3 and 4); no cycle in any `G(x)` gives a unique fixed point reachable from every state and E from every start (`sd_path`, `shih_dong_E`, Shih and Dong 2005). Breaks: `local_neg_free_no_fixed_point` (6 vertices, no local negative cycle, no fixed point; 6 is minimal by Tonello, Farcot and Chaouiya, cited), `ring_local_conditions` (Theorems 3 and 4 hold, two fixed points, a fair schedule that never settles), `shih_dong_not_fair` (no local cycle, E holds, a fair period-8 schedule never settles). Fair settlement under no local cycle (A) plus out-degree at most one (B) (#92, `LocalFairSettlement.v`, every `n`): (B), with (A) at one state of a synchronous periodic orbit, makes the orbit a fixed point (`sync_orbit_fixed`); so (A) and (B) make every synchronous orbit reach the unique fixed point within `2^n` steps (`sync_simple`, the conclusion of Shih and Ho 1999, Theorem 3.1, by a different proof); (B) alone makes the number of unstable vertices non-increasing along asynchronous runs (`ucnt_mono`); with (A), at most one unstable vertex at a state rules out every closed asynchronous run through it that changes the state (`one_token_closed`), so every fair schedule from such a start, and every fair run that ever reaches one, settles at the unique fixed point (`one_token_fair_settlement`, `fair_settles_once_one_token`); an acyclic asynchronous state graph gives fair settlement at the unique fixed point from every start (`fair_settles_closed`, `fair_settlement_of_acyclic`). Needed: (B) (`outdeg_needed`: Shih and Dong's network has (A), a synchronous 3-cycle and a fair schedule that never settles), no local positive cycle (`no_neg_not_enough`, the positive 3-ring), no local negative cycle (`no_pos_not_enough`, the negative 3-ring: no fixed point); non-vacuity `shih_ho_instance` (Shih and Ho's 4-vertex example: (A), (B), a cycle in the global graph, an acyclic asynchronous state graph) | Balance plus "no positive directed cycle" (Thomas's sign condition) leaves no directed cycle at all (`balanced_no_positive_acyclic`), so on balanced graphs the cited sign route to uniqueness reduces to Robert's acyclic case (mechanized: `rb_robert_boolean`); uniqueness stays a hypothesis (`unique_pos_cycle`, whose every certificate has a positive cycle: `unique_pos_cycle_every_certificate`). The local route is strictly weaker than the global one for fidelity: global implies local (`global_to_local`), and `local_weaker_than_global` has no cycle in any `G(x)` while every global certificate has a positive 2-cycle, and E holds | n/a (a non-monotone cycle fails `Build`) | **open** (medium for Boolean fibers, large in general; [LOSSY-NETWORKS.md](docs/LOSSY-NETWORKS.md#p2-rootless-convergence-in-reading-b-the-runtime-model) P2). The certificates are sufficient, not an exact characterization. Qualifier: the local conditions certify E with Settlement in its existential (flush) form, some update word reaching a fixed point, and not fair-schedule settlement (the analogue of `FairFlushR` in section 8): `shih_dong_not_fair` and `ring_local_conditions`; from every start, fair settlement still comes only from the global switching (`signed_settlement`, `signed_fidelity`, `local_signed_fidelity`); from local conditions alone it is mechanized under (A) and (B) for starts, or runs that reach a state, with at most one unstable vertex (#92). Open: fair-schedule settlement under (A) and (B) from every start, that is, no closed asynchronous run whose states all have two or more unstable vertices (computational evidence, not mechanized: no asynchronous state-graph cycle for n = 3 to 6, [research/gap3-fair-settlement](research/gap3-fair-settlement/README.md); not found in the literature searched, and Shih and Ho 1999 treat synchronous iteration only), multivalued local interaction graphs (Richard and Comet 2007, cited), value sets without bounds, and an exact condition |
| **Optimization:** minimum coordination (fewest edges whose deletion leaves a section; edges deleted by position, so parallel copies are distinct) | `F` is feasible iff the residual passes the root-set criterion, for any root set and spanning forest of the residual: `lfeasible_root_set`, `lfeasible_iff_root_set`; the minimum is the least `\|F\|` whose residual passes it: `lmin_root_set` (unique: `lmin_unique`). Decided on a finite fiber with decidable equality: `lmin_decide` (`is_lmin G k <-> lmin_b G = k`), `lmin_b_correct`, `lmin_le_b_spec`, `lmin_exists`. On group-labeled networks under the regular action it is the group feedback edge set minimum: `lossy_min_is_gfes`, per fundamental cycle `lift_cycle_basis` | Delete the non-forest edges: `lossy_lmin_le_nontree` (an outward forest `T` followed by `X`: minimum at most `\|X\|`), `rooted_coordination_suffices` | n/a | Qualifier: the minimum is not cycle-based; every lower bound that sees only cycles is 0 on the C22 tree, whose minimum is 1 (`lossy_min_exceeds_cycle_bounds`, `c22_lmin`), while the same tree with group labels has minimum 0 (`c22_group_lmin`). **hardness** (mechanized reduction): the 3-SAT network has minimum 0 iff the formula is satisfiable and 1 otherwise (`lmin_zero_iff_sat`, `net_lmin_dichotomy`, `lmin_reduction`, with `\|net f\| = 6\|f\| + 1`), so "minimum `<= k`" is NP-hard already at `k = 0`, and no efficient algorithm approximates the minimum within any factor unless P = NP, by the standard argument; membership in NP by a checkable certificate (`min_le_np_certificate`, `min_cert_size`, `lmin_le_np`). The resolver-reading variants of [LOSSY-NETWORKS.md](docs/LOSSY-NETWORKS.md#p4-minimum-coordination-for-lossy-networks) P4 (delete edges until every remaining cycle is non-negative, or non-positive) are a different question, tied to rootless reading-B convergence (gap 3). - (closed by #70; was gap 11) |

## 13. The full nerve as a 2-complex

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Convergence (existence of a section) | Decided on the graph: `section_iff_coboundary` covers every labeled graph, so triangles add no convergence question; on the complex, a section exists iff the labeling is a coboundary iff it is cohomologous to the identity labeling, independent of the cells, and a labeling with a section is a cocycle of every complex on its graph: `nerve_section_iff_coboundary` | n/a | n/a | - |
| **Counting:** `H^1` with triangle relations (2-cells: closed walks, triangles the length-3 case) | Any group: for a spanning tree `T` with extra edges `X`, the tree-fixed labelings that are cocycles are exactly the generator assignments satisfying every cell's relation word; every cocycle is cohomologous to one; two are cohomologous iff simultaneously conjugate; conjugation preserves the relations: `nerve_H1_classification`. So `H^1(K; G)` is `Hom(<X \| relation words>, G)` modulo conjugation; there is no rank for non-abelian `G`, and the classification replaces it. Abelian `G`: classes are exactly the relation-satisfying assignments (`nerve_H1_abelian`). Over Z/2: exactly `2^((\|E\| - \|V\| + 1) - rank)` classes, `rank` the number of independent cell relations (`nerve_H1_Z2_count`; `rank` depends only on the solution set, `rel_rank_solution_set`); no cells recovers `betti_number` (`nerve_Z2_no_cells`); the count is `2^(\|E\| - \|V\| + 1)` iff the cells impose no relation (`nerve_Z2_full_iff`); a cell never raises it (`nerve_Z2_cell_lowers`). Gauge invariance: `hol_gauge`, `cocycle_gauge`. On the 1-skeleton: `H1_classification`, `gauge_fix`, `betti_number` | n/a | n/a | Scope: the dimension formula is mechanized over Z/2 only (for other coefficients the classification gives the solution-space description); that the presented group `<X \| relation words>` is the fundamental group of the complex is standard and not mechanized. Non-vacuity: `triangle_kills_flip`, `square_dependent_cell`. - (closed by #71; was gap 12) |
| Sheaf gluing (R1/R2 as the gluing axiom, positive assembly), registry-level site: open sets are sub-federations, a cover of `W` is a list of them concatenating to `W`, sections over `U` are the states consistent on `U` | Separation with no hypothesis (`separation`). Under R1, a compatible family of local sections glues to a section over the union, unique there, when the cover refines the constraints (`Refines`: every constraint inside the union has its whole footprint in one member): `gluing`, `sheaf_condition`; on a refining cover a family is the restriction of a global section iff it is compatible and local: `sheaf_exact`; for fixed data, gluing iff local consistency on every member implies consistency on the union: `gluing_iff_local_global`. Exact and uniform in the data: gluing holds on `C` for every R1 federation on the graph iff `Refines C` (`sheaf_iff_refines`; the value type inhabited with two distinct shared values). Certificates: restriction of the global normalizer to `U` is `U`'s certificate iff `U` is closed under sources (`cert_restrict_iff`; relative form for every `U`: `cert_restrict`); on a cover by closed members the certificates are a compatible family of local sections whose gluing is the certificate of the union, lands in its sections and fixes them (`cert_glue`, `cert_sheaf`, `cert_retraction`) | Closed covers refine every constraint (`cert_sheaf`); the condition is on members, not overlaps (`chain_glues`) | n/a (gsm's resolver check `verifyResolved` covers R1; gsm has no cover-level check) | Qualifiers, each broken by an instance: `Refines` (`triangle_fails`), R1 (`r1_failure`; without R1 the sections are not a presheaf of `U`-states), certificate compatibility on the overlap (`gluing_cex_overlap`, wrapping `gluing_order_dependent`). Version 1's "R2 makes the merged normal form land in the agreed valid set" holds with SC in R2's role, as the version-2 paper now says; validity preservation (M1/R2) is not the condition (`cert_needs_sc`). **paper** (narrowed, gap 13): the paper's variable-level site (two subsystems may write one variable) and the monotone-overlap (cyclic, least-fixed-point) site of Cat section 5 are not mechanized; on covers not closed under sources only the relative restriction equation is proved, with no sheaf condition for relative certificates. Narrowed by #73 |

## 14. Compositional collapse

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Acyclic, convex `J`: the effective registry converges | C1 and C2 at witnesses reachable inside `J`: `collapse_a_guarded_exact` | C1 and C2 on `J`'s events: `collapse_a_guarded`, `collapse_modular_converges` | `Federation.Embed`, certificates (`validateCertificates`, seam re-check) | - |
| Acyclic: outer network `N'` converges iff `N` does | `collapse_c_exact`, `collapse_c_guarded_iff`, `collapse_c_unguarded_iff`, `collapse_c_guarded_exact` | `collapse_c_guarded_c1_c2` | as above | - |
| Cyclic `J` with monotone repair (FedMachine): `N'`, with `J` normalized by its own least fixed point at its inputs, converges iff `N` does | The repair is triangular across the condensation, and blockwise least fixed points are the least fixed point (`bekic_lfp`, Bekic's principle; finite height on `J`), so the normal forms agree (`mono_collapse_nf`) and so do the runs (`mono_collapse_runs_agree`); `N'` converges iff `N` does iff GC: `mono_collapse_converges_iff`, `mono_collapse_exact` | GC per target over normal-form images (`cyc_check_gc_lfp`) | gsm flattens embedded cyclic subs (the outer federation must opt in to `AllowMonotoneCycles`); flattening and collapse give the same normal form (`mono_collapse_nf`) | Non-vacuity: `mono_collapse_instance` (a root feeding the flag cycle; the flattened side is gsm's `normalizeCyclic`). - (gap 5, closed) |
| Blocks of different engines, coordination-free (an upstream system and a block reading its current state; any DAG of blocks by iteration): from every start a unique normal form | The composite converges iff the upstream converges, the block reaches a quiet state from every start at every quiet input, and two quiet states of the block at a quiet input that its steps at the inputs the upstream passes through connect are equal: `compose_exact`; the normal form is the block-by-block one: `compose_collapse`. Engines: rootless `rootless_conv_iff` (`net_unique_normal_form_iff` read as convergence), `mixed_rootless_exact`; monotone `mono_block_interface_iff`, `mixed_mono_iff` | A black-box interface, closed under composition exactly: each block settles, with normal forms determined by inputs its steps preserve (`interface_closed`, `settles_conv`, `interface_lk`); for a monotone block, one fixed point at the presented input | n/a (gsm flattens) | Each conjunct necessary: `compose_needs_A`, `compose_needs_wn`, `compose_isolated_refuted` (every block converges in isolation, the composite does not); with real engines `mixed_ghost_refuted` (a rootless block's transient value lifts a monotone cycle to its ghost); the block is constrained only at quiet inputs (`compose_transient_free`). Non-vacuity `mixed_instance`, `mixed_mono_instance`. - (gap 19 (a), closed) |
| Distributed model, acyclic `J` interleaving with outer events: `N` converges iff `N'` (`J` propagating as one atom) does | `N` converges iff `N'` converges and XU holds at every state `N` reaches, `J` half-propagated included: `dist_collapse_iff`; `N'` exactly: `dist_collapse_exact`, through `dist_atoms_exact` (any atom set; `dist_exact` recovered, `dist_exact_recovered`); `N` converges -> `N'` converges: `dist_collapse_sound` | Static XU: `N` converges iff `N'` does (`dist_collapse_xu`) | `verifyProjectionMerge` (static XU) makes the two agree | `collapse_c`'s plain statement fails: `dist_collapse_refuted` (a chain, `J = {1, 2}` convex, Common; `N'` converges, `N` does not); XU alone does not give `N'`: `dist_collapse_needs_c2`. A cyclic `J` in the distributed model is not stated. - (gap 19 (b), closed for an acyclic `J`; open on cycles) |

## Conclusion

### The open gaps

Every row above is `-` (exact, or unconditional inside its regime), `hardness`, or one of these.
This is the list the headline's "a gap stated in the open" refers to. Numbering is kept from the
989-gate revision, so closed gaps keep their numbers.

Convergence:

| # | Regime and question | Kind | Size |
|---|---|---|---|
| 1 | Distributed model with propagation steps (section 8) | **closed**: acyclic #60 (`dist_exact`); monotone cycles with reset epochs and under `LowR` #62 (`epoch_conv_iff`, `low_conv_iff`); monotone cycles without resets, unconditionally, #64 (`flush_fed_iff`, `fair_fed_iff`, with `FlushR` and `NoGhostR` characterized) | n/a |
| 2 | Rootless invertible networks beyond a single coherently oriented cycle (section 11) | **closed**, #91 (`net_nf_exists_iff`, `net_unique_iff`, `net_unique_normal_form_iff`; the reachable set `net_reachable_iff`; single cycles recovered) | n/a |
| 3 | Rootless propagation on non-invertible networks in the resolver reading (section 12) | open; progress #80: sufficient signed certificates for E on the global interaction graph (`signed_settlement`, `signed_fidelity`, each hypothesis shown needed); progress #83: sufficient certificates on Boolean local interaction graphs for every `n` (`local_fidelity_canon`, `richard_t3`, `richard_t4`, `shih_dong_E`), which certify E with Settlement in its existential (flush) form and not fair-schedule settlement (`shih_dong_not_fair`, `ring_local_conditions`); progress #92 and #93: under no local cycle plus out-degree at most one, fair-schedule settlement in the synchronous form (`sync_simple`) and from every start with at most two unstable vertices (`one_token_fair_settlement`, `two_token_fair_settlement`); a general imbalance law under out-degree at most one, for every number of tokens (`LocalTokenBalance.v`: `bad_le_good`, at most half the tokens are bad relative to a fixed point; gap 3 still open). Open: fair-schedule settlement from local conditions in general (under those two conditions, runs with three or more unstable vertices), multivalued local graphs, value sets without bounds, an exact condition | medium to large |
| 4 | Event order under non-invertible root-set coordination (section 12) | **closed**, #59 (`forest_events_exact`) | n/a |
| 5 | Cyclic monotone sub-federations under collapse (section 14) | **closed** in the FedMachine model, `CompositionBlocks.v` (`bekic_lfp`, `mono_collapse_nf`, `mono_collapse_exact`: `N'` converges iff `N` does iff GC); the distributed form is gap 19 (b)'s residue | n/a |
| 6 | Single registry with enabledness that a compensation step can disable (section 1) | **closed**, #56 (`jcg_exact`) | n/a |
| 7 | State-based CRDT merges as an instance of the exact theorems (section 4) | **closed**, #58 (`merge_action_exact`, `cvrdt_on_exact`; the iff as exported: `cvrdt_on_iff`) | n/a |
| 8 | Least fixed points on complete lattices without ACC (section 9) | design exclusion: classical Knaster-Tarski is outside the axiom-free gate; gsm's finite domains satisfy ACC, so nothing gsm accepts depends on it | n/a |
| 9 | Infinite streams: eventual agreement (section 5) | design: the naive claim is refuted (`base_thm_convergence_transient_counterexample`) | n/a |
| 14 | Distributed model on monotone cycles without resets: an exact condition for convergence among quiescent interleavings alone (`FlushR /\ DConvQ`), when interleavings may agree on a common ghost (section 8) | **closed**, #90 (`conv_quiet_exact`: `FlushR /\ FlushDetR /\ FlushXUR /\ QMConv`, the layers of `flush_fed_iff` relative to the quiescent state propagation settles in; each conjunct necessary) | n/a |
| 15 | Delivery and enabledness off the replay model (sections 3, 5, 7, 8): (a) at-least-once delivery under declared independence `I` (a registry with `Independent` pairs, the FedMachine): closed, `AtLeastOnceDeclared.v` (`dalo_exact`, `safe_i_exact`, unordered retries `dalo_r_exact`, `NotIdempotent` placed by `dalo_notidem_needs_dedup` and `dalo_gsm_unlisted_safe`; the FedMachine by P1); (b) at-least-once delivery for stream processors: closed, `StreamAtLeastOnce.v` (`stream_alo_exact_free`; any enabledness `stream_alo_exact`; `stream_exact` recovered at duplicate-free lists); (c) causal or at-least-once event delivery in the distributed model: closed, `DistributedDelivery.v` (`dist_delivery_exact` for any prefix-closed delivery class; `dist_causal_exact`, `dist_alo_exact`, `dist_causal_alo_exact`; `dist_exact_tc` recovered); (d) buffered guards in federations, events that wait until enabled: closed, `FederatedGuards.v` (`fed_buffered_exact`, per edge `fed_buffered_edge`, any enabledness `fed_jcg_exact`; `fed_guarded_exact`'s condition recovered) | **closed** (all four parts); from the coverage pass ([COVERAGE.md](docs/COVERAGE.md), cells C3, C6, C8, C10) | n/a |
| 16 | Distributed propagation off its current hypotheses (sections 7, 8, 11): (a) events interleaved with rootless propagation on cyclic invertible networks with authority roots; (b) monotone cycles with ACC and no finite height (every distributed module assumes `rank_bound`); (c) local compensation as separate steps on cycles (`G_Fed` is acyclic only); (d) settlement of every fair update schedule on an acyclic network, Robert's asynchronous half: closed, `RobertFair.v` (`rb_robert_fair` in the distributed propagation model, with the round bound `rb_rounds` and the effective-step bound `rb_effective`; with finitely many events `rb_events`, `rb_event_schedule`, and the exact form `rb_fair_dist_exact`; the resolver model `rb_lens_robert`; Boolean networks with an acyclic global interaction graph `rb_robert_boolean`, Robert 1986 and 1995 as restated in Richard 2019, Theorem 1, through `fair_settlement_of_acyclic`; acyclicity needed, `rb_neg2_cycle`, `rb_copyback_cycle`, `rb_dist_cycle_needed`, and not necessary, `rb_converse_fails`) | open (narrowed: (d) closed; (a), (b) and (c) open); from the coverage pass (cells A2, B3, B4, B7) | medium |
| 17 | Rootless edge-writer dynamics beyond the regular action (sections 11, 12): lossy maps at in-degree two or more, where the edge-writer and resolver readings differ, and invertible maps under a non-free action. Quiescent states are reading-A sections, so existence is exact and NP-complete (`root_set_criterion_graph`, `net_section_iff_sat`); open: when every fair order reaches one, and uniqueness. Gap 3 is the resolver reading only | open; from the coverage pass (cells A3, A8, A10) | medium |
| 18 | Existence and counting in reading B without a spanning root (section 12): fixed points of the resolver map at in-degree two or more have no row; the polynomial reductions between the readings ([LOSSY-NETWORKS.md](docs/LOSSY-NETWORKS.md#how-the-readings-relate)) are conjectures, and mechanizing one would transfer `net_section_iff_sat` and `net_count` | open; from the coverage pass (cells A11, F7) | small |
| 19 | Composition beyond acyclic collapse (section 14): (a) coordination-free networks whose cyclic blocks use different engines (a non-monotone cyclic block feeding or fed by other blocks; gap 5 is the monotone case): closed, `CompositionBlocks.v` (`compose_exact` for any engines, each conjunct necessary, `compose_isolated_refuted`; `compose_collapse`; `interface_closed`; engines `mixed_rootless_exact`, `mixed_mono_iff`; `mixed_ghost_refuted`); (b) collapse preservation in the distributed model, a block whose internal propagation interleaves with outer events: closed for an acyclic `J` (`dist_collapse_iff`: `N` converges iff `N'` does and `XUR`; `dist_collapse_refuted`, `dist_collapse_needs_c2`; `dist_collapse_xu`). Residue: (b) for a cyclic `J` (the no-reset cyclic distributed model and reset epochs, where `J`'s atom would be its own flush to quiescence) | open (narrowed: (a) closed; (b) closed for an acyclic `J`); from the coverage pass (cells A14, B11, B13) | medium |
| 20 | **New axis**: reconfiguration inside a run. The topology (`src`) or the rules (`apply`, `rho`, morphisms) change while events or propagation are in flight; every other module fixes them, and gsm only checks that participants share one policy (`PolicyDigest`, `PolicyIdentityDigest`). Modeled in `Reconfiguration.v`: a run under configuration A, one switch (a migration `m` of the state, a translation `tau` of the A-events still in flight), then a run under B. Single registry, free delivery: at a quiescent barrier, exact (`barrier_exact`: B's condition after every quiescent reachable state, and A's normal forms agreeing after `rhoB_star o m`); when that map is injective on the quiescent reachable states, each side's own condition (`barrier_exact_faithful`), the claim this row made, with its qualifier (`forgetful_migration`: an unfaithful migration hides a divergence of A). Live, exact (`live_exact`): B's condition from `m s` for every reachable `s`, quiescent or not, plus the cross-configuration critical pairs (S1) an in-flight event commutes with the switch and (S2) the switch absorbs A's compensation, both up to B's repair; A's own condition is not a conjunct, and is implied exactly for a faithful migration (`live_exact_faithful`); `live_no_change` recovers `cc_exact_from`. Each conjunct is needed, with A converging and the barrier switch converging: `cap_raise` (a cap of 5 raised to 10 with in-flight adds; S2), `doubling_migration` (S1), `migrated_transient` (B's condition at a migrated non-quiescent state); non-vacuity `rescaled_cap`. Classification for gsm's planned `CheckMigration` (online, behind a barrier only, unsafe): unique (`classified_unique`), decidable on finite instances (`live_dec`; `barrier_dec_faithful` and `classify_finite` for a faithful migration). Federations under FedMachine semantics (topology and rules change; what is in flight is the buffered events): live, exact with B's condition at the migrated start only (`fed_live_exact`: C1R1 and C2R of B at `M s0`, plus `feq (M (applyF_A e t)) (applyF_B (tau e) (M t))` at reachable `t`); barrier, each side's `fed_exact` condition (`fed_barrier_exact`); adding an edge read by an in-flight event diverges live and not at a barrier (`late_edge`; `late_edge_fresh` non-vacuity). Residue (c), a local form of the barrier's A part for a migration that is not faithful, is closed in the deterministic model (section `Det`, gsm's runtime) by `ReconfigurationClosure.v`: A converges modulo M iff M agrees on every pair of the pair closure (seeds: two adjacent events in both orders at a reachable state; closed under applying one event to both components) (`amodm_swap_exact`, `amodm_closure_exact`), so `det_barrier_closure_exact` states the barrier with no faithfulness hypothesis; on finite instances the closure is a finite search that finds a witness iff A diverges modulo M (`amodm_witness_exact`), and the outcome is decided with no unknown case (`det_classify_complete`); `det_barrier_faithful` is recovered (`det_barrier_closure_faithful`); non-injective instances `merged_barrier` (barrier only, certified by the closure, A diverging) and `partial_merge` (unsafe, a closure witness). In the rewriting model, where compensation steps interleave, `AmodF` keeps its exact but non-local form. Residue: (a) a live switch in the distributed model, where propagation is in flight (projections sent under A merged under B); (b) declared independence, causal or at-least-once delivery across the switch | open (narrowed: single registry and FedMachine exact, at a barrier and live; (c) closed in the deterministic model; (a) and (b) open); from the coverage pass ([COVERAGE.md section 4](docs/COVERAGE.md#4-candidates-outside-the-axes)) | small to medium |
| 21 | **New axis**: propagation over channels (section 8). Projections delivered late, reordered or duplicated: gsm's `MergeProjection` (no order check, so a late or duplicate projection is merged as it arrives and a stale one merged after a newer one wins) and `MergeProjectionAfter` (rejects a projection whose version is not newer than the last one applied). Modeled in `ProjectionChannels.v`: on acyclic networks, exact over channel-reachable states in either mode (`chan_exact`, `chan_exact_global`, `chan_global_exact_roots`); versioned merging converges at drain exactly when it does after a flush (`vsettle_exact_cond`, `vsettle_cv`, `vsettle_xu_c2`), plain merging settles iff nothing stale is in flight (`plain_settle_iff`) and fails under XU (`plain_stale_counterexample`); on two-level networks the versioned condition is `dist_exact`'s (`vchan_emulate`, `vchan_twolevel_exact`). Residue: (a) whether versioned channels reach new stale combinations beyond two-level networks (chains, multi-source targets), that is whether `CXUR true` equals `XUR` there; (b) cycles: the ghost survives versioned channels (`vchan_cyc_ghost`), and flush or reset epochs over channels have no theorem | open (narrowed: acyclic exact in reachable form; (a) and (b) open); from the coverage pass (section 4) | small to medium |

Open convergence gaps after the coverage pass: 3 and 16 to 21. Gaps 1, 2, 5, 14 and 15 are closed.
Gaps 8 and 9 are design exclusions, and so are X1 to X5 below.

Design exclusions stated by the coverage pass (justifications in
[COVERAGE.md section 5](docs/COVERAGE.md#new-design-exclusions)): X1, Byzantine participants
(crash faults and lost messages are the eventual-delivery limit); X2, nondeterministic repair
(the scope is deterministic: `rho` is a function in every module); X3, probabilistic schedules
(the axiom-free gate rules out the standard library's reals; on a finite state space almost-sure
settlement is, classically, the existential settlement already mechanized); X4, infinite networks;
X5, real-time semantics (a timer firing is an event; convergence time is the asymptotic cost that
ROADMAP item 7 lists out of scope).

How gap 2 closed. The single coherently oriented cycle was exact (#48), and what was open was how
several cycles compose with no authority. #91 answers it for every finite network. Relative to any
section, rootless propagation copies the offset `sg(u)^-1 t(u)` along each edge (`net_origin`), so
the reachable consistent states are exactly the sections that agree with the start somewhere
upstream of every registry (`net_reachable_iff`). Existence from every start then needs a section
(`H^1 = 0` on the whole underlying graph) and one source component per weakly connected component
(`co_rooted`), and uniqueness needs a registry that nobody else writes in each component
(`root_cover`); both together is an authority root per component (`net_unique_normal_form_iff`).
The guesses this replaces fail, and the failures are theorems: holonomy inside strongly connected
components does not decide existence (`rootless_global_holonomy`), a coboundary does not give
existence from every start (`rootless_mixed_square`), and a coherently oriented cycle over a
nontrivial group does not force non-uniqueness once a source feeds it
(`rootless_source_feeds_cycle`).

How gap 14 closed. It was a gap and not a qualifier because the property is defined in a regime
the development models (`DConvQ` in `DistributedCycles.v`), `conv_ghost_normal` exhibited a
deployment that converges on a state the FedMachine never produces, and only a sufficient
condition was known. #90 gives the exact condition. The ghost is not an obstacle to convergence; it
is the obstacle to agreement with the FedMachine. Convergence alone asks the same three layers as
`flush_fed_iff` (fidelity, state descent, history descent), each relative to the quiescent state
propagation settles in rather than to `Lfp`, and `agree_conv_noghost` makes the split exact:
agreement is convergence plus `NoGhostR`. The earlier note that the necessity instances for `XUcR`
and `FMConv` refute agreement, not `DConvQ` alone, is now settled: none of `XUcR`, `FMConv`,
`NoGhostR` is necessary for convergence alone (`ghost_conv_not_fed`), and their flush-relative
forms `FlushXUR`, `QMConv` are (`copy_conv_noxu`, `fm_conv_noqm`). It still does not bear on gsm: a
gsm check for cyclic deployments would certify agreement with the FedMachine, which is
`flush_fed_iff`.

Optimization and counting (unchanged from the first audit until the fifth wave, #70 to #73):

| # | Question | Kind |
|---|---|---|
| 10 | Minimum coordination on invertible networks tied to the authority-root plan model (section 11) | **closed**, #72: exact, `plan_min_exact` (connected networks; the minimum plan cost over rooted spanning trees is the group feedback edge set number, for every root); hardness by a mechanized Max-Cut reduction (`maxcut_reduction`, `maxcut_plan_reduction`), NP-completeness of Max-Cut cited |
| 11 | Minimum coordination on non-invertible networks (section 12) | **closed**, #70: exact, `lmin_root_set`, decided by `lmin_decide`; it is the group feedback edge set minimum on group-labeled networks (`lossy_min_is_gfes`) and not cycle-based in general (`lossy_min_exceeds_cycle_bounds`); hardness by a mechanized 3-SAT reduction (`lmin_reduction`: minimum 0 vs 1 is NP-hard, so no approximation within any factor unless P = NP), membership in NP (`min_le_np_certificate`) |
| 12 | `H^1` on the 2-complex (section 13) | **closed**, #71: `nerve_H1_classification` (any group: `Hom(<X \| relation words>, G)` modulo conjugation), `nerve_H1_Z2_count` (over Z/2, `2^((\|E\| - \|V\| + 1) - rank)` classes). Not mechanized, as scope rather than gap: the dimension formula over coefficients other than Z/2, and the identification of the presented group with the fundamental group of the complex (standard) |
| 13 | Sheaf gluing, positive assembly (section 13) | **narrowed**, #73: on the registry-level site gluing of consistent states is exact (`sheaf_iff_refines`, `sheaf_exact`; R1 and covers that refine the constraints), and certificates glue on covers closed under sources (`cert_sheaf`; restriction exact, `cert_restrict_iff`). Remaining, **paper**: the Cat paper's variable-level site and its monotone-overlap regime (cyclic, least fixed points); a sheaf condition for relative certificates on covers not closed under sources. Size: medium |

Items 6, 7 and 9 were already in the first audit's tables (as qualifiers or "minor") but not in its
conclusion; they were listed in the 989-gate revision because the headline asks that every
non-exact regime be named. Items 6 and 7 are now closed.

### The cyclic frontier

The theory is exact for acyclic composition. In the terms of the canonical-execution framework
([docs/THEORY.md](docs/THEORY.md#canonical-execution)), single systems are exact through E, S and
H, and acyclic composition through P (`factor_exact`, with the federation instance `fed_exact_P`).
On cycles P has the soundness direction only (`cyc_factor_sound`, `cyc_factor_sound_gc`), and
locality fails without acyclicity (`cyclic_lc_sound_fails`). The open convergence problems that
are cyclic are instances of one question: **what additional structure makes P exact on cycles.**
This is an organizing statement, not a theorem; it changes no gap's status or size.

Each open gap, checked against its own description above:

| Gap | Cyclic? | Why, from the gap's row | Exact acyclic or single-cycle counterpart |
|---|---|---|---|
| 2 (closed, #91) | yes | Section 11 scoped it as rootless invertible networks with several cycles or mixed orientation: a registry with no incoming edge is never written and acts as a de facto root (`rootless_orientation_matters`), the single coherently oriented cycle was exact, and what was open was how several cycles compose with no authority. Closed without P, like gap 14: `net_unique_normal_form_iff` is a whole-system statement. It does name the structure. With invertible transports and the regular action every cycle is rigid: relative to a section, propagation copies offsets downstream (`net_origin`), so the only cyclic content left is `H^1` of the whole underlying graph (whether a section exists) and the source components of the condensation, which is acyclic. Existence from every start needs one source component per weakly connected component, uniqueness a de facto root in each, and both an authority root per component. In this regime no compositional form of P is needed: invertibility reduces the cyclic dynamics to a global `H^1` condition plus the acyclic condensation. That reduction uses bijective transports and says nothing about P on the non-invertible (gap 3) or monotone (gap 5) cycles; it removes gap 2 from the frontier | `net_nf_exists_iff`, `net_unique_iff`, `net_unique_normal_form_iff`; earlier `rootless_unique_iff` (one cycle), `prop_minimal_qualified_iff` (with an authority root) |
| 3 | yes | Section 12 and [LOSSY-NETWORKS.md](docs/LOSSY-NETWORKS.md#p2-rootless-convergence-in-reading-b-the-runtime-model) P2 state it for a cyclic network in the resolver reading; the acyclic case is Robert's theorem (LOSSY-NETWORKS.md section 4.2), of which the federation model gates the unique fixed point and runs in topological order or followed by a final flush (`frun_solves`, `solve_unique`, `order_independent`, `propagation_flush`), and settlement under every fair asynchronous schedule on an acyclic network (`rb_robert_fair`, `rb_lens_robert`, `rb_robert_boolean`; gap 16 (d), closed). On cycles, sufficient signed certificates on the global interaction graph (#80) and on Boolean local interaction graphs (#83) are mechanized. The local ones give E's existential Settlement and not fair-schedule settlement, even with no cycle in any local graph (`shih_dong_not_fair`): by Robert's theorem (`rb_robert_boolean`) a fair schedule that never settles needs a cycle in the global graph, and here that cycle shows in no single local graph. #92 adds, under no local cycle plus out-degree at most one, the synchronous form and the single-token asynchronous case, and #93 the two-token case (`two_token_closed`: a closed two-token run rearranges into a synchronous orbit). Fair settlement from local conditions on runs with three or more unstable vertices, multivalued local graphs and an exact condition are the open part | acyclic resolver networks (Robert's theorem: every fair schedule converges, `rb_lens_robert`, `rb_robert_boolean`); on cycles, sufficient only (`signed_settlement`, `signed_fidelity`; locally `local_fidelity_canon`, `richard_t3`, `richard_t4`, `shih_dong_E`, `sync_simple`, `one_token_fair_settlement`, `two_token_fair_settlement`) |
| 5 (closed) | yes | Section 14: collapse of a sub-federation `J` that is itself a monotone cycle. Closed without P: the cycle is inside `J`, and between the blocks of the condensation the repair is triangular, so Bekic's principle makes the least fixed point blockwise (`bekic_lfp`) and the collapse exact (`mono_collapse_nf`, `mono_collapse_exact`). It says nothing about P on a cycle that crosses blocks; it removes gap 5 from the frontier | `mono_collapse_exact`; `collapse_c_exact` (acyclic) |
| 14 (closed, #90) | yes | Section 8: the no-reset distributed model on monotone cycles, convergence alone. What separated it from the exact rows was the ghost: interleavings can agree on a quiescent state that is a fixed point of the cyclic repair other than the least one (`conv_ghost_normal`). Closed without P: `conv_quiet_exact` is a whole-system E, S and H statement with the quiescent state propagation settles in as the canonical state. The obstacle was the choice of canonicalizer, not composition, so the result says nothing about P on cycles; it removes gap 14 from the frontier | `conv_quiet_exact`; earlier `dist_exact` (acyclic), `epoch_conv_iff` (reset epochs), `flush_fed_iff` (jointly with agreement) |
| 13, monotone-overlap site | yes | Section 13: the Cat paper's monotone-overlap regime is the cyclic, least-fixed-point site; `SheafGluing.v` is acyclic throughout | `sheaf_iff_refines`, `cert_sheaf` (registry-level site) |
| 13, relative certificates on covers not closed under sources | no | Not a cycle question: `SheafGluing.v` is acyclic and the witness is a three-registry chain (`chain_cert_nonclosed`); the open part is a sheaf condition for certificates that read external inputs (`cert_restrict` gives only the relative restriction equation). A separate residue | `cert_sheaf`, `cert_restrict_iff` (covers closed under sources) |
| 13, variable-level site | no | Not a cycle question: two subsystems writing one variable is a multi-writer site, which enters only through `gluing_cex_overlap`. A separate residue | n/a |
| 15 (closed) | no | Delivery and enabledness questions on single registries, acyclic federations and the distributed model; where a cycle is present, the cyclic content is that of the rows it extends. Closed in all four parts | `dalo_exact`, `stream_alo_exact_free`, `dist_delivery_exact`, `fed_buffered_exact` |
| 16 | yes | (a), (b) and (c) are cyclic: events with rootless propagation on invertible cycles, ACC on monotone cycles, local compensation as steps on cycles; (d), the acyclic part, is closed (`rb_robert_fair`) | `dist_exact`, `flush_fed_iff`, `epoch_conv_iff`, `net_unique_normal_form_iff`; for (d) `rb_robert_fair`, `rb_robert_boolean` |
| 17 | yes | Rootless edge-writer dynamics on lossy or non-free networks: the cyclic content is the same as gap 3's, in the other reading | `net_unique_normal_form_iff` (regular action), `root_set_criterion_graph` (existence) |
| 18 | yes | Reading-B fixed points without a spanning root; on acyclic networks one always exists (Robert; `rb_lens_robert`) | `net_section_iff_sat` (reading A) |
| 19 | in part | (a) is closed for any engines (`compose_exact`): like gap 5 it composes blocks of the condensation, which is acyclic, so it is settled without P; its content is the interleaving conjunct (a block's settled output must not depend on its steps at transient inputs, `compose_isolated_refuted`, `mixed_ghost_refuted`). (b) is closed for an acyclic `J` (`dist_collapse_iff`); its residue, a cyclic `J` in the distributed model, is cyclic | `compose_exact`, `dist_collapse_iff`; `collapse_c_exact` (acyclic) |
| 20 | no | A new axis: the topology and rules are fixed in every other module. The single-registry and FedMachine parts are exact, at a barrier and live; residue (a) is the acyclic distributed model, (b) is not a cycle question; (c) is closed in the deterministic model | `barrier_exact`, `live_exact`, `fed_barrier_exact`, `fed_live_exact`; `det_barrier_closure_exact`, `amodm_closure_exact` |
| 21 | in part | A new axis: the channel between a source and its target. The acyclic part is exact in reachable form (`chan_exact`, `vsettle_exact_cond`); residue (a) is acyclic; residue (b) is cyclic: the ghost survives versioned channels (`vchan_cyc_ghost`) | `chan_exact`, `vchan_twolevel_exact`; `flush_fed_iff`, `epoch_conv_iff` (propagation reads current values) |

Gaps 8 and 9, and X1 to X5, are design exclusions, not open problems, and are not part of the
claim. Gap 13 is
listed under optimization and counting; only its monotone-overlap part joins the frontier. Gaps 2,
5 and 14 stay in the table as the frontier instances settled so far; all three were settled outside P.

The cyclic raw material already mechanized:

- GC is exact on monotone cycles: `gc_iff`, `net_events_converge_iff` (gsm's normalizer:
  `cyc_events_converge_iff`); per-target checks over normal-form images are sufficient
  (`cyc_check_gc_lfp`).
- P on cycles, soundness: `cyc_factor_sound`, `cyc_factor_sound_gc`; and the failure of locality
  that any exact form has to get around: `cyclic_lc_sound_fails`.
- Reset epochs make the no-reset ghost go away by a barrier: `epoch_conv_iff` (and `low_conv_iff`
  under `LowR`).
- Without a barrier, convergence alone is exact once the canonical state is the one propagation
  settles in, ghost allowed (`conv_quiet_exact`, #90): the cyclic repair's extra fixed points need
  a different canonicalizer, not a compositional argument.
- Rootless invertible networks, any finite graph (#91): relative to a section, propagation copies
  offsets downstream (`net_origin`), so convergence reduces to `H^1` and the source components of
  the condensation (`net_nf_exists_iff`, `net_unique_iff`, `net_unique_normal_form_iff`); single
  cycles: `rootless_unique_iff` (unique iff the group is trivial).
- Signed certificates for E on resolver networks, global interaction graph (#80): balance makes
  every resolver monotone after a change of order (`switched_monotone`), and then low starts or a
  unique fixed point give E (`signed_settlement`, `signed_fidelity`); invertible obstructions are
  closed walks on any edge list (`invertible_merge_is_holonomy`), lossy ones can be merges on a
  tree (`obstruction_loop_vs_merge`).
- Local interaction graphs (#83, Boolean, every `n`): uniqueness from no local positive cycle
  (`rrt_sub`), reachability of a fixed point from Richard's Theorems 3 and 4 (`richard_t3`,
  `richard_t4`) and from local acyclicity (`sd_path`); the separation between existential and
  fair settlement on a network with no local cycle (`shih_dong_not_fair`): the fair schedule that
  never settles runs on a cycle of the global graph that no single local graph shows (with no
  cycle in the global graph every fair schedule settles: `rb_robert_boolean`).
- Fair settlement under no local cycle plus out-degree at most one (#92): the synchronous orbit
  theorem with the local condition at one orbit state (`sync_orbit_fixed`, `sync_simple`), token
  monotonicity (`ucnt_mono`) and the single-token asynchronous case (`one_token_closed`,
  `one_token_fair_settlement`); acyclicity of the asynchronous state graph gives fair settlement
  (`fair_settlement_of_acyclic`). The two-token case (#93, `LocalTwoToken.v`): at a state with one
  token on each side of the fixed point the token agreeing with it never points into the
  disagreement set (`head_arc`), so the closed run rearranges into a synchronous orbit
  (`swap_TH`, `W_main`) and `two_token_closed` follows. Three or more tokens are the open part.
- Root sets, which turn a rootless network into a driven one once their values are pinned:
  `root_set_criterion_graph`, `root_set_count`.

### Is the headline accurate?

Yes, regime by regime:

| Regime | Exact (machine-checked) | Hardness | Open gap (listed above) |
|---|---|---|---|
| Single registry, free delivery | `cc_exact_from`, `canonical_cc_exact_from` | | |
| Single registry, causal or guarded enabledness, including enabledness a compensation step can disable | `jcg_exact`, `jcsplit_exact`; under `enabled_after_comp`: `jc_exact`, `sn_jc_exact` | | |
| Single registry, any well-founded potential; termination itself | `wf_jc_exact`, `wf_cc_exact_from`, `terminating_iff_comp_wf`, `comp_wf_iff_wfc` | | |
| Causal replay | `causal_exact` | | |
| At-least-once, free, causal and under declared independence; per-event deduplication; stream processors and the distributed model | `alo_exact`, `causal_alo_exact`, `dalo_exact`, `dalo_r_exact`, `safe_free_exact`, `safe_at_exact`, `safe_i_exact`; `stream_alo_exact_free`, `stream_alo_exact`; `dist_alo_exact`, `dist_causal_alo_exact` | | |
| CRDT fragment, op-based and state-based | `causal_convergence_exact` with `compensation_free_exact` (op-based); `merge_action_exact`, `cvrdt_on_iff` (state-based); combined, with strictness on the same representation: `crdt_boundary` | | |
| Stream processors, exactly-once and at-least-once | `stream_exact`, `stream_exact_free`; `stream_alo_exact_free`, `stream_alo_exact` | | 9 (infinite streams, design) |
| Acyclic federations, repair normal form | unconditional in the regime (topological orders; every fair schedule, `rb_robert_fair`) | | |
| Acyclic federations, event order (guarded; unguarded; buffered guards; any enabledness) | `fed_exact`, `fed_guarded_exact`; `fed_grs_exact`; `fed_buffered_exact`, `fed_buffered_edge`; `fed_jcg_exact` | | |
| Distributed propagation model, acyclic, any event-delivery class (exactly-once, causal, at-least-once) | `dist_exact`, `dist_exact_global`, `dist_exact_consistent`, `dist_global_exact_roots`; `dist_delivery_exact`, `dist_causal_exact`, `dist_alo_exact`, `dist_causal_alo_exact`; fair propagation schedules `rb_robert_fair`, with finitely many events `rb_fair_dist_exact` | | |
| Distributed propagation over channels, acyclic (late, reordered, duplicated projections; plain and versioned merge) | `chan_exact`, `chan_exact_global`, `chan_global_exact_roots`; at drain `vsettle_exact_cond`, `plain_settle_iff`; two-level `vchan_twolevel_exact` | | 21 (a) (beyond two-level networks) |
| Distributed propagation model, monotone cycles: repair alone; reset epochs; no resets (under `LowR`; general) | `q1_sound_iff`, `q1_unique_iff`; `epoch_agree_iff`, `epoch_conv_iff`; `low_agree_iff`, `low_conv_iff`; `flush_agree_iff`, `flush_fed_iff`, `fair_agree_iff`, `fair_fed_iff` (`FlushR`: `fair_flush_sound_iff`; `NoGhostR`: `noghost_event_iff`, `noghost_inv_iff`); convergence alone `conv_quiet_exact`, `fair_conv_exact` | | 16 (b), (c); 21 |
| Monotone cycles: normal form, reachability, validity | unconditional; `kleene_reach_exact`; `lfp_valid_iff_reached`, `Ncyc_valid_exact` | | 8 (no ACC, design) |
| Monotone cycles, event order | `gc_iff` | | |
| Invertible cycles: existence; root-driven convergence | `section_iff_coboundary`; `prop_minimal_qualified_iff` | | |
| Invertible, rootless: single cycle; any finite network | `rootless_unique_normal_form_iff`; `net_nf_exists_iff`, `net_unique_iff`, `net_unique_normal_form_iff` (reachable set `net_reachable_iff`) | | 16 (a) (with events); 17 (non-free action) |
| Invertible, coordinated: what to coordinate; event order | `plan_exact`; `coordinated_events_exact` | | |
| Non-invertible: single cycle; rooted; root set; event order under root-set coordination | `thm_obstruction_general`, `rooted_criterion`, `root_set_criterion_graph`, `root_set_count`; `forest_events_exact` | existence NP-complete: reduction mechanized (`net_section_iff_sat`, `net_count`, `net_size`, `np_certificate`, #57), NP-completeness by the standard argument | 3 (rootless dynamics, resolver reading); 17 (edge-writer reading); 18 (reading-B existence) |
| Collapse; composition of blocks of any engines | `collapse_a_guarded_exact`, `collapse_c_exact` (acyclic); `mono_collapse_exact` (cyclic monotone `J`); `compose_exact`, `compose_collapse`, `interface_closed` (any engines); `dist_collapse_iff` (distributed, acyclic `J`) | | 19 (narrowed: a cyclic `J` in the distributed model) |
| Reconfiguration inside a run (new axis): single registry, free delivery; federations under FedMachine semantics; at a quiescent barrier and live | `barrier_exact`, `barrier_exact_faithful`, `live_exact`, `live_exact_faithful`; `fed_barrier_exact`, `fed_live_exact`; classification `classify_finite` | | 20 (narrowed: the distributed model; other delivery classes; an unfaithful migration's barrier A part) |
| Minimum coordination: invertible (plan model); lossy | `plan_min_exact`; `lmin_root_set`, `lmin_decide`, `lossy_min_is_gfes` | invertible: NP-hard, Max-Cut reduction mechanized (`maxcut_reduction`, #72), Max-Cut NP-completeness cited; lossy: NP-hard, even minimum 0 vs 1, 3-SAT reduction mechanized (`lmin_reduction`, #70), with an NP certificate (`min_le_np_certificate`) | |
| 2-complex: `H^1` with triangle relations; sheaf gluing | `nerve_H1_classification`, `nerve_H1_Z2_count`; `sheaf_iff_refines`, `sheaf_exact`, `cert_sheaf` (registry-level site) | | 13 (narrowed: variable-level and monotone-overlap site, paper) |

No regime is left that is neither exact, hardness-backed, nor listed. Until the coverage pass that
held relative to the regimes the audit listed; the pass ([docs/COVERAGE.md](docs/COVERAGE.md))
derived the regime space from the model's axes and found 21 cells and two dimensions no row
covered, now listed as gaps 15 to 21 (gap 15 since closed), so it holds for the derived space too, up to the axes the
pass names and the design exclusions X1 to X5. Two readings of the wording
need care, and both hold:

- "Machine-checked" applies to the exact conditions. Every hardness result now has its reduction
  machine-checked, with the NP-hardness of the source problem cited and the conclusion drawn by the
  standard argument. Root-set existence: `LossyHardness.v` (#57) proves that the 3-SAT construction
  is correct in both directions (`net_section_iff_sat`), parsimonious (`net_bijection`,
  `net_count`), linear in size (`net_size`), and that a section has a polynomially checkable
  certificate (`np_certificate`). Lossy minimum coordination: `LossyMinimum.v` (#70) reuses that
  network, whose minimum is 0 or 1 exactly as the formula is satisfiable or not (`lmin_reduction`),
  with a checkable certificate (`min_le_np_certificate`). Invertible minimum coordination:
  `CoordinationMinimum.v` (#72) reduces Max-Cut (`maxcut_reduction`, `maxcut_plan_reduction`,
  same size by `signed_size`). Cited, not mechanized: NP-completeness of 3-SAT and of Max-Cut, and
  the fixed-parameter and planar tractability results for the group feedback edge set problem (Cat
  section 8), which no row relies on. Until #72 the README's precision paragraph kept "cited" for
  minimum coordination; it now says that its reduction is machine-checked too. Updated in the same
  PR as this revision.
- "A hardness result showing no efficient one exists" is used only where the exact condition is
  also mechanized (root sets; both minimum-coordination problems). No convergence regime rests on
  hardness alone.

### Re-answering the first audit's questions

**Is "complete" accurate?** Still no, but the gap list is much shorter. Of the first audit's
convergence gaps, these closed: at-least-once delivery (#55), ordinal and lexicographic potentials
(#49), the stream level (#51), event order under coordination (#47), lfp validity and finite
reachability (#50), rootless single invertible cycles (#48), and the non-invertible existence
criterion without a spanning root (#54); rootless invertible networks in general (gap 2) closed
later (#91). Of the gaps the 989-gate revision added, event order under
root-set coordination (#59), enabledness a compensation step can disable (#56) and the state-based
CRDT instance (#58) closed, and the distributed propagation model (gap 1) became exact on acyclic
federations (#60), on monotone cycles under reset epochs or `LowR` (#62), and on monotone cycles
without resets with no reachable hypothesis left (#64). On the optimization and counting side,
gaps 10, 11 and 12 closed (#72, #70, #71) and gap 13 narrowed (#73), gap 14, added by #64,
closed (#90), and gap 2 closed (#91). Items 3 and 5 above remain open for convergence, the
coverage pass added items 15 to 21 (15 since closed), and gap 13's residual is paper only, so the map is not complete. The
headline does not claim completeness; it claims that every regime's status is stated.

**Is "exact conditions in every regime" accurate?** No. Items 3 and 5 are regimes with a
sufficient condition only, or none; item 2 was one until #91 made it exact. Item 14 was a question in a regime the development models
(`DistributedCyclesExact.v`), where convergence alone had a sufficient condition only; #90 makes it
exact (`conv_quiet_exact`). Item 15, from the coverage pass, is now exact in all four parts
(`dalo_exact`, `stream_alo_exact_free`, `dist_delivery_exact`, `fed_buffered_exact`). Items 16 to
21 have no exact condition (some have a sufficient one), except the acyclic part of item 21, now
exact in reachable form (`chan_exact`, `vsettle_exact_cond`), and the single-registry and FedMachine
parts of item 20, now exact at a barrier and live (`barrier_exact`, `live_exact`, `fed_live_exact`). Items 8 and 9, and X1 to X5, are design exclusions. The headline's three-way disjunction (exact, hardness, open) is
accurate.

**"A checker for the practical ones."** Accurate, with two qualifications. gsm checks the cheap
sufficient conditions (CC with declared pairs, `NotIdempotent`, M1, R1/R2, C1 and C2 on acyclic and
monotone-cyclic networks with joint images, monotonicity and image validity over visited states);
it checks none of the exact reachable-state conditions (JC, JC', CCR, GC), which is the stated
design. Only the single-registry result is oracle-certified; the federation checks are Go code
(ROADMAP item 5). Two earlier caveats are now resolved: gsm's lfp-validity check is proved sound
(`gsm_check_Ncyc_valid`, #50; gsm's comment in `federation_monotone.go` that its condition is "not
part of the Coq lemmas" can now cite it), and `NotIdempotent` is placed exactly: sound at reachable
witnesses, complete when exactly-once delivery converges, and able to over-report at unreachable
states (#55), under free or causal delivery; with declared `Independent` pairs it is sound at
reachable witnesses and complete when the declared pairs commute at reachable states and retries
respect the declared order (`dalo_notidem_needs_dedup`, `dalo_gsm_unlisted_safe`,
`fl_retry_order_needed`; gap 15 (a), closed). For projection deployments under causal or
at-least-once event delivery, gsm's static XU check covers the propagation layer for every delivery
class (`xu_xurd`); causal delivery needs only concurrent pairs to commute on the FedMachine
(`dist_causal_exact`), and at-least-once delivery needs the FedMachine step to be idempotent where
an event is first delivered (`dist_alo_exact`), which gsm's per-registry `NotIdempotent` does not
check (gap 15 (c), closed). New since the 1198 gate: gsm checks static XU for distributed projection merging and
reports it (`FedReport.ProjectionSafe`, opt-in `RequireProjectionSafe`, gsm #34); with `Build`'s C2
that check is sound (`dist_xu_c2_converge`) and exact for every valid start when the sources are
roots (`dist_global_exact_roots`). Over channels that deliver late, reorder or duplicate, the same
check with versioned merging (`MergeProjectionAfter`, versions strictly increasing per edge) gives
convergence once the channels drain after a final round (`vsettle_xu_c2`, gap 21), while plain
merging (`MergeProjection`) converges only after an outside flush (`chan_xu_c2`;
`plain_stale_counterexample`). gsm reports cyclic projection deployments not certified, which
`dist_cyc_ghost` shows is required without epochs; it has no epoch mode, so `lens_epoch` is not yet a
gsm check. For reconfiguration gsm checks only that participants share one policy
(`PolicyDigest`, `PolicyIdentityDigest`); the exact conditions for a change at a barrier and live
(`barrier_exact_faithful`, `live_exact`, `fed_live_exact`) and the classification
(`classify_finite`; in the deterministic model `det_classify_complete`, with no faithfulness
hypothesis, through the pair closure of `amodm_closure_exact`) are the basis of its planned
`CheckMigration` (gap 20). New since the 1370 gate: `lens_noreset_iff` says what a no-reset cyclic check would need on
top of gsm's C1cyc and C2cyc, exactly: `FlushR` and `NoGhostR`. The per-event and per-network
sufficient checks (`infl_evsound`, `evlow_fairflush`, `step_sound_fairflush`, `nc_sound_low`) are cheap;
`NoGhostR` in general needs a global invariant (`noghost_inv_iff`, `unique_or_low_noghost`) or a
global uniqueness check. gsm runs none of these, so "not certified" for cyclic projection deployments
remains the correct report (gsm #39 now says so in its documentation). New since the 1524 gate:
`plan_min_exact` gives gsm's `CoordinationPlan` a precise target. It cuts every cycle, which is
sound but not minimal; the minimum is attained by the plan of some rooted spanning tree
(`plan_min_attained`), finding it is NP-hard (`maxcut_plan_reduction`), and for a fixed tree the
plan's cost is the number of non-tree edges unbalanced against any tree section
(`plan_cost_any_section`). gsm has no lossy minimum-coordination check; `lmin_b`
is an exact but exponential procedure.

### Wording

The headline stays as adopted in the README, re-confirmed at this gate:

> **An exact regime map of governed concurrent state: in every regime, a machine-checked exact
> condition, a hardness result showing no efficient one exists, or a gap stated in the open, with a
> checker for the practical ones.**

The line does not say the hardness results are machine-checked, so #57 does not change it; it
changes the precision paragraph under it (previous section). #60 and #62 do not change it either:
they move most of gap 1 into the exact column and leave a residual that is still listed. #64 does not
change it: it closes gap 1 and adds gap 14, which the README lists, so every regime is still exact,
hardness-backed, or listed open. #90 does not change it: it moves gap 14 to the exact
column. #91 does not change it: it moves gap 2 to the exact column. The coverage pass does not
change it: it lists seven more gaps (15 to 21), so every regime it derives is still exact,
hardness-backed, or listed open, or a stated design exclusion. Closing gap 15 does not change
it: a listed gap moves to the exact column, part (a) first and parts (b) to (d) after. Narrowing gap 21 does not change it either:
its acyclic part moves to the exact column, and the residue stays listed. Narrowing gap 20 does
not change it: its single-registry and FedMachine parts move to the exact column, and the residue
stays listed. Closing residue (c) of gap 20 in the deterministic model does not change it either:
gap 20 stays narrowed, with (a) and (b) listed. The fifth wave (#70 to #73) does not change it: three listed gaps
move to the exact column with mechanized hardness reductions, and the fourth (gap 13) narrows to a
residual that stays listed. The precision paragraph changes (minimum coordination's hardness is now
a mechanized reduction, not only a citation). The first audit proposed narrower lines
that named the exact core; they are superseded because the exact core now covers every delivery
model of a single registry, the CRDT fragment in both forms, and every cyclic regime except those
in the list above.

### Mechanization tasks

From the first audit's list (numbering kept):

| # | Task | Status |
|---|---|---|
| 1 | Exact converses over any well-founded potential | done, #49 |
| 2 | Stream-level exact condition | done, #51 |
| 3 | Event order under coordination, exact | done, #47 |
| 4 | Monotone cycles: exact validity, gsm's check sound, exact finite reachability | done, #50 |
| 5 | Rootless invertible cycles | done for single coherently oriented cycles, #48; every finite network, #91 (gap 2 closed) |
| 6 | At-least-once exact converse, free and causal | done, #55 |
| 7 | Distributed propagation model, acyclic exact converse | done, #60 (`dist_exact`, `dist_exact_global`, `dist_global_exact_roots`) |
| 8 | Cyclic monotone collapse | open (gap 5), medium to large |
| 9 | Distributed propagation model on monotone cycles | done: exact under reset epochs (`epoch_conv_iff`) and under `LowR` (`low_conv_iff`), #62; without resets, unconditionally (`flush_fed_iff`, `fair_fed_iff`), with `FlushR` and `NoGhostR` characterized (`fair_flush_sound_iff`, `noghost_event_iff`, `noghost_inv_iff`) and gsm's checks reduced to them (`lens_noreset_iff`), #64. Convergence alone, without agreement, exact (`conv_quiet_exact`), #90 |
| 10 | Non-invertible graphs: exact section criterion; uniqueness and event order under coordination | criterion, counting and uniqueness done, #54; NP-completeness reduction mechanized, #57; event order done, #59; rootless dynamics open (gap 3; sufficient signed certificates for E on the global interaction graph, #80, and on Boolean local interaction graphs, #83; fair settlement under no local cycle plus out-degree at most one, synchronous and single-token, #92) |
| 11 | Complete lattices without ACC | stated as a design exclusion (gap 8) |
| 12 | Minimum coordination linked to the plan model | done, #72 (`plan_min_exact`, `feasible_plan`; Max-Cut reduction `maxcut_reduction`) |
| 13 | Non-invertible minimum coordination | done, #70 (`lmin_root_set`, `lmin_decide`, `lmin_reduction`, `min_le_np_certificate`, `lossy_min_is_gfes`) |
| 14 | Rank of `H^1` on the 2-complex | done, #71 (`nerve_H1_classification` for any group; `nerve_H1_Z2_count` over Z/2) |
| 15 | Sheaf gluing, positive assembly | done on the registry-level site, #73 (`sheaf_iff_refines`, `sheaf_exact`, `cert_sheaf`, `cert_restrict_iff`); the variable-level and monotone-overlap site open (gap 13, narrowed), medium |
| 16 | Repair-disabled enabledness (gap 6) | done, #56 |
| 17 | The state-based CRDT instance (gap 7) | done, #58 |
| 18 | The lossy-network 3-SAT reduction (correctness, parsimony, size, certificate) | done, #57 |
| 19 | No-reset cyclic distributed model: exact condition for `FlushR /\ DConvQ` alone (gap 14) | done, #90 (`conv_quiet_exact`, each conjunct necessary; `quiet_conv_iff` and `flush_fed_iff` recovered) |

Tasks 16 and 17 were added by the 989-gate revision, task 18 by the 1198-gate revision, task 19 by
the 1499-gate revision.

## Side findings (documentation drift)

Found while auditing. Fixed in the same PR as this revision:

- `ROADMAP.md` reported a 254-theorem gate and listed items 6 and 7 as open; item 6 landed
  (`FederationEventsCyclesCheck.v`, #31) and item 7's work packages WP1 to WP9 and the paper
  revision landed (#32 to #43).
- `REGIMES.md`, federation table: "Cyclic, non-monotone, coordination-free: no condition suffices"
  was contradicted by `c13_two_ways_not_exhaustive` (a non-monotone negation 2-cycle has a section)
  and is now exact on single cycles (`rootless_unique_normal_form_iff`); the monotone row omitted
  validity of the lfp; "Compositional collapse ... (paper)" is mechanized for acyclic `J`
  (`Collapse.v`); the acyclic row cited the refuted `thm:fed-convergence` without C1 and C2; the
  at-least-once row gave a sufficient condition only.
- `coq/README.md`: the gate paragraph said "all 327 headline results" while the gate passed more
  than twice that, and repeated a sentence fragment; the categorical-layer roadmap said the
  non-invertible case "is not mechanized", but `CohomologyGeneral.v` and `RootSet.v` now mechanize
  its single-cycle, rooted and root-set forms.

Found in the second-wave revision (at the 1198 gate), fixed in the same PR:

- `coq/README.md`: two count lines (the `Print Assumptions` sentence and the build instructions) said
  1017 while the expected tail and the roadmap line said 1198; the categorical-layer roadmap still
  called root-set NP-completeness "cited, not mechanized" after #57.
- `REGIMES.md`: "for any enabledness (causal, guarded) the exact condition is JC" omitted the
  `enabled_after_comp` qualifier of `jc_exact`; it now points to `jcg_exact` for the general case.

Found in the third revision (at the 1370 gate), fixed in the same PR:

- `coq/README.md`: the `Print Assumptions` sentence and the build instructions still said 1198 after
  #60 and #62 raised the gate to 1253 and 1370 (the expected tail and the roadmap line were updated by
  those PRs); the gate paragraph's module list did not name the distributed modules.
- `REGIMES.md`: "no exact condition is mechanized for that model, and it is not modeled on cycles"
  was stale after #60 and #62.

Found in the fourth revision (at the 1499 gate), fixed in the same PR:

- `coq/docs/distributed.md` (moved from `coq/README.md` by #65): the `DistributedCycles.v` section
  still called `FlushR` undischarged and `EvLow` the only check for `NoGhostR` ("the gap left in
  Q2"); it now points to the `DistributedCyclesExact.v` section that closes it. The
  `DistributedCyclesExact.v` section said convergence among interleavings is weaker than agreement
  "by exactly `NoGhostR`", which no theorem states (`conv_ghost_normal` shows only that `NoGhostR`
  is not necessary for `DConvQ`); it now says the exact condition for convergence alone is open
  (gap 14).
- `REGIMES.md` (now `docs/REGIMES.md`): revised as a field guide in the same PR. The opening
  diagram ordered CRDTs, I-confluence and normalization confluence from strongest to weakest, which
  they are not (they answer different questions); the tree row said everything beyond M1 "is
  derived from acyclicity", and the monotone row and flowchart read as if monotone repair gave
  event-order convergence on any topology, which `fed_thm_monotone_cycles_events_refuted` refutes;
  the CRDT paragraph called a state-based CRDT "exactly the monotone-cycles case with compensation
  switched off". The page now follows the mechanized statements (main map by execution semantics,
  the three monotone questions, `merge_action_exact` and `cvrdt_on_iff` for CRDTs).

Found in the fifth revision (at the 1783 gate), fixed in the same PR:

- `coq/README.md`, section 13: after #71 and #73 merged, the section kept the paragraph "No module:
  nothing is mechanized on the 2-complex itself (the rank of `H^1` with triangle relations is paper
  level)" above the `CohomologyNerve.v` row, and the paragraph below it still called the positive
  sheaf-gluing assembly "paper level"; both now point to `CohomologyNerve.v` and `SheafGluing.v`.
  The `Print Assumptions` sentence and the build instructions said 1560 (the standalone count of
  #73) while the expected tail and `verify.sh` say 1783.
- `coq/docs/federation-repair.md`, categorical-layer roadmap: "Still at paper level: the rank on
  the nerve as a 2-complex", stale after #71, and "currently 1560 theorems".
- `coq/docs/non-monotone-invertible.md`: "Paper-level (not mechanized): the complexity of choosing
  the spanning tree that minimizes the coordinated set", stale after #72 (`plan_min_exact`,
  `maxcut_reduction`).
- `docs/CATEGORICAL-STRUCTURE.md`: its status lines called the rank on the 2-complex, the
  non-invertible case and the sheaf assembly paper level or open; the non-invertible case had been
  mechanized since #36 and #54, and the other two since #71 and #73.
- `docs/LOSSY-NETWORKS.md` (merged by #52 the same day): P4 said open; it is done in reading A by
  #70.

Resolved outside this repository since the 1499 gate: gsm #39 rewrote the no-reset cyclic prose
that gsm #36 had introduced (it now cites `lens_noreset_iff` and the `FlushR` and `NoGhostR`
routes), and gsm's README now states the current headline.

Still open:

- `coq/PAPER-MAP.md` was written at the 254-theorem gate; its status columns predate WP1 to WP9.
  It carries a status note pointing here, and its tables are kept as a historical snapshot.

Resolved since:

- The version-2 fold of the papers (5 October 2026): the Cat paper had treated the input-port
  refinement "at the paper level" and called `prop:gluing`, the sheaf assembly and the rank on the
  2-complex paper level. It now cites `Collapse.v` (`port_c1_transfer`,
  `port_c2_transfer`, `port_interior_certificate`), `SheafGluing.v` (on the registry-level site,
  with SC in R2's role, `cert_needs_sc`; `prop:gluing` retitled) and `CohomologyNerve.v`.

Found in the sixth revision (at the 1968 gate), fixed in the same PR:

- `README.md`: the theorem count said 1783; the open-gap list did not mention the signed
  certificates on gap 3 or the second gap-13 residue (relative certificates on covers not closed
  under sources).
- `docs/SUBSUMPTION.md` and `coq/docs/federation-repair.md`: the count said 1783.
- `docs/LANDSCAPE.md`: two passages still called paper level the necessity counterexamples for
  acyclicity and M1 (`prop_cycle_necessary`, `prop_m1_necessary`), the minimal-coordination
  complexity (`maxcut_reduction`, `lmin_reduction`), the rank on the 2-complex
  (`nerve_H1_classification`), the non-invertible case (`root_set_criterion_graph`) and the sheaf
  assembly on the registry-level site (`sheaf_iff_refines`); and the formalization survey said no
  formalization of gain-graph balance was found, which `harary_balance` now supplies at Z/2.
- `docs/THEORY.md`, "What's new here": item 1's [paper] list named the necessity counterexamples,
  the complexity bound and the rest of the calculus, gated since WP1 to WP9 (`thm_necessity`,
  `prop_cc_necessary`, `base_thm_complexity_per_event`, `base_thm_strong_absorption`,
  `calc_decomp_normalizer`, `base_thm_product`; the asymptotic cost model stays paper level); item
  2's named the authority and resolution theorems and the necessity of acyclicity and M1, gated in
  their corrected form (`fed_lem_authority_c_corrected`, `fed_thm_fed_convergence_corrected`) and
  as `prop_cycle_necessary`, `prop_m1_necessary`.
- `docs/COMPANION-OUTLINE.md`: no note at the top said its status lines are a snapshot.

Found in the seventh revision (at the 2012 gate), fixed in the same PR:

- `docs/ROADMAP.md`: gap 3's "Next" still named local interaction graphs (Remy, Ruet and Thieffry
  for fidelity, Richard 2011 for settlement) as future work; #83 mechanized both.
- `docs/THEORY.md` ("Beyond groups") and `docs/LANDSCAPE.md` ("What is new"): both said the local
  interaction graph version is the open part of gap 3; what is open now is fair-schedule settlement
  from local conditions, multivalued local graphs, value sets without bounds and an exact
  condition.
- Current-count lines said 1968 (`README.md`, `docs/ROADMAP.md`, `docs/SUBSUMPTION.md`,
  `docs/COMPANION-OUTLINE.md`, two of the three in `coq/README.md`, `coq/PAPER-MAP.md`,
  `coq/docs/federation-repair.md`).
- Richard and Comet 2007 was described as a global result (the "no positive directed cycle" sign
  route) in the `SignedResolver.v` header comment, `coq/docs/non-invertible.md` and two places in
  `docs/LOSSY-NETWORKS.md` (the section 4.1 table and section 4.3). Its theorem is local
  (multivalued: no positive circuit in any local interaction graph gives at most one fixed point,
  as restated in Richard 2010, Theorem 3); the global statement is its corollary. Comments and
  prose only; no statement changed.
- `docs/LOSSY-NETWORKS.md`: Remy, Ruet and Thieffry 2008 had been checked only through Richard's
  and Ruet's restatements; it is now checked against the primary text (HAL hal-00692086, Theorems
  3.2 and 4.4). Shih and Dong 2005 is marked as checked through its abstract and restatements,
  since its full text was not accessible.
