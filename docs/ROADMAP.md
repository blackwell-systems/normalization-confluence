# Roadmap: removing the remaining caveats

Goal: a theory in which every remaining caveat is either a deliberate design exclusion or a
fundamental limit, and nothing is merely unproven. This page lists each caveat the development
still carries, what removing it would prove, how, what it depends on, and when it counts as done.

Role of this page: what is next. What is proved today, regime by regime, is
[REGIME-AUDIT.md](../REGIME-AUDIT.md); which combinations of the model's axes the audit covers, and
which it did not until gaps 15 to 21 were added, is [COVERAGE.md](COVERAGE.md); how to pick a regime as a user is [REGIMES.md](REGIMES.md);
prior work is [LANDSCAPE.md](LANDSCAPE.md). The map of all pages is [README.md](README.md).

Status of the gate: 3513 theorems, all axiom-free (`coq/verify.sh`), CI on Coq 8.18, Coq 8.20 and
Rocq 9.3 (135 when this page was first written). Items 1 to 4 and 6 have landed, item 7 has landed
except the parts listed under it, and item 5 is open. The exactness work that followed the regime
audit (#47 to #51, #54 to #60, #62, #64, #67, #70 to #74, #77, #80, #83, #90, #91, #92, #93) is in the Done table; what remains open is listed under "Open items"
below and, regime by regime, in [REGIME-AUDIT.md](../REGIME-AUDIT.md). Nothing on this page is claimed
proven until it lands in a module and passes the gate.

## Done

| Item | Module | Headline theorems | PR |
|---|---|---|---|
| 1. Finite state only for checking | `GovernanceWF.v`, `ChaoticACC.v` | `governance_wf_confluent`, `causal_governance_wf_confluent`, `zw_confluent` (infinite instance on `Z`); `chaotic_acc_reaches_lfp`, `kleene_acc_lfp`, `ole_no_rank` | #23 |
| Event interleaving for monotone cyclic federations | `FederationEventsCycles.v` | `gc_iff`, `gc_image`, `cyc_events_converge_iff`, `cyc_instance`, `bottom_matters`, `cyc_counterexample` | #24 |
| Exact converse of C1 and C2 (acyclic) | `FederationEventsConverse.v` | `fed_exact`, `fed_exact_full`, `acyclic_gc_iff`, `static_c1_c2_gc`, `naive_converse_fails` | #24 |
| 2. At-least-once delivery | `AtLeastOnce.v` | `alo_commuting_converges`, `causal_alo_converges`, `non_idempotent_diverges`, `late_duplicate_diverges` | #25 |
| 3. Exact converse of CC and of causal convergence | `GovernanceConverse.v` | `cc_exact_from`, `cc_exact_global`, `jc_exact`, `causal_exact`, `causal_convergence_exact` | #26 |
| 4. Non-monotone cycles under a computed coordination | `CoordinatedCycles.v` | `coordinated_sound`, `coordinated_unique_nf`, `plan_exact`, `coordination_needed`, `coordinated_events_converge`, `copyback_zero_coordination`, `negation_one_coordinated` | #27 |
| 6. Event order on monotone cycles, checked per edge | `FederationEventsCyclesCheck.v`, `FederationEventsCyclesMulti.v` | `cyc_check_gc`, `cyc_check_gc_lfp`, `multi_edge_c1`, `resolver_joint_c1`, `check_rejects_latch` | #31, #44 |
| 7. Paper results mechanized (audit and WP1 to WP9) | `PAPER-MAP.md`; `RhoStar.v`, `PaperInstances.v`, `Calculus.v`, `Stream.v`, `FederationGRS.v`, `MonotoneFederation.v`, `CategoricalBridge.v`, `Collapse.v`, `CohomologyGeneral.v` | see `CHANGELOG.md`; version 2 of the three papers states only corrected results, with an errata appendix | #30, #32 to #43 |
| Exact converses over any well-founded order | `GovernanceWFConverse.v` | `terminating_iff_comp_wf`, `comp_wf_iff_wfc`, `sn_jc_exact`, `wf_cc_exact_from`, `canonical_cc_exact_from` | #49 |
| Exact stream agreement | `StreamExact.v` | `stream_exact`, `stream_exact_free`, `jc_not_necessary` | #51 |
| Exact event order under coordination | `CoordinatedExact.v` | `coordinated_events_exact`, `coordinated_events_exact_global`, `old_condition_not_necessary` | #47 |
| Exact lfp validity and finite reachability; gsm's validity check sound | `MonotoneExact.v` | `lfp_valid_iff_reached`, `Ncyc_valid_exact`, `kleene_reach_exact`, `gsm_check_Ncyc_valid` | #50 |
| Rootless invertible cycles | `RootlessCycles.v` | `rootless_nf_exists_iff`, `rootless_unique_iff`, `rootless_unique_normal_form_iff` | #48 |
| Rootless invertible networks, any finite graph (audit gap 2) | `RootlessNetworks.v` | `net_reachable_iff`, `net_nf_exists_iff`, `net_unique_iff`, `net_unique_normal_form_iff`, `net_strong_iff`; single cycles recovered (`cycle_unique_normal_form_recovered`); `rootless_mixed_square`, `rootless_source_feeds_cycle`, `rootless_global_holonomy` | #91 |
| Root-set criterion for non-invertible networks | `RootSet.v` | `root_set_iff_forest`, `root_set_criterion_graph`, `root_set_count`, `root_set_decide` | #54 |
| Exact at-least-once delivery, free and causal | `AtLeastOnceExact.v` | `alo_exact`, `causal_alo_exact`, `safe_free_exact`, `notidem_needs_dedup`, `gsm_unlisted_safe` | #55 |
| Exact confluence when compensation may disable a buffered event (audit gap 6) | `EnabledAfterComp.v` | `jcg_exact`, `jcsplit_exact`, `jc_exact_recovered`, `gnf_iff`, `dc_jc_insufficient`, `nv_jc_not_necessary` | #56 |
| Lossy-network hardness: the 3-SAT reduction mechanized | `LossyHardness.v` | `net_section_iff_sat`, `net_bijection`, `net_count`, `net_size`, `np_certificate` | #57 |
| State-based CRDT merges through the exact theorems (audit gap 7) | `CvRDTExact.v` | `merge_action_exact`, `merge_conv_alo_exact`, `cvrdt_on_exact` (iff as exported: `cvrdt_on_iff`), `naive_cvrdt_iff_fails` | #58 |
| Exact event order under root-set coordination (audit gap 4) | `RootSetEvents.v` | `forest_events_exact`, `forest_perm_exact`, `forest_events_exact_global`, `forest_runs_by_root` | #59 |
| Distributed propagation model, acyclic: exact condition (audit gap 1, acyclic part) | `DistributedExact.v` | `dist_exact`, `dist_exact_local`, `dist_exact_global`, `dist_exact_consistent`, `dist_global_exact_roots`, `dist_xu_c2_converge`, `levels_exact_not_xu`, `dist_strictly_stronger_than_fed` | #60 |
| Distributed propagation model on monotone cycles: repair alone, reset epochs, events without resets (audit gap 1, cyclic part; residual open) | `DistributedCycles.v` | `q1_sound_iff`, `q1_unique_iff`, `epoch_agree_iff`, `epoch_conv_iff`, `lens_epoch`, `low_agree_iff`, `low_conv_iff`, `quiet_agree_iff`, `quiet_conv_iff`, `dist_cyc_ghost`, `dist_cyc_epoch_fix` | #62 |
| Distributed model on monotone cycles without resets, exactly (audit gap 1, residual; gap 1 closed) | `DistributedCyclesExact.v` | `flush_agree_iff`, `flush_fed_iff`, `fair_agree_iff`, `fair_fed_iff`; `FlushR`: `fair_flush_sound_iff`, `flushat_sound_iff`, `sand_settles`; `NoGhostR`: `noghost_event_iff`, `noghost_inv_iff`, `noghost_soundr_iff`, `soundr_fed_iff`; gsm: `lens_noreset_iff`, `lens_noreset_fair_iff`; necessity `copy_xu_fails`, `fm_conv_fails`, `flip_noflush`, `flip2_fair_livelock`, `ghost_exact` | #64 |
| Distributed model on monotone cycles without resets: convergence among quiescent interleavings alone (audit gap 14; closed) | `DistributedConvergenceExact.v` | `conv_quiet_exact`, `fair_conv_exact`, `flushdet_event_iff`; ghost-free case `quiet_conv_recovered`, `agree_conv_noghost`, `flush_fed_recovered`; `sand_flushdet`, `soundr_conv_iff`; necessity `flip_conv_noflush`, `fork_conv_nodet`, `copy_conv_noxu`, `fm_conv_noqm`; `conv_ghost_instance`, `ghost_conv_not_fed` | #90 |
| Minimum coordination on lossy networks (audit gap 11; `LOSSY-NETWORKS.md` P4, reading A) | `LossyMinimum.v` | `lfeasible_iff_root_set`, `lmin_root_set`, `lmin_decide`, `lmin_reduction`, `net_lmin_dichotomy`, `min_le_np_certificate`, `lossy_min_is_gfes`, `lossy_min_exceeds_cycle_bounds` | #70 |
| Signed cycles: loops versus merges, Harary balance, and sufficient signed certificates for E (audit gap 3, progress; gap stays open) | `SignedCycles.v`, `SignedResolver.v` | `invertible_merge_is_holonomy`, `holonomy_free_section`, `obstruction_loop_vs_merge`, `harary_balance`, `balanced_no_positive_acyclic`; `switched_monotone`, `signed_settlement`, `signed_fidelity` (and `_harary` forms); breaks `neg2_no_fixed_point`, `copyback_ghost`, `ring_low_start_E`, `unbalanced_unique_oscillates`, `flip_needs_top_resolver`, `xor_no_certificate`, `cyc3_unsignable`; statement review #81 | #80, #81 |
| Local interaction graphs, Boolean, every `n`: local fidelity and local settlement (audit gap 3, progress; gap stays open) | `LocalSigned.v` | `rrt_sub`, `local_fidelity`, `local_fidelity_canon`, `local_signed_fidelity`, `global_to_local`; `richard_t3`, `outdeg_nonexpansive`, `richard_t4`, `sd_path`, `shih_dong_E`; breaks `local_weaker_than_global`, `local_neg_free_no_fixed_point`, `shih_dong_not_fair`, `ring_local_conditions` | #83 |
| Fair settlement under no local cycle plus out-degree at most one: synchronous form and the single-token asynchronous case (audit gap 3, progress; gap stays open) | `LocalFairSettlement.v` | `sync_orbit_fixed`, `sync_simple` (Shih and Ho 1999, Theorem 3.1, by a different proof); `ucnt_mono`, `one_token_closed`, `one_token_fair_settlement`, `fair_settles_once_one_token`; `fair_settles_closed`, `fair_settlement_of_acyclic`; instances `shih_ho_instance`, `outdeg_needed`, `no_neg_not_enough`, `no_pos_not_enough` | #92 |
| Fair settlement under no local cycle plus out-degree at most one from at most two unstable vertices (audit gap 3, progress; gap stays open) | `LocalTwoToken.v` | `two_token_closed`, `two_token_no_closed_change`, `two_token_fair_settlement`, `fair_settles_once_two_tokens`; the rigidity lemma `head_arc` (with `not_both_bad`, `tight_arc`) and the rearrangement into a synchronous orbit (`swap_TH`, `W_sort`, `W_main`); instance `two_token_instance` | #93 |
| CRDT boundary: without compensation the CRDT algebra is exactly the remaining convergence condition; with it the class is strictly larger on the same transition representation | `CRDTBoundary.v` | `crdt_boundary`, `cf_causal_boundary`, `cf_merge_boundary`, `cf_cvrdt_boundary`, `witness_not_cvrdt_exact`, `boundary_nonvacuous`; qualifier `witness_governed_constant` (strictness is about representations, not observable behavior) | #67, #68 |
| Canonical execution framework (validated, scoped to single systems and acyclic composition; [THEORY.md](THEORY.md#canonical-execution)) | `CanonicalExecution.v`, `CanonicalInstances.v`, `CanonicalLocality.v` | E: `canonical_execution_exact`; S: `state_descent_iff_cc2`; P: `factor_exact` (with `factor_needs_sound`, `factor_needs_realizable`, `factor_needs_exposed`), `fed_exact_P`, `c_local_iff_r1`; on cycles soundness only, `cyc_factor_sound`, and `cyclic_lc_sound_fails`; statement review #78, promoted #79 | #74, #77 to #79 |
| `H^1` on the nerve as a 2-complex (audit gap 12; WP10, rank half) | `CohomologyNerve.v` | `nerve_H1_classification`, `nerve_H1_abelian`, `nerve_H1_Z2_count`, `nerve_Z2_full_iff`, `nerve_section_iff_coboundary`, `triangle_kills_flip` | #71 |
| Minimum coordination tied to the plan model (audit gap 10) | `CoordinationMinimum.v` | `plan_min_exact`, `feasible_plan`, `plan_coord_feasible`, `plan_min_attained`, `plan_min_root_independent`, `maxcut_reduction`, `maxcut_plan_reduction`; `plan_min_connected_needed`, `plan_min_nodup_needed`, `s3_tree_choice` | #72 |
| Sheaf gluing over sub-federation covers (audit gap 13, narrowed; WP10, sheaf half) | `SheafGluing.v` | `separation`, `gluing`, `sheaf_exact`, `sheaf_iff_refines`, `cert_restrict_iff`, `cert_sheaf`; `triangle_fails`, `r1_failure`, `gluing_cex_overlap`, `cert_needs_sc` | #73 |
| gsm check for **C2** (same-target event pairs, repair in between) | gsm | gsm PR #26 | gsm |
| gsm `EmbedCertified` executes the **certified tables** instead of live closures | gsm | gsm PR #27 | gsm |
| gsm check for **XU** on acyclic federations (distributed projection merging), reported as `FedReport.ProjectionSafe`, required by opt-in `RequireProjectionSafe` | gsm | gsm PR #34 (unreleased, after v0.13.0); the hypothesis of `dist_interleavings_converge`; it implies `dist_exact`'s condition and is strictly stronger (`levels_exact_not_xu`) | gsm |

### Qualifiers found

Each item reads "if and only if" or "converges" only with the qualifier stated in the theorem. The
naive statements are false, and each has a mechanized counterexample:

- **C1/C2 converse.** The exact converse needs witnesses realized by reachable states. Static C1 can
  fail while every interleaving from every valid consistent start converges
  (`naive_converse_fails`). Static C1 and C2 are sufficient, and necessary only at reachable
  witnesses.
- **CC converse.** Needs canonical repair (`rho_star` returns a valid state): with the identity as
  `rho_star`, CC1 fails yet normal forms are unique (`rho_star_qualifier`). Under causal or guarded
  enabledness CC1 is not necessary (`masked_cc1`); the exact condition is joinability of critical
  pairs at reachable configurations (`jc_exact`). When a compensation step can disable a buffered
  event, JC is neither sufficient (`dc_jc_insufficient`) nor necessary (`nv_jc_not_necessary`); the
  exact condition is JC' (`jcg_exact`).
- **State-based CRDTs.** Convergence of merges under every order and duplication is not "the merge
  is a join-semilattice on all states" (`naive_cvrdt_iff_fails`); the exact condition is
  commutation and idempotence at reachable states (`merge_action_exact`), and reachability is
  needed (`clamp_reach_qualifier`).
- **Distributed model.** The acyclic exact condition is strictly weaker than XU
  (`levels_exact_not_xu`) and strictly stronger than FedMachine convergence
  (`dist_strictly_stronger_than_fed`). On monotone cycles every check gsm runs can pass while
  projection nodes settle at a ghost fixed point the FedMachine never produces (`dist_cyc_ghost`);
  a reset epoch removes it only as a barrier (`dist_cyc_epoch_fix`), and a clear that resets only
  its own shared slot still ghosts (`local_reset_ghost`). Without resets, flushability is part of
  the certified property, not a hypothesis on it (`flip_noflush`), and "some propagation word
  reaches quiescence" does not give "every fair schedule does" (`flip2_fair_livelock`,
  `ring_exact`). No ghost is not necessary for convergence among interleavings alone
  (`conv_ghost_normal`); it is necessary for agreement with the FedMachine (`ghost_exact`).
- **Causal converse.** Reachability of the state is not enough; the non-commuting concurrent pair
  must be deliverable after a causally consistent prefix (`naive_causal_converse_fails`).
- **At-least-once.** Idempotence of each duplicated event is not enough under causal delivery: the
  redelivery must itself be causally consistent (`late_duplicate_diverges`).
- **Coordinated cycles.** The normal form is unique given the authority root, not absolutely: the
  result depends on the root (`root_choice_matters`), and without a root two orders reach different
  consistent states (`copyback_without_authority`). Balance is a static property of an edge only for
  invertible transports (`noninvertible_balance_not_static`), and the strong form of
  `unbalanced_blocks` needs the regular action (`nonfree_holonomy_counterexample`).
- **Rootless cycles.** Without a root, a single coherently oriented invertible cycle has a unique
  normal form from every start iff the group is trivial (`rootless_unique_normal_form_iff`); the
  orientation matters (`rootless_orientation_matters`). On any finite network the condition is an
  authority root per weakly connected component, or a trivial group, given `H^1 = 0`
  (`net_unique_normal_form_iff`); holonomy inside strongly connected components does not decide
  existence (`rootless_global_holonomy`), and a coboundary does not give existence from every start
  (`rootless_mixed_square`).
- **At-least-once, exactly.** Idempotence alone is not enough without commutation
  (`flag_idem_needs_dedup`, `fw_alo_fails`), and global idempotence is not necessary
  (`jmp_unreachable`), so gsm's `NotIdempotent` can over-report.
- **Streams.** The natural iff with the rewrite-system condition JC is false (`jc_not_necessary`);
  the exact condition is PJC under `Progress` (`progress_needed`).
- **Least fixed points.** Validity of the lfp needs neither bottom validity nor gsm's check
  (`bottom_validity_not_necessary`, `gsm_check_not_necessary`), and the reachability qualifier is
  needed (`lfp_valid_iff_needs_reach`).

### Exact versus checked

The exact conditions (JC, CCR and GC) quantify over reachable states or prefixes, so checking them
means exploring the reachable state space (on a cycle, the federated state space). The cheap
sufficient conditions (CC for a registry, C1 and C2 for an acyclic federation) are what gsm checks;
they imply the exact ones (`cc_reach_jc`, `static_c1_c2_gc`). Scope throughout: discrete,
deterministic governed state.

The cyclic result works through the federated normalizer `N` (the unique least fixed point from
`Federation.v` and `Chaotic.v`): each governed step is `N` after the event, and `Trace.run_tequiv`
gives convergence when steps commute on reachable states. In a cycle that condition is global, not
per edge, so a gsm check for it explores the federated state space.

## Removable caveats, high value

Each item below lists the theorem it would add, the approach, and the acceptance criterion. Items 1
to 4 and 6 are done, and item 7 is done except the parts listed under it; the "Today" paragraphs
record the state before they landed. Item 5 is open; items 8 and 9 are planned.

### 1. "Finite state" becomes a statement about checking only

**Status: done (#23).** `GovernanceWF.v` (WFC over any well-founded order, with the infinite
withdrawal registry on `Z` as instance and the nat-valued theorems as corollaries) and
`ChaoticACC.v` (chaotic and Kleene iteration under the ascending chain condition, with
`option nat` as an ACC lattice that provably has no rank into `nat`).

- **Today.** The single-registry convergence theorem (`Governance.v`) already quantifies over any
  state type, but its termination potential is natural-number valued (`Phi : State -> nat`). The
  monotone results assume finite height (`Chaotic.v`, `rank`). The paper's infinite-domain
  corollary (convergence is domain-independent) is proved on paper only.
- **Target.** Termination from any well-founded relation (ordinals, lexicographic products), and
  the monotone regime under the ascending chain condition instead of finite height.
- **Approach.** Restate WFC over an arbitrary well-founded order and rerun the termination proof;
  replace `rank` with well-foundedness of the strict order's converse in the chaotic-iteration
  proof.
- **Done when.** The generalized theorems pass the gate, a non-vacuity instance on an infinite
  domain (for example an unbounded integer counter with a floor repair) discharges every hypothesis,
  and the existing finite theorems are recovered as corollaries.
- **Effect.** "Finite" stops being a condition of the theory. It remains only what makes gsm's
  exhaustive check decidable.

### 2. "Exactly-once delivery" becomes a checked property

**Status: done (#25).** `AtLeastOnce.v`: duplicates of idempotent governed steps are absorbed
(`alo_absorbed`, `alo_commuting_converges`, `causal_alo_converges`), and a non-idempotent duplicate
diverges (`non_idempotent_diverges`, `inc_duplicate_diverges`). Qualifier: under causal delivery the
redelivery must be causally consistent (`late_duplicate_diverges`).

- **Today.** Convergence assumes every replica sees each event exactly once. A non-idempotent event
  delivered twice diverges.
- **Target.** Convergence under at-least-once delivery for the events whose governed step is
  idempotent, and a counterexample for any event that is not.
- **Approach.** Model delivery as a multiset of events and prove that duplicates of an idempotent
  governed step are absorbed, extending the order-independence results; this mirrors how state-based
  CRDTs absorb duplicates (`cvrdt_absorbs_duplicates`).
- **Done when.** The theorem passes the gate with a witness of divergence for a non-idempotent
  event. gsm reports non-idempotent events (`Report.NotIdempotent`, gsm PR #24, released in v0.13.0),
  so the documentation can say exactly which events need deduplication.

### 3. "Sufficient, not necessary" becomes "if and only if"

**Status: done (#24, #26).** `GovernanceConverse.v`: `cc_exact_from` (unique normal forms from `s0`
iff CC on the states reachable from `s0`, with canonical repair), `jc_exact` (any enabledness),
`causal_exact` and `causal_convergence_exact`. `FederationEventsConverse.v`: `fed_exact`,
`fed_exact_full`, `acyclic_gc_iff`. Qualifiers and counterexamples to the naive converses are listed
under "Qualifiers found" above.

- **Today.** The convergence conditions are proven sufficient; necessity is shown by
  counterexamples (the paper's necessity results, the CC counterexamples, the C1 and C2
  counterexamples). The general converse for C1 and C2 has since landed (#24).
- **Target.** General converses for the single-registry CC condition and for causal delivery: if
  CC fails at a reachable state, two event orders diverge; if a non-commuting pair can arrive out of
  causal order, a divergent run exists.
- **Approach.** Construct the diverging runs from the failure witness, with reachability as an
  explicit hypothesis. If the naive converse is false, prove the strongest true form and record the
  counterexample to the naive one.
- **Done when.** Each core result reads "converges if and only if," with any qualifier stated in
  the theorem.

### 4. Non-monotone cycles converge under a computed coordination

**Status: done (#27).** `CoordinatedCycles.v`: `coordinated_sound` and `coordinated_unique_nf`
(unique normal form given the authority root), `plan_exact`, `coordination_needed`,
`coordinated_events_converge`, with `copyback_zero_coordination` and `negation_one_coordinated` as
the two acceptance instances. Qualifiers: `root_choice_matters`, `copyback_without_authority`,
`noninvertible_balance_not_static`, `nonfree_holonomy_counterexample`.

- **Today.** Non-monotone cyclic federations have no unique normal form and are rejected (or
  coordinated by gsm's `CoordinationPlan`, which cuts every cycle). The holonomy-minimal plan in
  gsm's `HOLONOMY-COORDINATION-DESIGN.md` has a stated soundness condition but no theorem.
- **Target.** Soundness of the holonomy-minimal plan: with values driven along a spanning tree from
  a designated authority root, balanced non-tree edges kept as checked constraints, and unbalanced
  edges externally coordinated, the federation has a unique normal form.
- **Approach.** Compose the acyclic federation results (the tree is acyclic) with
  `tree_has_section`, `tree_unique`, `keep_balanced_suffices` and `unbalanced_blocks` from
  `CohomologyGraph.v`; the authority root fixes the constant that `tree_unique` leaves free.
- **Done when.** The soundness theorem passes the gate, with the copy-back loop (balanced, accepted
  with zero coordination) and the negation loop (unbalanced, one edge coordinated) as instances.
- **Effect.** Monotone cycles converge, and invertible non-monotone cycles converge given the
  computed coordination (event order exactly: `coordinated_events_exact`, #47). Invertible cycles
  with no authority root are exact on single coherently oriented cycles (`RootlessCycles.v`, #48)
  and on every finite network (`RootlessNetworks.v`, #91).

### 5. Federation-level checks become oracle-certified

**Status: open.**

- **Today.** gsm's single-registry builds pass a fail-closed oracle gate extracted from the proof.
  The federation-level checks (M1, R1/R2, acyclicity, monotone cycles, cross-registry order) are
  gsm's Go code and are not oracle-certified.
- **Target.** An extracted federation checker, proven sound against the federation theorems, run by
  gsm in-process on `Federation.Build`.
- **Approach.** A decidable checker over the federation's emitted tables (morphism and resolver
  tables, component step tables), proven to imply the hypotheses of the federation theorems
  (including C1, C2 and the now-landed items 1 to 4), extracted the same way as the table and rules
  oracles. This is also the outstanding item in gsm's `CERTIFICATE-DESIGN.md`.
- **Done when.** gsm's federation report states that the federated composition is oracle-certified,
  with differential tests against the Go checks.

### 6. Event order on monotone cycles is checked, not assumed

**Status: done (#31, #44).** `FederationEventsCyclesCheck.v`: gsm's per-target C1 and C2, read on
a cycle over a set containing every normal form's shared values (such as the morphism images),
imply GC (`cyc_check_gc`, `cyc_check_gc_lfp`), and the check rejects the `cyc_counterexample` latch
(`check_rejects_latch`). `FederationEventsCyclesMulti.v`: per-edge C1 checks compose for multi-edge
targets under M1 (`multi_edge_c1`), and resolver targets need the joint image
(`resolver_joint_c1`, `resolver_edge_insufficient`). gsm's report cites `cyc_check_gc_lfp`. Neither
cheap condition is necessary; the exact condition remains GC.

- **Today.** On a monotone cyclic federation the exact condition for event interleavings is GC
  (`cyc_events_converge_iff`), which is global, not per edge. Static C1 and C2 are proved sufficient
  only for acyclic federations (`static_c1_c2_gc`). gsm runs its C1 and C2 checks on
  `AllowMonotoneCycles` networks too, but nothing proves them sufficient there, and gsm does not
  check GC. So a monotone cyclic federation gsm accepts has a unique normal form (the least fixed
  point), but convergence of its event interleavings is not guaranteed by any check gsm runs.
- **Target.** Either a cheap sufficient condition for cycles, proved in Coq (for example C1 and C2
  over the iteration's visited states imply GC, or a counterexample showing they do not), or an exact
  GC check in gsm for small federations with a size cap. In the meantime gsm's report should state
  that event order on cycles is unchecked.
- **Done when.** Either the theorem lands and gsm's cycle check matches it, or gsm checks GC (capped)
  and reports it, with the `cyc_counterexample` latch federation as a regression test.

### 7. Every result in the papers is mechanized

**Status: done except the items below.** The audit step landed as `coq/PAPER-MAP.md` (#30), and
its work packages WP1 to WP9 landed (#32 to #39, #42), with version 2 of the three papers (#40,
#41, #43) stating only corrected results, each refuted version-1 statement backed by a gated
counterexample. `PAPER-MAP.md`'s status columns record the 254-theorem gate it was written at and
have not been re-run since the packages landed. What the version-2 papers still state at paper
level:

- **Sheaf gluing** (Cat `prop:gluing`, the sheaf assembly over the full cover): mechanized on the
  registry-level site, #73 (`SheafGluing.v`: exact, `sheaf_iff_refines`; certificates on covers
  closed under sources, `cert_sheaf`), with SC in the role the paper gives R2 (`cert_needs_sc`). The
  paper's variable-level site and its monotone-overlap regime stay at paper level (audit gap 13,
  narrowed). **The rank of `H^1` on the nerve as a 2-complex** (Cat section 6): done, #71
  (`CohomologyNerve.v`). The papers now match: Cat `prop:gluing` is restated as registry-level
  gluing with SC in R2's role and cites `SheafGluing.v`, and Cat section 6 cites
  `nerve_H1_classification` and `nerve_H1_Z2_count`.
- **The cyclic monotone case of `thm:collapse`** (Fed, after `thm:collapse` and in
  `rem:fed-mechanized`).
- **The lattice-compensation CC pattern** (Base 8.2, corrected with a short paper proof).
- Out of scope by design: cited complexity results (NP-completeness of 3-SAT and Max-Cut, and the
  fixed-parameter, planar and approximation results for group feedback edge sets; Cat section 8;
  the reductions themselves are mechanized, `LossyHardness.v`, `LossyMinimum.v`,
  `CoordinationMinimum.v`), the
  asymptotic cost of normalization (Base `thm:complexity`; the per-event step bound is mechanized),
  and the decidability remark for R1, R2, C1 and C2 (item 5).

The Cat paper now cites `Collapse.v` for the input-port refinement (`port_c1_transfer`,
`port_c2_transfer`, `port_interior_certificate`); the paper wording matches, and it was never a gap.

The original item text follows. Known gaps at the time, from the README's [paper] markers:

- **Necessity of acyclicity and of M1** (the federation paper's counterexamples, `prop:cycle-necessary`
  and the M1 counterexample). No Coq theorem states them; `Cohomology.v`'s negation-orbits example is
  related but not the same statement.
- **The authority and resolution theorems as stated.** The mechanized order-independence and
  retraction (`FederationOrder.v`, `Categorical.v`) cover their substance in a different form.
- **The rest of the verification calculus**: strong absorption, decomposable repair and product
  composition. Only the footprint-disjointness path is mechanized (`Gsm.v`).
- **The complexity bound** on normalization.
- **The necessity counterexamples as stated in the main paper.** Largely subsumed by the exact
  converses (`cc_exact_from`, `jc_exact`), to be confirmed against the paper's specific examples.
- **R1/R2 as the gluing axiom and the sheaf assembly over the full cover.** The gluing
  counterexample is mechanized; the positive assembly is not.
- **Done when.** Every numbered result in the papers has a named Coq theorem in the gate, except
  results cited from the literature (group-feedback-edge-set complexity), which stay cited.

### 8. Checking scales to realistic domains

**Status: step 1 (symmetry) landed (`SymmetryCutoff.v`, #107); step 2 (abstraction) landed for
comparison-only rules with a finite representative domain and for linear rules as an exact
reduction to formula validity (`AbstractionCutoff.v`), and for difference constraints with gsm's
saturating writes with a finite representative domain, no solver (`DifferenceAbstraction.v`); step 3 (compositional checking) landed for
WFC and gsm's guarantee, CC1 on valid states (`CompositionalCheck.v`); the history-side reduction
planned.**

- **Step 1, symmetry: check one item, conclude for all.** For a keyed collection of independent,
  identically governed items, WFC, CC2, CC1 with CC2 (so unique normal forms), at-least-once
  convergence, idempotence, declared independence, and federation C1 and C2 across a pointwise
  morphism each hold for any number of items iff they hold for one item (`wfc_cutoff`,
  `cc2_cutoff`, `un_cutoff`, `un_cutoff_global`, `alo_cutoff_exact`, `declared_cutoff`,
  `c1_cutoff`, `c2_cutoff`). CC1 alone has cutoff 2, and the cutoff is tight (`cc1_cutoff`,
  `cc1_cutoff_tight`): its cross-item pairs are the item's repair-then-event obligation
  (`cross_item_reduces`), which CC2 implies (`cc2_star`). The hypotheses (events and repair at a key
  read and write only that key, rules invariant under permutations of keys, invariant a
  conjunction of item invariants) are equivalent to being the lift of the one-item registry
  (`idgov_lift`), decided on finite descriptions by `symcheck` (`symcheck_decides`), and sound for
  the reduction (`symmetry_sound`). Each dropped hypothesis has a counterexample: an aggregate
  invariant (`aggregate_diverges`, `agg_not_idgov`) and different rules per item
  (`nonidentical_misleads`); non-vacuity is per-product inventory at any catalog size
  (`inventory_any_n`). Details: [coq/docs/symmetry.md](../coq/docs/symmetry.md). Not yet done: a
  shared global component alongside the items, and the gsm side.

- **Step 2, abstraction: check relationships, not values.** Over integer-valued state (n
  variables, events with m parameters, declared constants C), for rules invariant under the order
  isomorphisms that fix C (`OrdInv`: they compare and copy values and constants), repair within K
  steps, WFC, CC2, CC1 and unique normal forms each hold over all integers iff over the finite
  domain `reps N C` of `|C|(N+1) + N` representatives, with N = n for repair and WFC, n + m for
  CC2 and n + 2m for CC1 and unique normal forms (`term_abs`, `wfc_abs`, `cc2_abs`, `cc1_abs`,
  `un_abs`, `abs_check_exact`); a check instance has the truth value of every instance of the same
  order type (`cc1_order_type`, `cc2_order_type`). On a rule language, `ord_frag` decides membership
  syntactically and is sound (`ord_frag_sound`, `build_sound`). Linear rules (+, -, multiplication
  by a literal) get the formula form, not a representative set: repair within K steps, CC1 and CC2
  each hold over all integers iff a generated quantifier-free linear formula is valid
  (`phi_term_exact`, `phi_cc1_exact`, `phi_cc2_exact`, `lin_exact`, `lin_frag_linear`); deciding
  validity is the external solver's step. Boundaries: an undeclared exact test passes the
  representative check and diverges (`exact13_diverges`), an additive guard fools the order-pattern
  check (`triangle_diverges`), and the bound cannot drop below n (`copy_tight`). Non-vacuity:
  capped inventory over 7 representatives (`capped_un`), a wallet with integer balances through its
  13 formulas (`wallet_un`), and with symmetry a capped catalog of any size (`sym_abs`,
  `capped_catalog`). Details: [coq/docs/abstraction.md](../coq/docs/abstraction.md).
- **Step 2, arithmetic status: difference constraints, done (`coq/DifferenceAbstraction.v`).** For
  the most common business arithmetic, guards `x - y op c` and `x op c`, writes `x := y + c`,
  `x := x + c` and `x := c`, with every write saturating at the declared bounds as gsm's `Int`
  writes do, each condition gsm checks holds over the full declared ranges iff it holds over the
  in-range states with every variable within `n(W + 1)` of an anchor (the bounds and the absolute
  constants). `W` is the largest difference-guard constant `gam` plus the chained offsets:
  `gam + K mu` for repair within K steps (`dterm_abs`), `gam + 3(K + 1) mu` for idempotence
  (`didemv_abs`), `gam + 4(K + 1) mu` for CC1 at the valid states (`dcc1v_abs`) and for gsm's
  guarantee (`dgsm_exact`, `dgsm_sound`, end to end `dbuild_sound`), with `mu` the largest sum of
  offsets in one transform. The size does not depend on the widths of the ranges (657
  representatives for a wallet over `[-1000, 10^9]`). At threshold 0 the relation is the order type
  (`rel0_oiso`), so the comparison fragment is the special case. Boundaries: a difference guard
  that the order-pattern check misses is reported (`gap_check_fails`); `triangle_diverges`' guard
  and a sum of two variables are refused (`tri_refused`, `sum_diverges`); the threshold must cover
  chained increments (`granularity_needs_chain`). Not yet done: the least threshold (the one proved
  is sufficient), general linear rules over a finite domain (sums of variables, multiplication by
  a literal other than 1), repair whose step count depends on the values, dense orders (strings,
  decimals), and the gsm side (the design input is in
  [coq/docs/abstraction.md](../coq/docs/abstraction.md#for-gsm-1)).

- **Step 3, compositional checking: check each footprint component, conclude for the registry.**
  When every rule's footprint lies in one component, a repair step of the registry is a repair
  step of one component (`rho_step`).
  - WFC holds iff every component terminates on its own subspace (`wfc_iff`, `term_iff`). The
    repair bound is the sum of the component bounds (`bound_sum`).
  - CC1 holds at every valid state for events in different components, with no check
    (`cc1_cross`). For events in the same component it holds iff it holds on the component
    (`cc1_same_iff`, `cc1_component`).
  - gsm's guarantee (every order of the same events from a valid state reaches one state) is
    exactly CC1 on valid states (`conv_iff_cc1`). It holds iff it holds in every component
    (`compositional_exact`, `compositional_gsm`).
  - A boolean check that enumerates each component's subspace decides both conditions
    (`comp_check_exact`), at the cost of the sum of the subspaces (`enum_length`). gsm's
    zero-background component check computes the same conditions (`gsm_literal`).
  - Shared variables are allowed when no rule writes them.
  - For combinator rules the footprints are extracted and proved sound (`ast_event_local`,
    `ast_hyps`). Closure footprints remain a tested trust boundary (`TrustClosureFootprints`).
  - Each hypothesis has a counterexample: footprints without reads (the pay/ship pattern,
    `ws_diverges`), a repair that writes another component (`rc_diverges`), and a written shared
    variable (`sw_diverges`).
  - Non-vacuity: orders and inventory with an optional shared store flag (`shop_converges`,
    `shop_cost`).

  Details: [coq/docs/compositional.md](../coq/docs/compositional.md). Not yet done: CC2 and the
  unique normal forms of the rewrite system per component, a combined theorem with steps 1 and 2,
  and the gsm side.

- **Today.** gsm decides the exact and sufficient conditions by enumerating states, so a model must
  use small finite domains. Realistic types (64-bit amounts, string identifiers, thousands of
  independent items) have to be shrunk by hand, and nothing proves that a check on the shrunk
  model says anything about the real one. `BuildCompositional` already enumerates per footprint
  component instead of the global product.
- **Target.** Theorems that make a check on a small or abstract model imply the property on the
  real one: data independence and symmetry (independent, identically governed items: checking one
  suffices), abstraction soundness (a rule that depends only on relations between values, checked
  over representatives of every relation, implies the condition for all values), and
  compositional checking as the default path (per footprint, with the soundness of the footprint
  reduction stated for the conditions gsm checks).
- **Approach.** State each reduction as a theorem about the existing conditions (CC, C1, C2, XU,
  at-least-once), with the reduction's hypotheses as checkable side conditions, and a
  counterexample for each hypothesis dropped. Symbolic checking (an SMT query per rule pair over
  all values) can then be justified by the abstraction theorem rather than trusted.
- **Done when.** The reductions pass the gate, gsm can verify a model with realistic domains by
  one of them, and its report names which reduction was used and what it assumed.

- **History-side reduction (partial-order reduction).** The checks that explore reachable states by
  running event sequences (GC on cycles, the reachable-state forms CXUR and C2R, the migration
  check of item 9) can follow one order per class of commuting histories. Progression:
  1. **Pairwise swap lemma.** For events a and b that are independent at a state, u a b v and
     u b a v reach the same canonical state, and the swap is admissible in the execution model
     (enabledness, causal order, delivery). No free context rule: the swap is allowed only in the
     contexts the model admits, the lesson of causal at-least-once (`AbsorbAt`, see
     [THEORY.md](THEORY.md#absent-laws-explained)).
  2. **Trace equivalence.** The equivalence generated by admissible swaps preserves canonical
     outcomes (the existing `run_tequiv`, `causal_tequiv`).
  3. **Canonical histories.** One representative per class (a fixed topological order of each
     trace), with run(w) and run(w') canonically equal whenever w and w' are equivalent.
  4. **Exactness of the reduction, per condition.** Checking every reachable class through its
     representative decides the condition on all histories, under the stated admissibility
     hypotheses. For n pairwise independent events this replaces n! orders by one trace; in
     general, by the number of dependency-respecting traces.
  5. **Symmetry combined with it.** State quotients (symmetry, abstraction) and history quotients
     compose: thousands of items and thousands of events checked through one representative item and
     one trace per class.

  **Independence is derived, never declared.** The reduction uses a decidable, sound predicate
  Independent(a, b), established by the check itself: no read/write overlap or proved commutation
  at the states concerned, no enabledness interference, no causal dependency, and, where
  at-least-once applies, compatible duplicate landing points. Each restriction is already backed by
  a mechanized counterexample, which the reduction cites rather than rebuilds:
  - one event disables the other: `dc_jc_insufficient`, `bg_persistence_needed`;
  - a causal dependency makes the swap illegal: `naive_causal_converse_fails`;
  - duplicates make a local swap unsound: `late_duplicate_diverges`, `fl_partner_overtakes`;
  - compensation changes later enabledness: the `jcg_exact` setting;
  - masked commutation under guarded enabledness: `masked_cc1`;
  - different items with a shared aggregate constraint: the symmetry step's aggregate counterexample
    (`aggregate_diverges`).

  **Prior work.** Mazurkiewicz traces and partial-order reduction (persistent, stubborn and ample
  sets) are classical. What is specific here is deriving the reduction relation from the same
  history-descent conditions that prove convergence, including the causal, enabledness, repair and
  at-least-once refinements, so the soundness of each reduction is a theorem about the condition it
  is used for.

### 9. Reconfiguration inside a run (gap 20)

**Status: in progress (gap 20 narrowed, `coq/Reconfiguration.v`).** The coverage pass recorded this
as a new axis ([COVERAGE.md](COVERAGE.md), gap 20 in [REGIME-AUDIT.md](../REGIME-AUDIT.md)).

- **Done.** A run is a sequence of steps under configuration A, one switch (a migration `m` of the state, a
  translation `tau` of the A-events still in flight), then a run under B. For a single registry
  under free delivery: at a quiescent barrier, `barrier_exact` (each side's own condition when
  `rhoB_star o m` is injective on the quiescent reachable states, `barrier_exact_faithful`; the
  qualifier is needed, `forgetful_migration`); live, `live_exact` (B's condition from `m s` for every
  reachable `s`, quiescent or not, plus the cross pairs S1, an in-flight event commutes with the
  switch, and S2, the switch absorbs A's compensation; A's own condition is not a conjunct), each
  conjunct needed with A and the barrier switch converging (`cap_raise`, `doubling_migration`,
  `migrated_transient`). The classification safe online, safe behind a barrier only, unsafe is
  unique (`classified_unique`) and decidable on finite instances (`classify_finite`, under a
  faithful migration; `live_dec` always). Federations under FedMachine semantics, topology and rules
  changing: `fed_live_exact` (B's C1R1 and C2R at the migrated start, plus the switch commuting with
  every in-flight event), `fed_barrier_exact`; `late_edge` (adding an edge read by an in-flight event
  diverges live, not at a barrier).
- **Done (residue (c), `coq/ReconfigurationClosure.v`).** In the deterministic model (gsm's runtime),
  the barrier's A part for a migration that is not injective: A converges modulo M iff M agrees on
  every pair of the pair closure (two adjacent events in both orders at a reachable state, closed
  under applying one event to both components; `amodm_swap_exact`, `amodm_closure_exact`). On
  finite instances the closure is a finite search that finds a witness iff one exists
  (`amodm_witness_exact`), so the classification is decided with no faithfulness hypothesis and no
  unknown outcome (`det_classify_complete`); gsm's pruned search computes the same closure
  (`gsm_closure_exact`), so its empty result is a certificate.
- **Remaining.** A live switch in the distributed model, where propagation is in flight
  (projections sent under A merged under B); declared independence, causal or at-least-once
  delivery across the switch; and gsm's `CheckMigration` reporting the exhausted AmodM search as
  safe behind a barrier instead of unknown (gsm ROADMAP item 2).

- **Before.** Every module fixed the topology and the rules for a whole run. Real deployments add
  services, migrate schemas and change rules while events and projections are in flight. A change
  at a barrier (drain, then switch) was taken to reduce to the existing results applied per run; a
  live change had no theorem.
- **Target.** Exact conditions for a live change from configuration A to configuration B: when every
  run that mixes A-events and B-events (and projections sent under A, merged under B) converges, and
  when a barrier is necessary, with a counterexample at each boundary.
- **Approach.** Model a run as a sequence of configurations with a switch step, reuse the
  convergence conditions on each side, and characterize the cross-configuration critical pairs
  (an event or projection of A meeting one of B), in the style of C1 and C2.
- **Done when.** The exact conditions pass the gate, and gsm can expose them as a migration check
  that classifies a change as safe online, safe behind a barrier, or unsafe with a witness.

## Open items

The convergence regimes that still lack an exact condition, consistent with
[REGIME-AUDIT.md](../REGIME-AUDIT.md) (its gap numbers in parentheses). Every other regime has a
machine-checked exact condition, or a hardness result where no efficient one exists (for lossy
networks without a spanning root, the 3-SAT reduction is mechanized, #57).

**Lead item: make P exact on cycles.** The theory is exact for acyclic composition: in the
canonical-execution framework ([THEORY.md](THEORY.md#canonical-execution)), E, S and H are exact
for single systems and P (`factor_exact`) for acyclic composition, while on cycles P has the
soundness direction only (`cyc_factor_sound`, `cyc_factor_sound_gc`) and locality fails without
acyclicity (`cyclic_lc_sound_fails`). The open convergence problems that are cyclic are instances
of one question, what additional structure makes P exact on cycles: gap 3 (rootless propagation on lossy networks, [LOSSY-NETWORKS.md](LOSSY-NETWORKS.md#p2-rootless-convergence-in-reading-b-the-runtime-model)
P2) and the monotone-overlap part of gap 13. Gap 13's other
residues (relative certificates on covers not closed under sources, and the variable-level site)
are not cyclic and stay separate. Of the gaps the coverage pass added, 16 (a to c), 17, 18 and 19
are cyclic (19 only in its residue, a cyclic `J` in the distributed model); 15 and 20 are not
(16 (d), the acyclic part of 16, is closed: `RobertFair.v`), and 21 is in part (its residue (b), channels on cycles; classified in the audit's frontier
table). Gap 5 (cyclic monotone collapse) and gap 19 (a) (blocks of different engines) were on this list
and are closed without P (`CompositionBlocks.v`): the cycles sit inside blocks of the condensation,
which is acyclic, so Bekic's principle (`bekic_lfp`) and the interface theorem (`compose_exact`)
compose them; their content is the interleaving conjunct, not P on a cycle. Gap 14 (convergence alone in the no-reset cyclic distributed
model) was on this list and is closed (#90) without P: its exact condition (`conv_quiet_exact`)
is a whole-system E, S and H statement whose canonical state is the quiescent state propagation
settles in, ghost allowed, instead of the least fixed point. The obstacle there was the choice of
canonicalizer, not composition, so it says nothing about P on cycles. Gap 2 (rootless invertible
networks beyond a single cycle) was on this list too and is closed (#91), also without P: with
bijective transports and the regular action, propagation copies offsets relative to a section
(`net_origin`), so the cycles reduce to a global `H^1` condition plus the acyclic condensation
(`net_unique_normal_form_iff`: an authority root per component). That reduction needs invertible
transports and does not reach gaps 3 and 5. The cyclic raw material: GC and its exactness on monotone cycles (`gc_iff`,
`net_events_converge_iff`), per-target checks over normal-form images (`cyc_check_gc_lfp`), reset
epochs (`epoch_conv_iff`), rootless invertible networks (`net_unique_normal_form_iff`; single
cycles `rootless_unique_iff`), root sets
(`root_set_criterion_graph`) and P's soundness on cycles (`cyc_factor_sound_gc`). Each gap is
checked against its own description in
[REGIME-AUDIT.md, the cyclic frontier](../REGIME-AUDIT.md#the-cyclic-frontier). Done when some
gap in this list is settled by an exact form of P on cycles, or when a cyclic gap is shown to need
something outside P.

| Item | Status | Size |
|---|---|---|
| Make P exact on cycles: the cyclic frontier, of which gap 3 and gap 13's monotone-overlap part are instances (gaps 14, 2 and 5 were instances, closed by #90, #91 and `CompositionBlocks.v` without P) | open; soundness half mechanized (`cyc_factor_sound`, `cyc_factor_sound_gc`), locality fails without acyclicity (`cyclic_lc_sound_fails`) | large |
| Distributed propagation model (gap 1): acyclic exact converse; a model for monotone cycles | acyclic done, #60 (`dist_exact`); cycles modeled and exact under reset epochs and under `LowR`, #62 (`epoch_conv_iff`, `low_conv_iff`) | n/a |
| Distributed model on monotone cycles without resets and without `LowR` (gap 1, residual): move `FlushR` and `NoGhostR` off the hypothesis side and characterize them | done, #64: `flush_fed_iff`, `fair_fed_iff` (each conjunct necessary), `FlushR` via `fair_flush_sound_iff`, `NoGhostR` via `noghost_event_iff` and `noghost_inv_iff`, gsm reduction `lens_noreset_iff` | n/a |
| Distributed model on monotone cycles without resets: exact condition for convergence among quiescent interleavings alone (`FlushR /\ DConvQ`), when they may agree on a common ghost (gap 14) | done, #90: `conv_quiet_exact` (`FlushR /\ DConvQ <-> FlushR /\ FlushDetR /\ FlushXUR /\ QMConv`: the three layers of `flush_fed_iff` relative to the quiescent state propagation settles in instead of `Lfp`; each conjunct necessary), `fair_conv_exact`; recovers `quiet_conv_iff` and `flush_fed_iff` in the ghost-free case; `XUcR`, `FMConv` and `NoGhostR` are each not necessary (`ghost_conv_not_fed`) | n/a |
| Rootless invertible networks beyond a single coherently oriented cycle (gap 2) | done, #91: `net_reachable_iff` (the reachable set), `net_nf_exists_iff` (existence from every start iff `H^1 = 0` and one source component per weakly connected component, or `\|G\| = 1`), `net_unique_iff` (unique iff, given `H^1 = 0`, a de facto root in every component, or `\|G\| = 1`), `net_unique_normal_form_iff` (both: an authority root per component, or `\|G\| = 1`); single-cycle theorems recovered; counterexamples `rootless_global_holonomy`, `rootless_mixed_square`, `rootless_source_feeds_cycle` | n/a |
| Rootless propagation on non-invertible networks, resolver reading (gap 3; [LOSSY-NETWORKS.md](LOSSY-NETWORKS.md#p2-rootless-convergence-in-reading-b-the-runtime-model) P2) | open. Progress, #80: on the **global** signed interaction graph, sufficient certificates for E under an explicit resolver semantics (bounded finite-height value sets, fair asynchronous schedules): balance with low starts (`signed_settlement`) or with at most one fixed point (`signed_fidelity`), each hypothesis shown needed; sufficient, not an exact characterization. Progress, #83: on Boolean **local** (state-dependent) interaction graphs, for every `n`: no local positive cycle gives at most one fixed point and CanonicalFidelity (`local_fidelity`, `local_fidelity_canon`; Remy, Ruet and Thieffry 2008), strictly beyond the global certificates (`local_weaker_than_global`); no local negative cycle alone gives nothing (`local_neg_free_no_fixed_point`), but with non-expansiveness or one vertex on every local positive cycle it gives E's Settlement from every start (`richard_t3`, `richard_t4`; Richard 2011, Theorems 3 and 4), and no local cycle gives all of E (`shih_dong_E`; Shih and Dong 2005). These certify Settlement in its existential (flush) form only: none of these local conditions alone gives fair-schedule settlement (`shih_dong_not_fair`, `ring_local_conditions`). Progress, #92 (`LocalFairSettlement.v`): under no local cycle (A) plus out-degree at most one (B), the synchronous form (`sync_simple`: every synchronous orbit reaches the unique fixed point within `2^n` steps, the conclusion of Shih and Ho 1999, Theorem 3.1, by a different proof; `sync_orbit_fixed` needs (A) only at one orbit state), token monotonicity (`ucnt_mono`), and fair settlement from every start with at most one unstable vertex (`one_token_fair_settlement`), with (B) and both signs of (A) shown needed (`outdeg_needed`, `no_neg_not_enough`, `no_pos_not_enough`). Progress, #93 (`LocalTwoToken.v`): no closed asynchronous run with two unstable vertices changes the state (`two_token_closed`), so fair settlement holds from every start with at most two unstable vertices (`two_token_fair_settlement`): at a state with one token on each side of the fixed point, the token that agrees with the fixed point never points into the set where the state disagrees with it (`head_arc`), so a closed two-token run rearranges into a synchronous periodic orbit (`swap_TH`, `W_main`), which `sync_orbit_fixed` excludes. Next: (a) fair-schedule settlement under (A) and (B) from every start: show that no closed asynchronous run has three or more unstable vertices at each of its states (by `fair_settlement_of_acyclic` this suffices; for three tokens a token agreeing with the fixed point can pass to one that disagrees, so the two-token argument does not apply as it stands). Computational evidence, not mechanized: no network on n = 3 to 6 vertices with (A) and (B) has any cycle in its asynchronous state graph, by an exhaustive SAT search ([research/gap3-fair-settlement](../research/gap3-fair-settlement/README.md)). The conjectured key lemma is F2 in that directory's `REPORT.md`; #92 proves it for one unstable vertex (the isometry argument behind `sync_orbit_fixed`), #93 settles two by a different route, and three or more are open. The two-token case is also decided by SAT for n = 3 to 7 (`research/gap3-fair-settlement/K2.md`). Shih and Ho 1999 has been read: it treats synchronous iteration only, and its proof (von Neumann neighborhoods mapped into von Neumann neighborhoods) does not carry over to single asynchronous updates. Also open: other local conditions combined with a restriction on the global graph's cycles, and an exact condition; (b) multivalued local fidelity, Richard and Comet 2007 (cited, not mechanized; the Boolean case is `local_fidelity`), and the multivalued forms of Theorems 3 and 4 if they hold; (c) value sets without bounds; (d) an exact condition | medium to large |
| Event order under non-invertible root-set coordination (gap 4; P6) | done, #59 (`forest_events_exact`) | n/a |
| Cyclic monotone collapse (gap 5) | done in the FedMachine model (`CompositionBlocks.v`: `bekic_lfp`, `mono_collapse_nf`, `mono_collapse_exact`, so `N'` converges iff `N` does iff GC); the distributed form is gap 19 (b)'s residue | n/a |
| Enabledness that a compensation step can disable (gap 6; outside `jc_exact`'s `enabled_after_comp`) | done, #56 (`jcg_exact`) | n/a |
| State-based CRDT merges as an instance of the exact theorems (gap 7) | done, #58 (`merge_action_exact`, `cvrdt_on_exact`; the iff as exported: `cvrdt_on_iff`) | n/a |
| Mechanize the 3-SAT reduction behind NP-completeness of lossy-network existence ([LOSSY-NETWORKS.md](LOSSY-NETWORKS.md#32-the-reduction-from-3-sat) 3.2) | done, #57 (`net_section_iff_sat`, `net_size`, `np_certificate`; NP-completeness by the standard argument) | n/a |
| Least fixed points on complete lattices without ACC (gap 8) | design exclusion (classical Knaster-Tarski; gsm's finite domains satisfy ACC) | n/a |
| Delivery and enabledness off the replay model (gap 15; from the coverage pass, [COVERAGE.md](COVERAGE.md)): (a) at-least-once delivery under declared independence `I` (gsm's `NotIdempotent` with `Independent` pairs); (b) at-least-once delivery for stream processors; (c) causal or at-least-once delivery in the distributed model; (d) buffered guards in federations | done: (a) done (`AtLeastOnceDeclared.v`: `dalo_exact`, `safe_i_exact`, unordered retries `dalo_r_exact`; `NotIdempotent` sound at reachable witnesses, complete when declared pairs commute at reachable states and retries respect the declared order); (b) done (`StreamAtLeastOnce.v`: `stream_alo_exact_free`, any enabledness `stream_alo_exact`); (c) done (`DistributedDelivery.v`: `dist_delivery_exact` for any prefix-closed delivery class, `dist_causal_exact`, `dist_alo_exact`, `dist_causal_alo_exact`); (d) done (`FederatedGuards.v`: `fed_buffered_exact`, `fed_buffered_edge`, any enabledness `fed_jcg_exact`). Closed | n/a |
| Distributed propagation off its current hypotheses (gap 16): (a) events with rootless propagation on cyclic invertible networks; (b) ACC without finite height; (c) local compensation as separate steps on cycles; (d) every fair update schedule on an acyclic network (Robert's asynchronous half) | narrowed: (d) done (`RobertFair.v`: `rb_robert_fair` with the round bound `rb_rounds` and the effective-step bound `rb_effective`; with finitely many events `rb_events`, exactly `rb_fair_dist_exact`; resolver model `rb_lens_robert`; Boolean networks with an acyclic global graph `rb_robert_boolean`); (a), (b), (c) open | medium |
| Rootless edge-writer dynamics beyond the regular action (gap 17): lossy maps at in-degree two or more, non-free invertible actions; existence is exact and NP-complete, settlement and uniqueness are open | open | medium |
| Existence and counting in reading B without a spanning root (gap 18): mechanize one of the reductions between the readings | open | small |
| Composition beyond acyclic collapse (gap 19): cyclic blocks of different engines, coordination-free; collapse in the distributed model | narrowed (`CompositionBlocks.v`): (a) done for any engines (`compose_exact`, each conjunct necessary, `compose_isolated_refuted`; `compose_collapse`; `interface_closed`; `mixed_rootless_exact`, `mixed_mono_iff`); (b) done for an acyclic `J` (`dist_collapse_iff`; `dist_collapse_refuted`; `dist_collapse_xu`). Open: (b) for a cyclic `J` (the no-reset cyclic distributed model and reset epochs, `J`'s atom its own flush to quiescence) | medium |
| Reconfiguration inside a run (gap 20, **new axis**): topology or rules change while events or propagation are in flight | narrowed: modeled in `Reconfiguration.v`; single registry under free delivery, exact at a barrier (`barrier_exact`, `barrier_exact_faithful`) and live (`live_exact`: B's condition from every migrated reachable state plus the cross pairs S1 and S2; A's own condition not necessary, `forgetful_migration`); the classification online, barrier only, unsafe decidable on finite instances (`classify_finite`); federations under FedMachine semantics, exact at a barrier and live (`fed_barrier_exact`, `fed_live_exact`; `late_edge`); in the deterministic model, an unfaithful migration's barrier A part in local and finite form, with the classification decided with no unknown case (`ReconfigurationClosure.v`: `amodm_closure_exact`, `det_classify_complete`; residue (c) closed). Open: (a) a live switch with propagation in flight (the distributed model); (b) other delivery classes across the switch | small to medium |
| Propagation over channels (gap 21, **new axis**): late, reordered or duplicated projections; gsm's `MergeProjection` and `MergeProjectionAfter` | narrowed: modeled in `ProjectionChannels.v`; acyclic, exact over channel-reachable states in either mode (`chan_exact`, `chan_exact_global`); versioned merging converges at drain exactly when it does after a flush, and under gsm's XU and C2 (`vsettle_exact_cond`, `vsettle_xu_c2`); plain merging settles iff nothing stale is in flight (`plain_settle_iff`; fails under XU, `plain_stale_counterexample`); two-level networks, `dist_exact`'s condition (`vchan_twolevel_exact`); nested networks, every single-source network among them, the same (`vchan_nested_exact`, `vchan_single_exact`, `ProjectionChains.v`), and beyond them `CXUR true` is strictly stronger than `XUR` (`vchan_skip_counterexample`). Open: (a) the exact network class between nested networks and that counterexample (a diamond, for example); (b) flush and reset epochs over channels on cycles (the ghost survives, `vchan_cyc_ghost`) | small to medium |

Optimization and counting, which do not bear on when state converges (audit gaps 10 to 13):

| Item | Status | Size |
|---|---|---|
| Minimum coordination on invertible networks tied to the authority-root plan model (gap 10) | done, #72: `plan_min_exact` (connected networks; the best plan's cost is the group feedback edge set number, for every root); NP-hard by a mechanized Max-Cut reduction (`maxcut_reduction`), Max-Cut's NP-completeness cited | n/a |
| Minimum coordination on non-invertible networks (gap 11; `LOSSY-NETWORKS.md` P4, reading A) | done, #70: `lmin_root_set`, `lmin_decide`; NP-hard even to tell minimum 0 from 1, by a mechanized 3-SAT reduction (`lmin_reduction`); in NP (`min_le_np_certificate`). The reading-B variants of P4 go with gap 3 | n/a |
| `H^1` on the 2-complex (gap 12) | done, #71: `nerve_H1_classification` (any group), `nerve_H1_Z2_count` (over Z/2). Scope: the dimension formula for other coefficients, and the identification of the presented group with the fundamental group, are not mechanized | n/a |
| Sheaf gluing, positive assembly (gap 13) | narrowed, #73: exact on the registry-level site (`sheaf_iff_refines`, `cert_sheaf`). Open (paper only): the variable-level and monotone-overlap site; a sheaf condition for relative certificates on covers not closed under sources | medium |

Open convergence items after the coverage pass: gaps 3 and 16 to 21, plus the design exclusion
of gap 8 and the design exclusions X1 to X5 below. Gaps 1, 2, 5,
14 and 15 are closed. Of the optimization and counting gaps, only gap 13's residual remains.

## Removable caveats, lower value

- **Non-invertible cycles, mechanized criterion.** Done: a section around a cycle exists iff the
  loop composite has a reachable fixed point (`thm_obstruction_general`,
  `thm_obstruction_reachable`, `CohomologyGeneral.v`, #36), and on any graph iff some root
  assignment of a root set drives a consistent state (`root_set_criterion_graph`, `RootSet.v`, #54);
  deciding that is NP-complete, with the reduction mechanized (`LossyHardness.v`, #57), and event
  order under root-set coordination is exact (`forest_events_exact`, `RootSetEvents.v`, #59).
- **Distributed model for cycles.** Done: the acyclic exact converse is `dist_exact`
  (`DistributedExact.v`, #60); the model on monotone cycles is exact under reset epochs
  (`epoch_conv_iff`) and under `LowR` (`low_conv_iff`) (`DistributedCycles.v`, #62), and without
  resets with no reachable hypothesis left (`flush_fed_iff`, `fair_fed_iff`,
  `DistributedCyclesExact.v`, #64); convergence among interleavings alone, without agreement with
  the FedMachine, is exact too (`conv_quiet_exact`, `DistributedConvergenceExact.v`, #90, gap 14). Checking the no-reset condition
  in gsm: cheap per-event and per-network routes exist for `FlushR` (`infl_evsound`,
  `evlow_fairflush`, `step_sound_fairflush`); `NoGhostR` in general needs a global invariant
  (`noghost_inv_iff`, `unique_or_low_noghost`).
- **C2 converse over all valid starts in general networks.** The C2 converse applies when some
  valid consistent state realizes the witness pair `(z, b)` (for example a two-registry federation
  whose source has no repair); a general statement quantifying over all valid starts is open.
- **Cost of checking GC.** On a cycle the exact condition GC has no per-edge reduction, so a check
  enumerates reachable normal forms (or the image of `N`) and tests every independent pair. A
  cheaper sufficient check, or a bound on that exploration, is open.
- **Authority root in gsm's plan.** `CoordinatedCycles.v` shows the normal form is unique only given
  the authority root (`root_choice_matters`). Done for gsm's current plan as of gsm v0.13.0:
  `CoordinationPlan` still cuts every cycle, and each `CoordinationPoint` now names its `Authority`
  (`BuildCoordinated` rejects an authority other than the cut edge's target). Open: the
  holonomy-minimal plan in gsm's `HOLONOMY-COORDINATION-DESIGN.md` is not implemented; when it is,
  its plan must name its root the same way.
- **Synthesis.** gsm's `Registry.Synthesize` (exhaustive search for a convergent repair, or a witness
  that none exists) is implemented but not mechanized.
- **Rank of `H^1` on the full nerve.** Done, #71: with the triangle relations, `H^1` is classified
  for any group (`nerve_H1_classification`) and counted over Z/2 (`nerve_H1_Z2_count`); triangles
  can only lower the count (`nerve_Z2_cell_lowers`).
- **Complexity results.** NP-hardness of minimum coordination now has mechanized reductions (Max-Cut
  for invertible networks, `maxcut_reduction`, #72; 3-SAT for lossy ones, `lmin_reduction`, #70).
  Fixed-parameter tractability, planar tractability and approximation hardness are cited from the
  group feedback set literature; they are not this work's results.
- **gsm's coordination plan at the minimum.** `plan_min_attained` says some rooted spanning tree's
  plan attains the minimum; gsm's `CoordinationPlan` cuts every cycle. A gsm search for the
  minimum-cost plan would be exact for small networks and is NP-hard in general
  (`maxcut_plan_reduction`).

## Planned artifact: the Convergence Atlas

A public, illustrated catalog of the regime map, in the tradition of the Complexity Zoo, the
Information System on Graph Classes (graphclasses.org) and *Counterexamples in Topology*. Working
title: *The Convergence Atlas: governed concurrent state* (scoped to this theory's regimes, not to
convergence in general).

- **One entry per regime:** the setting, the exact condition (or the hardness result, or the gap
  stated in the open), the Coq theorem names, the cheap sufficient check gsm runs, and the prior
  work it relates to.
- **Plates:** each boundary counterexample drawn as a numbered plate in the style of a scientific
  atlas (for example the flip-flop ghost, the negation loop, `shih_dong_not_fair`'s period-8
  schedule), each backed by a gated theorem.
- **Neighbors as entries:** CRDTs, CALM, invariant confluence, Newman's lemma, Knaster-Tarski and
  the Thomas/Richard network results get entries of their own, with this work's results placed
  among them (sources: [LANDSCAPE.md](LANDSCAPE.md), [SUBSUMPTION.md](SUBSUMPTION.md)).
- **Generated, not hand-maintained:** built from [REGIME-AUDIT.md](../REGIME-AUDIT.md), so it stays
  as current as the audit and never claims more than the audit does.

Status: planned, not started. Not a caveat removal; it does not change what is proved.

Poster draft: [docs/atlas/](atlas/README.md) (`poster.html`: one tile per regime with a detail card, following REGIME-AUDIT.md; `check.py` verifies the theorem names against the gate).

## Planned paper: the regime map

A fourth paper whose main object is the map itself, not one regime. The three papers each state
part of the theory (the single registry, federated networks, the categorical structure); none
states the classification: one question asked in every regime, the axes that generate the regimes,
and in each cell an exact condition, a hardness result or a gap stated in the open, mechanized and
audited. The Atlas above is the reference catalog; this paper is the citable argument for it.

Working title: *An exact regime map of governed concurrent state*.

Outline:

1. **The question.** Do all event orders reach one normal form, and what condition is necessary
   and sufficient. The canonical execution layers E, S, H and P, and why the same layers recur in
   every regime ([THEORY.md](THEORY.md)).
2. **The axes.** The thirteen axes, the ten axis dependences that prune the product, and how the
   empty cells were found before any proof ([COVERAGE.md](COVERAGE.md)): gaps 15 to 21 were
   predicted by the axes, not discovered case by case.
3. **The map.** One table, one row per regime: the exact condition with its theorem name, the
   counterexamples showing each conjunct is needed, and the check gsm runs. Generated from
   [REGIME-AUDIT.md](../REGIME-AUDIT.md), like the Atlas.
4. **Representative theorems** in plain mathematics: the single-registry iff (`cc_exact`), a
   composition result (block composition, gap 19, when it lands), and reconfiguration
   (`live_exact`, `amodm_closure_exact`), each with its boundary counterexample.
5. **Transfer.** Results in one regime that are instances of another (`cvrdt_on_exact`, the
   rootless corollaries of `net_unique_normal_form_iff`, engine instances of block composition).
6. **The open part.** The gaps stated in the open, with the cyclic frontier as the one remaining
   question, and the design exclusions X1 to X5 with their justifications.
7. **Quotients for checking.** How the semantic quotients become verification quotients: the
   symmetry, abstraction, difference and compositional reductions behind gsm's scale features,
   each with the counterexample that marks its fragment.
8. **Method.** Every cited name read as a statement, every result gated axiom-free on three Coq
   versions, and the audit's rule that a cell claims no more than its theorem.

Constraints:

- **Scope in the claim.** "Exact" is relative to the model each regime states; the abstract and
  every table caption say so.
- **Related work per community.** CRDTs and CALM, invariant confluence, rewriting (Newman, Huet),
  Boolean and discrete networks (Robert, Thomas, Richard, Shih and Ho), fixed points (Knaster-Tarski,
  Bekić), using [LANDSCAPE.md](LANDSCAPE.md) and [SUBSUMPTION.md](SUBSUMPTION.md). No "first" or
  "new" without a literature check recorded there.
- **Venue.** arXiv first; then a journal that takes long mechanized work (for example Logical
  Methods in Computer Science); a conference version at a mechanization venue (CPP, ITP) only after
  checking its current dates.

Status: planned, not started. Drafting begins after gap 19 lands, so the map includes block
composition. Not a caveat removal; it does not change what is proved.

## Fundamental limits (stated, not removable)

- **Continuous state.** Convergence of continuous dynamics needs a different argument (contraction,
  see `LYAPUNOV-EXTENSION.md`). Multi-basin landscapes have no unique attractor.
- **Eventual delivery.** A replica that never receives an event cannot converge with one that did.
- **Purity of Go closures.** gsm can verify combinator rules exactly; arbitrary Go closures can be
  tested, not proven pure.
- **Trust base.** The extracted checkers rely on Rocq's extraction, the Go code generator and the Go
  toolchain.

## Design exclusions (stated by the coverage pass)

Not removable by proof within the stated scope; justifications in
[COVERAGE.md](COVERAGE.md#new-design-exclusions).

- **X1. Byzantine participants.** A participant that runs other rules is not governed state;
  crash faults and lost messages are the eventual-delivery limit above.
- **X2. Nondeterministic repair.** Compensation is a function in every module; the scope is
  deterministic governed state.
- **X3. Probabilistic schedules.** The axiom-free gate rules out the standard library's real
  numbers; on a finite state space, settlement with probability 1 is classically the existential
  settlement already mechanized.
- **X4. Infinite networks.** Every network, here and in gsm, is a finite list of registries and
  edges.
- **X5. Real-time semantics.** The model is untimed: a timer firing is an event, and convergence
  time is the asymptotic cost item 7 lists out of scope.

## Sequencing

Items 1 to 4 and 6, the monotone-cycle event result, the C1/C2 converse and item 7's work packages
have landed, so their theorem statements are fixed and item 5 can start. The open items above are
independent of item 5, and each can be attacked on its own, although the convergence gaps share one
question (the lead item, P on cycles); the smallest two (event order under root-set coordination
and the state-based CRDT instance) landed in #59 and #58, with #56 and #57. When item 5 and the open items land, every remaining caveat on
this page is either a design exclusion (least fixed points without ACC; X1 to X5) or a fundamental limit; the
lower-value items above remain open.
