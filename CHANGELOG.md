# Changelog

This file records notable changes to the papers and the mechanized proof in this repository.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The repository has no version tags, so entries are grouped by date (merge date for pull requests, commit date for earlier history, both as recorded in the git history, UTC-7). Theorem counts refer to the minimum enforced by the axiom-free gate in `coq/verify.sh`.

## [Unreleased]

### Added
- `coq/CausalReplay.v`: convergence under causal delivery, where only concurrent events need to commute (#19).
  - `causal_convergence`: if governed steps commute on concurrent pairs, any two causally consistent delivery orders reach the same state.
  - `causal_cmrdt_SEC`: op-based CRDTs (concurrent operations commute, causal delivery) converge, as an instance.
  - `compensation_free_exact`: a compensation-free system meets the causal condition if and only if it is an op-based CRDT.
  - `witness_causal_not_cmrdt`: strictness under causal delivery.
  - `witness_beyond_all_pairs`: a system that converges under causal delivery although not every operation pair commutes, so the all-pairs theorem does not cover it.
  - `causal_tequiv`: causally consistent orders are trace-equivalent under concurrency, connecting causal delivery to `run_tequiv` in `Trace.v`.
- `coq/GovernanceCausal.v`: `causal_governance_confluent`, the rewrite-system Convergence Theorem with compensation interleaving, with CC1 required only for distinct co-enabled events; witness `cw_confluent` / `cw_violates_all_pairs_cc1` satisfies the weakened hypothesis while violating the original (#19).
- `coq/README.md`: section for the causal modules (#19).
- `coq/FederationEvents.v`: convergence of event interleavings across registries in acyclic federations, local events on a target interleaving with propagation from its sources (#21).
  - `fed_events_commute`, `fed_interleavings_converge`, `fed_permutations_converge`: per-registry conditions plus C1 (cross-registry CC) and C2 (repaired CC) give convergence up to swaps of independent events.
  - `propagation_flush`, `dist_interleavings_converge`: the distributed model with propagation as separate steps; `xu_implies_c1_c2`.
  - `audit_counterexample`, `c2_counterexample`: C1 and C2 are each needed; `supply_instance`, `supply_converges`: non-vacuity.
- `ROADMAP.md`: the remaining caveats, split into removable (high and lower value) and fundamental limits, with approach and acceptance criterion for each (#22).
- `coq/GovernanceWF.v`: the Convergence Theorem with WFC over an arbitrary well-founded order (`governance_wf_confluent`, `causal_governance_wf_confluent`), a lexicographic-product potential, compensation with no potential, the nat-valued theorems recovered as corollaries, and an infinite instance on `Z` (`zw_confluent`) (#23, roadmap item 1).
- `coq/ChaoticACC.v`: chaotic iteration reaches the least fixed point under the ascending chain condition below it, with no rank (`chaotic_acc_reaches_lfp`); Kleene iteration under ACC stabilizes (`kleene_acc_lfp`); the finite-height theorems recovered; an ACC lattice with chains of every length and provably no rank into `nat` (`ole_no_rank`) (#23, roadmap item 1).
- `coq/FederationEventsCycles.v`: event interleaving for monotone cyclic federations. `gc_iff`: the global condition GC (independent governed steps commute at every reachable state) holds iff all trace-equivalent sequences converge; gsm's `normalizeCyclic` modeled (`cyc_N_lfp`, `cyc_N_unique`, `cyc_events_converge_iff`); `cyc_instance`, `bottom_matters`, `cyc_counterexample` (#24).
- `coq/FederationEventsConverse.v`: C1 and C2 are the exact check for acyclic federations at reachable witnesses (`fed_exact`, `fed_exact_full`, `acyclic_gc_iff`, `static_c1_c2_gc`); `naive_converse_fails`: static C1 fails yet every interleaving converges, so the converse needs reachable witnesses (#24).
- `coq/AtLeastOnce.v`: convergence under at-least-once delivery (#25, roadmap item 2).
  - `alo_absorbed`, `alo_commuting_exactly_once`, `alo_commuting_converges`: duplicates of idempotent governed steps are absorbed.
  - `causal_alo_exactly_once`, `causal_alo_converges`: the causal case, with causally consistent redelivery.
  - `non_idempotent_diverges`, `inc_duplicate_diverges`: a non-idempotent duplicate diverges; `late_duplicate_diverges`: the naive causal statement is false.
- `coq/GovernanceConverse.v`: the converse of CC and of causal convergence (#26, roadmap item 3).
  - `cc_exact_from`, `cc_exact`, `cc_exact_global`: unique normal forms iff CC on the reachable states, with canonical repair.
  - `jc_exact`: for any enabledness, confluence iff the critical pairs are joinable at every reachable configuration (JC).
  - `causal_exact`, `causal_convergence_exact`: causal convergence iff concurrent pairs commute after every causally consistent prefix (CCR).
  - Counterexamples to the naive converses: `rho_star_qualifier`, `masked_cc1`, `naive_causal_converse_fails`.
- `coq/CoordinatedCycles.v`: soundness of the holonomy-minimal coordination plan for non-monotone cycles (#27, roadmap item 4).
  - `coordinated_sound`, `coordinated_unique_nf`: driving values along a spanning tree from an authority root, with balanced non-tree edges kept as checked constraints and unbalanced edges coordinated, gives a unique normal form given the root, reached by every topological order.
  - `plan_exact`, `coordination_needed`, `coordinated_events_converge`.
  - Instances `copyback_zero_coordination` and `negation_one_coordinated`; counterexamples to the naive statement `copyback_without_authority`, `root_choice_matters`, `noninvertible_balance_not_static`, `nonfree_holonomy_counterexample`.
- `coq/PAPER-MAP.md`: every numbered result in the three papers mapped to its Coq counterpart with a status (EXACT, DIFF, PARTIAL, REFUTED, NOT, CITED, DEF), difficulty estimates and work packages for the gaps; the audit step of roadmap item 7 (#30). Headline findings: the federated convergence theorems (`thm:fed-cc`, `thm:fed-convergence`, `thm:resolved-convergence`, `lem:authority` (c)) are false as stated (`audit_counterexample`, `c2_counterexample`); the last sentence of `thm:monotone-cycles` is refuted by `cyc_counterexample`; base `thm:footprint-cc1` is false as stated.
- `coq/FederationEventsCyclesCheck.v`: event order on monotone cycles, checked per event (#31, roadmap item 6).
  - `cyc_check_gc`, `cyc_check_converges`: gsm's per-edge C1 and C2, read on a cycle (`C1cyc`, `C2cyc` over a set containing every normal form's shared values, such as the morphism images), imply GC and convergence of all trace-equivalent sequences from a normal form; `cyc_check_gc_lfp` for gsm's Kleene normalizer; `cyc_check_step`, `footprint_c1`, `lfp_commute_gc`.
  - Non-vacuity `cyc_check_instance`; `check_rejects_latch`: the check rejects the latch of `cyc_counterexample`.
  - Counterexamples to the naive candidates: `monotone_c2_insufficient` (monotone events plus C2 do not give GC), `c1_localcc_insufficient` (C1 plus each registry's own CC do not give GC, so C2 cannot be dropped).
- `coq/CategoricalBridge.v`: the categorical paper's structural core on one federation model (#32, WP7).
  - `cat_prop_one`, `cat_prop_one_product`, `cat_prop_one_limit`, `cat_LF_split`: Proposition 1 exactly, with `L_F` an equalizer into a finite product (a finite limit) and split into the component normal-form conjunct and `Categorical.Consistent`.
  - `rhoFold_run`, `consistentList_iff_LF`, `rhoFold_order_independent`, `rhoFold_order_perm`: `Categorical.rhoFold` over a topological order computes `FederationOrder.run` and inherits order independence.
  - Theorem 1 on `L_F` under local idempotence, the lens law and shared-component stability: `cat_thm_one_sound`, `cat_thm_one_complete`, `cat_thm_one_idempotent`, `cat_thm_one_image`, `cat_thm_one_fixed`, `cat_thm_one_order_independent`, `cat_thm_one_fold_image`.
  - `cat_thm_one_m1_counterexample`: with M1/R2 read as validity preservation, as the paper's Background defines them, Theorem 1 is false.
  - Gates the paper-cited `Categorical.v` names that were not in the gate (`fixed_is_equalizer`, `retract_fixes_fixed`, `rhoL_idempotent`, `rhoL_image_iff_L`, `rhoL_L_iff_fixed`, `rhoFold_sound`, `rhoFold_complete`, `rhoF_from_app`).
- `coq/RhoStar.v`: `rho*` constructed from WFC, and the base facts that rest on it (#33, WP1).
  - `strong_absorption_iff_cc2`: under WFC, CC2 holds iff strong absorption does.
  - `base_def_rhostar`, `base_def_rhostar_least_unique`, `rho_star_canonical`: `rho*` built (`rho_star`, and `rho_star_wf` over any well-founded order), computable and independent of the measure.
  - `wfc_governance_confluent`, `wfc_causal_governance_confluent`, `wfc_governance_wf_confluent`, `wfc_cc_exact_from` and their unique-normal-form forms: the `rho_star_reach` and `rho_star_valid` hypotheses discharged from WFC; `paper_governance_unique_normal_forms`, `paper_causal_governance_unique_normal_forms` in the paper's terms.
  - `base_rem_absorption`, `base_thm_strong_absorption`, `base_lem_termination_bound` (tight: `lv_termination_bound_tight`), `causal_lem_termination_bound`, `base_lem_finite_implies_ubc`, `base_thm_complexity_per_event`; deps-based enabledness (`deps_enabled_after_remove`, `deps_enabled_after_comp`, `deps_coenabled_independent`).
  - Qualifier `cat_bg_nonempty_needs_a_state`: WFC alone does not make the valid set non-empty (the empty state type).
- `coq/PaperInstances.v`: the papers' concrete examples on their own data (#34, WP2).
  - Order fulfillment (`of_cc1`, `of_cc2`, `of_unique_normal_forms`, `of_processors`); `R_infinity` (`thm_necessity`, `ri_depth_exact`, `ri_no_ubc`, `ri_cc_any_extension`, `ri_what_fails`); `prop_cc_necessary`; `prop_cycle_necessary`, `prop_m1_necessary`, `m1_single_round_fails`; `r2_necessary`, and `r1_necessary` as a precise existential; manufacturer-supplier (`ms_instance`, `ms_converges`).
  - `naive_paper_witness_fails`: the paper's witness `(pending, 0)` for the naive revert does not violate CC1; corrected `naive_cc1_fails` (witness `(pending, 1)`), `naive_stream_diverges`, and `naive_cc2_fails` (the naive revert also violates CC2).
- `coq/Stream.v`: stream processors and the Stream Convergence Theorem over the causal GRS with WFC over any well-founded order (#35, WP4).
  - Processor model: `prstep`, `processor`, `is_processor`, `settled`, `fair`, `incremental_computes`.
  - `stream_validity`, `stream_order_independence`, `stream_orders_agree`, `stream_agreement`, `base_thm_convergence_c`, `base_thm_convergence`, `stream_convergence`, `base_rem_set_function`, `base_cor_quiescent` (fairness explicit), `base_cor_infinite`, `base_cor_infinite_quiescent`.
  - `base_thm_convergence_c_counterexample`: equal received sets at the same time do not give equal states (one processor has not finished); corrected to finished processors, at the same or different times.
  - `base_thm_convergence_transient_counterexample`: on an infinite stream a processor one event behind disagrees forever, so disagreements are not transient.
- `coq/CohomologyGeneral.v`: cohomology for arbitrary edge maps, the diagnostic and coordination bounds (#36, WP9).
  - `thm_obstruction_general`, `sections_are_fixed_points`, `reaches_fixed_iff_section`, `thm_obstruction_reachable`, `diagnose_dichotomy`: sections are the fixed points of the loop composite; a section exists iff some seed reaches a fixed point; the finite-fiber test.
  - `prop_minimal_qualified_iff` (regular action and authority root; `prop_minimal_qualifiers_needed`), `c15_exact_refuter`, `c15_regular_definitive`, `c15_convergent_result_sound`, `edge_disjoint_lower_bound`, `edge_disjoint_min`, `min_G_ge_min_image` (any homomorphism, any graph), rooted non-invertible form `rooted_criterion`, `rooted_coordination_suffices`.
  - Counterexamples: `c15_definitive_claim_false` (one non-convergent seed is not definitive), `c22_cycle_basis_fails` (in the non-invertible case a cycle basis does not suffice), `c13_two_ways_not_exhaustive`.
- `coq/MonotoneFederation.v`: monotone cycles against the paper's hypotheses, with `Phi` built from the network (#37, WP6).
  - `net_events_converge_iff`: events converge iff GC; `net_lfp_valid`, `net_Ncyc_correct`, `net_Ncyc_idem` under bottom validity; `kleene_sup_lfp`, `kleene_sup_valid` (the Kleene supremum when `Phi` preserves it); `widening_sound`; `fed_rem_convexity_corrected`, `lfp_mono_param`; `fed_def_lattice_shared_cyclic_hyps`.
  - Counterexamples: `fed_thm_monotone_cycles_lfp_invalid` (the lfp is not federally valid without bottom validity), `fed_thm_monotone_cycles_kleene_formula_fails` (`s* = sup_k Phi^k(bot)` fails for a monotone, non-continuous `Phi`), `fed_thm_monotone_cycles_events_refuted`, `widening_not_normal_form`, `fed_rem_convexity_refuted`.
- `coq/Calculus.v`: the verification calculus of the base paper (#38, WP3).
  - `calc_footprint_cc1_iff`, `calc_footprint_cc1_valid_iff`: CC1 under disjoint footprints and repair locality, exactly; `calc_fp_absorb_iff_sa`, `calc_cc1_iff_commute_under_cc2`, `calc_canonical_cc2_iff`, `calc_components_cc1_iff`.
  - `calc_footprint_cc1`: CC1 at every state from repair locality, commutation up to `N` and footprint absorption, with no disjointness; `calc_footprint_cc1_valid`, `calc_canonical_pattern`, `base_lem_repair_commute`, `base_lem_repair_idempotent`, `base_thm_product`, `base_thm_product_decomposable`.
  - Counterexamples: `base_thm_footprint_cc1_refuted`, `base_thm_footprint_cc1_raw_refuted` (`thm:footprint-cc1` is false as stated, also with raw commutation), `base_rem_practical_import_refuted`, `base_pattern1_cc1_refuted`, `base_pattern1_cc2_refuted`; each hypothesis needed (`calc_valid_needs_commute`, `calc_valid_needs_disjoint`, `calc_valid_needs_repair_local`, `calc_all_needs_commute`, `calc_all_needs_absorb`, `calc_all_needs_repair_local`).
- `coq/FederationGRS.v`: the federated rewrite system `G_Fed` as a `Governance.step` instance, with the federated theorems in corrected form (#39, WP5).
  - `fed_guarded_exact`, `fed_thm_fed_convergence_exact`, `fed_thm_resolved_convergence_exact`: the guarded system (events fire only at federally valid states) has unique normal forms iff C1 and C2 hold at the reachable witnesses; `fed_grs_exact`: the unguarded `G_Fed` iff its CC1 and CC2 on reachable states.
  - `fed_thm_fed_convergence_guarded`, `fed_thm_resolved_convergence_guarded` (C1 and C2), `fed_thm_fed_convergence_corrected`, `fed_thm_resolved_convergence_corrected` (XU), `fed_thm_fed_cc_corrected_machine`, `fed_cor_fed_nf_corrected`, `fed_cor_resolved_nf_corrected`, `fed_lem_authority_a`, `fed_lem_authority_b`, `fed_lem_authority_c_local`, `fed_lem_fed_termination`, `fed_lem_resolved_termination`.
  - Counterexamples against the paper's hypotheses: `fed_thm_fed_cc_refuted`, `fed_thm_fed_convergence_refuted`, `fed_thm_resolved_convergence_refuted`, `fed_lem_authority_c_refuted`, `fed_c2_paper_counterexample`, `fed_cor_fed_nf_refuted`; `fed_grs_c1_c2_insufficient`: C1 and C2 do not suffice for the unguarded `G_Fed`.
- `coq/Collapse.v`: compositional collapse, effective registries, modular verification and port refinement (#42, WP8).
  - `collapse_a_guarded_exact`, `collapse_c_guarded_exact`, `collapse_c_guarded_iff`, `collapse_c_unguarded_iff`, `collapse_b_import_iff`, `collapse_b_export_iff`.
  - `collapse_a_wfc`, `collapse_a_guarded`, `collapse_nf_agree`, `collapse_nf_factor`, `collapse_block_order`, `collapse_contract_acyclic`, `collapse_b_import_corrected`, `collapse_b_export_corrected`, `collapse_modular_converges`, `collapse_hierarchical`; port refinement `port_c1_transfer`, `port_c2_transfer`, `port_interior_certificate`, `port_interior_invariant`.
  - Counterexamples: `collapse_a_refuted` (`R_J` need not satisfy CC under the paper's hypotheses), `collapse_every_order_refuted` (not every topological order visits a convex `J` contiguously), `collapse_convexity_needed`, `collapse_b_import_refuted`, `collapse_b_export_refuted`, `port_sealed_write_refuted`.
- `coq/FederationEventsCyclesMulti.v`: per-edge C1 checks compose into `C1cyc` for multi-edge targets (#44).
  - `multi_edge_c1`: per-edge C1 plus M1 give `C1cyc`; `multi_edge_c1_free` without M1, over all locals; `resolver_joint_c1`; `multi_edge_gc`, `multi_edge_converges`; instances `multi_edge_instance`, `resolver_instance`.
  - Counterexamples: `m1_necessary`, `resolver_edge_insufficient` (per-edge images do not suffice for a resolver component).
- `coq/CoordinatedExact.v`: the exact event-order condition under the coordination plan of a non-monotone cycle (#47).
  - `coordinated_events_exact`, `coordinated_perm_exact`: from a start consistent with the driving network, trace-equivalent event sequences all converge iff independent root events commute at every root value reachable by root events; `coordinated_events_exact_plan`, `coordinated_events_exact_global`, `coordinated_fed_exact`, `coordinated_gc_iff`, `coordinated_c2at_iff`, `coordinated_c1_static`.
  - `old_condition_not_necessary`: the hypothesis of `coordinated_events_converge` is the uniform condition, not necessary for a fixed start; instances `copyback_events_exact`, `negation_events_exact`.
- `coq/RootlessCycles.v`: invertible cycles with no authority root (#48).
  - `rootless_section_iff_holonomy`, `rootless_nf_exists_iff`, `rootless_unique_iff`, `rootless_unique_iff_general`, `rootless_unique_normal_form_iff`: a consistent state exists iff the holonomy is trivial, and it is unique from every initial state iff the group is trivial.
  - `rootless_two_orders`, `rootless_not_unique`; corners `rootless_selfloop_unique`, `rootless_orientation_matters`; instances `rootless_s3_not_unique`, `rootless_negation_no_nf`, `copyback_without_authority_recovered`.
- `coq/GovernanceWFConverse.v`: the exact converses over any well-founded order (#49).
  - `terminating_iff_comp_wf`, `comp_wf_iff_wfc`: termination iff the compensation relation is well-founded iff a potential into some well-founded order exists.
  - `sn_jc_exact`, `wf_jc_exact`, `lex_jc_exact`, `comp_wf_jc_exact`, `canonical_jc_exact`: confluence iff JC, with termination needed only from the start; `canonical_cc_exact_from`, `wf_cc_exact_from`: unique normal forms iff CC1 and CC2 on reachable states, with canonical repair and no termination hypothesis.
  - `comp_wf_nat_potential`, `canonical_comp_wf`, the constructed-`rho*` forms (`wf_cc_exact_from_built`, `comp_wf_cc_exact_from_built`), and the nat statements recovered (`jc_exact_from_wf`, `cc_exact_from_from_wf`, `wfc_cc_exact_from_from_wf`). No counterexample is needed; `rho_star_qualifier` remains the qualifier of the free iff.
- `coq/StreamExact.v`: the exact condition for stream agreement (#51).
  - `stream_exact`: under `Progress`, processors from `s0` that have finished the same received set agree iff `PJC` holds at every duplicate-free `(s0, E)`; `pjc_exact`, `stream_agree_set_function`, `stream_exact_free` (free delivery: iff `PCC`).
  - `pjc_stream_agreement`, `stream_diverge`, `stream_diverge_free`, `stream_agreement_recovered`, `jc_stream_agreement`.
  - Counterexamples: `jc_not_necessary` (JC and the condition of `cc_exact_from` fail yet all processors agree, so the natural iff with the rewrite-system condition is false), `progress_needed`, `jc_fail_disagree`.
- `coq/MonotoneExact.v`: exact validity of the least fixed point and exact finite reachability on monotone cycles (#50).
  - `lfp_valid_exact`, `lfp_valid_iff_reached`, `Ncyc_valid_exact`, `fixed_valid_iff_images`: the lfp is federally valid iff some Kleene iterate is valid; `net_lfp_valid_recovered`.
  - `kleene_reach_exact`, `kleene_reaches_iff`, `kleene_reach_nn`, `chaotic_reach_exact`: the lfp is reached at a finite stage iff the Kleene chain is eventually constant iff productive Kleene steps from bottom terminate; `rounds_reach_by_kleene`.
  - `gsm_check_fixed_valid`, `gsm_check_lfp_valid`, `gsm_check_Ncyc_valid`: gsm's validity check makes every fixed point federally valid, with no bottom-validity hypothesis.
  - Counterexamples: `bottom_validity_not_necessary`, `gsm_check_not_necessary` (the two sufficient conditions are incomparable), `lfp_valid_iff_needs_reach`, `acc_not_necessary`, `kleene_sup_not_sn`, `chaotic_sn_strictly_stronger`.
- `coq/RootSet.v`: the root-set criterion for non-invertible networks without a spanning root (#54).
  - `root_set_iff_forest`: `R` is a root set (every vertex reachable from some root) iff the graph has an outward spanning forest from `R`.
  - `root_set_criterion_graph`, `root_set_criterion_values`, `root_set_criterion`, `root_set_exists`, `root_set_agreement`: a section exists iff some root assignment drives a state satisfying every non-driving edge, equivalently two roots agree wherever both reach; `root_set_decide`: existence is a search over the product of root domains.
  - `root_set_bijection`, `root_set_count`: sections correspond one to one with consistent root assignments, and the two lists have equal length; `out_forest_section`, `out_forest_unique`, `drive_root`, `driving_paths`.
  - The single-root case recovered: `rooted_criterion_recovered`, `out_tree_section_recovered`, `out_tree_unique_recovered`. Instances: a lossy diamond with no section, the `c22` shape (two roots needed, re-deriving the no-section half of `c22_cycle_basis_fails`), two roots collapsing into one vertex (5 of 9 root tuples consistent, exactly 5 sections), and a root set containing a strongly connected component.
  - Existence is NP-complete in general (a 3-SAT reduction in the research note of #52), cited, not mechanized at the time (the reduction is mechanized in #57); the criterion is David's root-set decomposition (JAIR 1995), and the single-root case is Zhang and Yap (2011).
- `coq/AtLeastOnceExact.v`: exact conditions for at-least-once delivery, free and causal (#55).
  - `alo_exact`, `alo_exact_absorb`: every at-least-once delivery from `s0` reaches the exactly-once result iff exactly-once runs commute at reachable states and each event is idempotent at every reachable state where it is first delivered (equivalently, its duplicate is absorbed after every exactly-once run containing it); `alo_idem_reachable`.
  - `causal_alo_exact`, `causal_alo_exact_idem`: under causal delivery, iff CCR on the event set plus absorption (or idempotence) per event.
  - Per event: `safe_free_exact`, `safe_at_exact`, `needs_dedup_exact`, `needs_dedup_witness`, and under commutation `safe_free_iff_idem`, `safe_at_iff_idem`.
  - gsm's `Report.NotIdempotent`: `notidem_needs_dedup`, `causal_notidem_needs_dedup` (a witness at a reachable state means the event needs deduplication); `gsm_unlisted_safe`, `causal_gsm_unlisted_safe` (with exactly-once convergence and valid reachable states, an unlisted event needs none).
  - The earlier sufficient theorems placed under the iff: `old_free_implies`, `alo_commuting_recovered`, `old_causal_implies`, `causal_alo_recovered`.
  - Counterexamples: `inc_alo_fails`, `fw_alo_fails` (the commutation clause is needed), `flag_idem_needs_dedup` (idempotence alone is not enough), `jmp_unreachable` (global idempotence is not necessary, so `NotIdempotent` can over-report), `causal_absorb_qualifier`. Non-vacuity: `mx_alo_exact`, `fl_causal_alo_exact`, `n_causal_alo_exact`.
- `coq/EnabledAfterComp.v`: exact confluence when compensation may disable a buffered event, closing regime-audit gap 6 (#56).
  - `jcg_exact`: for any enabledness and any `c0` from which the system terminates, confluence from `c0` iff JC' (JC's event/event clause, and for each event `e` enabled at an invalid `sigma`, `(rho* (apply e sigma), B - e)` joinable with `(rho sigma, B)`) at every configuration reachable from `c0`; `jcg_iff_critical`, `cr_iff_critical`: JC' is exactly joinability of every critical pair at every reachable configuration; `jcsplit_exact`: the split form, under decidability of enabledness after compensation.
  - `jcsplit_iff_jc`, `jcg_iff_jc`, `jc_jcg`: under `enabled_after_comp`, JC' is JC; `jc_exact_recovered`, `sn_jc_exact_recovered`: the earlier `jc_exact` and `sn_jc_exact` re-derived, with their types checked against the originals.
  - `gnf_iff`, `stuck_nf_iff`: normal forms are (state, residual buffer) pairs, and the buffer may be non-empty; `free_nf_empty`.
  - Counterexamples: `dc_jc_insufficient` (JC holds at every configuration, yet `(Pending, [Settle])` has two normal forms, one stuck; `dc_not_jcg`, `fr_confluent` with the guard removed), `nv_jc_not_necessary` (a compensation disables an event, JC' holds and every configuration is confluent, JC fails).
- `coq/RootSetEvents.v`: exact event order under root-set coordination on non-invertible networks, closing regime-audit gap 4 (`LOSSY-NETWORKS.md` P6) (#59).
  - `forest_events_exact`: from a start consistent with the driving network of an outward spanning forest from a root set, J-trace-equivalent sequences all converge iff, for each root, its J-independent events commute at every value reachable from its start value by its own events; `forest_perm_exact` (permutation form), `forest_events_exact_global`, `forest_global_iff_static` (from every consistent start iff every root's independent events commute at every value, iff static C1 and C2).
  - `forest_c1_static`, `forest_c1r1`, `forest_c2at_iff`, `forest_c2_static_iff`: C1 always holds on the forest, and C2 reduces to root commutation; `forest_common`, `forest_cons_iff`, `forest_order`.
  - Roots never interact: `forest_root_run`, `forest_run_formula`, `forest_run_single_root` (every vertex depends on one root's events), `forest_runs_by_root`, `forest_cross_commute`, `forest_driven_noop`; the only coupling is through constraints (`forest_runs_kept`).
  - The group case recovered: `coordinated_events_exact_recovered`, `coordinated_events_exact_global_recovered`, `recovered_klein`.
  - Counterexamples and non-vacuity on a two-root lossy network: `tw_diverges_at_three`, `tw_reachable_matters` (two events commute at the start value, yet runs diverge because a non-commuting value is reachable), `tw_not_global`; `tw_root_set`, `tw_converges_at_zero`, `tw_cross_roots`, `tw_poke_noop`.
- `coq/LossyHardness.v`: the 3-SAT reduction for lossy networks without a spanning root (`LOSSY-NETWORKS.md` section 3.2, PR #52), mechanized; NP-completeness follows by the standard argument (#57).
  - `net_section_iff_sat`: for every 3-CNF `f`, the network `net f` has a section iff `f` is satisfiable (directions `section_of_sat`, `sat_of_section`).
  - `net_bijection`, `net_count`: sections and satisfying assignments correspond one to one (modulo agreement on the network's vertices and the occurring variables), and their counts are equal, so the reduction is parsimonious.
  - `net_size`, `net_tables`: `6|f| + 1` edges on `4|f| + 1` vertices, each map a 9-entry table; `np_certificate`, `np_certificate_net`: a section exists iff some tuple of one value per vertex passes the edge-by-edge checker `msection_b` (membership in NP).
  - Counterexamples (the gadget is needed): `no_filter_trivial`, `no_pin_trivial`. Non-vacuity: `fsat_check`, `fsat_count` (7 satisfying assignments, 7 sections), `funsat_gadget_needed` (an unsatisfiable formula with no section, whose gadget-free networks have sections).
- `coq/CvRDTExact.v`: state-based CRDT merges through the exact theorems, closing regime-audit gap 7 (#58).
  - `merge_action_exact`: deliveries over the event set with the same set of events, in any order and with any duplication, reach one state from `s0` iff the merges commute and are idempotent at every state reachable from `s0`; `merge_conv_alo_exact` (the conditions of `alo_exact`).
  - `cvrdt_on_exact`: with finitely many payloads and decidable state equality, convergence iff the reachable states carry a join-semilattice for which each merge is the join with its payload; the backward direction `cvrdt_on_conv` needs no qualifier.
  - `cf_cc_exact_from`, `cf_cc_exact_from_wfc`: a compensation-free registry has unique normal forms iff its actions commute at reachable states; `cvrdt_unique_normal_forms`, `cvrdt_alo`, `cvrdt_merge_conv`; `cvrdt_SEC_recovered`, `cvrdt_set_SEC`, `cvrdt_absorbs_duplicates_recovered`, `cvrdt_causal_cmrdt`, `cvrdt_compensation_free`.
  - Monotone regime: `merge_inflationary`, `merge_monotone`, `run_upper`, `run_least`, `cvrdt_lfp` (the delivered state is the least upper bound of `s0` and the payloads).
  - Counterexamples: `naive_cvrdt_iff_fails` (convergence is not "the merge is a join-semilattice on all states"), `clamp_reach_qualifier` (reachability is needed), `add_cc_not_alo` (unique normal forms without convergence under duplication), `lww_not_conv` (idempotent everywhere, diverges). Non-vacuity: `maxreg_exact`, `gcounter_exact`, `gset_exact`.
- `coq/DistributedExact.v`: the exact condition for the distributed propagation model on acyclic federations, closing the acyclic part of regime-audit gap 1 (#60).
  - `dist_exact`: from a valid start, every two words of local events and propagation steps with federated-trace-equivalent events give the same state after the final flush iff XU holds at every reachable stale combination (`XUR`) and C2 at states reachable from the flushed start; `dist_exact_local` (with reachable LocalCC), `dist_exact_tc` (with FedMachine convergence from the flushed start).
  - Quantified starts: `dist_exact_global` (every valid start iff `XUG` and `C2G`), `dist_exact_consistent` (every consistent start), `dist_global_exact_roots` (when every target's sources are roots, every valid start iff static XU and C2).
  - Sufficient forms: `dist_xu_c2_converge` (static XU plus C2, no LocalCC needed), `dist_interleavings_converge_recovered`, `xu_exact_condition`; converse witnesses `dist_xu_runs`, `dist_xu_diverge`, `flush_ev_at`, `xur_c1r1`.
  - `dist_implies_fed`, `dist_implies_fed_flush`: distributed convergence implies FedMachine convergence.
  - Counterexamples: `levels_exact_not_xu` (gsm's `levels` federation: C1 and C2 hold, XU fails, every consistent start converges; the exact condition is strictly weaker than XU), `dist_strictly_stronger_than_fed` (every FedMachine order converges from every consistent start, yet two propagation timings of the same events diverge). Non-vacuity: `supply_dist_exact`.
- `coq/DistributedCycles.v`: the distributed propagation model on monotone cycles, closing the cyclic part of regime-audit gap 1 except a residual (#62).
  - Repair alone: `q1_below`, `q1_from_bot`, `q1_sound_settles`, `q1_sound_iff` (from a sound start a fair schedule reaches the least fixed point iff the start is below it), `q1_stuck` (a ghost above another fixed point is never left), `q1_unique_iff` (every fair schedule from every start settles at the least fixed point iff it is the only fixed point); `dist_schedule_dependence`, `dist_ring_livelock`.
  - Events without resets: `track`, `quiet_ghost_only`; `quiet_agree_iff` (under `FlushR`: agreement with the FedMachine at quiescent states iff `XUcR` and `NoGhostR`), `quiet_conv_iff` (under `FlushR` and `NoGhostR`); `low_agree_iff`, `low_conv_iff` (exact under `LowR`, which gives `FlushR` and `NoGhostR`); sufficient `evlow_lowr`, `infl_evlow`, `uniq_agree`, `lens_quiet`.
  - Reset epochs: `epoch_agree_iff`, `epoch_conv_iff` (after a final epoch, agreement iff `XUcR`, convergence iff `XUcR` and FedMachine convergence), `lens_epoch` (gsm's per-target C1cyc and C2cyc over a covering set give both), `EP_run`, `epoch_flush`, `hs_reach`.
  - Counterexample `dist_cyc_ghost`: C1cyc, C2cyc, `XUcR` and FedMachine convergence all hold, yet a run quiesces at a ghost the FedMachine never produces; `dist_cyc_epoch_fix`: epochs repair it from every start, and a staggered reset re-creates it. Positive instances `dist_cyc_raise_only`, `dist_cyc_unique_no_reset`.
- `coq/README.md`: sections for each new module (#21, #23, #24, #25, #26, #27, #31 to #39, #42, #44, #47 to #51, #54 to #60, #62).

### Changed
- Axiom-free gate raised from 112 to 125 theorems, checked on Coq 8.18, Coq 8.20 and Rocq 9.3 (#19).
- Axiom-free gate raised from 125 to 135 theorems (#21).
- Axiom-free gate raised from 135 to 254 theorems: 166 (#23), 189 (#24), 205 (#25), 232 (#26), 254 (#27).
- Axiom-free gate raised from 254 to 915 theorems: 264 (#31), 314 (#32), 375 (#33), 413 (#34), 486 (#35), 548 (#36), 575 (#37), 609 (#38), 669 (#39), 715 (#42), 729 (#44), 752 (#47), 777 (#48), 827 (#49), 851 (#51), 915 (#50).
- Axiom-free gate raised from 915 to 989 theorems: 958 (#54), 989 (#55).
- Axiom-free gate raised from 989 to 1198 theorems: 1040 (#56), 1123 (#59), 1151 (#57), 1198 (#58).
- Docs pass at the 1198-theorem gate: `REGIME-AUDIT.md` closes gaps 4, 6 and 7 and marks the lossy-network 3-SAT reduction mechanized; the `README.md` precision paragraph says the reduction is machine-checked and NP-completeness follows by the standard argument; `ROADMAP.md`, `REGIMES.md` and `coq/README.md` updated to match (#61).
- Axiom-free gate raised from 1198 to 1370 theorems: 1253 (#60), 1370 (#62).
- Docs pass at the 1370-theorem gate: `REGIME-AUDIT.md` section 8 rewritten (the acyclic distributed model is exact; on monotone cycles it is exact under reset epochs and under `LowR`), gap 1 restated as the residual (cycles without resets and without `LowR`, exact only relative to `FlushR` and `NoGhostR`), headline line re-confirmed; `README.md` open-gap list and count, `ROADMAP.md`, `REGIMES.md` and `coq/README.md` updated to match (#63).
- Documentation restructured by reader, with nothing removed. `README.md` keeps the headline, its precision paragraph and the papers, and adds a "Start here" map for practitioners, researchers, proof readers and auditors; its overview, "What's new here", key concepts and the three-regimes comparison moved to `docs/THEORY.md`. `REGIMES.md`, `ROADMAP.md`, `LANDSCAPE.md`, `SUBSUMPTION.md`, `CATEGORICAL-STRUCTURE.md`, `LYAPUNOV-EXTENSION.md` and `COMPANION-OUTLINE.md` moved to `docs/`, with a stub at each old path and `docs/README.md` giving each page's role; `REGIME-AUDIT.md` and `CHANGELOG.md` stay at the root. `coq/README.md` is now an index (verify, how to read a module, one row per module grouped in `REGIME-AUDIT.md`'s order, and how to add a module); its per-module sections moved verbatim to one page per regime in `coq/docs/`. `coq/PAPER-MAP.md` notes that its status columns predate later merges and points to `REGIME-AUDIT.md`.
- Version 2 of all three papers, dated 4 October 2026. Each body states only the corrected results, and a new appendix "Errata and corrections" gives, for each changed statement, the old statement, its counterexample and the corrected theorem with Coq names. Every cited Coq name is in the gate.
  - Base paper, `normalization_confluence_2026.tex` (#41): `thm:footprint-cc1` corrected (an exact form under disjoint footprints and repair locality; at valid states CC1 iff commutation up to `N`; at every state, footprint absorption in place of disjointness), with the new `cor:cc1-under-cc2`; the "Practical import" remark and 8.2 pattern 1 corrected; the naive-revert witness moved to `(pending, 1)`; Stream Convergence (c) restated for processors that have finished processing equal received sets, the "disagreements are transient" sentence removed, and `cor:quiescent` stated for fair processors; the new `thm:cc-exact` replaces "CC is necessary"; `thm:strong-absorption` stated as an iff; `def:rhostar` constructed; the three-regime hierarchy stated precisely. 23 pages to 30.
  - Federation paper, `normalization_confluence_in_federated_registry_networks.tex` (#43): the federated rewrite system is now the guarded one (events fire only at federally valid states), and federated convergence needs C1 and C2 in that model, exact at reachable witnesses; component CC alone does not suffice, and the unguarded system needs XU (`rem:unguarded`). `lem:authority` (c), `thm:fed-cc`, `thm:fed-convergence`, `thm:resolved-convergence`, `cor:fed-nf` and `cor:resolved-nf` corrected; `thm:monotone-cycles` corrected (the Kleene supremum only under continuity, validity of the lfp needs bottom validity, event convergence iff GC with per-target C1 and C2 over images sufficient); `cor:acyclicity-monotone`, `rem:infinite-lattice` and the convexity remark corrected; `thm:collapse` and `cor:modular` restated from #42. The restated single-registry sections take the base paper's corrected passages, and the appendix carries both sets of errata. 32 pages to 47.
  - Categorical paper, `categorical_structure_of_federated_convergence.tex` (#40): Theorem 1 now assumes local idempotence, the lens law and shared-component stability, since M1/R2 as validity preservation do not suffice (`cat_thm_one_m1_counterexample`); `thm:obstruction` made precise; the diagnostic reading, "exactly two ways", `prop:minimal`, the edge-disjoint bound and the non-invertible cycle-basis claim corrected; the regimes give a unique repair normal form, while event order needs C1 and C2 in the guarded model (new Background paragraph "Repair confluence and event confluence"); the related-work claim on CvRDTs narrowed to one direction. Errata items E1 to E14; 14 pages to 20.
- `ROADMAP.md`: item 6 (event order on monotone cycles) and item 7 (every result in the papers mechanized, audit first) added; the authority root in gsm's plan and the unmechanized synthesis added to the lower-value list; gsm's `EmbedCertified` table execution marked done (#29).
- `README.md`: leads with convergence by compensation and the split between repair confluence and event confluence; C1 and C2 now cover monotone cycles; theorem count 729, with `coq/verify.sh` as the source of truth (#45).
- Docs sweep after roadmap items 1 to 4: `README.md` (one-line claim and scope, What's new), `ROADMAP.md` (items 1 to 4 done, qualifiers, new open questions), `REGIMES.md`, `SUBSUMPTION.md`, `LANDSCAPE.md`, `CATEGORICAL-STRUCTURE.md`, `COMPANION-OUTLINE.md` and `coq/README.md` updated to the exact conditions and the 254-theorem gate (#28).
- `SUBSUMPTION.md`: op-based CRDTs are now proven to be exactly the compensation-free fragment under causal delivery, with a new section on causal delivery (#19).
- `README.md` updated to match, including the "What's new here" item for the first paper (#19).
- `coq/README.md`: gated theorem count updated from 112 to 125 (#19).

### Fixed
- `LANDSCAPE.md`: corrected the placement of I-confluence. Its replay-convergent part is exactly the op-based CRDTs; non-commuting I-confluent systems converge by merge, outside the replay model (#19).

## 2026-10-04

### Added
- `README.md`: "What's new here" section, each item marked [mechanized], [paper] or [implemented]; the categorical paper added as a third publication; necessity, monotone cycles, compositional collapse and mechanization added to the federated paper's entry (#18).
- `LANDSCAPE.md`: "Related work for the cohomological layer" section (graph fundamental groups, gain-graph and signed-graph balance, cohomology of global-section obstructions, topology in distributed computing, cycle consistency and group synchronization, applied sheaf theory, related formalizations) (#17).

### Changed
- `LANDSCAPE.md`: expanded contribution list, "Where to coordinate: a cycle basis" added, three papers listed (#18).
- `coq/README.md`: Rocq 9.3 noted as CI-gated; gated theorem count corrected to 112 (#18).
- `README.md`: the oracle bullet now describes gsm's in-process, fail-closed oracle gate, scoped to `Build`, `SynthesizeWith` and `BuildCompositional`; `.tex` line counts corrected (#18).
- `CATEGORICAL-STRUCTURE.md` 10 and 10.1: related-work pointer, open items updated to match `coq/CohomologyGraph.v`, and contribution wording that credits the graph topology and balance criterion as classical (#17).

## 2026-10-03

### Added
- `coq/AstTables.v`: `checkBuildT`, the rules oracle through step tables, which evaluates the rules once per state and event. `checkBuildT_eq` proves it equal to `checkBuild` for every machine and declaration; supporting results include `scan_cells_fn`, `boxT_eq`, `enc_box`, `box_enc`, `tables_fn_eq` and `cells_ok`. `astchecker` and the generated Go `rulecheck` run it. Gate raised from 96 to 104 theorems (#14).
- `astdiff` differential test tool comparing the rules oracles (#14).
- `coq/AstCompact.v`: `checkBuildC`, the rules oracle in compact memory, which enumerates the valuation box on the fly (`foldB`) and holds only packed tables. `checkBuildC_eq` proves it equal to `checkBuild` unconditionally. Memory guard in `tests/run.sh` for 2^20-state machines in 256 MiB. Gate raised from 104 to 112 theorems (#15).

### Fixed
- Rules front ends (OCaml `astchecker`, Go `rulecheck`) refuse a machine whose product of domains exceeds 2^24 states, instead of enumerating it; `goextract/tests/run.sh` now requires matching stderr between the OCaml and Go front ends for every input error (#16).

## 2026-10-02

### Added
- Rules oracle aligned with gsm's signed arithmetic: `evalE` returns `Z`, with new theorems `check_no_overflow` and `check_binary_writes_exact`. Extraction regression tests (`make test`); CI builds the extracted checkers on every matrix job, and `oracles.yml` publishes digest-pinned binaries with `SHA256SUMS`. Gate raised from 67 to 69 theorems (#5).
- Table and rules oracles that decide the property checked by gsm's `Build` (#6):
  - `coq/Trace.v`: `tequiv`, `run_tequiv`, `perm_tequiv_total`.
  - `coq/TableCheck.v`: `check_tables` with `check_tables_nf_valid`, `check_tables_step_valid`, `check_tables_commute`, `check_tables_converges`, `check_tables_converges_all`, `check_tables_pairs_in_range`.
  - `AstChecker.v`: `checkBuild` with `checkBuild_wfc_terminates`, `checkBuild_wfc_potential`, `checkBuild_normalize_valid`, `checkBuild_step_valid`, `checkBuild_commute`, `checkBuild_converges`, `checkBuild_converges_all`, `checkBuild_no_overflow`, `checkBuild_binary_writes_exact`, `checkBuild_pairs_in_range`, `stepG_valid_eq`.
  - Tables format 2 and an optional pairs file for `astchecker`; the rules format is unchanged.
  - Gate raised from 69 to 89 theorems.
- `coq/TableFast.v`: `check_fast`, proven equal to `check_tables` (`check_fast_eq`), with `check_fast_converges`. Gate raised from 89 to 92 theorems (#8).
- `coq/TableFn.v`: `check_fn`, the table oracle over accessor functions, with `check_fn_converges`, `check_tables_fn` and `check_fast_fn`. The `checker` front end holds entries in arrays and calls `check_fn`. Gate raised from 93 to 96 theorems (#13).
- `goextract`: generates the verified checkers as Go from Rocq's JSON extraction (`gogen`), with `cmd/tablecheck` and `cmd/rulecheck` front ends, a prim check against Rocq definitions, and CI (`goextract.yml`) requiring byte-identical output in the pinned Rocq 9.3 image and zero differential disagreements against the OCaml checkers (#10).

### Changed
- `check_fast` reads each step target's column once per state using per-state cells and a 16-ary trie, keeping its name, signature and theorems; `vlook_of_listV` and `bget_chunk` replace `wlook_of_list16` in the gate (92 to 93 theorems) (#12).

### Fixed
- `AstChecker.v` evaluated rules over `nat`, so `Sub` truncated at 0 where gsm uses signed integers, and a `Bool` write stored a different value than gsm for negative results; both front ends now reject malformed and out-of-range input (#5).
- Extracted table oracle no longer overflows the stack on 2^20-state tables (#8).
- Rules oracle no longer overflows the stack on gsm-sized machines: `fuelOf` and `setClamped` use the mapped `Init.Nat.mul` and `Init.Nat.min`, `natZ` replaces `Z.of_nat` (`natZ_eq`), and `box` uses tail loops (`box_in`). A test guard rejects extracted calls to unary `nat` arithmetic (#11).

## 2026-10-01

### Added
- CI verifies the proof on Rocq 9.3 alongside Coq 8.18 and 8.20 (#1).
- `coq/CohomologyMin.v`: the S_3 theta-graph minimum-coordination counts (`min_G_lower`, `min_G_attained`, `min_ab_lower`, `min_ab_attained`, `sign_hom`, `section_G_implies_ab`, `theta_separation`) (#2).
- `coq/CohomologyGraph.v`: the completion on an arbitrary group-labeled graph (`section_iff_coboundary`, `tree_has_section`, `tree_unique`, `cycle_basis_criterion`, `keep_balanced_suffices`, `unbalanced_blocks`). Gate raised from 38 to 55 theorems (#2).
- `LYAPUNOV-EXTENSION.md`: forward-looking research note on continuous-state analogues (nothing in it is proven) (#3).
- `coq/FederationOrder.v`: `order_independent`, order-independence for arbitrary acyclic federations without assuming connectivity of linear extensions (#4).
- `coq/CohomologyGraph.v`: H^1 as a quotient and its rank (`gauge_fix`, `gauge_fixed_holonomy`, `H1_classification`, `tree_vertex_count`, `betti_number`, `tri_flip_not_cohomologous_to_identity`). Gate raised from 55 to 67 theorems (#4).

### Changed
- The categorical paper cites the new mechanized lemmas (#2, #4).

## 2026-09-25

### Added
- `coq/Categorical.v`: the categorical core (Lemma 0, the consistent set as an equalizer, Theorem 1 for a general acyclic federation, Theorem 2 compositionality).
- `coq/Cohomology.v`: the cohomological layer, single-cycle case, and the non-abelian minimal-coordination crux.
- Draft companion paper, "The Categorical Structure of Federated Convergence: Limits, Sheaves, and Minimal Coordination" (`categorical_structure_of_federated_convergence.tex`), with `COMPANION-OUTLINE.md`.
- Minimal-coordination results in `CATEGORICAL-STRUCTURE.md`, including the characterization of minimum coordination as Group Feedback Edge Set.
- Gate raised from 19 to 38 theorems over the day.

### Changed
- `LANDSCAPE.md`: positioning against CALM, Indigo/IPA, rewriting logic and self-stabilization.
- Prior-art citations added to all three papers.

### Fixed
- Corrected an abelian-polynomial complexity claim in the minimal-coordination analysis.
- Fixed an O(n log n) total-cost typo and renamed resolver `R_j` to `Gamma_j` in the papers.

## 2026-09-24

### Added
- Coq/Rocq mechanization in `coq/`: `Newman.v` and `Governance.v` (machine-checked confluence), `Defensibility.v` (non-vacuity and discrimination checks), `Gsm.v` (soundness of gsm's WFC and CC certification), `Federation.v` (monotone-cycles federated convergence core), `Chaotic.v` (chaotic, asynchronous iteration convergence), `Checker.v` (verified convergence checker with extraction), `AstChecker.v` (AST-level verified oracle), and `CRDT.v` (CRDTs as the compensation-free fragment).
- Axiom-free CI gate (`coq/verify.sh`, `.github/workflows/verify.yml`) on Coq 8.18 and 8.20, starting at 7 theorems and raised to 19 over the day.
- `REGIMES.md`, `LANDSCAPE.md`, `SUBSUMPTION.md` and `CATEGORICAL-STRUCTURE.md`.

### Changed
- Both papers reference the mechanization.

## 2026-09-23

### Added
- Federated paper: multi-source networks via resolution operators, the Monotone Cycles theorem (convergence beyond acyclicity), the Compositionality theorem (sub-federations as effective registries), and a federated-repair regime table.
- Infinite-domain results, split across both papers.

### Changed
- First paper forward-references the federated results.

## 2026-02-17 to 2026-02-20

### Added
- Initial publication of "Normalization Confluence for Registry-Governed Stream Processing" (`normalization_confluence_2026.tex` and PDF), with a Zenodo DOI (10.5281/zenodo.18671870).
- "Normalization Confluence in Federated Registry Networks" (`normalization_confluence_in_federated_registry_networks.tex` and PDF), cited by its Zenodo concept DOI (10.5281/zenodo.18677400).
- Makefile and script to compile the papers in a Docker container.

### Changed
- README restructured as a research-area overview; paper layout and typography refinements.
