# Mechanized confluence proof (Coq / Rocq)

[![verify](https://github.com/blackwell-systems/normalization-confluence/actions/workflows/verify.yml/badge.svg)](https://github.com/blackwell-systems/normalization-confluence/actions/workflows/verify.yml)

A machine-checked proof of the paper's Convergence Theorem: under the paper's stated conditions,
the governance rewrite system is confluent and every configuration has a unique normal form.
CI compiles it on Coq 8.18, Coq 8.20 and Rocq 9.3 and gates on it being **axiom-free**:
every key theorem is "Closed under the global context", no `Admitted`, no added axioms. The badge
is green only when that gate passes.

## Verify it yourself

With Coq/Rocq installed (`coqc` on PATH):

```
cd coq && bash verify.sh      # compiles everything, then prints the axiom-free gate result
```

Or with nothing but Docker (no local Coq), one command reproduces exactly what CI does:

```
docker run --rm -v "$PWD/coq":/src:ro coqorg/coq:8.20 \
  bash -lc "cp -r /src /tmp/c && cd /tmp/c && bash verify.sh"
```

Expected tail: `PASS: all 2241 theorems are Closed under the global context (no axioms, no admits)`.
The gate runs `Print Assumptions` on all 2241 gated results and fails if any of them depends on an
axiom or an admitted lemma. `verify.sh` lists them module by module: the single-registry confluence,
unique-normal-form and converse results (`Governance.v`, `GovernanceWF.v`, `GovernanceConverse.v`,
`GovernanceWFConverse.v`, `RhoStar.v`, the causal, at-least-once and stream modules), the gsm
certification-soundness results and the verified-checker results behind the table and rules oracles,
the CRDT-subsumption results, the categorical core and bridge, sheaf gluing over sub-federation covers, the cohomological layer
(`Cohomology.v` to `CohomologyGeneral.v`, `CohomologyNerve.v`, `RootSet.v`) with minimum
coordination (`CoordinationMinimum.v`, `LossyMinimum.v`), and the federation modules (acyclic event
order and its converse, monotone cycles and their exact validity and reachability, coordinated and
rootless cycles and networks, the distributed propagation model (acyclic and on monotone cycles), the federated
rewrite system and compositional collapse). The [module index](#modules-by-regime) below lists
each module with its headline theorems; the pages in [`docs/`](docs) give each module's results in
full.

## How to read a module

Each module states the paper's conditions as Coq hypotheses (section variables or a record), never
as axioms, and the gate checks that its headline results are "Closed under the global context". A
module's results usually come in four kinds, and the names say which:

- **The headline theorem.** Where a regime has an exact condition it is an `<->` theorem (names such
  as `cc_exact_from`, `fed_exact`, `dist_exact`), next to the cheap sufficient form a checker can
  afford.
- **Recovered results.** Earlier, weaker theorems re-derived from the new one with identical
  statements (names ending in `_recovered`, or `_from_wf`).
- **Counterexamples as theorems.** Naive statements that are false, and hypotheses shown to be
  needed, are recorded as theorems (typical names end in `_fails`, `_refuted`, `_counterexample`,
  `_not_necessary`, `_insufficient`, `_needed`, `_qualifier`).
- **Non-vacuity instances.** A concrete model that discharges every hypothesis, so the theorem is
  about something.

Qualifiers live in the statements, not in the names: read the statement before citing a name, as
[REGIME-AUDIT.md](../REGIME-AUDIT.md) does. [PAPER-MAP.md](PAPER-MAP.md) maps the papers' labels to
Coq names (its status columns predate later merges; current status is in REGIME-AUDIT.md).

## Modules by regime

One row per module, grouped in the order of [REGIME-AUDIT.md](../REGIME-AUDIT.md)'s sections, with
its headline theorems. The detailed results (full theorem lists, counterexamples, qualifiers and
what gsm checks) are on the linked page in [`docs/`](docs).

### 1. Single registry ([docs/single-registry.md](docs/single-registry.md))

| Module | Headline theorems | Details |
|---|---|---|
| `Governance.v` | The Convergence Theorem: `terminating`, `locally_confluent_step`, `governance_confluent`, `governance_unique_normal_forms` | [What is proven](docs/single-registry.md#what-is-proven), [what it rests on](docs/single-registry.md#what-it-rests-on-and-what-it-does-not) |
| `Defensibility.v` | Non-vacuity and discrimination: `example_confluent`, `example_unique_nf`, `instance_has_a_real_peak`, `not_confluent_tri` | [Defensibility](docs/single-registry.md#defensibility-defensibilityv) |
| `Gsm.v` | gsm's certification arguments: `disjoint_events_commute`, `repair_terminates` | [Implementation soundness](docs/single-registry.md#implementation-soundness-gsmv) |
| `GovernanceConverse.v` | Exact converses: `cc_exact_from`, `cc_exact_global`, `jc_exact`, `causal_exact`, `causal_convergence_exact`; naive converses refuted: `rho_star_qualifier`, `masked_cc1`, `naive_causal_converse_fails` | [The converse](docs/single-registry.md#the-converse-cc-and-causal-convergence-are-exact-governanceconversev) |
| `GovernanceWF.v` | WFC over any well-founded order: `governance_wf_confluent`, `causal_governance_wf_confluent`, `governance_lex_confluent`; infinite instance `zw_confluent` | [Finiteness only for checking](docs/single-registry.md#finiteness-only-for-checking-governancewfv-chaoticaccv) |
| `RhoStar.v` | `rho*` built from WFC: `rho_star`, `rho_star_wf`, `base_def_rhostar`; no `rho*` hypothesis: `wfc_governance_confluent`, `wfc_cc_exact_from`, `paper_causal_governance_unique_normal_forms`; `base_lem_termination_bound` | [rho* constructed from WFC](docs/single-registry.md#rho-constructed-from-wfc-rhostarv) |
| `GovernanceWFConverse.v` | Exact converses over any well-founded order: `terminating_iff_comp_wf`, `comp_wf_iff_wfc`, `sn_jc_exact`, `wf_cc_exact_from`, `canonical_cc_exact_from` | [The exact converses over any well-founded order](docs/single-registry.md#the-exact-converses-over-any-well-founded-order-governancewfconversev) |
| `EnabledAfterComp.v` | Compensation that disables a buffered event: `jcg_exact`, `jcsplit_exact`, `jcsplit_iff_jc`, `gnf_iff`; `dc_jc_insufficient`, `nv_jc_not_necessary` | [Compensation that disables a buffered event](docs/single-registry.md#compensation-that-disables-a-buffered-event-enabledaftercompv) |
| `Calculus.v` | Verification calculus: `base_thm_product`, `calc_footprint_cc1_iff`, `calc_footprint_cc1`; refuted: `base_thm_footprint_cc1_refuted`, `base_rem_practical_import_refuted` | [Verification calculus](docs/single-registry.md#verification-calculus-for-cc-calculusv) |

### 2. Causal delivery ([docs/causal.md](docs/causal.md))

| Module | Headline theorems | Details |
|---|---|---|
| `CausalReplay.v` | `causal_convergence`, `causal_cmrdt_SEC`, `compensation_free_exact`, `causal_tequiv`, `witness_causal_not_cmrdt` | [Causal delivery](docs/causal.md#causal-delivery-causalreplayv-governancecausalv) |
| `GovernanceCausal.v` | `causal_governance_confluent` (CC1 only for co-enabled distinct events); witness `cw_confluent` | [Causal delivery](docs/causal.md#causal-delivery-causalreplayv-governancecausalv) |

### 3. At-least-once delivery ([docs/at-least-once.md](docs/at-least-once.md))

| Module | Headline theorems | Details |
|---|---|---|
| `AtLeastOnce.v` | Sufficient conditions: `alo_absorbed`, `alo_commuting_converges`, `causal_alo_converges`; divergence: `non_idempotent_diverges`, `late_duplicate_diverges` | [At-least-once delivery](docs/at-least-once.md#at-least-once-delivery-atleastoncev) |
| `AtLeastOnceExact.v` | Exact, free and causal: `alo_exact`, `causal_alo_exact`, `safe_free_exact`; gsm's report: `notidem_needs_dedup`, `gsm_unlisted_safe` | [At-least-once delivery, exact](docs/at-least-once.md#at-least-once-delivery-exact-atleastonceexactv) |

### 4. CRDT fragment ([docs/crdt.md](docs/crdt.md))

| Module | Headline theorems | Details |
|---|---|---|
| `CRDT.v` | `cmrdt_SEC`, `cmrdt_governed_SEC`, `cvrdt_SEC`, `cvrdt_absorbs_duplicates`; strictness `witness_not_cmrdt`, `witness_leaves_valid_space` | [CRDTs as a special case](docs/crdt.md#crdts-as-a-special-case-crdtv) |
| `CvRDTExact.v` | `merge_action_exact`, `merge_conv_alo_exact`, `cvrdt_on_iff`, `cvrdt_lfp`; `naive_cvrdt_iff_fails`, `clamp_reach_qualifier` | [State-based CRDTs, exact](docs/crdt.md#state-based-crdts-exact-cvrdtexactv) |
| `CRDTBoundary.v` | The boundary: `crdt_boundary` (`cf_causal_boundary`, `cf_merge_boundary`, `cf_cvrdt_boundary`); strictness `witness_ops_not_commute`, `witness_not_cvrdt_order`, `witness_not_cvrdt_exact`, `witness_raw_not_causal`; qualifier `witness_governed_constant`; `boundary_nonvacuous` | [The CRDT boundary](docs/crdt.md#the-crdt-boundary-crdtboundaryv) |

### 5. Stream processors ([docs/streams.md](docs/streams.md))

| Module | Headline theorems | Details |
|---|---|---|
| `Stream.v` | `stream_convergence`, `base_thm_convergence`, `stream_order_independence`, `base_cor_quiescent`; refuted: `base_thm_convergence_transient_counterexample` | [Stream processors](docs/streams.md#stream-processors-and-stream-convergence-streamv) |
| `StreamExact.v` | `stream_exact`, `stream_exact_free`, `pjc_exact`, `stream_agree_set_function`; `jc_not_necessary`, `progress_needed` | [Stream agreement, exact](docs/streams.md#the-exact-condition-for-stream-agreement-streamexactv) |

### 6. Acyclic federation, repair normal form ([docs/federation-repair.md](docs/federation-repair.md))

| Module | Headline theorems | Details |
|---|---|---|
| `Categorical.v` | `image_iff_fixed`, `fixed_is_equalizer`, `consistent_iff_equalizer`, `rhoFold_retraction`, `rhoFold_compositional` | [Categorical core](docs/federation-repair.md#categorical-core-categoricalv) |
| `FederationOrder.v` | `order_independent` (any two topological orders agree, by bubbling) | [Categorical core](docs/federation-repair.md#categorical-core-categoricalv) |
| `CategoricalBridge.v` | `cat_prop_one`, `cat_thm_one_sound`, `cat_thm_one_order_independent`; `cat_thm_one_m1_counterexample` | [Categorical bridge](docs/federation-repair.md#categorical-bridge-categoricalbridgev) |
| `SheafGluing.v` | Sheaf gluing over sub-federation covers: `separation`, `gluing`, `sheaf_exact`, `sheaf_iff_refines`; certificates `cert_restrict_closed`, `cert_restrict`, `cert_restrict_iff`, `cert_sheaf`; broken hypotheses `triangle_fails`, `r1_failure`, `gluing_cex_overlap`, `cert_needs_sc` | [Sheaf gluing](docs/federation-repair.md#sheaf-gluing-over-sub-federation-covers-sheafgluingv) |
| `FederationGRS.v` | `fed_lem_fed_termination`, `fed_grs_exact`, `fed_guarded_exact`, `fed_thm_fed_convergence_exact`; refuted: `fed_thm_fed_convergence_refuted`, `fed_grs_c1_c2_insufficient` | [The federated theorems in corrected form](docs/federation-repair.md#the-federated-theorems-in-corrected-form-federationgrsv) |

The [categorical-layer roadmap](docs/federation-repair.md#roadmap-mechanizing-the-categorical-layer-companion-paper)
is on the same page.

### 7. Acyclic federation, event order ([docs/federation-events.md](docs/federation-events.md))

| Module | Headline theorems | Details |
|---|---|---|
| `FederationEvents.v` | `fed_interleavings_converge`, `fed_permutations_converge`, `dist_interleavings_converge`, `xu_implies_c1_c2`; `audit_counterexample`, `c2_counterexample` | [Event interleavings across registries](docs/federation-events.md#event-interleavings-across-registries-federationeventsv) |
| `FederationEventsConverse.v` | `fed_exact`, `fed_exact_full`, `acyclic_gc_iff`, `static_c1_c2_gc`; `naive_converse_fails` | [Monotone cycles and the exact converse](docs/federation-events.md#monotone-cycles-and-the-exact-converse-federationeventscyclesv-federationeventsconversev) |

### 8. Distributed model with propagation steps ([docs/distributed.md](docs/distributed.md))

| Module | Headline theorems | Details |
|---|---|---|
| `DistributedExact.v` | Acyclic, exact: `dist_exact`, `dist_exact_local`, `dist_exact_tc`, `dist_exact_global`, `dist_global_exact_roots`, `dist_xu_c2_converge`; `levels_exact_not_xu`, `dist_strictly_stronger_than_fed` | [The exact condition](docs/distributed.md#the-distributed-model-the-exact-condition-distributedexactv) |
| `DistributedCycles.v` | Monotone cycles: `q1_sound_iff`, `q1_unique_iff`; reset epochs `epoch_agree_iff`, `epoch_conv_iff`, `lens_epoch`; under `LowR` `low_agree_iff`, `low_conv_iff`; relative to `FlushR` and `NoGhostR` `quiet_agree_iff`, `quiet_conv_iff`; the ghost `dist_cyc_ghost` | [On monotone cycles](docs/distributed.md#the-distributed-model-on-monotone-cycles-distributedcyclesv) |
| `DistributedCyclesExact.v` | No resets, unconditional: `flush_agree_iff`, `fair_agree_iff`, `flush_fed_iff`, `fair_fed_iff`; each conjunct needed (`copy_xu_fails`, `fm_conv_fails`, `flip_noflush`, `ghost_exact`); gsm's per-target check: `lens_noreset_iff`, `lens_noreset_fair_iff` | [No-reset model, exactly](docs/distributed.md#the-no-reset-model-on-monotone-cycles-exactly-distributedcyclesexactv) |
| `DistributedConvergenceExact.v` | No resets, convergence alone (gap 14): `conv_quiet_exact` (`FlushR /\ DConvQ <-> FlushR /\ FlushDetR /\ FlushXUR /\ QMConv`, the canonical state is where propagation settles, ghost allowed), `fair_conv_exact`; each conjunct needed (`flip_conv_noflush`, `fork_conv_nodet`, `copy_conv_noxu`, `fm_conv_noqm`); ghost-free case `quiet_conv_recovered`, `agree_conv_noghost`, `flush_fed_recovered`; `soundr_conv_iff`; `conv_ghost_instance`, `ghost_conv_not_fed` | [Convergence alone](docs/distributed.md#convergence-alone-on-monotone-cycles-distributedconvergenceexactv) |

### 9 and 10. Monotone cycles ([docs/monotone-cycles.md](docs/monotone-cycles.md))

| Module | Headline theorems | Details |
|---|---|---|
| `Federation.v` | `iter_ascending`, `kleene_lfp`, `lfp_unique` | [Federated convergence](docs/monotone-cycles.md#federated-convergence-federationv) |
| `Chaotic.v` | `chaotic_terminates`, `chaotic_reaches_lfp`, `chaotic_limit_unique` | [Chaotic iteration](docs/monotone-cycles.md#chaotic-asynchronous-iteration-chaoticv) |
| `ChaoticACC.v` | Under ACC: `chaotic_acc_reaches_lfp`, `kleene_acc_lfp`, `kleene_acc_lfp_nn`; `ole_no_rank` | [Finiteness only for checking](docs/single-registry.md#finiteness-only-for-checking-governancewfv-chaoticaccv) (with `GovernanceWF.v`) |
| `MonotoneFederation.v` | `fed_def_lattice_shared_cyclic_hyps`, `net_lfp_valid`, `kleene_sup_lfp`, `net_events_converge_iff`; refuted: `fed_thm_monotone_cycles_lfp_invalid`, `fed_rem_convexity_refuted` | [Against the paper's hypotheses](docs/monotone-cycles.md#monotone-cycles-against-the-papers-hypotheses-monotonefederationv) |
| `MonotoneExact.v` | `lfp_valid_iff_reached`, `Ncyc_valid_exact`, `gsm_check_Ncyc_valid`, `kleene_reach_exact`, `chaotic_reach_exact` | [Exact validity and reachability of the lfp](docs/monotone-cycles.md#monotone-cycles-exact-validity-and-exact-reachability-of-the-lfp-monotoneexactv) |
| `FederationEventsCycles.v` | `gc_iff`, `cyc_N_lfp`, `cyc_events_converge_iff`; `cyc_counterexample`, `bottom_matters` | [Monotone cycles and the exact converse](docs/federation-events.md#monotone-cycles-and-the-exact-converse-federationeventscyclesv-federationeventsconversev) (with `FederationEventsConverse.v`) |
| `FederationEventsCyclesCheck.v` | `cyc_check_gc`, `cyc_check_gc_lfp`, `footprint_c1`, `check_rejects_latch`; `c1_localcc_insufficient` | [Checked per event](docs/monotone-cycles.md#event-order-on-monotone-cycles-checked-per-event-federationeventscyclescheckv) |
| `FederationEventsCyclesMulti.v` | `multi_edge_c1`, `multi_edge_gc`, `resolver_joint_c1`; `m1_necessary`, `resolver_edge_insufficient` | [Multi-edge targets](docs/monotone-cycles.md#multi-edge-targets-per-edge-c1-composes-federationeventscyclesmultiv) |

### 11. Non-monotone cycles, invertible transports ([docs/non-monotone-invertible.md](docs/non-monotone-invertible.md))

| Module | Headline theorems | Details |
|---|---|---|
| `Cohomology.v` | `gluing_order_dependent`, `fixed_point_iff_trivial_holonomy`, `simultaneous_section_iff`, the `S_3` crux (`S3Sep`) | [Cohomological layer](docs/non-monotone-invertible.md#cohomological-layer-cohomologyv) |
| `CohomologyMin.v` | `min_G_lower`, `min_ab_lower`, `theta_separation` | [Cohomological layer](docs/non-monotone-invertible.md#cohomological-layer-cohomologyv) |
| `CohomologyGraph.v` | `section_iff_coboundary`, `cycle_basis_criterion`, `H1_classification`, `betti_number` | [Cohomological layer](docs/non-monotone-invertible.md#cohomological-layer-cohomologyv) |
| `CoordinatedCycles.v` | `coordinated_sound`, `coordinated_unique_nf`, `plan_exact`, `coordination_needed`; `root_choice_matters`, `copyback_without_authority` | [Under a computed coordination](docs/non-monotone-invertible.md#non-monotone-cycles-under-a-computed-coordination-coordinatedcyclesv) |
| `RootlessCycles.v` | `rootless_section_iff_holonomy`, `rootless_nf_exists_iff`, `rootless_unique_iff`, `rootless_unique_normal_form_iff` | [Rootless propagation](docs/non-monotone-invertible.md#rootless-propagation-on-invertible-cycles-rootlesscyclesv) |
| `RootlessNetworks.v` | `net_reachable_iff`, `net_nf_exists_iff`, `net_unique_iff`, `net_unique_normal_form_iff`, `net_strong_iff`; recovered `cycle_unique_normal_form_recovered`; `rootless_mixed_square`, `rootless_source_feeds_cycle`, `rootless_global_holonomy` | [Rootless networks](docs/non-monotone-invertible.md#rootless-propagation-on-any-invertible-network-rootlessnetworksv) |
| `CoordinatedExact.v` | `coordinated_events_exact`, `coordinated_events_exact_global`; `old_condition_not_necessary` | [Event order under the plan](docs/non-monotone-invertible.md#the-exact-event-order-condition-under-the-coordination-plan-coordinatedexactv) |
| `CoordinationMinimum.v` | `plan_min_exact`, `feasible_plan`, `plan_coord_feasible`, `plan_min_attained`, `maxcut_reduction`; `plan_min_connected_needed`, `plan_min_nodup_needed`, `s3_tree_choice` | [Minimum coordination and the plan model](docs/non-monotone-invertible.md#minimum-coordination-and-the-plan-model-coordinationminimumv) |

### 12. Non-invertible (lossy) transports ([docs/non-invertible.md](docs/non-invertible.md))

| Module | Headline theorems | Details |
|---|---|---|
| `CohomologyGeneral.v` | `thm_obstruction_general`, `thm_obstruction_reachable`, `c15_exact_refuter`, `prop_minimal_qualified_iff`, `rooted_criterion`, `edge_disjoint_min`; `c15_definitive_claim_false`, `c22_cycle_basis_fails` | [General transport maps](docs/non-invertible.md#general-transport-maps-the-obstruction-the-diagnostic-and-coordination-bounds-cohomologygeneralv) |
| `RootSet.v` | `root_set_iff_forest`, `root_set_criterion_graph`, `root_set_bijection`, `root_set_count`, `root_set_decide` | [The root-set criterion](docs/non-invertible.md#the-root-set-criterion-for-lossy-networks-without-a-spanning-root-rootsetv) |
| `LossyHardness.v` | The 3-SAT reduction: `net_section_iff_sat`, `net_bijection`, `net_count`, `net_size`, `np_certificate` (NP-completeness then follows by the standard argument) | [The 3-SAT reduction](docs/non-invertible.md#the-3-sat-reduction-for-lossy-networks-lossyhardnessv) |
| `RootSetEvents.v` | `forest_events_exact`, `forest_perm_exact`, `forest_events_exact_global`, `forest_runs_by_root` | [Event order under root-set coordination](docs/non-invertible.md#the-exact-event-order-condition-under-root-set-coordination-rootseteventsv) |
| `LossyMinimum.v` | Minimum coordination: `lfeasible_iff_root_set`, `lmin_root_set`, `lmin_b_correct`, `lmin_zero_iff_sat`, `net_lmin_dichotomy`, `min_le_np_certificate`, `lossy_min_is_gfes`, `lossy_min_exceeds_cycle_bounds` | [Minimum coordination](docs/non-invertible.md#minimum-coordination-for-lossy-networks-lossyminimumv) |
| `SignedCycles.v` | Loops versus merges: `invertible_merge_is_holonomy`, `holonomy_free_section`, `section_transport`, `fundamental_cycles_holonomy`, `obstruction_loop_vs_merge`; Harary balance proved at Z/2: `harary_balance`, `balanced_no_positive_acyclic` | [Signed cycles](docs/non-invertible.md#signed-cycles-loops-versus-merges-and-the-signed-cycle-bridge-to-e-signedcyclesv-signedresolverv) |
| `SignedResolver.v` | The signed-cycle to E bridge (sufficient certificates, reading B): `switched_monotone`, `resp_reads_in_neighbors`, `signed_settlement`, `signed_settlement_harary`, `signed_fidelity`, `signed_fidelity_harary`; breaks `neg2_no_fixed_point`, `copyback_ghost`, `toggle_ghost`, `ring_needs_low_start`, `ring_low_start_E`, `unbalanced_unique_oscillates`, `flip_needs_top`, `flip_needs_top_resolver`, `xor_no_certificate`, `cyc3_unsignable`; `unique_pos_cycle_every_certificate` | [Signed cycles](docs/non-invertible.md#signed-cycles-loops-versus-merges-and-the-signed-cycle-bridge-to-e-signedcyclesv-signedresolverv) |
| `LocalSigned.v` | Local interaction graphs (Boolean, every `n`): local fidelity `rrt_sub`, `local_fidelity`, `local_fidelity_canon`, `local_signed_fidelity`, `global_to_local`; local settlement `richard_t3` (non-expansive), `outdeg_nonexpansive`, `richard_t4`, `shih_dong_E`; counterexamples `local_weaker_than_global`, `local_neg_free_no_fixed_point`, `shih_dong_not_fair`, `ring_local_conditions` | [Local interaction graphs](docs/non-invertible.md#local-interaction-graphs-local-fidelity-and-local-settlement-localsignedv) |
| `LocalFairSettlement.v` | Fair settlement under no local cycle plus out-degree at most one (gap 3 progress): synchronous form `sync_orbit_fixed` (no local cycle needed only on the orbit), `sync_simple` (Shih and Ho 1999, Theorem 3.1, by a different proof); token monotonicity `ucnt_mono`; single-token case `one_token_closed`, `one_token_fair_settlement`, `fair_settles_once_one_token`; from acyclicity `fair_settles_closed`, `fair_settlement_of_acyclic`, `rank_closed`; instances `shih_ho_instance`, `outdeg_needed`, `no_neg_not_enough`, `no_pos_not_enough`. Two tokens: `LocalTwoToken.v`; three or more are open | [Fair settlement under local conditions](docs/non-invertible.md#fair-settlement-under-local-conditions-localfairsettlementv) |
| `LocalTwoToken.v` | No closed asynchronous run with two unstable vertices under no local cycle plus out-degree at most one (gap 3 progress): `two_token_closed`, `two_token_no_closed_change`, `two_token_fair_settlement`, `fair_settles_once_two_tokens`; good and bad tokens relative to the fixed point `not_both_bad`, `tight`, `tight_arc`, the rigidity lemma `head_arc`, `G1_T`, `G1_H`; the rearrangement into a synchronous orbit `swap_TH`, `W_sort`, `W_main`, `run_bad_or_dec`; instance `two_token_instance`. Three or more tokens are open | [Two unstable vertices](docs/non-invertible.md#two-unstable-vertices-localtwotokenv) |

### 13. The full nerve as a 2-complex ([docs/non-monotone-invertible.md](docs/non-monotone-invertible.md))

| Module | Headline theorems | Details |
|---|---|---|
| `CohomologyNerve.v` | `nerve_H1_classification` (classes = relation-satisfying generator assignments up to simultaneous conjugation), `nerve_H1_abelian`, `nerve_H1_Z2_count` (`2^((\|E\| - \|V\| + 1) - rank)` classes), `nerve_Z2_full_iff`, `nerve_section_iff_coboundary`; `triangle_kills_flip` | [`H^1` on the 2-complex](docs/non-monotone-invertible.md#h1-on-the-nerve-as-a-2-complex-cohomologynervev) |

The 1-skeleton results are `H1_classification`, `gauge_fix` and `betti_number` in
`CohomologyGraph.v` (section 11 above). Sheaf gluing is mechanized over sub-federation covers in
`SheafGluing.v` (section 6 above), with the negative half, `gluing_order_dependent` in
`Cohomology.v`, placed as the counterexample to certificate compatibility; the paper's
variable-level and monotone-overlap site is not mechanized (`REGIME-AUDIT.md` gap 13).

### 14. Compositional collapse ([docs/collapse.md](docs/collapse.md))

| Module | Headline theorems | Details |
|---|---|---|
| `Collapse.v` | Acyclic `J`: `collapse_a_guarded_exact`, `collapse_c_exact`, `collapse_c_guarded_iff`, `collapse_modular_converges`; ports `port_c1_transfer`; refuted: `collapse_a_refuted` | [Compositional collapse](docs/collapse.md#compositional-collapse-sub-federations-as-effective-registries-collapsev) |

### Infrastructure ([docs/infrastructure.md](docs/infrastructure.md))

| Module | Headline theorems | Details |
|---|---|---|
| `Newman.v` | `newman`, `confluent_of_SN`, `unique_normal_forms` | [What is proven](docs/single-registry.md#what-is-proven) |
| `Trace.v` | `run_tequiv`, `perm_tequiv_total` | [Verified checkers](docs/infrastructure.md#verified-checkers-two-differential-oracles-for-gsm-checkerv-tracev-tablecheckv-tablefastv-tablefnv-astcheckerv-asttablesv-astcompactv-extraction) |
| `Checker.v` | `run_perm_invariant`, `check_commuting_sound`, `checked_converges` | [Table oracle](docs/infrastructure.md#table-oracle-tablecheckv-on-top-of-checkerv) |
| `TableCheck.v` | `check_tables_converges`, `check_tables_commute`, `tget_of_list` | [Table oracle](docs/infrastructure.md#table-oracle-tablecheckv-on-top-of-checkerv) |
| `TableFn.v` | `check_fn_converges`, `check_tables_fn`, `check_fast_fn`, `scan_cells_fn` | [Table oracle](docs/infrastructure.md#table-oracle-tablecheckv-on-top-of-checkerv) |
| `TableFast.v` | `check_fast_eq`, `check_fast_converges` | [Table oracle](docs/infrastructure.md#table-oracle-tablecheckv-on-top-of-checkerv) |
| `AstChecker.v` | `check_sound_converges`, `check_no_overflow`, `checkBuild_converges`, `checkBuild_wfc_terminates`, `stepG_valid_eq` | [Rules oracle](docs/infrastructure.md#rules-oracle-astcheckerv) |
| `AstTables.v` | `checkBuildT_eq`, `tables_fn_eq` | [Rules oracle](docs/infrastructure.md#rules-oracle-astcheckerv) |
| `AstCompact.v` | `checkBuildC_eq`, `checkBuildC_converges` | [Rules oracle](docs/infrastructure.md#rules-oracle-astcheckerv) |
| `extraction/`, `goextract/` | The two oracles extracted to OCaml (`checker`, `astchecker`) and generated as Go for gsm | [extraction/README.md](extraction/README.md), [goextract/README.md](goextract/README.md) |
| `PaperInstances.v` | The papers' examples: `of_unique_normal_forms`, `thm_necessity`, `prop_cc_necessary`, `prop_cycle_necessary`, `prop_m1_necessary`, `r1_necessary`, `r2_necessary` | [The papers' concrete examples](docs/infrastructure.md#the-papers-concrete-examples-paperinstancesv) |
| `CanonicalExecution.v`, `CanonicalInstances.v` | Validated, scoped to single systems and acyclic composition ([THEORY.md](../docs/THEORY.md#canonical-execution)): the canonical-execution kernel `peak_exact`, `classified_peak_exact`, `history_descent_exact`, `esh_exact`; rederivations `jc_exact_kernel`, `jcg_exact_kernel`, `causal_exact_kernel`, `causal_alo_exact_kernel`, `alo_exact_kernel`, `fed_exact_kernel`, `pjc_exact_kernel`, `flush_fed_iff_kernel`; `stream_free_hd_iff_pcc` (the kernel part of `stream_free_history`, which rereads `stream_exact_free`) | [Canonical execution](docs/canonical-execution.md) |
| `CanonicalLocality.v` | Validated, scoped to acyclic composition (on cycles, soundness only): the P layer, interaction locality as factorization through a composition boundary, `factor_exact`, `factor_pointwise`, `factor_needs_sound`, `factor_needs_exposed`, `factor_needs_realizable`; the acyclic federation as an instance, `gc_iff_reach_P`, `reach_commute_iff_P`, `fed_exact_P`, `fed_exact_full_P`, `fed_gc_sites`; `cyclic_lc_fails`, `cyclic_lc_sound_fails`, `cyc_factor_sound`, `cyc_factor_sound_gc`, `common_r1`, `c_local_iff_r1`, `fed_state_and_interaction` | [Canonical execution, the P layer](docs/canonical-execution.md#the-p-layer-interaction-locality-canonicallocalityv) |

## Adding a module

New modules do not append a section to this README. A new module gets:

1. its file in `_CoqProject` and its headline results in `verify.sh`'s gate (then update the gate
   count in this README: the expected tail, the gate paragraph and Build);
2. one row in the table above, in its regime's group, with its headline theorems;
3. a section in the matching `docs/<regime>.md` page (a new page only for a regime with no page yet,
   added to this index in REGIME-AUDIT.md's order);
4. if it changes what is proved for a regime, the matching row of
   [REGIME-AUDIT.md](../REGIME-AUDIT.md) and an entry in [CHANGELOG.md](../CHANGELOG.md).

## Build

```
make          # compiles every module (Newman, Governance, Defensibility, Gsm, Federation,
              # Chaotic, Checker, Trace, TableCheck, TableFast, TableFn, AstChecker,
              # AstTables, AstCompact, CRDT, ...)
make check    # prints the assumption base (expect "Closed under the global context")
```

`bash verify.sh` does the same compile and then runs the full axiom-free gate over all 2241
gated theorems. To build and run the two extracted oracles, see `extraction/` (`make`,
`make demo`, `make astdemo`). The same two checkers are also generated as Go, for gsm to run
in-process: see `goextract/` (`make test`).
