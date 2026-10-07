# Changelog

This file records notable changes to the papers and the mechanized proof in this repository.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The repository has no version tags, so entries are grouped by date (merge date for pull requests, commit date for earlier history, both as recorded in the git history, UTC-7). Theorem counts refer to the minimum enforced by the axiom-free gate in `coq/verify.sh`.

## [Unreleased]

### Added
- `coq/CompositionBlocks.v`: composition beyond acyclic collapse. Closes gap 5 in the FedMachine
  model and narrows gap 19 (REGIME-AUDIT.md section 14; COVERAGE.md cells A14, B11, B12, B13).
  Axiom-free.
  - **Blocks of any engines (gap 19 (a), closed):** a composite of an upstream system and a block
    that reads its current state converges (from every start a quiet state is reached, and every
    reachable one is the same) iff the upstream converges, the block reaches a quiet state from
    every start at every quiet input, and two quiet states of the block at a quiet input are equal
    when its steps at the inputs the upstream passes through connect them (`compose_exact`). The
    normal form is the block-by-block one (`compose_collapse`). A black-box interface (each block
    settles, with normal forms determined by inputs its steps preserve) is closed under
    composition, exactly (`interface_closed`, `settles_conv`, `interface_lk`), so it iterates over
    any DAG of blocks.
  - **Each conjunct needed:** `compose_needs_A`, `compose_needs_wn`, and
    `compose_isolated_refuted`: every block converges in isolation, and the composite reaches two
    normal forms (the sticky block). The block is constrained only at quiet inputs
    (`compose_transient_free`).
  - **Engines:** rootless invertible networks, `rootless_conv_iff` (`net_unique_normal_form_iff`
    read as convergence) and `mixed_rootless_exact`; monotone cycles, `mono_block_interface_iff`
    (one fixed point, through `q1_unique_iff`) and `mixed_mono_iff`. Instances `mixed_instance`,
    `mixed_mono_instance`, and `mixed_ghost_refuted`: a rootless block feeding the flag cycle, where
    a transient alarm lifts the cycle to its ghost.
  - **Cyclic monotone `J` (gap 5, closed in the FedMachine model):** Bekic's principle for the
    triangular repair (`bekic_lfp`), so `N'` and `N` have the same normal form
    (`mono_collapse_nf`), the same runs, and converge together, exactly under GC
    (`mono_collapse_converges_iff`, `mono_collapse_exact`); instance with gsm's `normalizeCyclic`
    (`mono_collapse_instance`).
  - **Distributed model (gap 19 (b), closed for an acyclic `J`):** `dist_atoms_exact`, the exact
    condition over any atom set (`dist_exact` recovered, `dist_exact_recovered`); with `J`
    propagating as one atom, `dist_collapse_exact`; `N` converges iff `N'` does and XU holds at
    every state `N` reaches (`dist_collapse_iff`, `dist_collapse_sound`); the plain collapse
    statement fails (`dist_collapse_refuted`: a chain, `J = {1, 2}`), XU alone is not enough
    (`dist_collapse_needs_c2`), and static XU restores it (`dist_collapse_xu`). Residue: a cyclic
    `J` in the distributed model.
  - **Docs:** `coq/docs/collapse.md` (new section), `coq/README.md` row, REGIME-AUDIT.md (section
    14, gaps 5 and 19, the cyclic frontier), docs/COVERAGE.md (cells and counts), docs/ROADMAP.md.
  - **Gate:** raised from 3384 to 3513.
- `coq/DifferenceAbstraction.v`: abstraction for difference constraints with saturating writes
  (roadmap item 8, step 2, the arithmetic route; gsm roadmap item 1b). Axiom-free. A finite
  representative cutoff, no solver.
  - **Model:** gsm's: integer variables with declared ranges, its combinators (`V`, `Lit`, `Add`,
    `Sub`, comparisons, `And`, `Or`, `Not`), guarded events of sequential assignments, the first
    violated invariant's repair, and every write saturating at the declared bounds (`clampZ`).
  - **Fragment:** `dfrag`: guards `x - y op c` with `|c| <= gam` and `x op a` with `a` an anchor;
    writes `x := y + c` and `x := a`; offsets per transform summing to at most `mu`; the bounds
    are anchors.
  - **Cutoffs (each an iff, over the declared ranges against the in-range states within
    `n(W + 1)` of an anchor):** repair within K steps at `W >= gam + K mu` (`dterm_abs`), CC1 at
    the valid states and at every state at `W >= gam + 4(K + 1) mu` (`dcc1v_abs`, `dcc1_abs`),
    idempotence at `W >= gam + 3(K + 1) mu` (`didemv_abs`); gsm's guarantee (`dgsm_exact`,
    `dgsm_sound`, `dgsm_sound_all`, end to end `dbuild_sound`; `dcheck_fail_real`). Through the
    region relation (`near`, `RelS`, `cc1_pair`) and compression by pigeonhole (`compress_d`,
    `shift_step`); size `RepS_length`, `dom_length`.
  - **Comparison fragment recovered:** at threshold 0 the relation is `AbstractionCutoff.v`'s order
    isomorphisms (`rel0_oiso`), and `reps n C` lies in the domain (`reps_in_dom`).
  - **Boundaries:** a difference guard passes the order-pattern check and diverges, and the new
    check reports it (`gap_order_check_passes`, `gap_check_fails`, `gap_diverges`);
    `triangle_diverges`' guard is refused (`tri_refused`, `tri_diverges`); a sum of two variables
    passes the representative check and diverges (`sum_refused`, `sum_check_passes`,
    `sum_diverges`); the threshold must cover chained increments (`granularity_needs_chain`).
  - **Non-vacuity, over ranges up to 10^9:** a wallet with overdraft repair over 657
    representatives (deposits converge; deposit against withdraw diverges at balance 5),
    capped inventory with restocks (233), reservations `reserved <= stock` (`102^2`), gsm's
    documented inventory at threshold 0 (`13^3`).
  - **Docs:** `coq/docs/abstraction.md` (new section with the gsm design input), `docs/ROADMAP.md`
    item 8, `docs/THEORY.md`, `coq/README.md` row, and the count lines.
  - **Gate:** raised from 3243 to 3384.
- `coq/ReconfigurationClosure.v`: the barrier's A part without injectivity, closing gap 20 residue
  (c) in the deterministic model (section `Det` of `Reconfiguration.v`, gsm's runtime). Axiom-free.
  Gap 20 stays narrowed: residues (a) and (b) remain.
  - **Exact characterization:** A converges modulo M (two permutations of the same A-events reach
    states with equivalent images, the A part of `det_barrier_exact`) iff M agrees after every
    adjacent swap at a reachable state followed by any common continuation (`amodm_swap_exact`),
    iff M agrees on every pair of the pair closure: the seeds `(b (a t), a (b t))` at reachable `t`,
    closed under applying one event to both components (`amodm_closure_exact`, `pc_iff`). Generic
    forms for any deterministic step and observation: `perm_swap_exact`, `closure_perm_exact`,
    `perm_local_exact`.
  - **The barrier and live outcomes in local form:** `det_barrier_closure_exact`,
    `det_barrier_local_exact`, `det_live_local_exact`, `permB_local_exact`, `permA_eq_local_exact`;
    `det_barrier_faithful` recovered (`det_barrier_faithful_closure`,
    `det_barrier_closure_faithful`), and the sufficient direction (`det_closure_of_permA`).
  - **Complete classification:** on finite instances the closure is computed (`pc_star_iff`,
    `closure_dec`) and finds a separated pair iff A diverges modulo M (`amodm_witness_exact`,
    `closure_witness_exact`); `det_classify_complete` decides Online, BarrierOnly or Unsafe with
    no faithfulness hypothesis and no unknown case (`det_live_dec`, `det_barrier_dec`,
    `det_classified_unique`, `det_unsafe_exact`).
  - **gsm's search:** the pruned closure `PCg` (one orientation per event pair, equal pairs
    skipped), as `CheckMigration` computes it, checks the same condition (`gsm_closure_exact`), so an
    exhausted search with no witness certifies the barrier.
  - **Instances:** last-writer-wins A with non-injective migrations: `merged_online` (Online),
    `merged_barrier` (BarrierOnly, certified by the closure, with A diverging and M not injective),
    `partial_merge` (Unsafe, `partial_merge_witness`); `closure_nonvacuous`,
    `gsm_search_instances`, `merged_classified_outcomes` (non-vacuity of every hypothesis).
  - **Docs:** `coq/docs/reconfiguration.md` (new section with the gsm design input, scope),
    `REGIME-AUDIT.md` gap 20, `docs/ROADMAP.md` item 9, `docs/COVERAGE.md`, `coq/README.md` row,
    and the count lines.
  - **Gate:** raised from 3180 to 3243.

- `coq/CompositionalCheck.v`: compositional checking by default, roadmap item 8 step 3 (gsm
  roadmap item 1c: check each footprint component, conclude for the registry). Axiom-free. Roadmap
  work, not a regime gap: no gap status changes.
  - **Model:** footprints as read and write sets (`Local`, `PLocal`), components (`Inside`, with
    shared read-only variables allowed), first-violated repair as in gsm, eager compensation to a
    repair bound; gsm's guarantee `Conv` (every order of the same events from a valid state, one
    state) is exactly CC1 on valid states (`conv_iff_cc1`, through `perm_good_iff`).
  - **Decomposition, each exact:** one repair step is a step of one component (`rho_step`,
    `iter_proj`); termination and WFC per component (`term_iff`, `wfc_iff`, `wfcb_iff`), the
    repair bound the sum of the component bounds (`bound_sum`); cross-component raw effects
    commute (`raw_cross_commute`) and cross-component pairs satisfy CC1 at valid states with no
    check (`cc1_cross`); same-component CC1 iff on the component (`cc1_same_iff`,
    `cc1_component`); the registry's guarantee iff every component's (`compositional_exact`,
    `compositional_gsm`); bound independence (`N_indep`, `conv_indep`).
  - **The check and its cost:** `comp_check` enumerates each component's subspace and decides WFC
    within the bounds and the guarantee (`comp_check_exact`, `wfc_check_exact`,
    `cc1_check_exact`); cost `|D|^(n_k)` per component (`enum_length`). gsm's zero-background
    component check computes the same conditions (`gsm_literal`, `gsm_literal_iter`,
    `gsm_literal_step`).
  - **Combinator footprints:** extraction over `AstChecker.v`'s grammar (`readsE`, `readsP`,
    `readsT`, `writesT`) proved to over-approximate reads and writes (`evalE_reads`,
    `evalP_reads`, `applyT_writes`, `applyT_reads`, `ast_event_local`, `ast_check_local`,
    `ast_repair_local`); `blocks_ok` certifies a component assignment (`ast_hyps`); the registry's
    normalization is `AstChecker.normalize` (`ast_N_normalize`). Closure footprints stay a tested
    trust boundary.
  - **Counterexamples and non-vacuity:** footprints without reads, the pay/ship pattern
    (`ws_ship_not_local`, `ws_check_passes`, `ws_diverges`, `ws_true_footprint`,
    `inside_merge`); a repair writing another component (`rc_repair_not_local`,
    `rc_check_passes`, `rc_diverges`); a written shared variable (`sw_pay_writes_shared`,
    `sw_check_passes`, `sw_diverges`); orders and inventory, with and without a shared store
    flag (`shop_hyps`, `shop_check`, `shop_converges`, `shop_repair_fires`, `shop_cost`,
    `shop_gsm_literal`, `shop_shared_read`); a combinator machine (`ast_demo`).
  - **Docs:** new `coq/docs/compositional.md` (with the gsm design input), `coq/README.md` row,
    `docs/ROADMAP.md` item 8 step 3, `docs/THEORY.md` (compositional checking as locality used
    for checking), and the count lines.
  - **Gate:** raised from 3029 to 3179.

- `coq/AbstractionGsm.v`: the gsm instantiation of `AbstractionCutoff.v` (roadmap item 8 step 2,
  gsm roadmap item 1b). gsm's Build checks CC1 at the valid representative states only and its
  runtime normalizes before applying; these theorems cover exactly that, for general m (gsm's
  m = 0 gives cutoff N = n). Axiom-free. Roadmap work, not a regime gap: no gap status changes.
  - **CC1 at the valid states:** `cc1_valid_abs` (for the checked pairs of a relation I on event
    kinds, over all integers iff over `reps N C`, N >= n + 2m), `cc1v_order_type`, the finite check
    `cc1v_check` (`cc1v_check_spec`).
  - **Idempotence transfers:** `idem_abs` (every state), `idem_valid_abs` (valid states),
    `idem_runtime_abs` (gsm's runtime step from every integer state), N >= n + m;
    `idem_order_type`, `idemv_check` (`idemv_check_spec`). gsm's `NotIdempotent` list computed from
    the representatives is exact for every integer state.
  - **Fragment preservation:** `OIMap`, `oimap_closed`, `oimap_id`, `oimap_comp` (order-invariant
    maps compose), `oimap_itr`, `oimap_rp`, `oi_ap_after`; the repair-first registry `apR` stays in
    the fragment (`derived_shaped`, `derived_ordinv`).
  - **The prose route mechanized:** `cc1_derived_valid` (CC1 at every state of the repair-first
    registry iff CC1 at the valid states), `cc1_valid_derived_abs` (through `cc1_abs`).
  - **gsm's guarantee:** `gsm_abs_exact` (given repair within K steps over the representatives,
    CC1 for I at the valid representative states iff trace-equivalent runs from every valid
    integer state converge, through `Trace.run_tequiv`), `gsm_abs_sound` (gsm's runtime step
    converges from every integer state, the zero state included), `gsm_abs_sound_all`
    (permutations).
  - **Boundary and non-vacuity:** `idem13_passes`, `idem13_diverges`, `idem13_refused` (an
    undeclared exact test fools the idempotence check); the capped inventory (`capped_cc1_valid`,
    `capped_idem`, `capped_derived`, `capped_runtime`); gsm's documented example with m = 0 over 343
    representative states (`inventory_runtime`, `inventory_idem`); a non-idempotent swap reported
    with an integer witness (`swapxy_not_idem`).
  - **Docs:** `coq/docs/abstraction.md` section "gsm instantiation", `coq/README.md` row, and the
    count lines.
  - **Gate:** raised from 2974 to 3029.

- `coq/AbstractionCutoff.v`: the abstraction reduction over integer-valued state, roadmap item 8
  step 2 (gsm roadmap item 1b: check relationships, not values). Axiom-free. Roadmap work, not a
  regime gap: no gap status changes.
  - **Bounded repair:** `un_bounded` (with repair within K steps, unique normal forms from every
    state iff CC1 and CC2 everywhere, through `cc_exact_from`), `un_at`.
  - **Order-invariant fragment:** `OIso`, `OrdInv`; the representatives `reps N C`, of size
    `|C|(N+1) + N` (`reps_length`); `compress` (any finite set of integers moved next to the
    constants, order and constants kept). Cutoffs, each an iff over all integers: repair within K
    steps and WFC with N = n (`term_abs`, `wfc_abs`), CC2 with N = n + m (`cc2_abs`), CC1 and
    unique normal forms with N = n + 2m (`cc1_abs`, `un_abs`); the finite check `abs_check`
    (`abs_check_spec`, `abs_check_exact`, `abs_check_sound`); one check per order type
    (`cc1_order_type`, `cc2_order_type`); no fresh values (`closure_ap`, `closure_rp`).
  - **The fragment decided:** a rule language (variables, literals, +, -, *, if-then-else,
    comparisons); `ord_frag_sound`, `prog_shaped`, `build_sound`.
  - **Linear fragment, exact reduction to formula validity:** generated formulas `phi_term`,
    `phi_cc1`, `phi_cc2`; `phi_term_exact`, `phi_cc1_exact`, `phi_cc2_exact`, `lin_exact`,
    `lin_sound`; `lin_frag_linear` (multiplication by literals only, so the formulas are QF_LIA).
    Deciding validity is left to an external solver; no finite representative set is claimed.
  - **Counterexamples and non-vacuity:** `exact13_passes`, `exact13_diverges`, `exact13_refused`,
    `exact13_declared` (an undeclared exact test); `triangle_passes`, `triangle_diverges`,
    `triangle_refused`, `triangle_formula_refuted` (an additive guard fools the order-pattern
    check); `copy_tight` (the bound cannot drop below n); capped inventory over 7 representatives
    (`capped_un`, `capped_repair_fires`); a wallet with integer balances through its 13 formulas
    (`wallet_formulas`, `wallet_un`); with symmetry, `sym_abs` and `capped_catalog`.
  - **Docs:** new `coq/docs/abstraction.md` (with the gsm design input), `coq/README.md` row,
    `docs/ROADMAP.md` item 8, `docs/THEORY.md` (abstraction as state descent on value relations),
    and the count lines.
  - **Gate:** raised from 2827 to 2974.

- `coq/SymmetryCutoff.v`: the symmetry reduction for keyed collections, roadmap item 8 step 1 (gsm
  roadmap item 1a: check one item, conclude for all). Axiom-free. Roadmap work, not a regime gap:
  no gap status changes.
  - **Cutoffs:** for independent, identically governed items, cutoff 1 for unique normal forms
    (`un_cutoff`, `un_cutoff_uniform`, `un_cutoff_global`, through `cc_lift_iff` and
    `cc_exact_from`), WFC (`wfc_cutoff`), CC2 (`cc2_cutoff`), at-least-once convergence with
    commutation and idempotence (`alo_cutoff`, `alo_cutoff_exact`, `alo_gov_cutoff`), idempotence
    and declared independence (`idem_reduces`, `declared_cutoff`), and federation C1 and C2 across a
    pointwise morphism (`c1_cutoff`, `c2_cutoff`). CC1 alone has cutoff 2 (`cc1_cutoff`,
    `cc1_cutoff_uniform2`), tight (`cc1_cutoff_tight`).
  - **Cross-item pairs:** `same_item_reduces`, `cross_item_reduces` (one repair-then-event
    obligation per item), `cross_valid_commute` (no hypothesis at valid states), `cc2_star`,
    `cross_commute`.
  - **Hypotheses made checkable:** `IdGov` (writes and reads only its key, repair pointwise, rules
    invariant under exchanging keys, invariant a conjunction of item invariants); `idgov_lift`,
    `lift_idgov`, `symcheck_decides` (a sound and complete decision on finite descriptions),
    `symmetry_sound`; `un_in_to_item` (the converse from in-range buffers).
  - **Counterexamples and non-vacuity:** `aggregate_diverges`, `agg_item_un`, `agg_not_idgov`,
    `itemwise_converges` (an aggregate invariant: one item converges, two diverge, the check
    refuses it); `nonidentical_misleads`, `nonidentical_not_idgov`; per-product inventory
    `inventory_any_n`, `inventory_repair_fires`, `inventory_idgov`.
  - **Docs:** new `coq/docs/symmetry.md` (with the gsm design input), `coq/README.md` row,
    `docs/ROADMAP.md` item 8, `docs/THEORY.md` (symmetry and state descent), and the count lines.
  - **Gate:** raised from 2693 to 2827.

- `coq/Reconfiguration.v`: reconfiguration inside a run, a switch from configuration A to
  configuration B (a migration `m` of the state, a translation `tau` of the A-events in flight);
  narrows audit gap 20 (a new axis). Axiom-free.
  - **Single registry, barrier:** `barrier_exact` (B's condition after every quiescent reachable
    state, and A's normal forms agreeing after `rhoB_star o m`); `barrier_exact_faithful` (each
    side's own condition when that map is injective on the quiescent reachable states);
    `barrier_sufficient`.
  - **Single registry, live:** `live_exact` (`LiveConv <-> LiveCond`: B's condition from `m s` for
    every reachable `s`, quiescent or not, plus the cross pairs S1, an in-flight event commutes with
    the switch, and S2, the switch absorbs A's compensation), `live_exact_faithful` (with A's
    condition, for a faithful migration), `live_implies_barrier`, `live_no_change` (recovers
    `cc_exact_from`); witnesses `s1_runs`, `s2_runs`, `live_b_runs`, `live_b2_runs`,
    `barrier_b_runs`, `amodf_runs`.
  - **Classification:** `classified_unique`, `classify`; on finite instances `reach_dec` (via
    `star_fin_dec`), `live_dec`, `faithful_dec`, `barrier_dec_faithful`, `classify_finite`.
  - **Federations (FedMachine):** `det_live_exact`, `det_barrier_exact`, `det_barrier_faithful`
    (deterministic steps, free delivery); `fed_live_exact` (B's C1R1 and C2R at the migrated start
    plus the switch commuting with in-flight events), `fed_barrier_exact`.
  - **Counterexamples:** `cap_raise` (S2), `doubling_migration` (S1), `migrated_transient` (B's
    condition at a migrated transient state), each with A and the barrier switch converging;
    `forgetful_migration` (A's condition not necessary, and the barrier qualifier needed);
    `late_edge` (adding an edge read by an in-flight event). Non-vacuity: `rescaled_cap`,
    `late_edge_fresh`, `finite_instance`, `instances_classified`, `lww_target`.
  - **Residue:** a live switch in the distributed model (propagation in flight); other delivery
    classes across the switch; a local form of the barrier's A part for an unfaithful migration.
  - **Docs:** `coq/docs/reconfiguration.md` and the `coq/README.md` row; `REGIME-AUDIT.md` gap 20
    row (narrowed), frontier and regime tables, summaries; `docs/COVERAGE.md` section 4 and section
    5's gap 20 row (cell counts unchanged: a new axis); `docs/ROADMAP.md` item 9; `docs/REGIMES.md`;
    `README.md` open-gap sentence (still eight open gaps), and the count lines.
  - **Gate:** raised from 2569 to 2693.
- `coq/RobertFair.v`: Robert's theorem for fair asynchronous schedules on acyclic networks,
  mechanized in the repository's propagation model; closes audit gap 16 (d). Gap 16 stays open for
  (a) to (c). The theorem is Robert's (1986, 1995; Richard 2019, Theorem 1). Axiom-free.
  - **Main results:** `rb_robert_fair` (distributed model: every fair schedule from every valid
    start settles at the run of one topological order), `rb_unique`, `rb_topo_runs`; rounds
    `rb_rounds`, `rb_rounds_all`, `rb_rounds_pos` (final after depth plus one rounds); effective
    steps `rb_effective` (fewer than `2^|o|` along any propagation word), `rb_closed` (the
    asynchronous state graph is acyclic); resolver model `rb_lens_robert`, `rb_lens_closed`; Boolean
    networks with an acyclic global interaction graph `rb_robert_boolean` (through
    `fair_settlement_of_acyclic`).
  - **Events:** `rb_events`, `rb_event_schedule` (finitely many events, then or interleaved with
    fair propagation: the FedMachine run of the events, under XU); `rb_fair_dist_exact` (the limits
    agree iff `XUR` and `C2R`, `dist_exact`'s condition).
  - **Recovered:** `rb_order_independent` (`order_independent` in the distributed model);
    `propagation_flush` with the final flush replaced by any fair schedule (`rb_events`).
  - **Counterexamples:** `rb_neg2_cycle` (no fixed point, no fair schedule settles),
    `rb_copyback_cycle` (two fair schedules settle at different fixed points),
    `rb_dist_cycle_needed`, `rb_absorb_needed`; the converse fails, `rb_converse_fails` (Shih and
    Ho's network). Non-vacuity: `rb_example`, `rb_bool3`, `rb_supply_events`,
    `rb_supply_fair_conv`, `rb_gg_not_fair_conv`.
  - **Docs:** `coq/README.md` row, `coq/docs/distributed.md` section, `REGIME-AUDIT.md` sections 6
    and 8 rows, gap 16 row, frontier and summary rows, and the Robert citations;
    `docs/LOSSY-NETWORKS.md` sections 2, 4.1, 4.2 and P2; `docs/LANDSCAPE.md`; `docs/COVERAGE.md`
    cell A2 and counts; `docs/REGIMES.md`; `docs/ROADMAP.md`; `docs/THEORY.md`;
    `coq/docs/non-invertible.md`; `README.md` open-gap sentence (eight open gaps, unchanged), and the
    count lines.
  - **Gate:** raised from 2467 to 2569.

- Gap 15 closed in full: `coq/StreamAtLeastOnce.v`, `coq/DistributedDelivery.v` and
  `coq/FederatedGuards.v` close audit gap 15 (b), (c) and (d); (a) closed earlier
  (`AtLeastOnceDeclared.v`). Axiom-free.
  - **(b) Streams:** received lists may repeat events. Free delivery: `stream_alo_exact_free`
    (`StreamAgreeA <-> PCC /\ PIdem`, idempotence where a processor first applies the event),
    `stream_alo_free_split` (exactly-once agreement plus `PIdem`, so `stream_exact_free` is
    recovered). Any enabledness under `Progress`: `stream_alo_exact` (PJC at every list plus
    absorption of one redelivered copy, a reduction); `stream_exact_recovered`.
  - **(c) Distributed model:** `dist_delivery_exact` for any delivery class closed under prefixes
    (XU at the class's reachable states plus FedMachine convergence over the class);
    `dist_causal_exact`, `dist_alo_exact`, `dist_causal_alo_exact`; `dist_exact_tc` recovered.
    The FedMachine conditions are a setoid form of `causal_exact` and `causal_alo_exact_idem`
    (`causal_conv_s_exact`, `causal_alo_s_exact`, with the Leibniz theorems recovered). gsm:
    static XU gives the propagation conjunct for every class (`xu_xurd`).
  - **(d) Buffered guards:** `fed_buffered_exact`, `fed_buffered_cr` (co-enabled events stay
    enabled after each other and commute at guard-feasible states), per edge `fed_buffered_edge`,
    the trivial guard recovers `fed_guarded_exact`'s condition (`fed_buffered_recovers`); any
    enabledness: `fed_jcg_exact` (JC', termination discharged).
  - **Counterexamples:** `ct_alo_fails`, `ow_alo_fails`, `ct_general`, `ow_general` (streams);
    `tr_causal_instance` (restricting `dist_exact` is not exact for causal delivery),
    `snap_xu_needed`, `set_comm_needed`, `inc_idem_needed` (distributed);
    `bg_persistence_needed`, `bg_commute_needed`, `bg_wait_exact` (guards). Non-vacuity:
    `mx_alo_holds`, `mk_alo_holds`, `bg_wait_exact`.
  - **Docs:** `coq/README.md` rows, `coq/docs/streams.md`, `coq/docs/distributed.md`,
    `coq/docs/federation-events.md` sections and an `at-least-once.md` pointer; `REGIME-AUDIT.md`
    sections 3, 5, 7 and 8 rows, gap 15 row (closed), frontier and regime tables, summaries;
    `docs/COVERAGE.md` cells C3, C6, C8 and counts (59 exact, 16 uncovered); `docs/REGIMES.md`,
    `docs/ROADMAP.md`, `README.md` open-gap sentence (now eight open gaps), and the count lines.
  - **Gate:** raised from 2380 to 2467.

- `research/gap3-fair-settlement/K3.md`: the three-token SAT decision extended to n = 7 (UNSAT
  with both encodings of (A) under CaDiCaL, about 2.5 h each). Gap 3 stays open.
- `coq/ProjectionChannels.v`: propagation over channels that deliver projections late, reordered
  or duplicated, for gsm's `MergeProjection` (plain) and `MergeProjectionAfter` (versioned);
  narrows audit gap 21 (a new axis). Axiom-free.
  - **Model:** projections in flight carry a version and a snapshot; `CDel` delivers any one of
    them (reordering, delay), `CDup` delivers one and keeps it (duplication); the version discipline
    `disc` is gsm's contract (strictly increasing per edge in send order). The current-value model
    is immediate delivery (`emb_run`, no hypothesis).
  - **Main results:** `chan_exact` (either mode, after a flush: `ChanConv <-> CXUR /\ C2R`),
    `chan_exact_global`, `chan_global_exact_roots`, `chan_xu_c2`; versioned at drain `vsettle`,
    `vsettle_exact`, `vsettle_exact_cond` (`SettleConv <-> CXUR true /\ C2R`, no outside flush),
    `vsettle_cv` (the drained state is the current-value run's), `vsettle_xu_c2`; plain at drain
    `plain_settle_iff`; two-level networks `vchan_emulate`, `vchan_twolevel_exact` (`dist_exact`'s
    condition).
  - **Counterexamples:** `plain_stale_counterexample` (plain merge under XU: a stale projection
    delivered after the fresh one leaves a drained run unsettled, and two drained runs of the same
    events disagree), `version_order_counterexample`, `no_final_send_counterexample`,
    `vchan_cyc_ghost` (the ghost survives versioned channels). Non-vacuity: `late_delivery_instance`.
  - **Residue:** the current-value form beyond two-level networks (`CXUR true` against `XUR`), and
    channels on cycles (flush and reset epochs).
  - **Docs:** `coq/README.md` row, `coq/docs/distributed.md` section, `REGIME-AUDIT.md` section 8
    rows, gap 21 row, frontier row and summaries, `docs/COVERAGE.md` section 4, `docs/REGIMES.md`,
    `docs/ROADMAP.md`, `README.md` open-gap sentence (nine open gaps, unchanged), and the count
    lines.
  - **Gate:** raised from 2290 to 2380.

- `coq/AtLeastOnceDeclared.v`: at-least-once delivery under declared independence `I`, exactly;
  closes audit gap 15 (a). Gap 15 stays open for (b) to (d). Axiom-free.
  - **Model:** a delivery `d` of a history `o` is `ALOI o d` when every pair some copy delivers out
    of `o`'s order is declared independent; on exactly-once deliveries this is trace equivalence
    (`aloi_nodup_iff`).
  - **Main results:** `dalo_exact` (convergence iff declared pairs commute after every reachable
    exactly-once prefix, `CommI`, and every event is idempotent at reachable first deliveries),
    `dalo_exact_absorb`, `dalo_exact_trace`, `tconv_exact`; per event `safe_i_exact`,
    `safe_i_iff_idem`; unordered retries `dalo_r_exact`, `safe_r_exact`, `dalo_r_implies`.
  - **Recovered:** `alo_exact_declared` (free) and `causal_alo_exact_declared` (causal) through
    `dalo_exact`.
  - **gsm:** `Report.NotIdempotent` with `Independent` pairs is sound at reachable witnesses
    (`dalo_notidem_needs_dedup`) and complete when the declared pairs commute at reachable states
    and every reachable state is valid (`dalo_gsm_unlisted_safe`); deduplicating the listed events
    then suffices (`dalo_unlisted_converge`); Build plus an empty report gives convergence
    (`build_comm_i`, `dalo_gsm_build`).
  - **Counterexamples:** `fl_retry_order_needed` (a retry of `Add` that crosses the undeclared
    `Remove` diverges although `Add` is idempotent everywhere: retries must respect the declared
    order), `fl_partner_overtakes` (`Add` and `Remove` declared: the redelivered `Add` overtakes its
    declared partner, so completeness needs `CommI`), `inc_declared_fails`,
    `jmp_declared_unreachable`. Non-vacuity: `fl_declared_exact`, `fl_gsm_build`, `mx_declared_r`.
  - **Docs:** `coq/README.md` row, `coq/docs/at-least-once.md` section, `REGIME-AUDIT.md` section 3
    rows, gap 15 row and summaries, `docs/COVERAGE.md` cell C10 and counts, `docs/REGIMES.md`,
    `docs/ROADMAP.md`, `README.md` open-gap sentence (nine open gaps, unchanged), and the count
    lines.
  - **Gate:** raised from 2251 to 2290.

- `coq/LocalTokenBalance.v`: the imbalance law under out-degree at most one (B), for every number
  of tokens; progress on audit gap 3, which stays open. Axiom-free, every `n`.
  - **Main results:** `image_distance` (d(F x, p) + g = d(x, p) + b for any state p, no
    hypothesis), `ucnt_split`, `bad_le_good` ((B) and a fixed point p: at most half the tokens are
    bad; neither (A) nor the absence of self-loops is used), `bad_half`, `bad_le_half`
    (b <= floor(k/2)).
  - **Corollaries:** `not_both_bad_k2` (`LocalTwoToken.not_both_bad` as the case k = 2) and
    `three_token_shape` (with three tokens, (g, b) is (3, 0) or (2, 1); counting only).
  - **Instance:** `token_balance_instance`, Shih and Ho's network: (1, 1) at `1110` (the bound
    attained), (3, 0) at `0100`, (2, 1) at `1001`.
  - **Docs:** `coq/README.md` row, `coq/docs/non-invertible.md` section, one line in the
    `REGIME-AUDIT.md` gap 3 row and in `docs/LOSSY-NETWORKS.md` P2, and the count lines.
  - **Gate:** raised from 2241 to 2251.

- `research/gap3-fair-settlement/K3.md` and scripts: the three-token case of audit gap 3, not
  proved and not mechanized. No closed asynchronous run with exactly three unstable vertices under
  (A) and (B) for n = 3 to 6 (SAT, two encodings of (A), two solvers; n = 7 running at the time of
  writing); transition statistics over 31,490 sampled moves; structural lemmas with short proofs
  (at most half the tokens are bad, near-rigidity at one bad token, the two critical pairs); every
  candidate order tried and how it fails; and the obstruction (a per-token rate balance needed to
  normalize a closed run into synchronous rounds). Gap 3 stays open.
- `docs/COVERAGE.md`, the regime coverage matrix: a systematic coverage pass that checks
  `REGIME-AUDIT.md` from the model's axes. Thirteen axes are derived from the Coq premises and the
  audit's vocabulary (composition, transport class, writer semantics, authority, execution model,
  schedule and reset, delivery, enabledness, state and order, start quantification, reference
  state, property, network size), compared in both directions with the axes proposed for the pass,
  and pruned by ten axis dependences. Of 179 cells: 58 covered (54 exact, 4 exact with a mechanized
  hardness reduction), 12 excluded, 19 open under existing gaps, 55 degenerate, 14 ill-formed, and
  21 with no row (12 distinct questions). No theorem added, removed or renamed; no existing gap's
  status changes.
  - **New open gaps 15 to 21** (`REGIME-AUDIT.md` gap table, frontier table and summaries;
    `README.md` open-gap sentence, now nine open convergence gaps; `docs/ROADMAP.md` open items;
    `docs/README.md`): 15, delivery and enabledness off the replay model; 16, the distributed
    model off its current hypotheses; 17, rootless edge-writer dynamics beyond the regular action;
    18, existence and counting in reading B; 19, composition beyond acyclic collapse; 20,
    reconfiguration inside a run (new axis); 21, propagation over channels (new axis: gsm's
    `MergeProjection` and `MergeProjectionAfter` behavior is outside the mechanized model).
  - **New design exclusions X1 to X5**: Byzantine participants, nondeterministic repair,
    probabilistic schedules, infinite networks, real-time semantics (`REGIME-AUDIT.md`,
    `docs/ROADMAP.md`, `README.md`).
- `coq/LocalTwoToken.v` (#93): no closed asynchronous run with two unstable vertices under no
  local cycle (A) plus out-degree at most one (B); progress on audit gap 3, which stays open.
  Axiom-free, every `n`.
  - **Main results:** `two_token_closed` (no closed asynchronous run from a state with at most two
    unstable vertices changes the state), `two_token_no_closed_change`, and fair settlement at the
    unique fixed point from every start with at most two unstable vertices
    (`two_token_fair_settlement`) and for every fair run that ever reaches such a state
    (`fair_settles_once_two_tokens`).
  - **Proof:** relative to the fixed point p, a token is good when its vertex disagrees with p.
    With two tokens one is good (`not_both_bad`, from non-expansiveness). With one of each, the
    synchronous step is exactly as far from p as the state (`tight`), which forces every vertex
    of the disagreement set to have an out-arc into it plus the bad token (`tight_arc`); so the
    bad token never points into that set (`head_arc`), and the token types are invariant on
    two-token runs (`G1_T`, `G1_H`). Two good tokens move strictly toward p (`run_bad_or_dec`).
    In the mixed case "good then bad" swaps into "bad then good" (`swap_TH`), and a closed run
    rearranges into (good, bad) pairs (`W_sort`, `W_main`), each the synchronous step, which
    `sync_orbit_fixed` excludes.
  - **Instance:** `two_token_instance`, Shih and Ho's network at `1110` (one good and one bad
    token), from which every fair schedule settles at `1111`.
  - **Evidence and mining:** `research/gap3-fair-settlement/K2.md` and scripts: the two-token case
    decided UNSAT by SAT for n = 3 to 7 (two solvers, two encodings of (A)); the candidate
    invariants tested and how each fails; the good-token count is the one that survives, and for
    three tokens it can rise (a SAT witness at n = 4).
  - **Open:** three or more tokens.
  - **Docs:**
    - `REGIME-AUDIT.md`: header, current state, history, gap 3 rows (open-gap table and cyclic
      frontier), and the cyclic raw material.
    - `docs/ROADMAP.md`: Done row and gap 3's progress and "Next".
    - `docs/LOSSY-NETWORKS.md`: P2.
    - `docs/LANDSCAPE.md`, `docs/THEORY.md`, `docs/REGIMES.md`, `README.md` (open-gap sentence).
    - `coq/README.md` row and `coq/docs/non-invertible.md`, a section on `LocalTwoToken.v`.
    - `research/gap3-fair-settlement/README.md`.
    - Current-count lines.
  - **Gate:** raised from 2189 to 2241.
- `coq/LocalFairSettlement.v` (#92): fair settlement for Boolean resolver networks under no local
  cycle (A) plus out-degree at most one (B); progress on audit gap 3, which stays open.
  Axiom-free, every `n`.
  - **Synchronous form:** `sync_orbit_fixed` shows that (B), with (A) at one state of a
    synchronous periodic orbit, makes the orbit a fixed point. The proof uses isometry of the
    orbit under the shift, from non-expansiveness and periodicity, plus `cycle_or_sink`.
    `sync_simple` follows: (A) and (B) give a unique fixed point that every synchronous orbit
    reaches within `2^n` steps. This is the conclusion of Shih and Ho 1999, Theorem 3.1, by a
    different proof.
  - **Single-token lemma:** `ucnt_mono` shows that (B) alone makes the number of unstable
    vertices non-increasing. With one unstable vertex an asynchronous move is the synchronous
    step (`one_step_F`, `orbit_of_run`). So `one_token_closed` holds: under (B), with (A) at a
    state with at most one unstable vertex, no closed asynchronous run through that state changes
    it.
  - **Fair settlement from acyclicity:** `fair_settles_closed` (by fair rounds and pigeonhole:
    `round`, `pigeon`, `nodup_states_bound`) and `fair_settlement_of_acyclic`. A rank certificate
    can supply the acyclicity: `rank_closed`, decided on Boolean vectors by `rank_ok_b`
    (`rank_ok_sound`).
  - **Fair settlement under (A) and (B):** `one_token_fair_settlement` gives it from every start
    with at most one unstable vertex. `fair_settles_once_one_token` gives it for every fair run
    that ever reaches such a state.
  - **Boundary instances:**
    - `shih_ho_instance` is Shih and Ho's 4-vertex example. It satisfies (A) and (B), its global
      graph has a cycle, its asynchronous state graph is acyclic, and every fair schedule from
      every start settles.
    - `outdeg_needed` (Shih and Dong's network): (A) without (B), with a synchronous 3-cycle and a
      fair schedule that never settles.
    - `no_neg_not_enough`: the positive 3-ring.
    - `no_pos_not_enough`: the negative 3-ring, with a closed asynchronous run and no fixed point.
  - **Open:** under (A) and (B), closed asynchronous runs with two or more unstable vertices at
    every state (F2 for k >= 2). Not found in the literature searched; Shih and Ho 1999, now read
    in full, treat synchronous iteration only.
  - **Docs:**
    - `REGIME-AUDIT.md`: section 12 rootless row, gap 3 row, the cyclic frontier, header, history.
    - `docs/ROADMAP.md`: Done row and gap 3's "Next".
    - `docs/LOSSY-NETWORKS.md`: P2 and the literature list.
    - `docs/LANDSCAPE.md`, `docs/THEORY.md`, `docs/REGIMES.md`, `README.md` (open-gap sentence).
    - `coq/README.md` row and `coq/docs/non-invertible.md`, new section.
    - `research/gap3-fair-settlement/README.md`.
    - Current-count lines.
  - **Gate:** raised from 2160 to 2189.
- `coq/RootlessNetworks.v` (#91): rootless propagation on any finite invertible network, exactly;
  closes audit gap 2. Axiom-free. Same semantics as `RootlessCycles.v` (every edge a writer, the
  regular action), on an arbitrary edge list: several cycles, mixed orientation, sources feeding
  cycles. Graph notions: `reach`, `linked` (weak connectivity), `co_rooted` (every two linked
  registries have a common upstream registry; `co_rooted_iff_roots`: each weakly connected
  component has a registry upstream of all of it), `de_facto_root` (no in-edge from another
  registry), `root_cover`, `authority_cover` (`authority_cover_iff`: `co_rooted` and `root_cover`).
  The reachable set: `net_origin` (offsets relative to a section copy downstream),
  `net_reachable_iff`, `net_reachable_fair_iff` (a section is reached from `t0` iff it agrees with
  `t0` somewhere upstream of every registry), `net_nf_from_iff`. Existence from every start:
  `net_nf_exists_iff` (iff a section exists and `co_rooted`, or `|G| = 1`),
  `net_nf_exists_iff_nontrivial`. Uniqueness: `net_unique_iff`, `net_unique_fair_iff` (iff, given a
  section, `root_cover` or `|G| = 1`), `unique_fair_iff`, `net_unique_sufficient`,
  `net_unique_iff_nontrivial`. Both: `net_unique_normal_form_iff` (iff a section exists and
  `authority_cover`, or `|G| = 1`), `net_unique_normal_form_iff_nontrivial`. Strongly connected:
  `net_strong_iff`. Recovered from the network theorems: `cycle_nf_exists_recovered`,
  `cycle_unique_recovered`, `cycle_unique_general_recovered`,
  `cycle_unique_normal_form_recovered` (the statements of `rootless_nf_exists_iff`,
  `rootless_unique_iff`, `rootless_unique_iff_general`, `rootless_unique_normal_form_iff`),
  `selfloop_recovered`, `orientation_matters_recovered`, `copyback_recovered_net`. Boundary cases
  over Z/2: `rootless_figure_eight` (two cycles sharing a registry: existence, not unique),
  `rootless_mixed_square` (mixed orientation: unique, yet some start reaches nothing),
  `rootless_source_feeds_cycle` (a cycle with `|G| = 2` and a unique normal form),
  `rootless_cycle_feeds_cycle`, `rootless_global_holonomy` (an authority root and no directed
  cycle, yet no consistent state: the obstruction is global `H^1`). Docs:
  `coq/docs/non-monotone-invertible.md` (new section), a `coq/README.md` row, `REGIME-AUDIT.md`
  (gap 2 row, section 11, the cyclic frontier, header, open-gap summary), `docs/ROADMAP.md`,
  `README.md` (open-gap list), `docs/REGIMES.md`, `docs/THEORY.md`. Gate raised from 2067 to 2160.
- `coq/DistributedConvergenceExact.v` (#90): convergence among quiescent interleavings alone in
  the no-reset distributed model on monotone cycles (`FlushR /\ DConvQ`), exactly; closes audit gap
  14. Axiom-free. The canonical state is the quiescent state propagation settles in (a ghost is
  allowed) instead of the FedMachine's least fixed point, read as a relation: `Flushes`,
  `FlushDetR` (E: every reachable state flushes to at most one quiescent state), `FlushXUR` (S: an
  event at a stale state and at its flush flush to a common state), the quiescent machine `QM` and
  `QMConv` (H: trace-equivalent events have the same quiescent-machine outcomes).
  `conv_quiet_exact`: `FlushR /\ DConvQ <-> FlushR /\ FlushDetR /\ FlushXUR /\ QMConv` (no lattice
  hypothesis; the forward direction for every `r`: `conv_flushdet`, `conv_flushxu`, `conv_qmconv`);
  `fair_conv_exact` (with `FairFlushR`); `flushdet_event_iff`. Each conjunct necessary:
  `flip_conv_noflush`, `fork_conv_nodet`, `copy_conv_noxu`, `fm_conv_noqm`. Ghost-free case:
  `noghost_flushdet`, `noghost_flushxu_iff` (`FlushXUR` is `XUcR`), `noghost_qmconv_iff` (`QMConv`
  is `FMConv`; `noghost_qm`: the quiescent machine is the FedMachine), `quiet_conv_recovered`
  (`quiet_conv_iff` at `r = false`), `agree_conv_noghost` (agreement is convergence plus
  `NoGhostR`), `flush_fed_recovered` (`flush_fed_iff` at `r = false`). Sound states:
  `sand_flushdet`, `sandr_flushdet`, `soundr_flushdet`, `soundr_conv_iff`. Instances:
  `conv_ghost_instance` (`conv_ghost_normal` satisfies all four conjuncts and converges on the
  quiescent machine's ghost), `ghost_conv_not_fed` (from a ghost start, `FairFlushR` and `DConvQ`
  hold while `XUcR`, `FMConv`, `NoGhostR` and `DAgreeQ` all fail), `raise_only_conv`. Docs:
  `coq/docs/distributed.md` (new section), a `coq/README.md` row, `REGIME-AUDIT.md` (gap 14 row,
  section 8, the cyclic frontier, header), `docs/ROADMAP.md`, `README.md` (open-gap list), and
  `docs/THEORY.md` (canonical execution: a canonicalizer chosen by the dynamics). Gate raised from
  2012 to 2067.
- `coq/LocalSigned.v` (#83): local (state-dependent) interaction graphs of Boolean resolver
  networks, every `n`, axiom-free. Local fidelity: `rrt_sub`, `local_fidelity` (Remy, Ruet and
  Thieffry 2008: no local positive cycle gives at most one fixed point), `local_fidelity_canon`
  (CanonicalFidelity from every start, no global sign hypothesis), `local_signed_fidelity` (the
  uniqueness hypothesis of `signed_fidelity` derived), `local_in_global`, `global_to_local`
  (instance `global_to_local_instance`), and `local_weaker_than_global` (no local cycle, a positive
  2-cycle in every global certificate, E holds). Local settlement, in the reachability form (from
  every state some update word reaches a fixed point, so E's Settlement holds from every start):
  `richard_t3` (Richard 2011, Theorem 3, following Richard's proof; `outdeg_nonexpansive`),
  `t4_full`, `richard_t4` (Theorem 4), `sd_path`, `shih_dong_E` (Shih and Dong 2005: a unique fixed
  point and all of E). Breaks: `local_neg_free_no_fixed_point` (Tonello's 6-vertex network, no
  local negative cycle, no fixed point), `ring_local_conditions` (Theorems 3 and 4 hold, two fixed
  points, a fair schedule that never settles), `shih_dong_not_fair` (no local cycle, E holds, a fair
  period-8 schedule never settles). Documented in `coq/docs/non-invertible.md`, a `coq/README.md`
  row and `docs/LOSSY-NETWORKS.md` P2 (progress on gap 3, which stays open). Gate raised from 1968
  to 2012.
- Statement review of `SignedCycles.v` and `SignedResolver.v` (#81), same method as #78: every
  exported theorem checked with `Check`/`About` (section variables and hypotheses as premises)
  against its name, comments, the #80 description, `coq/docs/non-invertible.md` and the P2
  progress bullet of `docs/LOSSY-NETWORKS.md`. No error; `invertible_merge_is_holonomy` and
  `harary_balance` carry no spanning-tree, connectivity or simple-graph premise. Added
  correctly-stated theorems where the prose claimed more than a statement:
  `resp_reads_in_neighbors` (`Resp` makes each resolver read only its in-neighbors),
  `signed_fidelity_harary` (attempt 2 with the switching derived from balance),
  `ring_low_start_E` (from `(1, 0, 0)` on the 3-ring E's Settlement half holds and E fails through
  CanonicalFidelity, so the start condition is needed for fair settlement and fidelity, not for
  E's Settlement), `flip_needs_top_resolver` (the flip inside the resolver model: every hypothesis
  of `signed_fidelity` but the greatest element, and no flush word) and
  `unique_pos_cycle_every_certificate` (every certificate of `unique_pos_cycle` has the positive
  cycle). Qualifiers: Harary is stated for closed walks (the simple-cycle form is not mechanized);
  `tree` in `obstruction_loop_vs_merge` is `CohomologyGraph.tree`; `signed_settlement_harary` has a
  subset of `signed_settlement`'s conclusions; both bridge theorems assume the greatest element;
  sound starts are sound in the switched order; `SgOn` is a premise. Docs wave: `REGIME-AUDIT.md`
  (section 12: a loops-versus-merges row and the signed certificates on the rootless row; gap 3
  progress with the local interaction graph version as the open part; cyclic frontier),
  `docs/ROADMAP.md` (gap 3 progress and next steps: local interaction graphs, Remy, Ruet and
  Thieffry 2008 for fidelity, Richard 2011 for settlement, or a Ruet 2017 style counterexample),
  `docs/THEORY.md` ("Mathematical structure": Harary proved, loop versus merge as a theorem pair,
  signed certificates for E), `docs/LOSSY-NETWORKS.md` and `coq/docs/non-invertible.md`
  (consistency with the new theorems). Gate raised from 1963 to 1968.
- `coq/SignedCycles.v` and `coq/SignedResolver.v` (#80). Loops versus merges:
  `section_transport`, `holonomy_free_section` (every closed walk trivial gives a section, on any
  finite edge list, no spanning tree), `invertible_merge_is_holonomy` (two directed paths with
  different labels give a non-trivial closed walk and no section; section iff holonomy-free iff
  path-independent iff coboundary), `fundamental_cycles_holonomy`, `obstruction_loop_vs_merge`
  (invertible trees have sections; the lossy C22 tree has none, minimum coordination 1). Harary's
  balance theorem for finite signed graphs, proved as the Z/2 instance (`harary_balance`), with
  `balanced_dicycles_positive` and `balanced_no_positive_acyclic`. The signed-cycle to E bridge
  (reading B, sufficient certificates, not an identity): `switched_monotone`, `signed_settlement`
  and `signed_settlement_harary` (low starts), `signed_fidelity` (at most one fixed point, every
  start); breaks `neg2_no_fixed_point`, `copyback_ghost`, `toggle_ghost`, `ring_needs_low_start`,
  `unbalanced_unique_oscillates`, `flip_needs_top`, `xor_no_certificate`, `cyc3_unsignable`;
  non-vacuity `neg_chain_settles`, `unique_pos_cycle`. Documented in `coq/docs/non-invertible.md`
  and `docs/LOSSY-NETWORKS.md` P2 (progress on gap 3, which stays open). Gate raised from 1926 to
  1963.
- Experimental (do not cite yet): statement review of the canonical-execution modules (#78).
  Every rederivation (`*_kernel`, `*_P`) has the same exported statement as the theorem it
  rederives (`flush_fed_iff_kernel` with fewer premises), and the six-criteria outcome stands.
  Added correctly-stated theorems where the prose claimed more than a statement:
  `stream_free_hd_iff_pcc` (the kernel part of `stream_free_history`, which rereads
  `stream_exact_free`), `xur_state_descent` (XUR as pointwise state descent),
  `cyclic_lc_sound_fails` (`cyclic_lc_fails` does not mention `LC`), `factor_needs_exposed` (the
  third premise of `factor_exact` is needed), `cyc_grun_nf` and `cyc_factor_sound_gc` (`GC` from
  every normal form), `c_local_iff_r1` (the equivalence behind `common_r1`) and
  `fed_state_and_interaction` (the two P halves as a conjunction). Qualifiers added to comments
  and `coq/docs/canonical-execution.md`: the effective kernel's `ok_inj` (every event admissible
  after every admissible word), `state_descent_iff_cc2` is the all-events CC2, peak kinds are
  labels, Settlement sits on both sides of `esh_exact`, C1R1 is pointwise state descent with a
  point-dependent canonicalizer. Gate raised from 1918 to 1926.
- Experimental (do not cite yet): `coq/CanonicalLocality.v`, the P layer of the
  canonical-execution meta-theory, interaction locality as factorization through a composition
  boundary (#77). Generic: `factor_exact` (`LC -> Realizable -> (GlobalRes <-> LocalRes /\
  InterfaceRes)`), `factor_pointwise`, with each premise shown necessary (`factor_needs_sound`,
  `factor_needs_realizable`; `factor_needs_exposed` added in #78). Acyclic federation as an
  instance: interface ambiguities are the C1 shape (kernel `StateDescentAt`), local ambiguities
  the C2 shape (kernel `grun`), `LC` is `pair_commute` and realizability `pair_commute_nec`;
  `gc_iff_reach_P`, `fed_exact_P` (criterion D now passes: kernel history layer, then the P
  layer, without `gc_iff_reach`), `fed_exact_full_P`, `reach_commute_iff_P`, `fed_gc_sites`,
  `fed_factor_supply` (non-vacuity). `cyclic_lc_fails`: on a two-registry cycle every field of
  `Common` but the topological order holds, C1R1 and C2R hold, and `GCF` fails (the failure of
  `LCSound` is `cyclic_lc_sound_fails`, #78). `cyc_factor_sound`: on monotone cycles, the
  soundness half only, with a static decomposition. `common_r1`: `Common`'s `c_local` gives
  `SheafGluing.R1`, the one hypothesis shared with state gluing (an observation, not a combined
  theorem). Documented in `coq/docs/canonical-execution.md`. Gate raised from 1891 to 1918.
- Experimental (do not cite yet): `coq/CanonicalExecution.v` and `coq/CanonicalInstances.v`, a
  candidate meta-theory in which convergence decomposes into effective canonicalization (E:
  settlement and canonical fidelity), state descent (S) and history descent (H) (#74). Kernel:
  `state_descent_iff_respects_canon`, `state_descent_iff_cc2`, `normalization_descent`,
  `peak_exact` and `classified_peak_exact` (localized Newman, credited), `history_descent_exact`
  over admissible executions, `esh_exact`. Validation against six existing exact results:
  `jc_exact`/`jcg_exact`, `causal_exact`, the at-least-once results (free and causal), streams,
  and the ghost family reduce to short corollaries (`stream_exact_free` is reread rather than
  rederived); `fed_exact` is partial, pending a
  compositional (P-layer) locality theorem. Documented in `coq/docs/canonical-execution.md`,
  marked experimental. Gate raised from 1783 to 1891.
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
- `coq/CRDTBoundary.v`: the CRDT boundary as one theorem, with the strictness witness sharpened (#67).
  - `crdt_boundary`: for a compensation-free system (normalization the identity), (a) causal convergence from every start iff concurrent raw operations commute (`cf_causal_boundary`, through `causal_convergence_exact` and `compensation_free_exact`); (b) convergence under every order and duplication iff the raw actions are commutative and idempotent at reachable states (`cf_merge_boundary`, through `merge_action_exact`); (b') with a finite event range and decidable state equality, iff a join-semilattice representation on reachable states (`cf_cvrdt_boundary`, through `cvrdt_exact_all`); (c) the witness converges with compensation under both delivery models while (a) and (b) fail for its raw operations.
  - Witness: `witness_ops_not_commute` (the specific pair, at every state), `witness_not_cvrdt_order` (no partial order on `bool` makes `settrue` and `flip` both inflationary; `witness_not_inflationary_antisym` needs only antisymmetry), `witness_not_cvrdt_exact` (not commutative, not idempotent, no `MergeConv`, no `CvRDTOn`, from every start), `witness_raw_not_causal`, `witness_governed_converges`.
  - Qualifier `witness_governed_constant`: the governed composite is constant `false`, a CmRDT and a CvRDT on `bool` (join `andb`), so strictness is about the transition representation, not observable behavior. Non-vacuity: `boundary_nonvacuous`.
- `coq/CvRDTExact.v`: `cvrdt_on_iff`, the iff `MergeConv s0 <-> CvRDTOn s0` with the finite event range and decidable event and state equality as explicit premises. `cvrdt_on_exact`, as exported from section `Finite`, also takes `MergeConv s0` as a premise (the discharged section hypothesis), so outside the section it is not an iff; it is kept unchanged. Non-vacuity: `cvrdt_on_iff_nonvacuous` (both sides true for the clamped merge from 0 over `{0..5}`, both false for overwrite over `{1, 2}`).
- `coq/README.md`: sections for each new module (#21, #23, #24, #25, #26, #27, #31 to #39, #42, #44, #47 to #51, #54 to #60, #62).

- `coq/DistributedCyclesExact.v`: the distributed propagation model on monotone cycles without resets, exactly, closing regime-audit gap 1 (#64).
  - Unconditional iffs: `flush_agree_iff` (`FlushR /\ DAgreeQ <-> XUcR /\ FlushR /\ NoGhostR`), `flush_fed_iff` (`FlushR /\ DAgreeQ /\ DConvQ <-> XUcR /\ FMConv /\ FlushR /\ NoGhostR`), and the fair-schedule forms `fair_agree_iff`, `fair_fed_iff` (`FairFlushR`: every fair schedule from every reachable state reaches quiescence). Each right-hand conjunct is necessary: `copy_xu_fails` (`XUcR`), `fm_conv_fails` (`FMConv`), `flip_noflush` (`FlushR`), `flip2_fair_livelock` and `ring_exact` (`FairFlushR`), `ghost_exact` (`NoGhostR`).
  - `FlushR` exactly: `fair_flush_sound_iff` (a fair run reaches quiescence iff it reaches a sound state), `flushat_sound_iff`, `fairflushR_sound_iff`, `flushR_sound_iff`; `sand_settles` (recovers `q1_below` as `sand_recovers`, and `q1_sound_settles`); sufficient `sandr_fairflush`, `soundr_fairflush`, `lowr_fairflush`, per event `evsand_sandr`, `evsound_soundr`, `infl_evsound`, `evlow_fairflush`, per network `step_sound_fairflush`; `nc_sound_low` (gsm starts are sound and low).
  - `NoGhostR` exactly: `noghost_event_iff` (the start and every post-event state are ghost-free), `ghost_witness`, `ghostfree_sound_iff`, `noghost_soundr_iff` (under `SoundR`, `NoGhostR <-> LowR`), `lowr_post_iff`, `soundr_agree_iff`, `soundr_fed_iff`, `noghost_inv_iff` (an invariant with no quiescent ghost), `unique_or_low_noghost` (recovers `uniq_noghost` and the `EvLow` route, `unique_or_low_recovers`).
  - gsm: `lens_noreset_iff`, `lens_noreset_fair_iff` (with C1cyc and C2cyc over a covering set, a no-reset cyclic deployment is certified exactly when it flushes and has no reachable ghost).
  - Qualifiers and instances: `conv_ghost_normal` (`NoGhostR` is not necessary for `DConvQ` alone), `latched_exact`, `local_reset_ghost`, `ghostfree_unsound`, `raise_only_exact`.
- `coq/README.md`: sections for each new module (#21, #23, #24, #25, #26, #27, #31 to #39, #42, #44, #47 to #51, #54 to #60, #62, #64).
- `docs/LOSSY-NETWORKS.md`: research note on lossy (non-invertible) networks without a spanning root, with its validation script `research/lossy/validate.py` and recorded output `research/lossy/validate.out` (13 checks, all agreeing) (#52). The constraint reading (A) and the resolver reading (B) of a lossy network, with polynomial reductions between them and the classification of the existing modules by reading; the complexity map of reading A (NP-complete by a parsimonious 3-SAT reduction, polynomial with one source component, David's root sets in the number of source components, W[1]-hardness in that number, join-width tractability); reading B as a finite discrete dynamical system (Thomas's rules, Robert, Richard, Aracena), with the copy-back and negation counterexamples as the extremal positive and negative 2-cycles; monotonizability as a common generalization; ranked open problems. Claims mechanized since the note was written are tagged with their theorems: the root-set criterion and counting (`root_set_criterion_graph`, `root_set_count`, #54; P1 done), the 3-SAT reduction (`net_section_iff_sat`, `net_bijection`, `net_count`, `net_size`, `np_certificate`, #57), event order under a root set (`forest_events_exact`, #59; P6 done) and rootless single invertible cycles (`rootless_unique_iff`, #48); P2 and P4 stay open as regime-audit gaps 3 and 11. Linked from the `README.md` researchers paragraph, `docs/README.md`, `docs/THEORY.md` (Mathematical structure), `REGIME-AUDIT.md` section 12, `docs/ROADMAP.md` and `coq/docs/non-invertible.md`.
- `coq/LossyMinimum.v`: minimum coordination for lossy networks, closing regime-audit gap 11 (#70). Edges are deleted by position (`cset`, `resid`); `lfeasible G F` says the residual has a section and `is_lmin G k` that `k` is the minimum (`lmin_unique`).
  - Exact characterization through `RootSet.v`: `lfeasible_root_set` (for any root set and spanning forest of the residual), `lfeasible_iff_root_set`, `lmin_root_set`; upper bounds `forest_residual_feasible`, `lossy_lmin_le_nontree`.
  - Decision procedure on finite fibers: `sec_b_spec`, `lfeasible_decide_forest`, `lmin_le_b_spec`, `lmin_b_correct`, `lmin_decide`, `lmin_exists`.
  - Hardness through the 3-SAT network of `LossyHardness.v`: `lmin_zero_iff_section`, `lmin_zero_iff_sat`, `min_le_zero_iff_sat`, `net_lmin_dichotomy`, `lmin_reduction` (`|net f| = 6|f| + 1`; minimum 0 iff satisfiable, 1 iff not), so telling minimum 0 from 1 is NP-hard by the standard argument. Membership in NP: `min_le_np_certificate`, `min_cert_size`, `lmin_le_np`.
  - Invertible case: `lossy_min_is_gfes` (on group-labeled networks under the regular action the lossy minimum is the group feedback edge set minimum), `lift_cycle_basis`, `group_tree_lmin_zero`, `group_lmin_le_nontree`.
  - Not cycle-based: `c22_lmin`, `lossy_min_exceeds_cycle_bounds` (every cycle-only lower bound is 0 on the C22 tree, whose minimum is 1), `cycle_bounds_nonvacuous`, `c22_group_lmin`. Instances `c22_lmin_b`, `c22_certificate`, `diamond_lmin`, `two_lmin`, `scc_lmin`, `tri_lmin`, `bow_lmin`, `fsat_lmin`, `funsat_lmin`.
- `coq/CohomologyNerve.v`: `H^1` on the nerve as a 2-complex, closing regime-audit gap 12 (#71). 2-cells are closed walks (triangles the length-3 case); `cocycle L C` says every cell has trivial holonomy.
  - `nerve_H1_classification` (any group): tree-fixed cocycles are exactly the generator assignments satisfying every cell's relation word, every cocycle is cohomologous to one, two are cohomologous iff simultaneously conjugate, and conjugation preserves the relations; so `H^1(K; G)` is `Hom(<X | relation words>, G)` modulo conjugation. `nerve_H1_abelian` for commutative `G`. `hol_gauge`, `cocycle_gauge`, `hol_tree_fixed`, `relations_in_generators`.
  - `nerve_section_iff_coboundary`: a section exists iff the labeling is a coboundary, independent of the cells.
  - `nerve_H1_Z2_count`: over Z/2, exactly `2^((|E| - |V| + 1) - rank)` classes, `rank` the number of independent cell relations; `ker_count`, `ker_count_pow`, `rel_rank_le`, `rel_rank_solution_set`, `rel_rank_zero_iff`; `nerve_Z2_no_cells` (recovers `betti_number`), `nerve_Z2_full_iff`, `nerve_Z2_cell_lowers`. The dimension formula is mechanized over Z/2 only; the identification of the presented group with the fundamental group of the complex is standard and not mechanized.
  - Instances: hollow and filled triangle (`triangle_kills_flip`, `filled_cocycle_has_section`), the square with a diagonal with 0, 1 and 2 filled triangles (`square_hollow`, `square_one_triangle`, `square_two_triangles`) and a dependent third cell (`square_dependent_cell`).
- `coq/CoordinationMinimum.v`: minimum coordination tied to the authority-root plan model, closing regime-audit gap 10 (#72). Any group with decidable equality, the regular action; `plan Es r T X` is a rooted spanning tree of the network, `plan_cost` the number of unbalanced non-tree edges, `feasibleM` deletion of a sub-multiset leaving a section.
  - `plan_coord_feasible`, `plan_coord_exact`, `plan_cost_any_section`, `plan_cost_le_betti`, `section_decide`.
  - `feasible_plan`: every feasible set yields a plan from the same root that costs no more (the residual need not be connected). `plan_min_exact`: on a connected network, some plan rooted at `r` costs at most `k` iff some feasible coordination deletes at most `k` edges, so the best plan's cost is the group feedback edge set number. `plan_min_lower_iff`, `plan_min_attained`, `plan_min_root_independent`, `plan_min_exact_set` (membership deletion, duplicate-free networks), `plan_cost_ge_disjoint`.
  - Hypotheses needed: `plan_min_connected_needed`, `plan_min_nodup_needed`.
  - Complexity: `maxcut_reduction`, `maxcut_plan_reduction`, `signed_size` (Max-Cut reduces to minimum coordination over Z/2, in the plan model too; reduction correctness and size mechanized, NP-completeness of Max-Cut cited); instance `maxcut_triangle`.
  - Instances: `negation_plan_min`, `bowtie_plan_min`, `pendant_tree_uses_F`, `s3_tree_choice` (over `S_3` the tree choice matters: 3 against the minimum 2, while the abelian image needs 1).
- `coq/SheafGluing.v`: sheaf gluing over sub-federation covers, narrowing regime-audit gap 13 (#73). Site: sub-federations and covers; `F(U)` the states consistent on `U`.
  - `separation` (no hypothesis), `sec_restrict`, `sec_local` (under R1, `F(U)` depends only on `U`'s values), `gluing`, `sheaf_condition`, `sheaf_exact`, `gluing_iff_local_global`, and `sheaf_iff_refines`: gluing holds on a cover for every R1 federation on the graph iff every constraint inside the union lies inside one member.
  - Broken hypotheses: `triangle_fails` (refinement), `r1_failure` (R1), `gluing_cex_overlap` (certificate compatibility, wrapping `gluing_order_dependent`).
  - Certificates: `cert_restrict_closed`, `cert_restrict`, `cert_pointwise`, `cert_restrict_iff` (plain restriction holds for all data iff `U` is closed under sources), `sec_iff_LF`, `cert_retraction`, `cert_glue`, `cert_sheaf`; `cert_needs_sc` (with M1 in place of SC the certificate misses its sections); `collapse_restrict`.
  - Instances: `chain_glues`, `sheaf_iff_refines_instance`, `vs_cert_sheaf`, `chain_cert_nonclosed`, `cert_restrict_iff_instance`, `collapse_restrict_instance`. Not covered: the variable-level site, the monotone-overlap regime, a sheaf condition for relative certificates on covers not closed under sources, the event layer.
- `coq/README.md` and `coq/docs/`: index rows and sections for `LossyMinimum.v` (`coq/docs/non-invertible.md`), `CohomologyNerve.v` and `CoordinationMinimum.v` (`coq/docs/non-monotone-invertible.md`), and `SheafGluing.v` (`coq/docs/federation-repair.md`) (#70 to #73).

### Changed
- `README.md`: the status paragraph under the headline (one 45-line paragraph) is now a short list: exact, hardness, counting and gluing, the eight open convergence gaps by number, and the design exclusions. Details stay in `REGIME-AUDIT.md`. No theorem added, removed or renamed.

- `docs/COVERAGE.md` section 4: four candidate dimensions outside the axes, added after the pass with dispositions pending: observation before convergence (what intermediate reads return), irreversible external effects, compaction (deduplication and history that forget), and nondeterministic events (the event-side twin of X2). No gap numbered, no cell count changed, no theorem added, removed or renamed.

- `docs/ROADMAP.md`: planned paper, the regime map (a fourth paper whose main object is the classification: the question, the axes, the map table, representative theorems, transfer between regimes, the open part, quotients for checking, and the audit method; drafting after gap 19 lands). No theorem added, removed or renamed.
- `coq/verify.sh`: gates `NC.Checker.run_perm_invariant` (axiom-free), which gsm's `docs/theory.md` cites for CC1 correctness but which was not in the gate. Gate 3029 to 3030.
- `docs/ROADMAP.md` item 8: the history-side reduction expanded into a progression (pairwise swap, trace equivalence, canonical histories, per-condition exactness, symmetry combined with it), with independence derived rather than declared and each restriction tied to an existing mechanized counterexample. `docs/THEORY.md`: new subsection "Quotients for checking" (every proved semantic quotient is a potential verification quotient, qualified per condition). No theorem added, removed or renamed.
- `docs/ROADMAP.md` item 8: a history-side reduction (partial-order reduction) for the checks that explore reachable states, with soundness to be proved per condition. No theorem added, removed or renamed.
- `docs/COVERAGE.md`: the header distinguishes the commit the coverage pass ran at (2241) from the current state it is kept at (2380).
- `docs/ROADMAP.md`: two planned items. Item 8, checking scales to realistic domains (data independence and symmetry, abstraction soundness, compositional checking as the default, each a theorem about the existing conditions). Item 9, reconfiguration inside a run (gap 20): exact conditions for live changes between configurations, and a migration check in gsm. No theorem added, removed or renamed.
- Gap 3 computational evidence (not mechanized): `research/gap3-fair-settlement/` (SAT search scripts, n = 6 logs, report). Under no local cycle plus out-degree at most one, no asynchronous state-graph cycle exists for n = 3 to 6, so fair schedules settle there; the general case is open (conjectured lemma F2; Shih and Ho 1999 unread). Noted in `REGIME-AUDIT.md` (gap 3 row), `docs/ROADMAP.md` and `docs/LOSSY-NETWORKS.md` P2. No theorem added, removed or renamed.
- `docs/ROADMAP.md`: planned artifact, the Convergence Atlas (a public, illustrated catalog of the regime map with counterexample plates, generated from `REGIME-AUDIT.md`). No theorem added, removed or renamed.
- The three version-2 papers fold in the corrections queued for a version 3, before version 2 is
  published; all three are dated 5 October 2026 and their PDFs are rebuilt. CRDT strictness
  (Base and Fed, design-space section and Related Work): strict on the same transition
  representation, with the witness's governed behavior itself a CRDT (`crdt_boundary`,
  `witness_governed_constant`); "which CRDTs cannot accommodate" removed (errata item updated, it
  was in version 1). `compensation_free_exact` is described as the structural step it is, with
  behavioral exactness cited from `causal_convergence_exact` (part (a) of `crdt_boundary`) and, for
  state-based CRDTs, `cvrdt_on_iff` (Base and Fed errata, Cat Related Work and errata). Cat
  `prop:gluing` is retitled "Gluing on the registry-level site" and restated to match
  `SheafGluing.v` (`separation`, `gluing`, `sheaf_exact`, `sheaf_iff_refines`, `cert_glue`,
  `cert_sheaf`), with SC in the role version 1 gave R2 (`cert_needs_sc`) and overlaps alone shown
  insufficient (`triangle_fails`, `r1_failure`, `gluing_cex_overlap`); new Cat errata item. Stale
  "paper level" statements in Cat replaced by citations: `H^1` on the nerve as a 2-complex
  (`nerve_H1_classification`, `nerve_H1_Z2_count`), the input-port refinement
  (`port_c1_transfer`, `port_c2_transfer`, `port_interior_certificate`), the effective-registry
  reading of Theorem 2 (`collapse_nf_agree`, `collapse_a_wfc`, `collapse_c_guarded_iff`) and the
  Max-Cut reduction (`maxcut_reduction`); only the NP-completeness of Max-Cut and the other cited
  complexity results stay cited. Each paper's mechanization remark gives the gate as 2012 and
  points to `REGIME-AUDIT.md` for results mechanized after it was written. Still at paper level:
  cyclic monotone collapse (gap 5), the Base 8.2 lattice-compensation pattern, the asymptotic cost
  model, and Cat's variable-level and monotone-overlap sheaf site. `docs/ROADMAP.md` item 7 and
  `REGIME-AUDIT.md` updated to say the paper wording now matches.
- Axiom-free gate raised from 112 to 125 theorems, checked on Coq 8.18, Coq 8.20 and Rocq 9.3 (#19).
- Axiom-free gate raised from 125 to 135 theorems (#21).
- Axiom-free gate raised from 135 to 254 theorems: 166 (#23), 189 (#24), 205 (#25), 232 (#26), 254 (#27).
- Axiom-free gate raised from 254 to 915 theorems: 264 (#31), 314 (#32), 375 (#33), 413 (#34), 486 (#35), 548 (#36), 575 (#37), 609 (#38), 669 (#39), 715 (#42), 729 (#44), 752 (#47), 777 (#48), 827 (#49), 851 (#51), 915 (#50).
- Axiom-free gate raised from 915 to 989 theorems: 958 (#54), 989 (#55).
- Axiom-free gate raised from 989 to 1198 theorems: 1040 (#56), 1123 (#59), 1151 (#57), 1198 (#58).
- Docs pass at the 1198-theorem gate: `REGIME-AUDIT.md` closes gaps 4, 6 and 7 and marks the lossy-network 3-SAT reduction mechanized; the `README.md` precision paragraph says the reduction is machine-checked and NP-completeness follows by the standard argument; `ROADMAP.md`, `REGIMES.md` and `coq/README.md` updated to match (#61).
- Axiom-free gate raised from 1198 to 1370 theorems: 1253 (#60), 1370 (#62).
- Docs pass at the 1370-theorem gate: `REGIME-AUDIT.md` section 8 rewritten (the acyclic distributed model is exact; on monotone cycles it is exact under reset epochs and under `LowR`), gap 1 restated as the residual (cycles without resets and without `LowR`, exact only relative to `FlushR` and `NoGhostR`), headline line re-confirmed; `README.md` open-gap list and count, `ROADMAP.md`, `REGIMES.md` and `coq/README.md` updated to match (#63).
- Axiom-free gate raised from 1370 to 1499 theorems (#64).
- Documentation restructured by reader, with nothing removed. `README.md` keeps the headline, its precision paragraph and the papers, and adds a "Start here" map for practitioners, researchers, proof readers and auditors; its overview, "What's new here", key concepts and the three-regimes comparison moved to `docs/THEORY.md`. `REGIMES.md`, `ROADMAP.md`, `LANDSCAPE.md`, `SUBSUMPTION.md`, `CATEGORICAL-STRUCTURE.md`, `LYAPUNOV-EXTENSION.md` and `COMPANION-OUTLINE.md` moved to `docs/`, with a stub at each old path and `docs/README.md` giving each page's role; `REGIME-AUDIT.md` and `CHANGELOG.md` stay at the root. `coq/README.md` is now an index (verify, how to read a module, one row per module grouped in `REGIME-AUDIT.md`'s order, and how to add a module); its per-module sections moved verbatim to one page per regime in `coq/docs/`. `coq/PAPER-MAP.md` notes that its status columns predate later merges and points to `REGIME-AUDIT.md`.
- Axiom-free gate raised from 1499 to 1522 theorems (#67).
- `docs/SUBSUMPTION.md` rewritten around `crdt_boundary`: the lead claim states the CmRDT, commutative-idempotent and CvRDT regimes as exactly the compensation-free fragment under each delivery model, with nontrivial normalization strictly extending them on the same transition representation; the background paragraph distinguishes the convergence mechanism from application invariants (citing invariant confluence) and drops "because there is no invariant to violate"; "No CRDT can represent it" replaced by the representation-level statement with the new witness theorems and the `witness_governed_constant` qualifier; `compensation_free_exact` described as a structural equivalence after the behavioral exact theorems; `GovernanceCausal.v` described as the co-enabled-events theorem with causal delivery as an instance; CRDT literature cited (Shapiro et al. 2011, delta-state CRDTs). `REGIME-AUDIT.md` section 4 strictness row and summary row, `docs/THEORY.md`, `docs/README.md`, `coq/README.md` (row and gate count) and `coq/docs/crdt.md` updated to match (#67).
- Axiom-free gate raised from 1522 to 1524 theorems (`cvrdt_on_iff`, `cvrdt_on_iff_nonvacuous`).
- Citations of `cvrdt_on_exact` as an iff now cite `cvrdt_on_iff` (`docs/SUBSUMPTION.md`, `docs/REGIMES.md`, `REGIME-AUDIT.md`, `docs/ROADMAP.md`, `coq/docs/crdt.md`, `coq/README.md`, and the `CvRDTExact.v` header).
- Strictness wording aligned with the representation-level claim: `docs/LANDSCAPE.md`, `docs/REGIMES.md`, `coq/docs/crdt.md` and the comments in `coq/CRDT.v` and `coq/CausalReplay.v` say the witness's raw transitions are not a CRDT, since its governed behavior is itself trivially one (`witness_governed_constant`). Current-count lines (`README.md`, `docs/ROADMAP.md`, `docs/SUBSUMPTION.md`, `coq/README.md`, `coq/docs/federation-repair.md`) updated to 1524.
- `docs/THEORY.md`: new "Mathematical structure" section placing the theory in pure mathematics, with what is mechanized (each claim tied to a gated Coq name) and what is classical or paper-only: the two engines (well-founded rewriting and monotone fixed points), normalization as a retraction onto an equalizer, the sheaf framing (positive assembly paper-only, gap 13), holonomy and `H^1` with its qualifiers, the non-abelian `S_3` separation, minimal surgery (gaps 10 and 11), the lossy side (NP-completeness reduction and root-set criterion), trace monoids, the repair and event split, the four questions, the continuous analogue and a calibration paragraph. Pointers added from `docs/README.md` and the README's researchers paragraph (#69).
- Axiom-free gate raised from 1524 to 1783 theorems: 1591 (#70, 67 results), 1677 (#71, 86), 1747 (#72, 70), 1783 (#73, 36). The PR titles and bodies give each PR's count on its own base (#71: 1610; #72: 1594; #73: 1560); the figures here are the thresholds in `coq/verify.sh` at each merge commit.
- Docs pass at the 1783-theorem gate: `REGIME-AUDIT.md` closes gaps 10, 11 and 12 (minimum coordination exact on invertible networks through the plan model and on lossy networks through root sets, each with a mechanized hardness reduction, from Max-Cut and from 3-SAT; `H^1` on the 2-complex classified for any group and counted over Z/2) and narrows gap 13 (sheaf gluing exact on the registry-level site; the variable-level and monotone-overlap site stays paper only); sections 11 to 13, the open-gap tables, the regime-by-regime headline check (headline re-confirmed), the hardness paragraph and the mechanization tasks updated, and new side findings recorded. The `README.md` precision paragraph says minimum coordination's hardness is now a machine-checked reduction too, and its open-gap list drops gaps 10 to 12 and narrows 13 (headline unchanged). `docs/ROADMAP.md` (Done rows, item 7, an optimization table under Open items, lower-value items), `docs/REGIMES.md` (minimum coordination in the coordination paragraph and module table, `SheafGluing.v` in the tree and DAG row), `docs/THEORY.md` (Mathematical structure: sheaves, the 2-complex, minimal surgery, the four questions; the [paper] list in "What's new"), `docs/LOSSY-NETWORKS.md` (P4 done in reading A), `docs/CATEGORICAL-STRUCTURE.md` (status lines) and `docs/SUBSUMPTION.md` (count) updated to match. Fixed in `coq/`: stale paragraphs in `coq/README.md` section 13 and its two count lines, the categorical-layer roadmap in `coq/docs/federation-repair.md`, and a stale paper-level note in `coq/docs/non-monotone-invertible.md`.
- Canonical execution promoted, scoped (#79). After the statement review (#78), the framework of #74 and #77 is validated for single systems (E, S, H) and acyclic composition (P), with the soundness direction only on cycles (`cyc_factor_sound`, `cyc_factor_sound_gc`; `cyclic_lc_sound_fails`). The "do not cite yet" entries above stay as the record of the experiment. `docs/THEORY.md`: new section "Canonical execution" (the one-line statement, the decomposition E, S, H, P with `factor_exact` and state gluing as separate theorems sharing `c_local_iff_r1`, the scope, the six exact results as corollaries with proof-body line counts, the absent laws for streams and causal at-least-once, the missing compositional ingredient, the review's qualifiers, and what it is not yet: no new exact result for an unstudied regime), cross-linked with "Mathematical structure". `coq/docs/canonical-execution.md`, `coq/README.md` and the headers of `CanonicalExecution.v`, `CanonicalInstances.v` and `CanonicalLocality.v` (comments only) relabeled from experimental to validated with that scope. `REGIME-AUDIT.md`: new subsection "The cyclic frontier": every open convergence gap (2, 3, 5, 14) and the monotone-overlap part of gap 13 is an instance of one question, what additional structure makes P exact on cycles, checked gap by gap; gap 13's relative certificates on covers not closed under sources and its variable-level site are not cyclic and stay separate residues. `docs/ROADMAP.md`: that question as the lead open item, and the gate count updated to 1926. `docs/LOSSY-NETWORKS.md`: P2 (gap 3) noted as part of the frontier. `README.md` (researchers paragraph) and `docs/README.md` (THEORY.md row) point to the new section; headline and precision paragraph unchanged. No theorem added, removed or renamed.

- Docs sweep at the 1968-theorem gate. `README.md`: theorem count 1783 to 1968; the open-gap list
  names the signed certificates on gap 3 (with Harary's balance theorem proved), states the four
  open convergence gaps as cyclic, and adds the second gap-13 residue (relative certificates on
  covers not closed under sources). `REGIME-AUDIT.md`: header current at `dc610a9` and gate 1968,
  with a current-state paragraph (gaps 10 to 12 closed, gap 13 closed on the registry-level site
  with two paper residues, signed certificates on gap 3, the cyclic frontier); history kept; a
  sixth-revision side-findings list. `docs/LANDSCAPE.md`: new placements for canonical execution
  (localized Newman's lemma, Church-Rosser modulo an equivalence, trace theory, quotient monoid
  actions, descent; what is new is the E/S/H/P decomposition with presentation adequacy and
  locality completeness, validated by six rederivations) and for signed cycles (Harary, Zaslavsky,
  Thomas's rules and their proofs by Remy, Ruet and Thieffry, Richard and Comet, Richard, Aracena,
  Ruet's counterexample, Robert's theorem; what is new is the sufficient certificates for E, the
  global-sign collapse `balanced_no_positive_acyclic` and the loop-versus-merge separation
  `obstruction_loop_vs_merge`); the Harary passage says it is now mechanized; stale paper-level
  claims corrected (necessity counterexamples, the calculus, minimum-coordination hardness, the
  2-complex, the non-invertible case, sheaf gluing on the registry-level site). `docs/THEORY.md`:
  the [paper] lists in "What's new here" no longer name results that are gated (the base paper's
  necessity counterexamples, step bounds and calculus; the corrected authority and resolution
  theorems; the necessity of acyclicity and M1). `coq/PAPER-MAP.md` and
  `docs/COMPANION-OUTLINE.md`: status notes at the top mark their status columns as a 254-theorem
  era snapshot and point to `REGIME-AUDIT.md`; tables unchanged. `docs/SUBSUMPTION.md` and
  `coq/docs/federation-repair.md`: count 1783 to 1968.
- Docs wave for the local interaction graphs at the 2012-theorem gate (#84). No theorem added,
  removed or renamed. `REGIME-AUDIT.md`: header current at `69ef03a` and gate 2012; the
  current-state paragraph and history record #83; section 12's rootless resolver row gains the
  local certificates (`local_fidelity_canon`, `richard_t3`, `richard_t4`, `shih_dong_E`), the breaks
  (`local_neg_free_no_fixed_point`, `ring_local_conditions`, `shih_dong_not_fair`), the strict
  extension over the global route (`global_to_local`, `local_weaker_than_global`) and the
  qualifier that local conditions certify E with Settlement in its existential (flush) form, not
  fair-schedule settlement (the analogue of `FairFlushR`); gap 3 progress and what remains open
  (fair settlement from local conditions, multivalued local graphs, value sets without bounds, an
  exact condition); the cyclic frontier row and raw-material list; the mechanization-task row;
  seventh-revision side findings. `docs/ROADMAP.md`: gate 2012, a Done row for `LocalSigned.v`, and
  gap 3's status and next steps (fair-schedule settlement on local graphs, multivalued local
  fidelity after Richard and Comet 2007, value sets without bounds, an exact condition).
  `docs/THEORY.md` ("Mathematical structure"): a local-interaction-graph paragraph after the signed
  certificates, and the four-questions convergence cell. `README.md`: count 1968 to 2012 and the
  gap-3 clause of the open-gap list (headline and gap count unchanged). `docs/LANDSCAPE.md`: Robert's
  asynchronous statement, and placements for Shih and Dong 2005 (with Shih and Ho 1999), Remy, Ruet
  and Thieffry 2008, Richard 2011 Theorems 3 and 4, Tonello 2017 (DAM 2019) and Tonello, Farcot and
  Chaouiya 2018 (SIAM J. Appl. Dyn. Syst. 2019), each citation checked; a novelty check for
  `shih_dong_not_fair` (the weaker fact that local acyclicity does not make the asynchronous state
  graph acyclic is recorded in Richard 2019, attributed to a 4-component example of Shih and Dong
  2005; the fair-schedule form was not found in the literature searched, with the search scope
  stated); "What is new" updated. `docs/LOSSY-NETWORKS.md` P2: the same novelty result and journal
  references for the Tonello papers, Remy, Ruet and Thieffry 2008 checked against the primary text
  (Theorems 3.2 and 4.4), a Shih and Dong entry, and new references (Robert 1995, Shih and Ho 1999,
  Richard 2015 and 2019). Richard and Comet 2007 described as the local theorem it is (its global
  form is a corollary) in `docs/LOSSY-NETWORKS.md`, `docs/LANDSCAPE.md`,
  `coq/docs/non-invertible.md` and the header comment of `coq/SignedResolver.v` (comment only; no
  statement changed; `make` and `verify.sh` pass at 2012). `coq/docs/non-invertible.md`: the
  literature relation of `shih_dong_not_fair`. Counts 1968 to 2012 in `docs/SUBSUMPTION.md`,
  `docs/COMPANION-OUTLINE.md`, `coq/README.md`, `coq/PAPER-MAP.md` and
  `coq/docs/federation-repair.md`.
- `docs/ROADMAP.md` drift fixed. Done table: rows for the CRDT boundary (#67, #68) and the
  canonical execution framework (#74, #77 to #79), and a gsm row for the XU check
  (`FedReport.ProjectionSafe`, `RequireProjectionSafe`, gsm PR #34, unreleased). Lower-value item
  "Authority root in gsm's plan": gsm v0.13.0 names the root of each `CoordinationPoint`
  (`Authority`), so only the holonomy-minimal plan remains open. Item 2: `Report.NotIdempotent` is
  released (gsm v0.13.0), not "next release". The status paragraph's PR list matches the table.
  No theorem added, removed or renamed.
- `docs/REGIMES.md` module table: the state-based CRDT row adds `CRDTBoundary.v`; the coordinated
  non-monotone row says each `CoordinationPoint` names its `Authority` (gsm v0.13.0); the
  non-invertible row adds the rootless signed certificates (`SignedCycles.v`, `SignedResolver.v`,
  `LocalSigned.v`; gap 3 stays open). `docs/COMPANION-OUTLINE.md`: a "the gate is now at 254" line
  in the snapshot section points to the current gate. No theorem added, removed or renamed.
- Docs pass at the 1499-theorem gate: `REGIME-AUDIT.md` closes gap 1 (the distributed model is exact on acyclic federations and on monotone cycles with reset epochs and without resets; section 8's no-reset row now cites `flush_fed_iff`, `fair_fed_iff` and the characterizations of `FlushR` and `NoGhostR`), adds gap 14 (convergence among quiescent interleavings alone on no-reset cycles, where `NoGhostR` is not necessary, `conv_ghost_normal`), and re-confirms the headline line; the `README.md` open-gap list and `docs/ROADMAP.md` updated to match, and two stale sentences in `coq/docs/distributed.md` corrected. `docs/REGIMES.md` revised as a field guide: related regimes in place of the strongest-to-weakest diagram, the convergence definition stated per admissible delivery order, a main map ordered by execution semantics then topology (guarded and unrestricted acyclic execution, cyclic repair, cyclic events, collapse) with exact, sufficient and refuted conditions, the monotone narrative split into three questions, the boundaries section and the CRDT paragraph rewritten, and a pointer to the papers' errata (#66).
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
- Robert's theorem was described as mechanized in the federation model. What is gated is the
  unique fixed point and runs in topological order or followed by a final flush (`frun_solves`,
  `solve_unique`, `order_independent`, `propagation_flush`); settlement under every fair
  asynchronous schedule on an acyclic network is cited, now gap 16 (d). Corrected in
  `docs/LOSSY-NETWORKS.md` (section 2, the section 4.1 and 4.2 tables, P2's mechanization needs),
  `docs/LANDSCAPE.md` (the Robert entry) and `REGIME-AUDIT.md` (the frontier row for gap 3, which
  said the federation model "already has" the acyclic case).
- gsm's `Report.NotIdempotent` placement (sound at reachable witnesses, complete when exactly-once
  delivery converges) is stated for free and causal delivery; `REGIME-AUDIT.md` (section 3 row and
  the conclusion), `docs/REGIMES.md` and `coq/docs/at-least-once.md` now say that with declared
  `Independent` pairs neither placement is stated (gap 15 (a)).
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
