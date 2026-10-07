/* Tile and detail-card data for the Convergence Atlas poster (docs/atlas/poster.html).
 *
 * Source of truth: REGIME-AUDIT.md (and docs/COVERAGE.md for the gaps). Every field paraphrases an
 * audit row and states no more than the row does. docs/atlas/check.py verifies that every theorem
 * name below is declared in coq/*.v, is in coq/verify.sh's Print Assumptions list, and is declared
 * in one of the tile's listed modules, and that every link anchor is a heading of the target file.
 *
 * Plain script (no fetch), so the poster works opened from disk. The object literal is strict JSON
 * (check.py parses it with json.loads), so keep keys and strings double-quoted.
 *
 * Tile fields:
 *   kind      exact | hard | open | excl
 *   mark      corner label: iff, NP, a gap number, or X
 *   name      tile title
 *   thm       theorem name shown on the tile (checked); thmNote is extra tile text after it
 *   note      tile text for tiles with no single theorem (open, excluded)
 *   fresh     closed in #117 (gold ring)
 *   setting   the regime in one plain sentence
 *   condition the exact condition, the hardness result, the open part, or why it is outside the map
 *   needed    [theorem, what it shows] pairs: counterexamples the audit names for each conjunct
 *   gsm       what gsm checks, where the audit's gsm column says
 *   theorems  main theorem names; modules: the .v files declaring them
 *   section   REGIME-AUDIT.md heading anchor; gap: the gap number for open tiles (row in "The open gaps")
 */
window.ATLAS = {
"repo": "https://github.com/blackwell-systems/normalization-confluence/blob/main/",
"families": [
{ "code": "01", "name": "Single registry", "tiles": [
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Free delivery, every order",
    "thm": "cc_exact",
    "setting": "One registry; events arrive in any order and an invalid state is repaired after each one.",
    "condition": "Every buffer has a unique normal form from s0 iff CC1 and CC2 hold at the states reachable from s0, with canonical repair.",
    "needed": [
      ["rho_star_qualifier", "canonical repair is needed"]],
    "gsm": "Registry.Build checks CC exhaustively; re-certified by the table and rules oracles.",
    "theorems": ["cc_exact", "cc_exact_from", "canonical_cc_exact_from"],
    "modules": ["GovernanceConverse.v", "GovernanceWFConverse.v"],
    "section": "1-single-registry"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Enabledness repair can disable",
    "thm": "jcg_exact",
    "setting": "A single registry whose events are guarded, where a compensation step can disable an enabled event.",
    "condition": "With termination from c0, confluence iff JC' at reachable configurations: every critical pair, compensation against event included, is joinable.",
    "needed": [
      ["dc_jc_insufficient", "JC alone is not sufficient: two normal forms, one stuck"],
      ["nv_jc_not_necessary", "JC is not necessary when compensation disables an event"]],
    "gsm": "CC1 is checked on declared Independent pairs only.",
    "theorems": ["jcg_exact", "jcg_iff_critical", "jcsplit_exact"],
    "modules": ["EnabledAfterComp.v"],
    "section": "1-single-registry"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Any well-founded potential",
    "thm": "wf_jc_exact",
    "setting": "Infinite state, with termination measured by an ordinal, lexicographic or other well-founded potential.",
    "condition": "Given any well-founded potential that repair decreases, confluence iff JC holds, with no finite-state assumption; the nat statements are recovered.",
    "theorems": ["wf_jc_exact", "lex_jc_exact", "comp_wf_jc_exact"],
    "modules": ["GovernanceWFConverse.v"],
    "section": "1-single-registry"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Termination of repair",
    "thm": "terminating_iff_comp_wf",
    "setting": "Whether repair and events terminate from every configuration.",
    "condition": "The system terminates from every configuration iff compensation is well-founded, iff some potential into a well-founded order exists.",
    "gsm": "WFC cycle detection in Build.",
    "theorems": ["terminating_iff_comp_wf", "comp_wf_iff_wfc"],
    "modules": ["GovernanceWFConverse.v"],
    "section": "1-single-registry"
  }
] },
{ "code": "02", "name": "Delivery", "tiles": [
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Causal delivery",
    "thm": "causal_exact",
    "setting": "Events delivered in any order consistent with causality (the replay model).",
    "condition": "All causally consistent orders reach one state from s0 iff concurrent pairs commute after every causally consistent prefix (CCR).",
    "needed": [
      ["naive_causal_converse_fails", "reachability of the state alone is not enough"]],
    "gsm": "Declared Independent pairs are read as the concurrent ones.",
    "theorems": ["causal_exact", "causal_convergence_exact"],
    "modules": ["GovernanceConverse.v"],
    "section": "2-causal-delivery-replay-model"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "At-least-once",
    "thm": "alo_exact",
    "setting": "Free delivery where events may be delivered more than once.",
    "condition": "Every delivery with duplicates reaches the exactly-once result iff exactly-once runs commute at reachable states and each event is idempotent where it is initially delivered.",
    "gsm": "Report.NotIdempotent.",
    "theorems": ["alo_exact", "alo_exact_absorb", "alo_idem_reachable"],
    "modules": ["AtLeastOnceExact.v"],
    "section": "3-at-least-once-delivery"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Which events need dedup",
    "thm": "needs_dedup_exact",
    "setting": "Per event, under at-least-once delivery: does this event need deduplication.",
    "condition": "An event needs none iff its duplicate is absorbed after every exactly-once run containing it.",
    "needed": [
      ["flag_idem_needs_dedup", "idempotence alone is not enough without commutation"],
      ["fw_alo_fails", "idempotence alone is not enough without commutation"]],
    "gsm": "Report.NotIdempotent is sound at reachable witnesses and complete when exactly-once delivery converges; it can over-report (jmp_unreachable).",
    "theorems": ["needs_dedup_exact", "safe_free_exact", "notidem_needs_dedup", "gsm_unlisted_safe"],
    "modules": ["AtLeastOnceExact.v"],
    "section": "3-at-least-once-delivery"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Causal, with redelivery",
    "thm": "causal_alo_exact",
    "setting": "Causal delivery where a delivered event may be redelivered.",
    "condition": "Convergence iff CCR on the event set plus absorption of duplicates (equivalently plus idempotence).",
    "needed": [
      ["late_duplicate_diverges", "the redelivery qualifier is needed"],
      ["causal_absorb_qualifier", "absorption at every causal run is not necessary"]],
    "gsm": "Report.NotIdempotent, placed as in the free case.",
    "theorems": ["causal_alo_exact", "causal_alo_exact_idem"],
    "modules": ["AtLeastOnceExact.v"],
    "section": "3-at-least-once-delivery"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Declared independence",
    "thm": "dalo_exact",
    "setting": "At-least-once delivery for a registry that declares Independent pairs; retries respect the declared order.",
    "condition": "Convergence iff declared pairs commute after every reachable exactly-once prefix (CommI) and each event is idempotent where it is initially delivered.",
    "needed": [
      ["inc_declared_fails", "the idempotence clause is needed"],
      ["fl_retry_order_needed", "retries must respect the declared order"],
      ["fl_partner_overtakes", "NotIdempotent is complete only under CommI"]],
    "gsm": "Report.NotIdempotent with Independent pairs: sound at reachable witnesses, complete when CommI holds and reachable states are valid.",
    "theorems": ["dalo_exact", "dalo_exact_absorb", "dalo_gsm_unlisted_safe"],
    "modules": ["AtLeastOnceDeclared.v"],
    "section": "3-at-least-once-delivery"
  }
] },
{ "code": "03", "name": "CRDTs and streams", "tiles": [
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Op-based CRDTs",
    "thm": "compensation_free_exact",
    "setting": "A compensation-free registry under causal delivery.",
    "condition": "The causal condition holds iff the system is an op-based CRDT; composed with causal_convergence_exact it is the exact condition.",
    "gsm": "The rules oracle certifies the compensation-free classification.",
    "theorems": ["compensation_free_exact", "causal_convergence_exact"],
    "modules": ["CausalReplay.v", "GovernanceConverse.v"],
    "section": "4-crdt-fragment"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "State-based CRDTs",
    "thm": "cvrdt_on_iff",
    "setting": "Merges as events of a compensation-free registry, delivered in any order and with any duplication.",
    "condition": "One state from s0 iff the merges commute and are idempotent at reachable states; with finitely many payloads, iff the reachable states carry a join-semilattice where each merge is a join.",
    "needed": [
      ["naive_cvrdt_iff_fails", "a semilattice on all of S is the wrong iff"],
      ["clamp_reach_qualifier", "reachability is needed"],
      ["add_cc_not_alo", "the idempotence clause is needed"],
      ["lww_not_conv", "the commutation clause is needed"]],
    "theorems": ["merge_action_exact", "cvrdt_on_iff", "merge_conv_alo_exact"],
    "modules": ["CvRDTExact.v"],
    "section": "4-crdt-fragment"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Where CRDTs end",
    "thm": "crdt_boundary",
    "setting": "How the compensation-free (CRDT) fragment sits inside governed state.",
    "condition": "Compensation-free: causal convergence iff concurrent raw operations commute, and convergence under any order and duplication iff raw actions commute and are idempotent at reachable states. With compensation, a witness converges under both while its raw transitions fail each condition.",
    "needed": [
      ["witness_raw_not_causal", "the witness fails the causal condition"],
      ["witness_not_cvrdt_exact", "the witness fails the state-based conditions"]],
    "theorems": ["crdt_boundary", "cf_causal_boundary", "cf_merge_boundary", "boundary_nonvacuous"],
    "modules": ["CRDTBoundary.v"],
    "section": "4-crdt-fragment"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Stream processors",
    "thm": "stream_exact",
    "setting": "Settled stream processors that received the same set of events.",
    "condition": "Under Progress, they agree iff PJC holds at every duplicate-free (s0, E); under free delivery, iff PCC.",
    "needed": [
      ["jc_not_necessary", "the rewrite-system JC is the wrong iff"],
      ["progress_needed", "Progress is needed"]],
    "theorems": ["stream_exact", "stream_exact_free", "pjc_exact"],
    "modules": ["StreamExact.v"],
    "section": "5-stream-processors"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Streams, at-least-once",
    "thm": "stream_alo_exact_free",
    "setting": "Stream processors whose received lists may repeat events, compared by their set of events.",
    "condition": "Under free delivery, agreement iff PCC plus idempotence of each event where a processor initially applies it.",
    "needed": [
      ["ct_alo_fails", "the exactly-once condition is not sufficient"],
      ["ow_alo_fails", "idempotence alone is not sufficient"]],
    "theorems": ["stream_alo_exact_free", "stream_alo_exact", "stream_exact_recovered"],
    "modules": ["StreamAtLeastOnce.v"],
    "section": "5-stream-processors"
  },
  {
    "kind": "excl",
    "mark": "X",
    "name": "Infinite streams, eventual agreement",
    "note": "naive claim refuted",
    "setting": "Infinite streams, asking that processors eventually agree.",
    "condition": "Gap 9, a design exclusion: the naive claim is false, since a lagging processor need never agree. Agreement at settled times with equal received sets is proved.",
    "theorems": ["base_thm_convergence_transient_counterexample", "stream_agreement"],
    "modules": ["Stream.v"],
    "section": "5-stream-processors"
  }
] },
{ "code": "04", "name": "Acyclic federations", "tiles": [
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Repair normal form",
    "thm": "order_independent",
    "thmNote": "(unconditional)",
    "setting": "An acyclic federation with a single source per shared part (M1): the federated repair normal form.",
    "condition": "No condition needed: under the network hypotheses the normal form is unique and every topological order reaches it.",
    "needed": [
      ["prop_cycle_necessary", "acyclicity is needed"],
      ["prop_m1_necessary", "M1 is needed"]],
    "gsm": "M1, shared-only writes and source determinacy (verifyEdge).",
    "theorems": ["order_independent", "cat_thm_one_order_independent", "fed_lem_fed_termination"],
    "modules": ["FederationOrder.v", "CategoricalBridge.v", "FederationGRS.v"],
    "section": "6-acyclic-federation-the-repair-normal-form"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Event order, guarded",
    "thm": "fed_exact",
    "setting": "An acyclic federation whose events fire at federally valid states (FedMachine.Apply).",
    "condition": "All trace-equivalent sequences converge from a valid consistent s0 iff C1 and C2 hold at witnesses reachable from s0.",
    "needed": [
      ["naive_converse_fails", "static C1 is not necessary"]],
    "gsm": "C1 and C2 (verifyCrossOrder, verifyRepairedCC).",
    "theorems": ["fed_exact", "fed_exact_full", "acyclic_gc_iff"],
    "modules": ["FederationEventsConverse.v"],
    "section": "7-acyclic-federation-event-order"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Event order, unguarded",
    "thm": "fed_grs_exact",
    "setting": "An acyclic federation as a rewrite system (G_Fed), where events may fire before compensation.",
    "condition": "Convergence iff CC1 and CC2 of G_Fed hold on reachable states; the exact form is global, with no per-edge form.",
    "needed": [
      ["fed_grs_c1_c2_insufficient", "C1 and C2 do not suffice here"]],
    "gsm": "No XU check; gsm's runtime is the guarded model.",
    "theorems": ["fed_grs_exact", "grs_unique_nf"],
    "modules": ["FederationGRS.v"],
    "section": "7-acyclic-federation-event-order"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Buffered guards",
    "thm": "fed_buffered_exact",
    "setting": "An event waits in the buffer until the state is federally valid and its guard holds; normal forms may hold stuck events.",
    "condition": "Unique normal forms for every buffer iff, at every state a guard-feasible word reaches, co-enabled distinct events stay enabled after each other and commute (GCR).",
    "needed": [
      ["bg_persistence_needed", "commutation alone is not sufficient"],
      ["bg_wait_exact", "commutation is not necessary"],
      ["bg_commute_needed", "commutation of co-enabled events is needed"]],
    "gsm": "No buffered guard in gsm's runtime.",
    "theorems": ["fed_buffered_exact", "fed_buffered_edge", "fed_jcg_exact"],
    "modules": ["FederatedGuards.v"],
    "section": "7-acyclic-federation-event-order"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Every fair schedule",
    "thm": "rb_robert_fair",
    "setting": "Every fair asynchronous schedule of propagation steps on an acyclic network, from every valid start (Robert's asynchronous half).",
    "condition": "No condition needed: every fair schedule settles at the run of one topological order, the only quiescent state a propagation word reaches, within a round bound by depth.",
    "needed": [
      ["rb_dist_cycle_needed", "acyclicity is needed"],
      ["rb_absorb_needed", "absorption of a later overwrite is needed"],
      ["rb_converse_fails", "acyclicity is not necessary"]],
    "theorems": ["rb_robert_fair", "rb_unique", "rb_rounds", "rb_robert_boolean"],
    "modules": ["RobertFair.v"],
    "section": "6-acyclic-federation-the-repair-normal-form"
  }
] },
{ "code": "05", "name": "Distributed propagation", "tiles": [
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Acyclic networks",
    "thm": "dist_exact",
    "setting": "An acyclic network where local events interleave with propagation steps that read possibly stale sources; compared after a final flush.",
    "condition": "Convergence iff XU holds at every reachable stale combination (XUR) and C2 holds at states reachable from the flushed start.",
    "needed": [
      ["levels_exact_not_xu", "static XU is not necessary; the reachability qualifier is"],
      ["dist_strictly_stronger_than_fed", "FedMachine convergence is not sufficient"]],
    "gsm": "verifyProjectionMerge checks static XU per single-source target; with Build's C2 it is sound, and exact from every valid start when the sources are roots.",
    "theorems": ["dist_exact", "dist_exact_tc", "dist_global_exact_roots", "dist_xu_c2_converge"],
    "modules": ["DistributedExact.v"],
    "section": "8-distributed-model-with-propagation-steps"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Any delivery class",
    "thm": "dist_delivery_exact",
    "setting": "The acyclic distributed model under any prefix-closed event-delivery class: causal, at-least-once, or both.",
    "condition": "Convergence iff XU at every state a word of the class reaches (XURD) plus convergence of the FedMachine over the class from the flushed start.",
    "needed": [
      ["snap_xu_needed", "the propagation conjunct is needed"],
      ["set_comm_needed", "the FedMachine conjunct is needed"],
      ["inc_idem_needed", "at-least-once needs idempotence"],
      ["tr_causal_instance", "restricting dist_exact is not exact for causal delivery"]],
    "gsm": "verifyProjectionMerge (static XU) covers the propagation layer for every class; no gsm check targets idempotence of the FedMachine step.",
    "theorems": ["dist_delivery_exact", "dist_causal_exact", "dist_alo_exact", "dist_causal_alo_exact"],
    "modules": ["DistributedDelivery.v"],
    "section": "8-distributed-model-with-propagation-steps"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Monotone cycles, reset epochs",
    "thm": "epoch_conv_iff",
    "setting": "Monotone cycles with events, where a barrier resets every shared value to bottom and propagation runs to quiescence; compared after a final epoch.",
    "condition": "All interleavings agree iff each event's local outcome is the same at every reachable stale state as at its flushed form (XUcR) and the FedMachine converges from the flushed start.",
    "needed": [
      ["dist_cyc_epoch_fix", "the reset must be a barrier"]],
    "gsm": "No epoch mode; cyclic projection deployments are reported not certified.",
    "theorems": ["epoch_conv_iff", "epoch_agree_iff", "lens_epoch"],
    "modules": ["DistributedCycles.v"],
    "section": "8-distributed-model-with-propagation-steps"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Monotone cycles, no resets",
    "thm": "flush_fed_iff",
    "setting": "Monotone cycles with events and no resets: the deployment flushes, its quiescent states agree with the FedMachine, and quiescent interleavings agree.",
    "condition": "That property holds iff XUcR, FedMachine convergence (FMConv), FlushR and NoGhostR all hold, with nothing else on the left of the iff.",
    "needed": [
      ["copy_xu_fails", "XUcR is needed"],
      ["fm_conv_fails", "FMConv is needed"],
      ["flip_noflush", "FlushR is needed"],
      ["ghost_exact", "NoGhostR is needed"]],
    "gsm": "None: gsm reports cyclic projection deployments not certified and has no check for FlushR or NoGhostR.",
    "theorems": ["flush_fed_iff", "flush_agree_iff", "fair_fed_iff", "noghost_event_iff"],
    "modules": ["DistributedCyclesExact.v"],
    "section": "8-distributed-model-with-propagation-steps"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Convergence alone, ghost allowed",
    "thm": "conv_quiet_exact",
    "setting": "Monotone cycles, no resets: quiescent interleavings agree with each other, possibly on a common ghost, without matching the FedMachine.",
    "condition": "FlushR and DConvQ iff FlushR, FlushDetR, FlushXUR and QMConv: the layers of flush_fed_iff read against the state propagation settles in, not the least fixed point.",
    "needed": [
      ["flip_conv_noflush", "FlushR is needed"],
      ["fork_conv_nodet", "FlushDetR is needed"],
      ["copy_conv_noxu", "FlushXUR is needed"],
      ["fm_conv_noqm", "QMConv is needed"]],
    "gsm": "gsm's C1cyc and C2cyc are stated against Lfp; nothing checks FlushXUR or QMConv when a ghost is reachable.",
    "theorems": ["conv_quiet_exact", "fair_conv_exact", "agree_conv_noghost"],
    "modules": ["DistributedConvergenceExact.v"],
    "section": "8-distributed-model-with-propagation-steps"
  },
  {
    "kind": "open",
    "mark": "16",
    "name": "ACC without height; repair as steps on cycles",
    "note": "open",
    "setting": "Distributed propagation on monotone cycles with ACC but no finite height, or with local compensation as separate steps on cycles.",
    "condition": "Open: gap 16 (b) and (c). Every distributed module assumes a rank bound, and G_Fed is acyclic only. Part (d), fair schedules on acyclic networks, is closed.",
    "theorems": ["flush_fed_iff", "epoch_conv_iff", "rb_robert_fair"],
    "modules": ["DistributedCyclesExact.v", "DistributedCycles.v", "RobertFair.v"],
    "section": "8-distributed-model-with-propagation-steps",
    "gap": 16
  }
] },
{ "code": "06", "name": "Channels and reconfiguration", "tiles": [
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Channels, acyclic",
    "thm": "chan_exact",
    "setting": "Acyclic networks whose projections are delivered late, reordered or duplicated, in plain or versioned merge mode; compared after a final flush.",
    "condition": "Convergence iff XU at every channel-reachable state (CXUR) plus C2 at states reachable from the flushed start.",
    "gsm": "The static XU check (FedReport.ProjectionSafe) with Build's C2 is sound for both merge modes after a flush.",
    "theorems": ["chan_exact", "chan_exact_global", "chan_global_exact_roots"],
    "modules": ["ProjectionChannels.v"],
    "section": "8-distributed-model-with-propagation-steps"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Versioned merge at drain",
    "thm": "vsettle_exact_cond",
    "setting": "Versioned merging (MergeProjectionAfter), compared after a final round and any drain, with no outside flush.",
    "condition": "Converging at drain is converging after a flush: CXUR plus C2. On two-level and, more generally, nested networks this is dist_exact's own condition.",
    "needed": [
      ["version_order_counterexample", "versions must increase in send order"],
      ["no_final_send_counterexample", "a send after the last source change is needed"]],
    "gsm": "MergeProjectionAfter's version check is proved: gsm's XU and C2 give convergence once the channels drain after a final round.",
    "theorems": ["vsettle_exact_cond", "vsettle_xu_c2", "vchan_twolevel_exact"],
    "modules": ["ProjectionChannels.v"],
    "section": "8-distributed-model-with-propagation-steps"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Versioned channels, nested networks",
    "thm": "vchan_nested_exact",
    "setting": "Versioned merging on nested acyclic networks: whenever a registry that is not a pure root lies above a target, every source of the target lies below it too (every two-level network, every single-source network: chains and trees of any depth).",
    "condition": "Every versioned channel state is a current-value state, so CXUR equals XUR, and convergence after a flush or at drain holds iff XUR plus C2: dist_exact's condition.",
    "needed": [
      ["vchan_skip_counterexample", "beyond nested networks CXUR is strictly stronger than XUR"]],
    "gsm": "On single-source targets, the only ones gsm certifies for projection deployments, the reachable condition over versioned channels is dist_exact's.",
    "theorems": ["vchan_nested_exact", "cxur_nested", "vchan_single_exact", "vchan_nested_emulate"],
    "modules": ["ProjectionChains.v"],
    "section": "8-distributed-model-with-propagation-steps"
  },
  {
    "kind": "open",
    "mark": "21",
    "name": "Channels beyond nested networks; on cycles",
    "note": "open",
    "setting": "Propagation over versioned channels on acyclic networks that are not nested, and over channels on cycles.",
    "condition": "Open: gap 21 (a), the exact network class between nested networks (settled) and the pattern of vchan_skip_counterexample, where versioned channels reach a stale combination no current-value run does; (b), cycles, where the ghost survives versioned channels and epochs over channels have no theorem.",
    "theorems": ["chan_exact", "vchan_nested_exact", "vchan_skip_counterexample", "vchan_cyc_ghost"],
    "modules": ["ProjectionChannels.v", "ProjectionChains.v"],
    "section": "8-distributed-model-with-propagation-steps",
    "gap": 21
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Live rule change",
    "thm": "live_exact",
    "setting": "A single registry under free delivery switches configuration (rules or migration) while events are in flight.",
    "condition": "Convergence iff B's condition holds from every migrated reachable state plus two cross-configuration critical pairs: in-flight events commute with the switch (S1), and the switch absorbs A's compensation (S2).",
    "needed": [
      ["cap_raise", "S2 is needed"],
      ["doubling_migration", "S1 is needed"],
      ["migrated_transient", "B's condition at a migrated non-quiescent state is needed"],
      ["forgetful_migration", "A's own condition is not necessary"]],
    "gsm": "gsm checks only that participants share one policy (PolicyDigest); a classifier (CheckMigration) is planned.",
    "theorems": ["live_exact", "barrier_exact", "fed_live_exact", "classify_finite"],
    "modules": ["Reconfiguration.v"],
    "section": "the-open-gaps",
    "gap": 20
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Unfaithful migration",
    "thm": "amodm_closure_exact",
    "setting": "A switch at a barrier whose migration is not injective, in the deterministic model (gsm's runtime).",
    "condition": "A converges modulo the migration iff every pair in the closure of adjacent swaps under common continuations has equal images; a finite search on finite instances.",
    "theorems": ["amodm_closure_exact", "det_barrier_closure_exact", "det_classify_complete"],
    "modules": ["ReconfigurationClosure.v"],
    "section": "the-open-gaps",
    "gap": 20
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Switch under a delivery class",
    "thm": "live_delivery_exact",
    "setting": "A switch in the deterministic model (gsm's runtime) under declared independence, causal or at-least-once delivery, live or at a barrier.",
    "condition": "Live iff B's class condition holds over the combined alphabet (in-flight events translated) from the migrated start and S1 holds at every A-prefix the class admits; at a barrier iff B's class condition holds at every migrated reachable state and A converges under the class modulo the migration, plus, at least once, a redelivery straddling the switch is absorbed.",
    "needed": [
      ["cross_declared_barrier", "the cross pairs the class reorders are needed"],
      ["count_dup_prefix", "S1 at a duplicate prefix is needed"],
      ["reset_straddle", "absorbing a redelivery that straddles the barrier is needed"]],
    "gsm": "CheckMigration refuses registries with Independent pairs; classify_declared_complete states the check for them.",
    "theorems": ["live_delivery_exact", "barrier_delivery_exact", "barrier_alo_exact", "classify_causal_complete", "classify_alo_complete"],
    "modules": ["ReconfigurationDelivery.v"],
    "section": "the-open-gaps",
    "gap": 20
  },
  {
    "kind": "open",
    "mark": "20",
    "name": "Switch with propagation in flight",
    "note": "open",
    "setting": "Reconfiguration in the distributed model, where projections sent under A are merged under B.",
    "condition": "Open: gap 20 residue (a), a live switch while propagation is in flight.",
    "theorems": ["live_exact", "fed_live_exact", "amodm_closure_exact", "live_delivery_exact"],
    "modules": ["Reconfiguration.v", "ReconfigurationClosure.v", "ReconfigurationDelivery.v"],
    "section": "the-open-gaps",
    "gap": 20
  }
] },
{ "code": "07", "name": "Monotone cycles", "tiles": [
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Unique repair normal form",
    "thm": "cyc_N_unique",
    "setting": "Cyclic networks with monotone repair on lattices of finite height or with ACC.",
    "condition": "No condition needed inside the regime: the repair normal form is the least fixed point, and every sweep and chaotic schedule reaches it.",
    "gsm": "verifyMonotone and verifyMonotoneVisited (cover-step monotonicity over visited states).",
    "theorems": ["cyc_N_unique", "cyc_N_lfp", "chaotic_reaches_lfp", "kleene_acc_lfp"],
    "modules": ["FederationEventsCycles.v", "Chaotic.v", "ChaoticACC.v"],
    "section": "9-monotone-cycles-the-repair-normal-form"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Event order",
    "thm": "gc_iff",
    "setting": "Events on a monotone cyclic network: do all trace-equivalent sequences converge from s0.",
    "condition": "Convergence iff GC holds at reachable federated states. GC has no per-edge reduction.",
    "gsm": "Per-target C1 and C2 with image sets over every valid source state (FedReport.Checks): sufficient, not necessary.",
    "theorems": ["gc_iff", "net_events_converge_iff", "cyc_check_gc_lfp"],
    "modules": ["FederationEventsCycles.v", "MonotoneFederation.v", "FederationEventsCyclesCheck.v"],
    "section": "10-monotone-cycles-event-order"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Multi-edge targets",
    "thm": "gc_iff",
    "thmNote": "(same GC)",
    "setting": "Monotone cycles where a target has several incoming edges.",
    "condition": "The exact condition is the same GC. Per-edge C1 plus M1 is a sufficient route to it.",
    "needed": [
      ["m1_necessary", "M1 is needed for the per-edge route"]],
    "gsm": "gsm checks C1 against the joint image of all incoming edges, not the per-edge route.",
    "theorems": ["gc_iff", "multi_edge_gc", "multi_edge_c1_free"],
    "modules": ["FederationEventsCycles.v", "FederationEventsCyclesMulti.v"],
    "section": "10-monotone-cycles-event-order"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Validity of the fixed point",
    "thm": "lfp_valid_exact",
    "setting": "Whether the least fixed point the cyclic repair reaches is a valid state.",
    "condition": "Under ACC, the least fixed point is valid iff some Kleene iterate is valid; a fixed point is valid iff the images are valid at it.",
    "needed": [
      ["bottom_validity_not_necessary", "bottom validity is not necessary"],
      ["lfp_valid_iff_needs_reach", "the reachability qualifier is needed"]],
    "gsm": "Image validity over visited states (verifyMonotoneVisited), proved sound: sufficient, not necessary.",
    "theorems": ["lfp_valid_exact", "lfp_valid_iff_reached", "gsm_check_lfp_valid"],
    "modules": ["MonotoneExact.v"],
    "section": "9-monotone-cycles-the-repair-normal-form"
  },
  {
    "kind": "excl",
    "mark": "X",
    "name": "Fixed points without ACC",
    "note": "design exclusion",
    "setting": "Least fixed points on a complete lattice without ACC.",
    "condition": "Gap 8, a design exclusion: existence is classical Knaster-Tarski, outside the axiom-free gate. Mechanized instead: the exact condition for the fixed point to be reached by iteration.",
    "theorems": ["kleene_reach_exact", "kleene_acc_lfp_nn", "kleene_sup_lfp"],
    "modules": ["MonotoneExact.v", "ChaoticACC.v", "MonotoneFederation.v"],
    "section": "9-monotone-cycles-the-repair-normal-form"
  }
] },
{ "code": "08", "name": "Invertible networks", "tiles": [
  {
    "kind": "exact",
    "mark": "iff",
    "name": "A consistent state exists",
    "thm": "section_iff_coboundary",
    "setting": "Cycles whose edges are transports by group elements (the regular action).",
    "condition": "A consistent state exists iff the labeling is a coboundary (H^1 = 0); per fundamental cycle, iff each has trivial holonomy.",
    "needed": [
      ["nonfree_holonomy_counterexample", "the regular action is needed"]],
    "gsm": "DiagnoseCycle on one cycle, a sound refuter on the regular action.",
    "theorems": ["section_iff_coboundary", "cycle_basis_criterion"],
    "modules": ["CohomologyGraph.v"],
    "section": "11-non-monotone-cycles-invertible-transports"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "What must be coordinated",
    "thm": "plan_exact",
    "setting": "An invertible network coordinated relative to a spanning tree.",
    "condition": "Exactly the unbalanced non-tree edges must be coordinated.",
    "gsm": "CoordinationPlan cuts a feedback edge set (every cycle): sound, not the holonomy-minimal plan.",
    "theorems": ["plan_exact", "coordination_needed", "coordinated_sound"],
    "modules": ["CoordinatedCycles.v"],
    "section": "11-non-monotone-cycles-invertible-transports"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Rootless, any finite network",
    "thm": "net_unique_normal_form_iff",
    "setting": "Any finite invertible network with no authority root: every edge writes.",
    "condition": "Existence and uniqueness from every start iff H^1 = 0 and every component has an authority root, or the group is trivial.",
    "needed": [
      ["rootless_global_holonomy", "holonomy inside components does not decide existence"],
      ["rootless_mixed_square", "a coboundary does not give existence from every start"],
      ["rootless_source_feeds_cycle", "a cycle over Z/2 fed by a source is still unique"]],
    "theorems": ["net_unique_normal_form_iff", "net_nf_exists_iff", "net_unique_iff", "net_reachable_iff"],
    "modules": ["RootlessNetworks.v"],
    "section": "11-non-monotone-cycles-invertible-transports"
  },
  {
    "kind": "hard",
    "mark": "NP",
    "name": "Minimum coordination",
    "thm": "maxcut_plan_reduction",
    "setting": "The fewest edges to coordinate over all spanning trees and roots, on an invertible network.",
    "condition": "Exact on a connected network: the minimum is the group feedback edge set number. NP-hard already over Z/2, by a mechanized reduction from Max-Cut (NP-completeness of Max-Cut cited).",
    "needed": [
      ["plan_min_connected_needed", "connectivity is needed"],
      ["plan_min_nodup_needed", "NoDup is needed for the set form"]],
    "gsm": "CoordinationPlan gives an upper bound, not necessarily the minimum.",
    "theorems": ["maxcut_plan_reduction", "maxcut_reduction", "plan_min_exact"],
    "modules": ["CoordinationMinimum.v"],
    "section": "11-non-monotone-cycles-invertible-transports"
  },
  {
    "kind": "open",
    "mark": "16",
    "name": "Events with rootless cycles",
    "note": "open",
    "setting": "Events interleaved with rootless propagation on cyclic invertible networks with authority roots.",
    "condition": "Open: gap 16 (a). There is no distributed model off monotone cycles; the rootless repair alone is exact.",
    "theorems": ["net_unique_normal_form_iff", "dist_exact"],
    "modules": ["RootlessNetworks.v", "DistributedExact.v"],
    "section": "11-non-monotone-cycles-invertible-transports",
    "gap": 16
  }
] },
{ "code": "09", "name": "Lossy networks", "tiles": [
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Existence via root sets",
    "thm": "root_set_criterion_graph",
    "setting": "Non-invertible transports on a general graph: does a consistent state exist.",
    "condition": "For any root set and spanning forest, a consistent state exists iff some root assignment drives a state satisfying every edge.",
    "theorems": ["root_set_criterion_graph", "root_set_iff_forest", "root_set_decide"],
    "modules": ["RootSet.v"],
    "section": "12-non-invertible-transports"
  },
  {
    "kind": "hard",
    "mark": "NP",
    "name": "Consistency, no spanning root",
    "thm": "net_section_iff_sat",
    "setting": "Existence of a consistent state on a non-invertible network with no spanning root.",
    "condition": "NP-complete: a mechanized, parsimonious reduction from 3-SAT gives a network with a consistent state iff the formula is satisfiable, plus an NP certificate.",
    "needed": [
      ["no_filter_trivial", "the gadget is needed"],
      ["no_pin_trivial", "the gadget is needed"]],
    "theorems": ["net_section_iff_sat", "net_bijection", "np_certificate"],
    "modules": ["LossyHardness.v"],
    "section": "12-non-invertible-transports"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Monotone transports on a chain",
    "thm": "ac_exact",
    "setting": "A fixed family of monotone transport maps on a finite chain {0..N}, any graph, pinned vertices allowed: does a consistent state exist.",
    "condition": "Arc consistency decides it: the procedure returns true iff a consistent state with values in the chain exists, and the minimum of each arc-consistent domain is one. Per fixed family, existence is CSP(Gamma_F), classified by the operations commuting with every map (cited dichotomy); min and max are among them on a chain.",
    "needed": [
      ["ac_needs_mono", "monotonicity is needed: a negation triangle passes arc consistency with no section"],
      ["diamond_join_fails", "the chain is needed: on the diamond a monotone lossy map does not commute with join"]],
    "theorems": ["ac_exact", "chain_pol", "section_iff_csp", "pol_gamma_iff", "hard_family_csp"],
    "modules": ["TransportCSP.v"],
    "section": "12-non-invertible-transports"
  },
  {
    "kind": "hard",
    "mark": "NP",
    "name": "Minimum coordination",
    "thm": "lmin_reduction",
    "setting": "The fewest edges to delete so that a non-invertible network has a consistent state.",
    "condition": "Exact and decidable, but deciding minimum 0 is NP-hard by a mechanized 3-SAT reduction, so no approximation within any factor unless P = NP.",
    "needed": [
      ["lossy_min_exceeds_cycle_bounds", "the minimum is not cycle-based"]],
    "theorems": ["lmin_reduction", "lmin_root_set", "lmin_decide", "min_le_np_certificate"],
    "modules": ["LossyMinimum.v"],
    "section": "12-non-invertible-transports"
  },
  {
    "kind": "open",
    "mark": "3",
    "name": "Rootless resolvers: fair settlement",
    "note": "up to 2 unstable: proved",
    "setting": "Rootless propagation in the resolver reading on non-invertible networks: does every fair order reach one consistent state.",
    "condition": "Open; only sufficient certificates. Under no local cycle plus out-degree at most one, fair settlement is proved from starts with at most two unstable vertices; three or more is open, as is an exact condition.",
    "needed": [
      ["shih_dong_not_fair", "local conditions do not give fair settlement"],
      ["ring_local_conditions", "local conditions do not give fair settlement"]],
    "theorems": ["two_token_fair_settlement", "one_token_fair_settlement", "signed_settlement", "shih_dong_E"],
    "modules": ["LocalTwoToken.v", "LocalFairSettlement.v", "SignedResolver.v", "LocalSigned.v"],
    "section": "12-non-invertible-transports",
    "gap": 3
  },
  {
    "kind": "open",
    "mark": "17",
    "name": "Edge-writer dynamics",
    "note": "open",
    "setting": "Rootless edge-writer dynamics beyond the regular action: lossy maps at in-degree two or more, and invertible maps under a non-free action.",
    "condition": "Open: when every fair order reaches a consistent state, and uniqueness. Existence is exact and NP-complete.",
    "theorems": ["root_set_criterion_graph", "net_section_iff_sat"],
    "modules": ["RootSet.v", "LossyHardness.v"],
    "section": "12-non-invertible-transports",
    "gap": 17
  },
  {
    "kind": "open",
    "mark": "18",
    "name": "Resolver fixed points",
    "note": "open",
    "setting": "Existence and counting of resolver fixed points (reading B) at in-degree two or more, with no spanning root.",
    "condition": "Open: no row. The reductions between the readings are conjectures; mechanizing one would transfer net_section_iff_sat and net_count.",
    "theorems": ["net_section_iff_sat", "net_count", "rb_lens_robert"],
    "modules": ["LossyHardness.v", "RobertFair.v"],
    "section": "12-non-invertible-transports",
    "gap": 18
  }
] },
{ "code": "10", "name": "Composition", "tiles": [
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Acyclic collapse",
    "thm": "collapse_c_exact",
    "setting": "An acyclic convex sub-federation J contracted to one effective registry.",
    "condition": "The outer network N' converges iff N does, with the same exact condition.",
    "gsm": "Federation.Embed and certificates (validateCertificates, seam re-check).",
    "theorems": ["collapse_c_exact", "collapse_c_guarded_iff"],
    "modules": ["Collapse.v"],
    "section": "14-compositional-collapse"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Blocks of any engines",
    "thm": "compose_exact",
    "fresh": true,
    "setting": "An upstream system and a block reading its current state, with any engines; any DAG of blocks by iteration.",
    "condition": "The composite converges iff the upstream converges, the block settles from every start at every quiet input, and its settled states are not separated by its steps at transient inputs.",
    "needed": [
      ["compose_needs_A", "upstream convergence is needed"],
      ["compose_needs_wn", "settling at every quiet input is needed"],
      ["compose_isolated_refuted", "every block converging in isolation is not enough"],
      ["mixed_ghost_refuted", "the same, with real engines"]],
    "gsm": "None: gsm flattens.",
    "theorems": ["compose_exact", "compose_collapse", "interface_closed", "mixed_rootless_exact", "mixed_mono_iff"],
    "modules": ["CompositionBlocks.v"],
    "section": "14-compositional-collapse"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Cyclic monotone collapse",
    "thm": "mono_collapse_exact",
    "fresh": true,
    "setting": "A cyclic J with monotone repair in the FedMachine model, normalized by its own least fixed point at its inputs.",
    "condition": "Blockwise least fixed points are the least fixed point (Bekic), so N' and N have the same normal form and converge together, exactly under GC.",
    "gsm": "gsm flattens embedded cyclic subs (opt-in AllowMonotoneCycles); flattening and collapse give the same normal form.",
    "theorems": ["mono_collapse_exact", "bekic_lfp", "mono_collapse_nf", "mono_collapse_converges_iff"],
    "modules": ["CompositionBlocks.v"],
    "section": "14-compositional-collapse"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Distributed collapse, acyclic J",
    "thm": "dist_collapse_iff",
    "fresh": true,
    "setting": "The distributed model with an acyclic J whose internal propagation interleaves with outer events.",
    "condition": "N converges iff N' (J propagating as one atom) converges and XU holds at every state N reaches, J half-propagated included.",
    "needed": [
      ["dist_collapse_refuted", "collapse_c's plain statement fails"],
      ["dist_collapse_needs_c2", "XU alone does not give N'"]],
    "gsm": "verifyProjectionMerge (static XU) makes N and N' agree.",
    "theorems": ["dist_collapse_iff", "dist_collapse_exact", "dist_atoms_exact", "dist_collapse_xu"],
    "modules": ["CompositionBlocks.v"],
    "section": "14-compositional-collapse"
  },
  {
    "kind": "open",
    "mark": "19",
    "name": "Distributed collapse, cyclic J",
    "note": "open",
    "setting": "Collapse preservation in the distributed model when J is cyclic.",
    "condition": "Open: gap 19 residue (b) for a cyclic J, in the no-reset cyclic model and with reset epochs, where J's atom would be its own flush to quiescence. Parts (a) and acyclic (b) are closed.",
    "theorems": ["dist_collapse_iff", "compose_exact"],
    "modules": ["CompositionBlocks.v"],
    "section": "14-compositional-collapse",
    "gap": 19
  }
] },
{ "code": "11", "name": "Structure", "tiles": [
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Counting H1 on the nerve",
    "thm": "nerve_H1_classification",
    "setting": "H^1 of the nerve as a 2-complex, with triangle relations as 2-cells.",
    "condition": "For any group, H^1 is classified as Hom(<X | relation words>, G) modulo conjugation; over Z/2 it has exactly 2^((|E| - |V| + 1) - rank) classes.",
    "theorems": ["nerve_H1_classification", "nerve_H1_abelian", "nerve_H1_Z2_count"],
    "modules": ["CohomologyNerve.v"],
    "section": "13-the-full-nerve-as-a-2-complex"
  },
  {
    "kind": "exact",
    "mark": "iff",
    "name": "Sheaf gluing of states",
    "thm": "sheaf_exact",
    "setting": "The registry-level site: sub-federations as open sets, consistent states as sections.",
    "condition": "Under R1, on a cover that refines the constraints, a family is the restriction of a global section iff it is compatible and local; gluing holds for every R1 federation iff the cover refines.",
    "needed": [
      ["triangle_fails", "refinement is needed"],
      ["r1_failure", "R1 is needed"],
      ["gluing_cex_overlap", "compatibility on the overlap is needed"]],
    "gsm": "verifyResolved covers R1; gsm has no cover-level check.",
    "theorems": ["sheaf_exact", "sheaf_iff_refines", "cert_sheaf"],
    "modules": ["SheafGluing.v"],
    "section": "13-the-full-nerve-as-a-2-complex"
  },
  {
    "kind": "open",
    "mark": "13",
    "name": "Variable-level site",
    "note": "paper only",
    "setting": "Sheaf gluing on the paper's variable-level site (two subsystems may write one variable) and its monotone-overlap site.",
    "condition": "Gap 13, narrowed: these sites are at paper level, not mechanized, as is a sheaf condition for relative certificates on covers not closed under sources.",
    "theorems": ["sheaf_iff_refines", "cert_sheaf", "cert_restrict_iff"],
    "modules": ["SheafGluing.v"],
    "section": "13-the-full-nerve-as-a-2-complex",
    "gap": 13
  }
] }
]
};
