# Regime audit of the headline claim

The README's headline claim:

> A complete, mechanized map of when governed concurrent state converges, with exact conditions in
> every regime and a checker for the practical ones.

This page audits that sentence against the development, regime by regime and question by question.
It adds no proofs. Audited at `main` `bb8ea95` (gate: `coq/verify.sh`, 729 axiom-free results) and
gsm `main` `a71a1b0`. Every Coq name cited was read as a statement in `coq/*.v`, not matched by
name; a name in an "exact" cell is an `<->` theorem (or a conjunction containing one).

## How to read the tables

Each row is one question asked of one regime. Columns:

- **Exact (N and S).** A mechanized necessary-and-sufficient condition, with its theorem, or
  "none mechanized", or "none known".
- **Cheap sufficient, and the link.** The condition gsm-style checking can afford (per state, per
  pair, per edge), and the theorem that makes it imply the exact one.
- **gsm.** Whether gsm `main` implements a check (file or API named).
- **Gap.** `paper` (proved in a paper, not mechanized), `open` (not proved anywhere, or listed open
  by the development itself), `design` (excluded by the model or the axiom-free constraint), or `-`.

Three kinds of question are kept apart, because the claim is about the first:

1. **Convergence**: does a unique normal form exist; do all event orders reach it.
2. **Optimization**: what is the minimum coordination.
3. **Counting**: the rank of `H^1`.

## 1. Single registry

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Free delivery: unique normal form for every buffer from `s0` | CC1 and CC2 on states reachable from `s0`, with canonical repair: `cc_exact_from`, `cc_exact`, `cc_exact_global`; with `rho*` built from WFC: `wfc_cc_exact_from` | CC1 and CC2 at every state: `governance_unique_normal_forms`, `paper_governance_unique_normal_forms`; reachable form implies JC: `cc_reach_jc` | `Registry.Build` (exhaustive CC; footprint path `disjoint_events_commute`); re-certified by the table and rules oracles | Qualifier: canonical repair needed (`rho_star_qualifier`). - |
| Causal or guarded enabledness: confluence from `c0` | JC at configurations reachable from `c0`: `jc_exact` | CC1 on co-enabled pairs plus CC2, on reachable states: `cc_reach_jc`, `cc_reach_unique_normal_forms`; deps-based enabledness: `paper_causal_governance_unique_normal_forms` | CC1 checked on declared `Independent` pairs only | Qualifier: `jc_exact` assumes enabledness persists under compensation (`enabled_after_comp`); enabledness that a repair step can disable is outside it. CC1 not necessary: `masked_cc1`. |
| Any well-founded potential (infinite state, ordinal-valued `Phi`): unique normal form | **None mechanized.** Every exact converse (`cc_exact_from`, `jc_exact`) is stated with `Phi : State -> nat`. Infinite state with a `nat` potential is covered (the state type is arbitrary); an ordinal or lexicographic potential is not | `governance_wf_confluent`, `causal_governance_wf_confluent`, `governance_lex_confluent`, instance `zw_confluent` | n/a (gsm needs finite state to decide) | open (small: rerun the converse over `GovernanceWF.v`'s termination) |
| WFC itself (termination) | Taken as part of the model (Base `def:registry`) | `repair_terminates`; `base_lem_finite_implies_ubc` | WFC cycle detection in `Build` | design |

## 2. Causal delivery (replay model)

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Do all causally consistent orders of the same events reach one state from `s0` | CCR: concurrent pairs commute after every causally consistent prefix: `causal_exact` | Governed steps commute on every concurrent pair at every state: `causal_convergence`; the global iff `causal_convergence_exact` (needs `hb` irreflexive) | Declared `Independent` pairs read as the concurrent ones (`causal_tequiv`, `run_tequiv`) | Qualifier: reachability of the state is not enough (`naive_causal_converse_fails`). - |

## 3. At-least-once delivery

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Does a delivery with duplicates reach the exactly-once result (all orders) | **None mechanized.** The necessity side is a local witness only: a step not idempotent at `s` diverges when delivered twice from `s` (`non_idempotent_diverges`), with no reachability or delivery-position qualifier tying it to a run | `alo_absorbed` (each redelivered event idempotent and commuting with the events delivered in between); `alo_commuting_exactly_once`, `alo_commuting_converges` | `Report.NotIdempotent` lists events whose step is not idempotent | open (medium) |
| Same, under causal delivery | **None mechanized** | `causal_alo_exactly_once`, `causal_alo_converges` (needs `causal_alo` redelivery); `late_duplicate_diverges` shows the qualifier is needed | as above | open (medium) |

## 4. CRDT fragment

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Op-based, causal delivery: convergence of a compensation-free system | `compensation_free_exact` (causal condition iff op-based CRDT) composed with `causal_convergence_exact` | `cmrdt_SEC`, `causal_cmrdt_SEC` | Rules oracle certifies the compensation-free classification | - |
| State-based: convergence of merges | Not stated for the CvRDT model; the general exact theorems apply by instantiation (merges as events, identity repair) but no instance is proved | `cvrdt_SEC`, `cvrdt_absorbs_duplicates` (commutative, associative, idempotent join) | n/a | Not proved as an instance of `thm:monotone-cycles` (Fed remark says so). Minor. |
| Strictness of the inclusion | n/a | `witness_not_cmrdt`, `witness_leaves_valid_space`, `witness_causal_not_cmrdt` | n/a | - |

## 5. Stream processors

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Settled processors with the same received set agree | **None mechanized at stream level.** `stream_convergence` and `base_thm_convergence` assume CC1 on co-enabled pairs and CC2 at every state; the reachable-state iff (`jc_exact`) is not lifted through `prstep` | `stream_convergence`, `stream_order_independence`, `base_cor_quiescent` | n/a | open (small) |
| Infinite streams: eventual agreement | None; the naive claim is false (`base_thm_convergence_transient_counterexample`) | Agreement at settled times with equal received sets (`stream_agreement`) | n/a | design (a lagging processor need never agree) |

## 6. Acyclic federation: the repair normal form

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Single source (M1): unique federated repair normal form | **No iff.** Under the network hypotheses the normal form is unconditional: `frun_solves`, `solve_unique`, `order_independent`, `cat_thm_one_order_independent`, one round from any state `fed_lem_fed_termination`. Each hypothesis is shown needed only existentially: acyclicity `prop_cycle_necessary`, M1 `prop_m1_necessary` | M1 per morphism | M1, shared-only writes, source determinacy (`verifyEdge`) | The regime is defined by its hypotheses; "M1 is necessary" means "some M1-violating network fails", not an iff. Not an obstacle to the claim. |
| Multi-source (R1, R2) | **No iff**, same shape: `fed_lem_resolved_termination`; R1 `r1_necessary`, R2 `r2_necessary` | R1 and R2 per resolver | `verifyResolved`, every combination of valid source states | Decidability remark for R1, R2 is paper-only (Fed `rem:fed-mechanized`). |

## 7. Acyclic federation: event order

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Guarded (events at federally valid states, `FedMachine.Apply`): all trace-equivalent sequences converge from a valid consistent `s0` | C1 and C2 at witnesses reachable from `s0`: `fed_exact`, `fed_exact_full`, `acyclic_gc_iff`; as a rewrite system `fed_guarded_exact`; by paper label `fed_thm_fed_convergence_exact`, `fed_thm_resolved_convergence_exact` | Static C1 and C2: `static_c1_c2_gc`, `fed_permutations_converge`, `fed_thm_fed_convergence_guarded` | C1 and C2 (`verifyCrossOrder`, `verifyRepairedCC`) | Qualifier: static C1 not necessary (`naive_converse_fails`). A C2 converse quantifying over all valid starts is open (ROADMAP, lower value); the reachable-witness iff stands. Not oracle-certified (ROADMAP item 5). |
| Unguarded `G_Fed` (events may fire before compensation) | CC1 and CC2 of `G_Fed` on reachable states: `fed_grs_exact` (no per-edge form) | XU plus component CC: `grs_unique_nf`, `fed_thm_fed_convergence_corrected`; C1 and C2 do not suffice (`fed_grs_c1_c2_insufficient`) | No XU check; gsm's runtime is the guarded model | - (exact, but only in global form) |

## 8. Distributed model with propagation steps

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Acyclic: every interleaving of local events and propagation reaches one state once propagation completes | **None mechanized** | XU plus each registry's own CC: `propagation_flush`, `dist_interleavings_converge`; `xu_implies_c1_c2` | n/a (gsm's `FedMachine` is the synchronous model) | open (medium) |
| Cyclic (monotone or coordinated) | **None; not modeled** | none | n/a | open (large; ROADMAP lower value, coq/README "not extended to cycles") |

## 9. Monotone cycles: the repair normal form

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Unique repair normal form, finite height or ACC | Unconditional inside the regime: `cyc_N_lfp`, `cyc_N_unique`, `cyc_sweep_order_independent`, `kleene_lfp`, `lfp_unique`, `chaotic_reaches_lfp`, `chaotic_limit_unique`, `chaotic_acc_reaches_lfp`, `kleene_acc_lfp` | Monotone `Phi` (`fed_def_lattice_shared_cyclic_hyps`) | `verifyMonotone`, `verifyMonotoneVisited` (cover-step monotonicity over visited states) | - |
| Same on a complete lattice without ACC | Existence of the lfp is classical Knaster-Tarski: **paper only** (`thm:monotone-cycles` (a)). Mechanized: double-negated existence under ACC (`kleene_acc_lfp_nn`), the Kleene supremum when `Phi` preserves it (`kleene_sup_lfp`) | Continuity at the Kleene chain | n/a (finite lattices) | design (axiom-free gate excludes classical KT) |
| Finite reachability of the lfp by iteration | **No iff.** ACC below the lfp is sufficient (`chaotic_acc_reaches_lfp`); a continuous operator can have an lfp no iterate reaches (`kleene_sup_instance`); the Kleene formula fails without continuity (`fed_thm_monotone_cycles_kleene_formula_fails`); widening gives a bound, not a normal form (`widening_not_normal_form`) | ACC; finite height | `kleeneCap` from the lattice bound | open (small: the exact condition is strong normalization of productive updates from bottom) |
| Validity of the lfp | **No structural iff.** Valid at bottom is sufficient: `net_lfp_valid`, `net_Ncyc_correct`; needed in the sense that dropping it fails (`fed_thm_monotone_cycles_lfp_invalid`, where a valid non-least fixed point exists) | Every component valid with bottom shared values | A different sufficient check: image validity over visited states (`verifyMonotoneVisited`), plus a run-time panic on an invalid fixed point. gsm's own comment says its condition is "not part of the Coq lemmas" | open (small: prove gsm's visited-image condition sufficient, and state the exact one) |
| The paper's monotone repair inside the non-monotone engine (non-monotone `rho_Fed^J` of a sub-federation) | n/a | `fed_rem_convexity_corrected` (phase 1 and `Phi` monotone in locals) | n/a | - (`fed_rem_convexity_refuted` corrects the paper) |

## 10. Monotone cycles: event order

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| All trace-equivalent sequences converge from `s0` | GC at reachable federated states: `gc_iff`, `cyc_events_converge_iff`, `net_events_converge_iff`, `fed_thm_monotone_cycles_events_corrected` | C1cyc and C2cyc over a set containing every normal form's shared values: `cyc_check_gc`, `cyc_check_converges`, `cyc_check_gc_lfp` (image sets over valid sources suffice); read footprint `footprint_c1`; global variant `lfp_commute_gc` | Per-target C1 and C2 with image sets over every valid source state (`FedReport.Checks`, citing `cyc_check_gc_lfp`) | GC has no per-edge reduction; neither cheap condition is necessary. Not oracle-certified. |
| Multi-edge targets | Same GC | Per-edge C1 plus M1 compose: `multi_edge_c1`, `multi_edge_gc`, `multi_edge_converges`; M1 needed: `m1_necessary`; without M1, check every local part: `multi_edge_c1_free` | gsm checks C1 against the joint image of all incoming edges (C1cyc directly), not the per-edge route | - |
| Resolver targets on a cycle | Same GC | C1 over the resolver image `R`: `resolver_joint_c1`; per-source images insufficient: `resolver_edge_insufficient` | Joint image `R` over every combination of valid source states | - |

## 11. Non-monotone cycles, invertible transports

Model: the shared fiber is the group `G` acting on itself (regular action); edges are transports by
group elements.

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Does a consistent state exist (`H^0` non-empty) | The labeling is a coboundary (`H^1 = 0`): `section_iff_coboundary`; per fundamental cycle: `cycle_basis_criterion`, `sat_iff_trivial_holonomy`; single cycle: `fixed_point_iff_trivial_holonomy` | Trivial holonomy of each fundamental cycle of a spanning tree | `DiagnoseCycle` on one cycle (sound refuter on the regular action: `c15_regular_definitive`) | Regular action needed (`nonfree_holonomy_counterexample`). - |
| Coordination-free convergence to a unique normal form, given an authority root | `H^1 = 0` iff, for every root value, the root-driven implementation has a unique consistent state reached by every propagation order: `prop_minimal_qualified_iff` | as above | Not implemented: gsm has no root-driven coordination-free mode for cycles; a non-monotone cycle fails `Build` | - for the theory; gsm gap (holonomy-minimal plan "proposed, not implemented", `HOLONOMY-COORDINATION-DESIGN.md`) |
| Same, with no authority root (every edge a writer) | **None mechanized.** Only an instance: `copyback_without_authority` (trivial holonomy, two orders reach different consistent states) | none | n/a | open (small to medium: generalize the instance to any regular-action cycle with `\|G\| > 1`) |
| What must be coordinated, relative to a spanning tree | Exactly the unbalanced non-tree edges: `plan_exact`, `coordination_needed`; soundness `coordinated_sound`, `coordinated_unique_nf`; balance is static `balanced_any_section`; root dependence `root_choice_matters` | Coordinate all unbalanced edges | `CoordinationPlan` cuts a feedback edge set by DFS (every cycle, not only unbalanced ones) and names the authority; `BuildCoordinated` | gsm's plan is sound but not the holonomy-minimal one. |
| Event order under the coordination | **None mechanized** (the driving network is acyclic, so `fed_exact` should instantiate, but no theorem states it) | Root's own events commute: `coordinated_events_converge` | `BuildCoordinated` runs the acyclic C1 and C2 on the residual | open (small) |
| **Optimization:** minimum coordination over all trees and roots | The minimum deletion set with a feasible residual is the group feedback edge set number. That equality is definitional given `section_iff_coboundary` and `feasible`; no theorem links it to the plan model (tree, root, `C`). Mechanized pieces: `edge_disjoint_lower_bound`, `edge_disjoint_min`, `min_G_ge_min_image`, `theta_separation` (`S_3`: `min_G = 2 > 1 = min_{G^ab}`) | Unbalanced edges of any rooted tree: size at most `betti_number` | `CoordinationPlan` (upper bound, "not necessarily the minimum") | Complexity (NP-hard, FPT, planar) is cited. Plan-model link open (medium). |

## 12. Non-invertible transports

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Single cycle: does a consistent state exist | Loop composite has a fixed point: `thm_obstruction_general`, `sections_are_fixed_points`; "some seed reaches a fixed point": `thm_obstruction_reachable`, `reaches_fixed_iff_section` | Finite fiber: `g^N x0` fixed for some seed (`diagnose_bounded`, `diagnose_dichotomy`) | `DiagnoseCycle` | - |
| Reading the diagnostic | No section iff no seed reaches a fixed point: `c15_exact_refuter`; one seed is definitive only when fixed points are all-or-nothing (`c15_free_definitive`) | A settling seed proves existence: `c15_convergent_result_sound` | `DiagnoseCycle` tests one representative seed | gsm's one-seed result is not a refuter off the regular action (`c15_definitive_claim_false`); documented. |
| Graph with an out-arborescence from a root: consistent state with a given root value | Driven state satisfies every non-tree edge: `rooted_criterion`; uniqueness `out_tree_unique` | Delete every non-tree edge: `rooted_coordination_suffices` | n/a | Edge need depends on the root value (`noninvertible_balance_not_static`). |
| General graph (no out-arborescence, several cycles) | **None mechanized; none known.** A tree with no cycles can lack a section (`c22_cycle_basis_fails`) | none | n/a | open (large; the Cat paper's conclusion lists "a cohomological account of the non-invertible case" as open) |
| Uniqueness and event order with non-invertible coordination | **None mechanized** | none | n/a | open |
| **Optimization:** minimum coordination | **None known**; "the minimum is not a cohomological rank" (Cat section 8) | `rooted_coordination_suffices` (upper bound) | n/a | open |

## 13. The full nerve as a 2-complex

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Convergence (existence of a section) | Decided on the graph: `section_iff_coboundary` covers every labeled graph, so triangles add no convergence question | n/a | n/a | - |
| **Counting:** rank of `H^1` with triangle relations | **None mechanized.** On the 1-skeleton: `H1_classification`, `gauge_fix`, `betti_number` (`\|E\| - \|V\| + 1`) | n/a | n/a | paper (Cat section 6) and open (Cat conclusion: "the classification on the full 2-dimensional nerve") |
| Sheaf gluing (R1/R2 as the gluing axiom, positive assembly) | **None mechanized**; the negative half is `gluing_order_dependent` | n/a | n/a | paper (Cat `prop:gluing`, section 5) |

## 14. Compositional collapse

| Question | Exact (N and S) | Cheap sufficient, and the link | gsm | Gap |
|---|---|---|---|---|
| Acyclic, convex `J`: the effective registry converges | C1 and C2 at witnesses reachable inside `J`: `collapse_a_guarded_exact` | C1 and C2 on `J`'s events: `collapse_a_guarded`, `collapse_modular_converges` | `Federation.Embed`, certificates (`validateCertificates`, seam re-check) | - |
| Acyclic: outer network `N'` converges iff `N` does | `collapse_c_exact`, `collapse_c_guarded_iff`, `collapse_c_unguarded_iff`, `collapse_c_guarded_exact` | `collapse_c_guarded_c1_c2` | as above | - |
| Cyclic `J` with monotone repair | **None mechanized** | none | gsm flattens embedded cyclic subs (the outer federation must opt in to `AllowMonotoneCycles`), so its check does not rely on a collapse theorem | paper (Fed, after `thm:collapse`: "not covered by the mechanization") |

## Conclusion

### Is "complete" accurate?

No. Read against convergence questions only, the development leaves regimes it itself models without
a mechanized exact condition, and two regimes are modeled only on paper or not at all:

| Breaks "complete" | Regime and question | Kind |
|---|---|---|
| 1 | At-least-once delivery, free and causal: absorption of duplicates (section 3) | convergence, open |
| 2 | Distributed model with explicit propagation: acyclic has only a sufficient condition; cyclic is not modeled (section 8) | convergence, open |
| 3 | Cyclic networks outside the two covered cyclic regimes: rootless propagation on invertible cycles (one instance only), and non-invertible graphs without an out-arborescence (sections 11, 12) | convergence, open (the Cat paper lists the non-invertible case as open) |
| 4 | Cyclic monotone sub-federations under collapse (section 14) | convergence, paper only |
| 5 | Monotone cycles on complete lattices without ACC: existence of the lfp (section 9) | convergence, paper only (classical, outside the axiom-free gate) |
| 6 | Sheaf gluing and the 2-complex rank (section 13) | not convergence; paper only |

Items 1 to 5 are about convergence. Item 6 is structure and counting; it does not bear on "when
state converges", but it does bear on "mechanized".

### Is "exact conditions in every regime" accurate?

No. These regimes have a mechanized sufficient condition (or none) and no mechanized iff for a
convergence question; rows e to h restate items 1 to 4 above, and item 5 is the design exclusion of
section 9:

| Breaks "exact" | Regime and question | Size of the fix |
|---|---|---|
| a | Single registry with an ordinal or lexicographic WFC potential (exact converses are `nat`-potential only) | small |
| b | Stream processors at stream level (the rewrite-system iff is not lifted) | small |
| c | Event order under a coordinated non-monotone cycle | small |
| d | Monotone cycles: validity of the least fixed point, and finite reachability of it | small |
| e | At-least-once delivery (item 1) | medium |
| f | Distributed propagation model, acyclic (item 2) | medium |
| g | Cyclic monotone collapse (item 4) | medium to large |
| h | Rootless or non-invertible cyclic propagation (item 3) | small (rootless invertible) to large (non-invertible graphs) |

The option "exact conditions in every regime it covers" does not rescue the sentence: a, b, c, d, e
and f are regimes the development does cover (`GovernanceWF.v`, `Stream.v`, `CoordinatedCycles.v`,
`MonotoneFederation.v`, `AtLeastOnce.v`, `FederationEvents.v`), with sufficient conditions only.

Where the claim does hold: single registry (free delivery with canonical repair, and causal or
guarded enabledness that persists under repair), causal replay, the op-based CRDT fragment, acyclic
federations (guarded event order per edge at reachable witnesses; unguarded in global form),
event order on monotone cycles (GC), existence of a consistent state on invertible cycles
(`H^1 = 0`), root-driven coordination-free convergence on invertible cycles, the coordinated set
relative to a tree, the single-cycle non-invertible obstruction, and acyclic collapse. That is the
core of the theory, and it is exact.

### Optimization and counting gaps

They do not affect the convergence claim. The minimum coordination on invertible cycles is the group
feedback edge set number by definition once `section_iff_coboundary` holds, but no theorem ties it to
the authority-root plan model, its complexity is cited, and on non-invertible networks the minimum
is unknown. The rank of `H^1` on the 2-complex is unmechanized and listed open. A reader who takes
"map" to include "how little coordination suffices" (as the README's Federations paragraph does)
should see these listed; the headline's subject, when state converges, is not affected.

### "A checker for the practical ones"

Accurate as worded, with two qualifications. gsm checks the cheap sufficient conditions (CC with
declared pairs, `NotIdempotent`, M1, R1/R2, C1 and C2 on acyclic and monotone-cyclic networks with
joint images, monotonicity and image validity over visited states); it checks none of the exact
reachable-state conditions (JC, CCR, GC), which is the stated design. Only the single-registry
result is oracle-certified; the federation checks are Go code (ROADMAP item 5), and gsm's
lfp-validity condition is not the one Coq proves sufficient (section 9).

### Proposed wording

Strongest accurate replacement, same register, naming the exact core:

> **A mechanized map of when governed concurrent state converges: exact conditions for single
> registries, acyclic federations and event order on monotone cycles, sufficient conditions and a
> computed coordination beyond them, and a checker for the practical ones.**

Shorter, if naming the core is too long:

> **A mechanized map of when governed concurrent state converges, exact across the core regimes and
> sufficient at the edges, with a checker for the practical ones.**

Both drop "complete". The first is the more precise: "single registries" there means exactly-once
or causal delivery (at-least-once is in "beyond"), and "monotone cycles" claims exactness for event
order only, not for validity of the least fixed point.

### Mechanization tasks that would make the original wording accurate

Convergence (needed for "exact conditions in every regime"):

1. **Exact converses over any well-founded potential**: `cc_exact_from` and `jc_exact` restated on
   `GovernanceWF.v`'s lexicographic termination. Small.
2. **Stream-level exact condition**: lift `jc_exact` (or `cc_exact_from`) through `prstep` to
   settled processors. Small.
3. **Event order under coordination, exact**: instantiate `fed_exact` on the driving network of
   `CoordinatedCycles.v`. Small.
4. **Monotone cycles, exact validity and reachability**: the iff for validity of the lfp, a theorem
   that gsm's visited-image validity check is sufficient, and finite reachability iff strong
   normalization of productive updates from bottom. Small.
5. **Rootless invertible cycles**: generalize `copyback_without_authority` to every regular-action
   cycle with `|G| > 1` (no authority, no unique propagation normal form). Small to medium.
6. **At-least-once exact converse**: absorption iff, at reachable states and for each redelivery
   position, the duplicate is idempotent and commutes with the events between its copies; free and
   causal forms. Medium.
7. **Distributed propagation model, acyclic exact converse**: the reachable-witness iff for
   `dist_interleavings_converge`. Medium.
8. **Cyclic monotone collapse**: `thm:collapse` (a), (a'), (c) with `thm:monotone-cycles` in place
   of the acyclic lemmas. Medium to large.
9. **Distributed propagation model on monotone cycles**: model and exact condition. Large.
10. **Non-invertible graphs**: an exact section criterion without an out-arborescence, and uniqueness
    under non-invertible coordination. Large (open in the Cat paper).
11. **Complete lattices without ACC**: classical Knaster-Tarski existence. Large, and in tension with
    the axiom-free gate; the alternative is to state the constructive scope (ACC or continuity) as a
    design exclusion.

For "complete" in the wider sense (optimization, counting, structure):

12. **Minimum coordination linked to the plan model**: some rooted tree attains the group feedback
    edge set number, or a counterexample. Medium.
13. **Non-invertible minimum coordination**. Large (open).
14. **Rank of `H^1` on the 2-complex**. Large (open).
15. **Sheaf gluing, positive assembly** (Cat `prop:gluing`, after reformulation). Large.

## Side findings (documentation drift)

Not part of the claim, found while auditing:

- `ROADMAP.md` still reports a 254-theorem gate and lists items 6 and 7 as open; item 6 landed
  (`FederationEventsCyclesCheck.v`, #31) and item 7's work packages WP1 to WP9 landed (#32 to #42).
- `REGIMES.md`, federation table: "Cyclic, non-monotone, coordination-free: no condition suffices"
  is contradicted by `c13_two_ways_not_exhaustive` (trivial-holonomy and non-free cycles have
  sections); the monotone row omits "valid at bottom"; "Compositional collapse ... (paper)" is now
  mechanized (`Collapse.v`); the acyclic row cites the refuted `thm:fed-convergence` without C1
  and C2.
- `coq/README.md`: the gate paragraph (lines 27 to 46) says "all 327 headline results" while the
  gate passes 729, and repeats a sentence fragment; the categorical-layer roadmap says the
  non-invertible case "is not mechanized", but `CohomologyGeneral.v` now mechanizes its single-cycle
  and rooted forms.
- The Cat paper's conclusion lists the input-port refinement as not mechanized; `Collapse.v`
  mechanizes it (`port_c1_transfer`, `port_c2_transfer`, `port_interior_certificate`).
