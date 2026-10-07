# Regime coverage matrix

[REGIME-AUDIT.md](../REGIME-AUDIT.md) certifies the headline regime by regime: every row is exact,
hardness-backed, or a numbered gap. That claim is complete relative to the rows the audit lists.
This page tests it from the other side. It derives the regime space from the model's own axes (the
hypotheses that vary across the Coq theorems and the audit's vocabulary), maps every meaningful
combination to the audit, and lists what no row covered. It adds no proofs and changes no
existing gap's status. The pass ran at `main` `d24d26d` (gate: 2241 axiom-free results) and gsm
`main` `0f094f1`; the page has been kept current since, through #98, the closing of gap 15 and of gap 16 (d), the narrowing of gap 20 (gate: 2693), and the closing of gap 5 and narrowing of gap 19 (gate: 3513).

Results, in one paragraph. Thirteen axes vary in the source. Of the 179 cells of the matrix below
(section 3), 58 are covered (54 by an exact theorem, 4 more by an exact theorem together with a
mechanized hardness reduction; no cell rests on a sufficient-only theorem without a gap that owns
its converse), 12 are excluded (9 by a design exclusion or a counterexample, 3 as out of scope),
19 are open under existing gaps (3, 5, 13) or a ROADMAP item, 55 are degenerate (they collapse
into a named representative cell), 14 are ill-formed, and 21 had no row at all. The 21 uncovered
cells are 12 distinct questions, proposed as gaps 15 to 19. Outside the axes, seven candidate
dimensions are not represented in the model at all (section 4): two become gaps 20 and 21 (new
axes), five become explicit design exclusions X1 to X5, and the rest map onto existing cells or
stated limits. Four further candidates were added after the pass (section 4: observation before convergence, irreversible external effects, compaction, nondeterministic events), each with its disposition pending. Since the pass, gap 15 has closed: cell C10 (15 (a)) is exact
(`AtLeastOnceDeclared.v`, `dalo_exact`), and so are C8 streams (15 (b), `StreamAtLeastOnce.v`,
`stream_alo_exact_free`), C3 and C8 distributed (15 (c), `DistributedDelivery.v`,
`dist_causal_exact`, `dist_alo_exact`) and C6 rewrite (15 (d), `FederatedGuards.v`,
`fed_buffered_exact`); A2's fair-schedule cell (16 (d), `RobertFair.v`, `rb_robert_fair`) is exact
too; the counts in section 3 include these changes. The new axis of gap 21 (propagation
over channels) is now modeled (`ProjectionChannels.v`) and partly covered: acyclic networks are
exact in reachable form, two-level networks in the current-value form, and the residue is listed
under gap 21 (section 4; the counts in section 3, which are cells of the axes, do not change).
The new axis of gap 20 (reconfiguration inside a run) is modeled too (`Reconfiguration.v`) and
partly covered: for a single registry under free delivery and for federations under FedMachine
semantics, a change at a quiescent barrier and a live change with events in flight are exact
(`barrier_exact`, `live_exact`, `fed_barrier_exact`, `fed_live_exact`), and in the deterministic
model the barrier's A part for a migration that is not faithful has a local, finite exact form
(`ReconfigurationClosure.v`: `amodm_closure_exact`, `det_classify_complete`); the residue is listed
under gap 20 (section 4; again the counts in section 3 do not change). Gap 5 is closed and gap 19
narrowed by `CompositionBlocks.v`: A14's normalizer and asynchronous cells, B11's distributed cell,
B12's replay cell and B13's replay cell are exact (`compose_exact`, `compose_collapse`,
`dist_collapse_iff`, `mono_collapse_exact`), B12's rewrite cell is degenerate (B3's, gap 16 (c)),
and B12's distributed cells are open under gap 19 (b), whose residue is a cyclic block in the
distributed model; the counts in section 3 include these changes.

How to read the statuses:

- **exact**: a mechanized necessary-and-sufficient theorem, or an unconditional result inside the
  regime, named in the cell. **exact + hardness**: the same, with a mechanized hardness reduction.
  **sufficient**: only a sufficient theorem, with no gap that owns the converse (none occur).
- **excluded (design)**: a stated design exclusion or a counterexample that refutes the naive
  question (gaps 8 and 9). **excluded (scope)**: outside the stated scope or a stated fundamental
  limit ([ROADMAP.md, Fundamental limits](ROADMAP.md#fundamental-limits-stated-not-removable)).
- **open (gap N)**: an existing numbered gap owns the cell, or a ROADMAP lower-value item.
- **degenerate**: the cell collapses into another one by an axis dependence (section 2); the
  representative is named.
- **ill-formed**: the combination has no meaning; the reason is given.
- **uncovered**: no row, no exclusion, no gap; now proposed as the gap named in the cell.

A cell counts as covered only if a specific theorem or a specific scope sentence covers it. A
generic theorem (one stated for any step function or any group) covers its instances.

## 1. Axis inventory

Derived from the section variables and hypotheses of the Coq modules and the audit's vocabulary,
not from the brief's guesses.

| # | Axis | Values | Source |
|---|---|---|---|
| 1 | Composition (topology) | single registry; acyclic federation (tree with M1; resolved, R1 and R2); cyclic | `src : nat -> list nat` with a topological order `o` (`FederationEvents.v` `Common`, `FederationGRS.v` `Hrange`); cyclic modules drop `o` (`DistributedCycles.v`, `FederationEventsCycles.v`); REGIMES.md "execution semantics first, topology second" |
| 2 | Transport class | monotone on a lattice; invertible, regular action; invertible, non-free action; arbitrary (lossy) maps; resolvers with a sign structure | `f_mono`, `u_mono` (`Federation.v`, `DistributedCycles.v`); group `op e inv` acting on itself (`CohomologyGraph.v`, `RootlessNetworks.v` header); `nonfree_holonomy_counterexample`; `@edge (V -> V)` (`CohomologyGeneral.v` `msection`, `RootSet.v`); `Resp` (`SignedResolver.v`), Boolean `Fv` (`LocalSigned.v`) |
| 3 | Writer semantics | per-target merge of all sources (reading B: morphism or resolver); every edge a writer (reading A dynamics); single-writer or multi-writer variables | `f j t x` and R1 (`FederationEvents.v`); `fire1` (`RootlessNetworks.v`); [LOSSY-NETWORKS.md](LOSSY-NETWORKS.md) "Reading A", "Reading B"; the variable-level site of gap 13 (`SheafGluing.v` header) |
| 4 | Authority | authority root (out-arborescence); root set (outward forest, pinned values); coordination plan (cut edges); de facto roots and co-rooted components; rootless | `tree r T` (`CoordinatedCycles.v`), `oforest R F` (`RootSet.v`), `de_facto_root`, `co_rooted`, `authority_cover` (`RootlessNetworks.v`) |
| 5 | Execution model | rewrite system (events and compensation steps interleave over a buffer); governed-step replay (an event, then repair to the normal form; a run is a word); stream processors; repair only, as a normalizer; repair only, as asynchronous schedules; events with propagation as separate steps (distributed); driving from roots; collapse; static (existence of a consistent state, no dynamics) | `Governance.v` `step`, `FederationGRS.v` (unguarded `G_Fed`); `CausalReplay.v` `step`, `AtLeastOnceExact.v` `step`, `FederationEventsCycles.v` `gstep := Nf (ev e s)`; `Stream.v` `processor`; `frun`, `kleene_lfp`; `Chaotic.v`, `fire`, resolver updates; `DistributedExact.v`, `DistributedCycles.v`; `CoordinatedCycles.v`, `RootSetEvents.v`; `Collapse.v`; `is_section`, `msection` |
| 6 | Schedule and reset | some word (existential); every fair schedule; synchronous; every schedule; reset epochs (barrier) or none | `FlushR`, `richard_t3` vs `Fair`, `FairFlushR`; `sync_simple`; `chaotic_sn_strictly_stronger`; the flag `r : bool` (`DistributedCyclesExact.v`) |
| 7 | Delivery | exactly-once, any order; exactly-once, trace-equivalent under declared independence `I`; causal; at-least-once, free or causal; unordered merges with duplication; incremental finite received sets; infinite streams | `Permutation`; `tequiv` and `I : E -> E -> Prop` (`Trace.v`; gsm `Independent`); `hb` (`CausalReplay.v`); `Ev`, `hb` (`AtLeastOnceExact.v`); `act` (`CvRDTExact.v`); `Stream.v`; `base_thm_convergence_transient_counterexample` |
| 8 | Enabledness | free; guarded or causal, persisting under compensation; disableable by compensation; the federal guard (events only at federally valid states) or none | `enabled`, `enabled_after_comp` (`Governance.v`); `EnabledAfterComp.v`; `en` and `genab` (`FederationGRS.v`) |
| 9 | State and order | finite or `nat` potential; well-founded potential in any order; non-terminating compensation; finite-height lattice; ACC lattice without a rank; complete lattice without ACC; any group; finite fiber with decidable equality; Boolean; bounded finite-height value set; unbounded value set | `Phi : State -> nat`; `ltP`, `wf_ltP` (`GovernanceWF.v`); `terminating_iff_comp_wf`; `rank_bound`; `ole_no_rank` (`ChaoticACC.v`); gap 8; `CohomologyGraph.v`; `root_set_decide`, `lmin_decide`; `LocalSigned.v`; `SignedResolver.v` (`rX_bound`, `botX`, `topX`) |
| 10 | Start quantification | one start `s0`, conditions at reachable states; every valid start; every consistent start; restricted starts (low, sound, at most two unstable vertices) | `cc_exact_from` vs `cc_exact_global`; `dist_exact`, `dist_exact_global`, `dist_exact_consistent`; `signed_settlement`, `q1_sound_iff`, `two_token_fair_settlement` |
| 11 | Reference state | the system's own unique normal form; the FedMachine's least fixed point; the state propagation settles in, ghost allowed; a section given root values; a constant canonicalizer | `DAgreeQ`, `NoGhostR`; `conv_quiet_exact`; `out_forest_unique`; `signed_settlement` |
| 12 | Property | existence; termination; unique repair normal form (settlement, fidelity); event-order convergence; agreement with a reference; validity of the canonical state; finite reachability; per-event deduplication; minimum coordination; counting; gluing; collapse preservation | the audit's three kinds of question; [THEORY.md, The four questions](THEORY.md#the-four-questions) |
| 13 | Network size | finite (constant across the development) | every network is a finite list (`js`, `o`, edge lists) |

### Compared with the brief's proposed axes

The brief proposed seven axes (delivery, topology, authority, execution model, enabledness, state,
property). Both directions:

- **In the brief, not axes or values of the source.** "Unordered" delivery is free delivery (or the
  merge model). "Causal" enabledness is not a value of its own: dependency-based enabledness is an
  `enabled` predicate (`paper_causal_governance_unique_normal_forms`), so it falls under guarded
  enabledness. "Infinite" state is not a value: the source splits it into a well-founded potential
  (`wf_cc_exact_from`) and termination itself (`terminating_iff_comp_wf`). "Fair settlement" is not
  a property: it is settlement (axis 12) under fair schedules (axis 6). The brief's topology values
  mix two axes (topology, axis 1, and transport class, axis 2), and "FedMachine/synchronous" mixes
  two values: the FedMachine is governed-step replay, while synchronous update is a schedule of
  the resolver dynamics (`sync_simple`).
- **In the source, not in the brief.** Writer semantics (axis 3), schedule and reset (axis 6), start
  quantification (axis 10), reference state (axis 11), declared independence `I` (a delivery
  value), the federal guard (an enabledness value), regular versus non-free group actions (a
  transport value), the rewrite-system versus replay split (an execution value), coordination by
  cut edges (an authority value), single- versus multi-writer variables, and network size
  (constant: finite).

## 2. Axis dependences used to prune

The product of the axes is not the regime space: several axes collapse others. Each dependence
below marks cells **degenerate** and names the representative.

- **P1. Generic step.** `causal_exact`, `alo_exact`, `causal_alo_exact`, `safe_free_exact`,
  `merge_action_exact` and `gc_iff` are stated for any step function `step : E -> S -> S` (`gc_iff`
  for any `Nf (ev e s)` with any declared `I`). Every execution model whose run is a word of a
  deterministic governed step (the FedMachine, a coordinated or root-set driving network, a
  collapsed network) inherits the delivery cells of the replay model by instantiation.
- **P2. Authority collapses off non-monotone cycles.** On acyclic networks the sources are de facto
  roots and the normal form is unconditional (`frun_solves`, `solve_unique`); on monotone cycles
  the least fixed point is the canonical state, whatever the authority
  ([THEORY.md, Two engines](THEORY.md#two-engines)). Authority varies only on non-monotone cycles.
- **P3. Coordination makes the network acyclic.** A coordination plan or a root-set forest drives
  values along a tree or forest; coordinated edges are removed, balanced ones become checks, not
  writers (`CoordinatedCycles.v`; C1 holds unconditionally on the driving network,
  `coordinated_c1_static`, `forest_c1_static`). Every execution model on a coordinated network is
  the acyclic one on its driving network.
- **P4. The readings coincide at in-degree at most one** ([LOSSY-NETWORKS.md, How the readings
  relate](LOSSY-NETWORKS.md#how-the-readings-relate)). On single cycles and trees the edge-writer
  and resolver dynamics are one cell.
- **P5. Invertible maps are arbitrary maps.** `RootSet.v`, `LossyHardness.v`, `RootSetEvents.v` and
  `LossyMinimum.v` take any maps `V -> V`, so non-free invertible actions, and networks that mix
  invertible and lossy edges, are instances of the lossy rows for existence, counting, driven event
  order and minimum coordination. Only the rootless dynamics is specific to the regular action.
- **P6. Balance reduces signed resolvers to monotone ones** (`switched_monotone`).
- **P7. Acyclic propagation forgets stale shared values.** A flush recomputes every target from its
  sources (`propagation_flush`), so a reset barrier changes nothing on an acyclic network.
- **P8. A rootless invertible network with a unique normal form is authority-rooted**
  (`net_unique_normal_form_iff`, `authority_cover_iff`), so its replay cells are the coordinated
  ones; without uniqueness the repair layer already fails (`net_unique_iff`,
  `copyback_without_authority`).
- **P9. Flattening.** A collapsed acyclic network has the same runs as the flattened one
  (`collapse_c_runs_agree`), and gsm flattens embedded sub-federations.
- **P10. Streams never act at invalid states.** A stream processor normalizes before every event,
  so its state-peak class is empty (`stream_state_peaks_empty`) and compensation-disabled
  enabledness has nothing to disable.

## 3. The matrix

Rows are grouped; each row is a combination of the axes it names, and each cell one question.
Reference row IDs (A1, B3, ...) are used for degenerate cells.

### 3.1 Repair layer (no events): existence and settlement

Columns: existence of a consistent state (static); repair as a normalizer; asynchronous repair,
some word; asynchronous repair, every fair schedule.

| Row | Composition, transport, authority, writers | Existence | Normalizer | Async, some word | Async, every fair schedule |
|---|---|---|---|---|---|
| A1 | Single registry | **exact**: termination iff compensation is well-founded (`terminating_iff_comp_wf`, `comp_wf_iff_wfc`) | **degenerate**: A1 existence (one deterministic compensation chain) | **ill-formed**: one registry has one compensation chain, no schedule | **ill-formed**: as before |
| A2 | Acyclic, reading B (M1 trees, R1 and R2 resolvers) | **exact**: unconditional (`frun_solves`; each hypothesis needed, `prop_cycle_necessary`, `prop_m1_necessary`, `r1_necessary`, `r2_necessary`) | **exact**: unconditional (`solve_unique`, `fed_lem_fed_termination`, `fed_lem_resolved_termination`) | **exact**: every topological order (`order_independent`) | **exact**: unconditional, every fair schedule from every valid start settles at the run of one topological order (`rb_robert_fair`, bound `rb_rounds`, `rb_effective`; resolver model `rb_lens_robert`, Boolean `rb_robert_boolean`); acyclicity needed (`rb_dist_cycle_needed`, `rb_neg2_cycle`); gap 16 (d), closed |
| A3 | Acyclic, reading A (edges as equations), in-degree two or more | **exact**: root-set criterion with the sources as root set (`root_set_criterion_graph`); a tree can fail (`c22_cycle_basis_fails`) | **degenerate**: A10 normalizer (the sources are a root set, P2) | **uncovered**: edge-writer dynamics on lossy merges; gap 17 | **uncovered**: as before; gap 17 |
| A4 | Monotone cycles, finite height or ACC, any authority (P2) | **exact**: `kleene_lfp`, `lfp_unique`, `kleene_acc_lfp`; validity `lfp_valid_iff_reached` | **exact**: `kleene_reach_exact`, `cyc_N_lfp` | **exact**: `chaotic_reach_exact`, `chaotic_reaches_lfp` | **exact**: from any stale start `q1_sound_iff`, `q1_unique_iff` |
| A5 | Monotone, complete lattice without ACC | **excluded (design)**: gap 8 | **excluded (design)**: gap 8 | **excluded (design)**: gap 8 | **degenerate**: A5 async (gap 8) |
| A6 | Invertible, regular action, authority root or coordination plan | **exact**: `section_iff_coboundary`, `cycle_basis_criterion` | **exact**: `prop_minimal_qualified_iff`, `coordinated_sound`, `plan_exact` | **degenerate**: A2 on the driving tree (P3) | **degenerate**: A2 (P3) |
| A7 | Invertible, regular action, rootless, every edge a writer | **exact**: `section_iff_coboundary`, `net_nf_from_iff` | **ill-formed**: no canonical normalizer without an authority; the question is the dynamics | **exact**: `net_reachable_iff`, `net_nf_exists_iff`, `net_unique_iff` | **exact**: `net_reachable_fair_iff`, `net_unique_fair_iff`, `net_unique_normal_form_iff` |
| A8 | Invertible, non-free action | **degenerate**: A10 existence (P5); the cohomological criterion stops here (`nonfree_holonomy_counterexample`) | **degenerate**: A10 normalizer (P5) | **uncovered**: rootless edge-writer dynamics off the regular action; gap 17 | **uncovered**: as before; gap 17 |
| A9 | Lossy, authority root or root set | **exact + hardness**: `rooted_criterion`, `root_set_criterion_graph`; 3-SAT reduction `net_section_iff_sat`, `net_size`, `np_certificate` | **exact**: driven state unique given root values (`out_forest_unique`, `root_set_bijection`) | **degenerate**: A2 on the driving forest (P3) | **degenerate**: A2 (P3) |
| A10 | Lossy, rootless, every edge a writer, in-degree two or more | **degenerate**: A9 existence (quiescent states of the edge-writer dynamics are reading-A sections by definition) | **ill-formed**: no canonical normalizer without an authority | **uncovered**: gap 17 | **uncovered**: gap 17 |
| A11 | Lossy, rootless, resolver reading B, in-degree two or more | **uncovered**: no row for fixed points of the resolver map without a spanning root; the reductions between the readings are conjectures (LOSSY-NETWORKS.md section 1); gap 18 | **ill-formed**: as A10 | **open (gap 3)**: sufficient `richard_t3`, `richard_t4`, `shih_dong_E` | **open (gap 3)**: sufficient `signed_settlement`, `signed_fidelity`, `one_token_fair_settlement`, `two_token_fair_settlement`; synchronous `sync_simple` |
| A12 | Lossy, single cycle (in-degree one, P4) | **exact**: `thm_obstruction_general`, `thm_obstruction_reachable`, `c15_exact_refuter` | **degenerate**: A9 (a root on the cycle) | **open (gap 3)**: the rootless resolver row includes cycles | **open (gap 3)** |
| A13 | Signed resolvers with a balanced global graph | **degenerate**: A4 after switching (P6) | **degenerate**: A4 (P6) | **open (gap 3)**: sufficient `signed_settlement` | **open (gap 3)**: sufficient `signed_settlement`, `signed_fidelity` |
| A14 | Mixed engines in one network, coordination-free | **degenerate**: A9 existence on one sum fiber (P5) | **exact**: monotone blocks, blockwise least fixed points (`bekic_lfp`, `mono_collapse_nf`; gap 5, closed); any engines, the normal form is the block-by-block one under `compose_exact`'s conjuncts (`compose_collapse`) | **exact**: `compose_exact` (each conjunct needed, `compose_isolated_refuted`, `mixed_ghost_refuted`), engines `mixed_rootless_exact`, `mixed_mono_iff`; interface closed under composition `interface_closed`; gap 19 (a), closed | **degenerate**: A14 async, some word |

Notes. Within one strongly connected block a mixture of edge kinds is simply the most general
class present (a cycle with one negation edge is non-monotone), so it falls to A7, A8, A10 or A11.
Mixing happens across blocks, and that needs a composition argument (A14). A14's fair cell is
marked degenerate to keep the uncovered count to distinct questions.

### 3.2 Event layer: event-order convergence (and agreement where stated)

Columns: rewrite system (events may fire before repair completes); governed replay (repair to the
normal form after each event; the FedMachine); distributed, no reset; distributed, barrier
epochs.

| Row | Composition, transport, authority | Rewrite system | Governed replay | Distributed, no reset | Distributed, epochs |
|---|---|---|---|---|---|
| B1 | Single registry | **exact**: `cc_exact_from`, `jc_exact`, `jcg_exact` | **exact**: `causal_exact` (empty `hb`), `gc_iff` (one registry) | **ill-formed**: one registry has no propagation step | **ill-formed**: as before |
| B2 | Acyclic | **exact**: `fed_grs_exact`, `fed_guarded_exact` | **exact**: `fed_exact`, `fed_exact_full` | **exact**: `dist_exact`, `dist_exact_global`, `dist_exact_consistent`, `dist_global_exact_roots`; limits of fair schedules with finitely many events `rb_fair_dist_exact` | **degenerate**: B2 distributed (P7) |
| B3 | Monotone cycles, finite height | **uncovered**: `G_Fed` with local compensation as separate steps is acyclic only (`FederationGRS.v` uses a topological order); gap 16 (c) | **exact**: `gc_iff`, `net_events_converge_iff` | **exact**: `flush_fed_iff`, `fair_fed_iff`; convergence alone `conv_quiet_exact` | **exact**: `epoch_agree_iff`, `epoch_conv_iff` |
| B4 | Monotone cycles, ACC without a rank | **degenerate**: B3 rewrite (gap 16 (c)) | **exact**: `gc_iff` (any normalizer) with `kleene_acc_lfp` | **uncovered**: every distributed module assumes finite height (`rank_bound`); gap 16 (b) | **uncovered**: gap 16 (b) |
| B5 | Monotone, complete lattice without ACC | **excluded (design)**: gap 8 | **excluded (design)**: gap 8 | **excluded (design)**: gap 8 | **degenerate**: B5 distributed (gap 8) |
| B6 | Invertible, coordination plan or authority root | **degenerate**: B2 on the driving network (P3) | **exact**: `coordinated_events_exact`, `coordinated_events_exact_global` | **degenerate**: B2 (P3) | **degenerate**: B2 (P3) |
| B7 | Invertible, rootless, unique normal form (authority cover) | **degenerate**: B7 distributed (repair steps are edge firings, so the rewrite system is the propagation model) | **degenerate**: B6 (P8) | **uncovered**: events interleaved with rootless propagation on a cyclic invertible network; no distributed model off monotone cycles; gap 16 (a) | **ill-formed**: a reset epoch needs a bottom element, which a group fiber lacks |
| B8 | Invertible, rootless, no unique normal form | **excluded (design)**: the repair layer already diverges (`copyback_without_authority`, `rootless_two_orders`; `net_unique_iff`) | **degenerate**: B8 rewrite | **degenerate**: B8 rewrite | **ill-formed**: as B7 |
| B9 | Lossy, root-set coordination | **degenerate**: B2 on the driving forest (P3) | **exact**: `forest_events_exact`, `forest_events_exact_global` | **degenerate**: B2 (P3) | **degenerate**: B2 (P3) |
| B10 | Lossy, rootless | **open (gap 3)**: the repair layer is open (A11; for edge writers, gap 17) | **open (gap 3)** | **open (gap 3)** | **open (gap 3)** |
| B11 | Collapse of an acyclic convex block | **exact**: `collapse_c_unguarded_iff` | **exact**: `collapse_c_exact`, `collapse_a_guarded_exact` | **exact**: `dist_collapse_iff` (`N` converges iff `N'` does and XU holds at every state `N` reaches), `dist_collapse_exact`; the plain statement fails (`dist_collapse_refuted`); gap 19 (b), closed for an acyclic block | **degenerate**: B11 distributed |
| B12 | Collapse of a monotone cyclic block | **degenerate**: B3 rewrite (gap 16 (c)) | **exact**: `mono_collapse_converges_iff`, `mono_collapse_exact` (gap 5, closed) | **open (gap 19 (b))**: the flattened network is B3; collapse with `J`'s propagation as one step is not stated on cycles | **open (gap 19 (b))**: as before, with reset epochs |
| B13 | Collapse of a non-monotone cyclic block | **degenerate**: B13 replay | **exact**: the composite's normal form is the block-by-block one exactly under `compose_exact`'s conjuncts (`compose_collapse`), and event order is `gc_iff` for that normalizer; gap 19 (a), closed | **degenerate**: B13 replay | **degenerate**: B13 replay |

### 3.3 Delivery and enabledness, by execution model

Columns: single-registry rewrite system; governed replay (one registry, or a network's governed
step by P1); stream processors; distributed propagation.

| Row | Delivery or enabledness | Rewrite system | Governed replay | Streams | Distributed |
|---|---|---|---|---|---|
| C1 | Exactly-once, any order | **exact**: `cc_exact_from`, `canonical_cc_exact_from` | **exact**: `causal_exact` (empty `hb`), `causal_convergence_exact`; `gc_iff` with total `I` | **exact**: `stream_exact_free` | **exact**: `dist_exact` |
| C2 | Exactly-once, declared independence `I` | **degenerate**: C4 rewrite (an ordering constraint on a buffer is an enabledness predicate) | **exact**: `gc_iff` (any `I`); per edge on acyclic networks `fed_exact` | **degenerate**: C4 streams (`stream_exact`, any enabledness) | **exact**: `dist_exact` (federated trace equivalence) |
| C3 | Causal | **degenerate**: C4 rewrite (dependency-based enabledness, `paper_causal_governance_unique_normal_forms`) | **exact**: `causal_exact` (any step, P1) | **degenerate**: C4 streams | **exact**: `dist_causal_exact` (XU at causally reachable states plus CCR on the FedMachine), an instance of `dist_delivery_exact`; restricting `dist_exact` is not exact (`tr_causal_instance`); gap 15 (c), closed |
| C4 | Guarded enabledness, persisting under compensation | **exact**: `jc_exact`, `sn_jc_exact` | **degenerate**: C2 replay (a no-op guard folds into the step; gsm's `DeclEventGuarded` is a no-op when false) | **exact**: `stream_exact` | **degenerate**: C2 distributed (no-op guards fold into the local step) |
| C5 | Enabledness that compensation can disable | **exact**: `jcg_exact`, `jcsplit_exact` | **degenerate**: C2 replay (no-op guards) | **degenerate**: C4 streams (P10) | **degenerate**: C4 distributed |
| C6 | Buffered (waiting) guards in a federation | **exact**: under the federal guard with a guard on the federated state, `fed_buffered_exact` (co-enabled events stay enabled after each other and commute at guard-feasible states), per edge `fed_buffered_edge`; any enabledness, `fed_jcg_exact` (JC' on the federated GRS); gap 15 (d), closed | **degenerate**: C6 rewrite | **degenerate**: C6 rewrite | **degenerate**: C6 rewrite |
| C7 | The federal guard (FedMachine) versus none | **exact**: none: `fed_grs_exact`; guard: `fed_guarded_exact` | **exact**: `fed_exact` | **degenerate**: C2 replay (with every event enabled at every federally valid state, a settled processor is the FedMachine run of its received set) | **exact**: `dist_exact` (no guard) |
| C8 | At-least-once, free | **degenerate**: C8 replay (the property compares duplicated deliveries with the exactly-once result, which the replay model states) | **exact**: `alo_exact`, `safe_free_exact` (any step, P1) | **exact**: `stream_alo_exact_free`, `stream_alo_free_split` (free delivery); any enabledness `stream_alo_exact`; gap 15 (b), closed | **exact**: `dist_alo_exact` (`XUR` plus FedMachine commutation and idempotence at first deliveries), causal redelivery `dist_causal_alo_exact`; gap 15 (c), closed |
| C9 | At-least-once, causal | **degenerate**: C9 replay | **exact**: `causal_alo_exact`, `causal_alo_exact_idem`, `safe_at_exact` | **degenerate**: C8 streams | **degenerate**: C8 distributed |
| C10 | At-least-once, declared independence `I` | **degenerate**: C10 replay | **exact**: `dalo_exact`, `dalo_exact_absorb`, `safe_i_exact`; unordered retries `dalo_r_exact`, `safe_r_exact` (any step, P1, so the FedMachine with declared `I`); gsm's `NotIdempotent` placed by `dalo_notidem_needs_dedup`, `dalo_gsm_unlisted_safe`; gap 15 (a), closed | **degenerate**: C8 streams | **degenerate**: C8 distributed |
| C11 | Unordered merges with duplication | **degenerate**: C11 replay (compensation-free, identity repair: `cf_cc_exact_from`) | **exact**: `merge_action_exact`, `cvrdt_on_iff` | **degenerate**: C11 replay | **ill-formed**: in the merge model the merges are the propagation |
| C12 | Infinite streams | **ill-formed**: the other models compare finite words | **ill-formed**: as before | **excluded (design)**: gap 9 (`base_thm_convergence_transient_counterexample`) | **ill-formed**: as before |

### 3.4 State and order, by engine

| Row | State or order | Status |
|---|---|---|
| D1 | Finite, or a `nat` potential | **exact**: every engine (the original statements) |
| D2 | Well-founded potential in any order, infinite state | **exact**: `wf_cc_exact_from`, `wf_jc_exact`, `lex_jc_exact`; streams `stream_exact` (any well-founded order); acyclic federations use no finiteness |
| D3 | Compensation that need not terminate | **exact**: termination `terminating_iff_comp_wf`; unique normal forms with no termination hypothesis `canonical_cc_exact_from` |
| D4 | ACC lattice without a rank (`ole_no_rank`) | **exact**: repair (`chaotic_acc_reaches_lfp`, `kleene_acc_lfp`) and replay (B4). The distributed cells are B4's (uncovered, gap 16 (b)); resolver value sets of this kind fall under gap 3, which is sized "large in general" |
| D5 | Complete lattice without ACC | **excluded (design)**: gap 8 |
| D6 | Any group, finite or not | **exact**: the invertible rows use no finiteness (`section_iff_coboundary`, `net_unique_normal_form_iff`) |
| D7 | Arbitrary fiber for lossy maps | **exact**: the criteria (`root_set_criterion_graph`); decision procedures need a finite fiber with decidable equality (`root_set_decide`, `lmin_decide`) |
| D8 | Unbounded or multivalued resolver value sets | **open (gap 3)**: listed |
| D9 | Continuous state | **excluded (scope)**: fundamental limit, [LYAPUNOV-EXTENSION.md](LYAPUNOV-EXTENSION.md) |

### 3.5 Optimization, counting and gluing

| Row | Question | Status |
|---|---|---|
| F1 | Minimum coordination, invertible | **exact + hardness**: `plan_min_exact`, `maxcut_reduction` |
| F2 | Minimum coordination, lossy, reading A | **exact + hardness**: `lmin_root_set`, `lmin_reduction` |
| F3 | Minimum coordination, reading-B variants (delete until no negative or no positive cycle) | **open (gap 3)**: the audit ties them to gap 3 |
| F4 | Minimum coordination, monotone cycles | **ill-formed**: monotone repair needs no coordination for a unique repair normal form (`cyc_N_lfp`) |
| F5 | Counting, invertible (`H^1`) | **exact**: `nerve_H1_classification`, `nerve_H1_Z2_count`, `H1_classification` |
| F6 | Counting, lossy, reading A | **exact + hardness**: `root_set_count`; the reduction is parsimonious (`net_count`) |
| F7 | Counting, reading B (fixed points of the resolver map) | **uncovered**: as A11; gap 18 |
| F8 | Gluing, registry-level site | **exact**: `sheaf_iff_refines`, `sheaf_exact`, `cert_sheaf` |
| F9 | Gluing, variable-level (multi-writer) site; monotone-overlap site; relative certificates | **open (gap 13)** |
| F10 | Start quantification: a C2 converse over all valid starts in general networks | **open**: ROADMAP lower-value item ("C2 converse over all valid starts") |
| F11 | Delivery that never arrives (lost events, crashed replicas) | **excluded (scope)**: fundamental limit, eventual delivery |
| F12 | Purity of implementation closures; the trust base | **excluded (scope)**: fundamental limits |
| F13 | Validity of the canonical state, invertible and lossy | **degenerate**: the fiber is the set of valid shared values or normal forms ([LOSSY-NETWORKS.md, Networks](LOSSY-NETWORKS.md#networks)), so validity is A6 to A12 existence |
| F14 | Finite reachability of the canonical state | **exact**: `kleene_reach_exact` (monotone); `fed_lem_fed_termination` (acyclic, one round); `base_lem_termination_bound` (one registry) |

### Counts

| Status | Cells |
|---|---|
| exact | 65 |
| exact + hardness | 4 |
| sufficient (no owning gap) | 0 |
| excluded (design: gaps 8 and 9, and B8's counterexamples) | 9 |
| excluded (scope: fundamental limits) | 3 |
| open, existing gaps 3, 13, 19 (b) and one ROADMAP item | 16 |
| degenerate | 56 |
| ill-formed | 14 |
| **uncovered (now gaps 16 to 18)** | **12** |
| total | 179 |

Cells are counted per table row and column (sections 3.1 to 3.3), and per row in sections 3.4
and 3.5, by the status that leads the cell. One question can span several cells, so the 12
uncovered cells are 5 distinct questions (the four questions of gap 15, cells C10, C8 streams, C3
and C8 distributed, and C6, A2's fair schedules, 16 (d), and gap 19's composition across engines,
A14 and B13, and collapse in the distributed model, B11, are now exact; gap 5's cells B12 are exact
in replay and open under gap 19 (b) in the distributed columns): the edge-writer dynamics of A3, A8
and A10 (17); reading-B existence and counting, A11 and F7 (18); local compensation as steps on
cycles, B3 (16 c); distributed ACC, B4 (16 b); and rootless propagation with events, B7 (16 a).

What surprised: A2's fair cell. LOSSY-NETWORKS.md called Robert's theorem mechanized in the
federation model (`frun_solves`, `solve_unique`, `order_independent`), and the audit's frontier
table said the federation model "already has" the acyclic case; but those theorems give the unique
fixed point and runs in topological order (and `propagation_flush` a final flush), and arbitrary
fair update schedules on an acyclic network had no gated statement (since closed: `rb_robert_fair`,
`rb_robert_boolean`, `RobertFair.v`). The pages are corrected in
the same change (LOSSY-NETWORKS.md sections 2, 4.1, 4.2 and P2, LANDSCAPE.md, the audit's frontier
row for gap 3). Also C10: at-least-once delivery with declared independence is the case
gsm's `Report.NotIdempotent` meets whenever a registry declares `Independent` pairs, and the exact
theorems covered only free and causal delivery (since closed: `dalo_exact`,
`dalo_notidem_needs_dedup`, `dalo_gsm_unlisted_safe`).

## 4. Candidates outside the axes

Kept apart from section 3: an uncovered combination is a cell of the axes above; a new axis is a
dimension the model does not represent at all.

| Candidate | Kind | Status | Disposition |
|---|---|---|---|
| Dynamic topology: registries or edges added or removed at run time | new axis (`src` is a fixed parameter of every module) | a change at a quiescent barrier is two runs, the second from the reached state, so each is an existing cell, exactly when the migration is faithful (`barrier_exact_faithful`; `barrier_exact` in general); a change with events in flight is modeled (`Reconfiguration.v`) and exact for a single registry (`live_exact`) and for FedMachine federations, where adding an edge read by an in-flight event can diverge (`fed_live_exact`, `late_edge`); with propagation in flight (the distributed model) it is not represented | **gap 20**, narrowed |
| Rule or schema evolution mid-run | new axis (`apply`, `rho`, `f` are fixed parameters; gsm binds tables and certificates to `PolicyDigest` and `PolicyIdentityDigest` and rejects a mismatch in `EmbedCertified`) | barrier case as above; a live rule or schema change with events in flight (a migration of the state, in-flight events applied under the new rules) is exact for a single registry: B's condition from every migrated reachable state plus two cross-configuration critical pairs (`live_exact`), each needed (`cap_raise`, `doubling_migration`, `migrated_transient`); mixed-version replicas with propagation in flight are not represented | **gap 20**, narrowed (with dynamic topology) |
| Propagation over channels: late, reordered or duplicated projections | new axis (the current-value propagation step reads the sources' current values; gsm's `MergeProjection` merges whatever arrives, and `MergeProjectionAfter` drops a projection not newer than the last applied) | partly covered (`ProjectionChannels.v`): acyclic, exact over channel-reachable states in either mode (`chan_exact`); versioned merging converges at drain exactly when it does after a flush (`vsettle_exact_cond`); plain merging settles iff nothing stale is in flight (`plain_settle_iff`) and fails under XU (`plain_stale_counterexample`); two-level networks, the current-value condition (`vchan_twolevel_exact`); cycles, the ghost survives (`vchan_cyc_ghost`) | **gap 21**, narrowed |
| Faulty or Byzantine participants | new axis | crash faults and lost messages are the eventual-delivery limit; a participant that deviates from its declared rules is not governed state | **design exclusion X1** |
| Nondeterministic repair | new axis value (`rho : State -> State` is a function throughout; THEORY.md: "Compensation operator repairing violations deterministically") | excluded by the scope sentence "discrete, deterministic governed state"; made explicit | **design exclusion X2** |
| Probabilistic schedules (convergence with probability 1) | new axis value of the schedule axis | not represented | **design exclusion X3** |
| Infinite networks | new axis value (axis 13 is constant) | not represented | **design exclusion X4** |
| Time and deadlines | new axis | a timer firing is an event, so time-triggered rules are existing cells; bounds on convergence time are the asymptotic cost ROADMAP item 7 lists out of scope by design (step bounds are mechanized where they exist: `base_lem_termination_bound`, `sync_simple`'s `2^n`) | **design exclusion X5** (real-time semantics) |
| Message loss without redelivery | cell of the delivery axis | stated fundamental limit (eventual delivery) | excluded (scope), F11 |
| Partial replication | not a new axis | a replica holding part of the state with single-writer overlaps is a federation (sections 6 to 12 of the audit); overlapping writers are the variable-level site | existing cells; multi-writer part is **gap 13** |
| Mixed federations | cells (A14, B13) | across blocks needs composition: exact for any engines (`compose_exact`, `compose_collapse`), and for monotone blocks by Bekic's principle (`bekic_lfp`, `mono_collapse_exact`) | **gap 19 (a)** and **gap 5**, closed |
| Multivalued local interaction graphs | value of the state axis on the resolver rows | listed in gap 3 | **gap 3** |
| Nested federations, collapse with distributed propagation | cells (B11, B12) | flattening covers convergence of the flattened network; collapse preservation is exact for acyclic blocks (`dist_collapse_iff`; the plain statement fails, `dist_collapse_refuted`) and not stated for cyclic blocks | **gap 19 (b)**, closed for acyclic blocks, open on cycles |
| Synthesis of a convergent repair | value of the property axis | gsm `Registry.Synthesize` is implemented, not mechanized | open, ROADMAP lower-value item ("Synthesis") |
| Observation before convergence: what a read or query returns while events are in flight (session guarantees such as read-your-writes and monotonic reads) | new axis (every property on axis 12 is about normal forms, reachable states or agreement at the end; no theorem states what an intermediate read may return) | not represented | **candidate**, added after the pass; disposition pending (a new gap if a property of intermediate reads is stated, otherwise a scope sentence) |
| Irreversible external effects: an event that emits an effect outside the state (a message sent, a payment charged), which repair cannot undo | new axis (`apply : E -> State -> State` keeps every effect in the state, so `rho` can repair it) | an effect recorded in the state (an outbox) and emitted only from a normal form is an existing cell; an effect emitted from an intermediate state is not represented | **candidate**, added after the pass; disposition pending (a new gap or a design exclusion) |
| Compaction: snapshots, log truncation, deduplication tables that forget | new value of the delivery axis (the at-least-once modules deliver duplicates against an unbounded history; `dalo_notidem_needs_dedup` places deduplication but not its retention) | not represented: whether the at-least-once results survive a redelivery after the history that would reject it is gone | **candidate**, added after the pass; disposition pending |
| Nondeterministic events: an event whose effect reads a clock, a random source or other local input | value of the execution axis, the event-side twin of X2 | a value fixed when the event is created is part of the event (`E` is any type), so existing cells cover it; a value read separately at each replica when the event is applied makes `apply` a relation, which is not represented | **candidate**, added after the pass; disposition pending (the second case is likely a design exclusion with X2) |

## 5. Proposals

### New open gaps

Numbered after the audit's last gap (14). Sizes follow the audit's scale.

| # | Regime and question | Kind | Size | Audit section |
|---|---|---|---|---|
| 15 | Delivery and enabledness off the replay model: (a) at-least-once delivery under declared independence `I` (a registry with `Independent` pairs, the FedMachine); (b) at-least-once delivery for stream processors; (c) causal or at-least-once event delivery in the distributed model (sufficient only, by restricting `dist_exact`); (d) buffered guards in federations (events that wait until enabled). Since closed: (a) `dalo_exact`, (b) `stream_alo_exact_free`, (c) `dist_delivery_exact`, (d) `fed_buffered_exact` | cells | small to medium | 3, 5, 7, 8 |
| 16 | Distributed propagation off its current hypotheses: (a) events interleaved with rootless propagation on cyclic invertible networks with authority roots (no distributed model off monotone cycles); (b) monotone cycles with ACC and no finite height (every distributed module assumes `rank_bound`); (c) local compensation as separate steps on cycles (`G_Fed` is acyclic only); (d) settlement of every fair update schedule on an acyclic network, Robert's asynchronous half: since closed (`RobertFair.v`: `rb_robert_fair`, `rb_fair_dist_exact`, `rb_lens_robert`, and for Boolean networks with an acyclic global graph `rb_robert_boolean`, through `fair_settlement_of_acyclic`) | cells | medium | 8, 11 |
| 17 | Rootless edge-writer dynamics beyond the regular action: lossy maps at in-degree two or more (where the edge-writer and resolver readings differ), and invertible maps under a non-free action. Quiescent states are reading-A sections, so existence is already exact and NP-complete (`root_set_criterion_graph`, `net_section_iff_sat`); open is when every fair order reaches one, and uniqueness. Gap 3 is the resolver reading only | cells | medium | 11, 12 |
| 18 | Existence and counting in reading B without a spanning root (fixed points of the resolver map, in-degree two or more): no row. The polynomial reductions between the readings (LOSSY-NETWORKS.md section 1) are conjectures validated by checks 8 and 9; mechanizing one transfers `net_section_iff_sat` and `net_count` | cells | small | 12 |
| 19 | Composition beyond acyclic collapse: (a) coordination-free networks whose cyclic blocks use different engines (a non-monotone cyclic block, invertible or lossy, feeding or fed by other blocks); (b) collapse preservation in the distributed model (a block whose internal propagation interleaves with outer events). An instance of the cyclic frontier for (a). Since narrowed by `CompositionBlocks.v`: (a) closed for any engines (`compose_exact`, `compose_collapse`, `interface_closed`), (b) closed for an acyclic block (`dist_collapse_iff`); the residue is (b) for a cyclic block | cells | medium to large | 14 |
| 20 | **New axis.** Reconfiguration inside a run: the topology (`src`) or the rules (`apply`, `rho`, morphisms) change while events or propagation are in flight. A change at a quiescent barrier reduces to two runs of existing cells. Since narrowed by `Reconfiguration.v` (`barrier_exact`, `barrier_exact_faithful`, `live_exact`, `fed_live_exact`, `classify_finite`); an unfaithful migration's barrier A part is local and finite in the deterministic model (`ReconfigurationClosure.v`: `amodm_closure_exact`, `det_classify_complete`); the residue is a live change in the distributed model (propagation in flight) and other delivery classes across the switch | new axis | medium | none (COVERAGE.md section 4) |
| 21 | **New axis.** Propagation over channels: projections delivered late, reordered or duplicated. gsm's `MergeProjection` (no order check: a late or duplicate projection is merged as it arrives, and a stale one merged after a newer one wins) and `MergeProjectionAfter` (rejects a projection whose version is not newer than the last one applied from that edge) are outside the mechanized propagation model, whose step reads the sources' current values, so no theorem covers a deployment whose projections travel over such channels. Freshness keeps an older value from overwriting a newer one; it is not proved to give convergence (gsm's own documentation says the same). Since narrowed by `ProjectionChannels.v` (`chan_exact`, `vsettle_exact_cond`, `vsettle_xu_c2`, `plain_settle_iff`, `vchan_twolevel_exact`); the residue is the current-value form beyond two-level networks and cycles | new axis | small to medium | 8 |

Why gaps and not exclusions: each is a question in the model's own vocabulary that nothing in the
scope ("discrete, deterministic governed state") rules out, and gsm meets 15 (a), 20 (policy
digests) and 21 (projection merging) in practice.

### New design exclusions

| # | Exclusion | Justification |
|---|---|---|
| X1 | Byzantine participants | Governed state is defined by each registry's declared rules; a participant that runs other rules is not governed state, and crash faults reduce to the eventual-delivery limit. Agreement under adversarial participants is consensus, placed in [LANDSCAPE.md](LANDSCAPE.md) |
| X2 | Nondeterministic repair | The scope is deterministic governed state: compensation is a function (`rho : State -> State`) in every module. Nondeterminism of event order is modeled; nondeterminism of repair is not |
| X3 | Probabilistic schedules | The axiom-free gate rules out the standard library's real numbers, which rest on axioms. On a finite state space, settlement with probability 1 under a random scheduler of full support is, by the classical absorbing-chain argument, exactly the existential form already mechanized (from every reachable state some word reaches a fixed point: `FlushR`, E's Settlement, `richard_t3`); cited, not mechanized |
| X4 | Infinite networks | Every network is a finite list of registries and edges, as are gsm's federations; fairness and flush arguments use that finiteness |
| X5 | Real-time semantics | The model is untimed: a timer firing is an event, so time-triggered rules are existing cells, and bounds on convergence time are the asymptotic cost that ROADMAP item 7 lists out of scope by design |

## 6. Missing-axis report

Dimensions that appear in gsm or in theorem premises but are not axes of the audit's tables:

- **Start quantification** (axis 10). It varies across exact theorems (`cc_exact_from` and
  `cc_exact_global`; `dist_exact`, `dist_exact_global`, `dist_exact_consistent`) and is recorded
  per row as a qualifier. One cell is open along it (F10).
- **Writer semantics** (axis 3). The audit names readings A and B in section 12 and "every edge a
  writer" in section 11, but does not cross them; crossing them gives gap 17.
- **Schedule** (axis 6). Existential, fair and synchronous settlement appear only inside gap 3's
  text; the distinction is general (`FlushR` versus `FairFlushR` in section 8).
- **Declared independence** (a delivery value). gsm's `Independent` and `OnlyDeclaredPairs` and the
  premise `I : E -> E -> Prop`; crossing it with at-least-once delivery gives gap 15 (a).
- **Propagation transport** (gsm only): `Projection.Version`, `MergeProjection`,
  `MergeProjectionAfter`; gap 21 (narrowed, `ProjectionChannels.v`).
- **Policy identity** (gsm only): `PolicyDigest`, `PolicyIdentityDigest`, certificate digests;
  the theory fixed the rules, gsm checks that participants share them; gap 20 (narrowed,
  `Reconfiguration.v`: a change of rules or topology at a barrier and live, and the classification
  behind gsm's planned `CheckMigration`).
- **Closure purity and domains** (gsm only): `TrustClosureFootprints`, lazy machines, domain checks;
  a stated fundamental limit (purity of closures) and implementation hygiene, not a regime.
- **Repair synthesis** (gsm only): `Registry.Synthesize`; a ROADMAP lower-value item.
