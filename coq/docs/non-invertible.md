# Non-invertible (lossy) transports

Detailed results for general transport maps: the obstruction and the diagnostic, the root-set
criterion, the 3-SAT reduction, and event order under root-set coordination. Each module's one-line
summary is in the [module index](../README.md#modules-by-regime); the status of each question in
this regime is in [REGIME-AUDIT.md](../../REGIME-AUDIT.md#12-non-invertible-transports), section 12.

## General transport maps: the obstruction, the diagnostic, and coordination bounds (`CohomologyGeneral.v`)

The general-map content of the companion paper's sections 6 to 8 (work package WP9 of
`PAPER-MAP.md`), axiom-free. Where a paper statement is false or imprecise, the counterexample is a
theorem and the strongest true form is proven next to it.

**The obstruction theorem (`thm:obstruction`).** A cycle carries edge maps `f_0, ..., f_{n-1}`
(any maps on any fiber `V`, no invertibility); a section is `s 0, ..., s n` with
`s (i+1) = f_i (s i)` and `s n = s 0` (`cycle_section`). "Reachable fixed point", which the paper
does not define, is made precise as `reaches_fixed g x0`: some iterate `g^n x0` is fixed by `g`.

- `thm_obstruction_general`: a section exists iff the loop composite has a fixed point.
  `sections_are_fixed_points`: restriction to vertex 0 is a bijection from sections onto `Fix(g)`,
  so the witness lives on the shared fiber alone.
- `reaches_fixed_iff_section`: a fixed point is reachable from `x0` iff some section has its vertex-0
  value on the forward orbit of `x0`. `thm_obstruction_reachable`: the paper's statement, with
  "reachable" meaning "reachable from some seed".
- gsm's `DiagnoseCycle`, on a finite fiber with decidable equality (`N` = its size):
  `diagnose_bounded` (the seed reaches a fixed point iff `g^N x0` is fixed), `diagnose_orbit_witness`
  (the orbit repeats within `N` steps), `diagnose_dichotomy` (exactly one of the two outcomes).

**Reading the diagnostic (section 7).** "A non-convergent result is definitive" is false:
`c15_definitive_claim_false`, with the loop copy-then-swap on `{t0, t1, t2}` (swap `t0, t1`, fix
`t2`): seed `t0` orbits (`c15_seed_orbits`) while `t2` is a section (`c15_tri_section`). Corrected
forms: `c15_exact_refuter` (no section iff no seed reaches a fixed point), `c15_free_definitive`
(one seed is definitive when the fixed points of `g` are all-or-nothing),
`c15_injective_reaches_iff_fixed` (for an invertible composite a seed reaches a fixed point iff it
is fixed), `c15_regular_definitive` and `c15_regular_is_free` (translation by the holonomy: from any
seed, reaches iff `h = e`). `c15_convergent_result_sound`: a settling seed proves a section exists;
`c15_convergent_result_not_global`: it does not prove every seed settles.

**Minimal coordination with its qualifiers (`prop:minimal`).** `prop_minimal_qualified_iff`: in the
regular action with an authority root `r` and spanning tree `T`, the labeling `T ++ X` is a
coboundary (`H^1 = 0`) iff for every authority value the uncoordinated network (tree drives, every
non-tree edge kept as a checked constraint) has a consistent state that is the unique one with that
root value and that every propagation order reaches. `prop_minimal_qualifiers_needed`: Z/2 acting on
`{t0, t1, t2}` by the swap gives a non-coboundary with a section (the regular action is needed), and
`nonfree_holonomy_counterexample`, `copyback_without_authority` (the authority root is needed).

**Coordination as edge deletion (section 8).** `feasible Es D`: some state satisfies every edge of
`Es` outside `D`.

- Edge-disjoint obstructions: `edge_disjoint_lower_bound` (`k` pairwise edge-disjoint cycles with no
  section force at least `k` deleted edges, for any labels) and `edge_disjoint_min` (with a spanning
  tree whose unbalanced non-tree edges number `k`, the minimum is exactly `k`); instance
  `bowtie_min_two`.
- `min_G >= min_{G^ab}` in general: `section_pushforward`, `feasible_pushforward` and
  `min_G_ge_min_image` push sections and feasible coordinations along any homomorphism, any graph;
  instance `klein_min_ge_1`.
- The non-invertible case, "a cycle basis still suffices", is false: `c22_cycle_basis_fails` is a
  tree (empty cycle basis) with constant maps 0 and 1 into one vertex, which has no section; one
  deletion restores one. Corrected for root-oriented trees (`otree`, every edge pointing away from the
  authority root): `out_tree_section`, `out_tree_unique`, `rooted_criterion` (a section with the
  tree-driven root value exists iff the driven state satisfies every non-tree edge),
  `rooted_coordination_suffices`; instance `c22_rooted_instance`.

**Two regimes, not exhaustive (section 6).** `c13_two_ways_not_exhaustive`: a cyclic loop of two
negations (trivial holonomy, non-monotone edges) and copy-then-swap on `nat` (non-trivial holonomy,
non-monotone composite) both have sections, so acyclicity and monotonicity are two sufficient
conditions, not the only ones.

## The root-set criterion for lossy networks without a spanning root (`RootSet.v`)

Reading A of [LOSSY-NETWORKS.md](../../docs/LOSSY-NETWORKS.md) (the constraint reading, as in `CohomologyGeneral.v`): a network is a
list `G` of edges `(u, v, f)` with `f : V -> V` an arbitrary, possibly lossy, map on one fiber `V`;
a state `s` is a section when `f (s u) = s v` on every edge (`msection s G`). `rooted_criterion`
decides this when one vertex reaches all others. This file replaces the root by a **root set** and
closes, for reading A, the row "general graph: none mechanized; none known" of the regime audit
(open problem P1 of [LOSSY-NETWORKS.md](../../docs/LOSSY-NETWORKS.md)).

**Setting.** `root_set R G`: every vertex of `G` is reachable (`reach`) from some vertex of `R`; for
instance one representative per source strongly connected component, plus any others (a minimum
root set is exactly one per source component, David, JAIR 1995). An outward spanning forest from
`R` (`oforest R F`) attaches one fresh vertex per edge to the reached set `R ++ verts F`, so it gives
every vertex exactly one driving path from exactly one root; `spanning_forest R G F` asks `F` to be
a subgraph of `G` covering every vertex of `G`. `drive F a` pushes root values `a` along `F`.

**The structure.**

- `root_set_iff_forest`: `root_set R G <-> exists F, spanning_forest R G F` (the forest is grown
  greedily, by a crossing-edge search with a vertex-count measure).
- `out_forest_section`, `drive_root`: for every root assignment the driven state is a section of
  the forest with those root values. `out_forest_unique`: sections of the forest that agree on `R`
  agree on every reached vertex. `driving_paths`: each reached vertex `w` is driven by one root
  `rho w` through one path composite `p w`, `drive F a w = p w (a (rho w))`.

**The criterion (exact).**

- `root_set_criterion`: for `oforest R F`, a forest section `sF` and non-driving edges `X` among the
  reached vertices, `(exists s, msection s (F ++ X) /\ s = sF on R) <-> every edge of X holds at sF`.
  `root_set_criterion_driven` is the same for a root assignment `a` and its driven state.
- `root_set_exists`: `(exists s, msection s (F ++ X)) <-> exists a, every edge of X holds at drive F a`.
- `root_set_agreement`: the same in agreement form: for every non-driving edge `(u, w, f)`,
  `f (p u (a (rho u))) = p w (a (rho w))`. When `rho u <> rho w` this says the two roots agree at a
  vertex reached from both; when `rho u = rho w` it is the single-root condition of
  `rooted_criterion`.
- On a graph: **`root_set_criterion_graph`**, for any root set `R` of `G` and spanning forest `F`,
  `(exists s, msection s G) <-> exists a, msection (drive F a) G`;
  `root_set_criterion_values`, the same with the root values fixed.

**Sections are root assignments.** `root_set_bijection`: a section is the driven state of its own
root values (on every vertex of the network), the driven state keeps its root values, and two
sections with the same root values agree on the network. `root_set_count`: with `V` enumerated
without duplicates and `R` duplicate-free, the consistent root tuples (`consistent_roots`, a filter
of the product of the root domains, `tuples`) and the sections recorded on the network's vertices
(`sections_on`) are both duplicate-free lists, the second contains exactly the restrictions of the
sections of `G`, and they have the same length: **the number of sections equals the number of
consistent root assignments**. `root_set_decide`: existence is
`existsb (rs_ok R G F) (tuples lv (length R)) = true`, a search over the product of the root
domains (`O(prod |X_r| (|V| + |E|))`).

**The single-root case.** `otree_oforest` (`otree r T <-> oforest [r] T`) and
`rooted_criterion_recovered`, `out_tree_section_recovered`, `out_tree_unique_recovered` re-derive
`CohomologyGeneral.v`'s theorems as `R = [r]`.

**Instances.**

- The diamond (`diamond_*`): one root, paths `0 -> 1 -> 3` (copies) and `0 -> 2 -> 3` through the
  lossy `dia_h` on `{t0, t1, t2}` (`diamond_not_injective`). The paths disagree at 3 for every root
  value: `diamond_no_section` through the criterion, `diamond_count` (zero consistent root values).
- Two constant maps into one vertex (`c22_*`, the shape of `c22_cycle_basis_fails`): `[0; 1]` is a
  root set and neither root alone is (`c22_root_set`); no root tuple is consistent
  (`c22_no_consistent_root`, `c22_count`), so `c22_no_section_recovered` re-derives the no-section
  half of `c22_cycle_basis_fails`.
- Two roots with sections (`two_*`): roots 0 and 1 into 2 through the lossy collapse
  `t0, t1 |-> t0, t2 |-> t2`. `two_has_section`; `two_count` and `two_count_is_sections`: 5 of the
  9 root tuples are consistent and the network has exactly 5 sections.
- A root set containing a strongly connected component (`scc_*`): `{0, 1}` is a source component
  (copy `0 -> 1`, lossy back edge `1 -> 0` constant `true`), 2 a second source, and `1 -> 3` (copy),
  `2 -> 3` (negation) meet at 3. `scc_component`: 0 and 1 reach each other, `[0; 2]` is a root set,
  `[0]` and `[2]` are not. `scc_consistent_roots`: the only consistent root tuple is
  `(true, false)` (the back edge pins 0, the meeting at 3 pins 2); `scc_unique_section`.

**What this settles.** Together with the NP-completeness of existence ([LOSSY-NETWORKS.md](../../docs/LOSSY-NETWORKS.md)
section 3.2, a reduction from 3-SAT, consistent with Cooper, Cohen and Jeavons 1994 as reported by
David 1995; the reduction's correctness and size are mechanized in `LossyHardness.v`), this is the exact criterion for the regime "non-invertible graphs
without a spanning root", and no efficient exact criterion exists unless P = NP: the search over
the product of the root domains is the irreducible cost, polynomial for a bounded number of source
components (one, in `rooted_criterion`) and exponential in that number in general. The criterion is
David's root-set decomposition (JAIR 1995, Theorem 1; the single-root case is Zhang and Yap 2011,
Corollary 3); what is new here is the axiom-free mechanization, the bijection with root
assignments, and the recovery of `rooted_criterion`.

## The 3-SAT reduction for lossy networks (`LossyHardness.v`)

[LOSSY-NETWORKS.md](../../docs/LOSSY-NETWORKS.md) section 3.2 states that deciding whether a lossy network has a section
(reading A, `msection` of `CohomologyGeneral.v`) is NP-complete, by a reduction from 3-SAT. This
file mechanizes **the reduction's correctness and its size bound**; it does not formalize Turing
machines or polynomial time. NP-completeness then follows by the standard argument: membership
because a section restricted to the network's vertices is a certificate of one value per vertex,
checked by one table lookup per edge (`np_certificate`), and hardness because the construction is
linear in the formula (`net_size`, `net_tables`) and preserves satisfiability exactly
(`net_section_iff_sat`).

**Formulas.** A 3-CNF `f : cnf` is a list of clauses, each three literals `(x, negated)`;
`satisfies a f` for `a : nat -> bool`, `satisfiable f := exists a, satisfies a f`, with the boolean
checker `sat_check` (`sat_check_spec`). `occ f` lists the occurring variables, one entry per
occurrence.

**The construction `net f`** on the single fiber `nat`, with codes `0..7` (three bits) and poison
`8`:

- a clause vertex `cv j = 2j + 2` per clause, whose value is a 3-bit code;
- a variable vertex `xv i = 2i + 1` per variable;
- for the `p`-th literal `x` of clause `C_j`, a projection edge `(cv j, xv x, prj C_j p)`: a code
  satisfying `C_j` goes to its `p`-th bit, every other value to poison;
- the **filter gadget** that fits the typed fibers (`{0, 1}` for a variable, the 7 satisfying codes
  for a clause) into `msection`'s one fiber: a filter vertex `zv = 0` pinned to `0` by the constant
  self-loop `(zv, zv, pin)`, and a filter edge `(xv x, zv, filt)` per occurrence, with `filt`
  sending `0, 1` to `0` and everything else to `1`.

**Correctness (exact).**

- `net_section_iff_sat`: `(exists s, msection s (net f)) <-> satisfiable f`, for every 3-CNF `f`
  (repeated variables in a clause included). The directions are `section_of_sat` (a satisfying
  assignment `a` gives the section `state_of f a`) and `sat_of_section` (a section `s` gives the
  satisfying assignment `assign_of s`, reading `xv i`); `section_clause` is the local content: in
  a section the filter vertex is `0`, each clause value is a satisfying code, and each variable
  holds the matching bit.

**Parsimony (the count is preserved).**

- `net_bijection`: `state_of` and `assign_of` are mutually inverse between sections, up to
  equality on the network's vertices `nverts f`, and satisfying assignments, up to equality on the
  occurring variables: `assign_of (state_of f a) = a`, `state_of f (assign_of s) = s` on
  `nverts f`, and both are well defined on classes (`state_of_ext`). Corollaries
  `sections_determined` and `assignments_determined`.
- `net_count`: the sections recorded on the (duplicate-free) network vertices with values in
  `{0..8}` (`section_tuples`) and the satisfying assignments recorded on the (duplicate-free)
  occurring variables (`sat_tuples`) are duplicate-free lists, each characterized exactly, of
  **equal length**: #sections = #satisfying assignments, as [LOSSY-NETWORKS.md](../../docs/LOSSY-NETWORKS.md) claims (its
  "[our conjecture]" on parsimony, now mechanized).

**Size.**

- `net_size`: `length (net f) = 6 |f| + 1` edges; the vertex list `nverts f` has length
  `4 |f| + 1` and contains every vertex of `net f`.
- `net_tables`: every map of `net f` sends `{0..8}` into `{0..8}` and is constant from `8` on, so
  it is a 9-entry table and the network restricts to the 9-element fiber of the note.

**Membership in NP.**

- `np_certificate`: for any network over a fiber with decidable equality listed by `lv`, a section
  exists iff some tuple of values on the (duplicate-free) vertex list, drawn from `lv`, passes
  `msection_b` (one equality test per edge; `RootSet.v`). `msection_ext`: a section depends only on
  the network's vertices.
- `np_certificate_net`: the same for `net f` with values in `{0..8}` (`cert_ok`).

**The gadget is needed (counterexamples to the reduction without it).**

- `no_filter_trivial`: with the projection edges only (`pedges`), the constant poison state is a
  section for every formula.
- `no_pin_trivial`: with projection and filter edges but no pinning self-loop (`cedges`), poison
  everywhere and `1` at the filter vertex is a section for every formula.

**Instances.**

- `fsat = [x0 \/ x1 \/ x2]`: `fsat_satisfiable`, `fsat_has_section`; `fsat_check` runs the
  certificate checker on the section of the all-true assignment; `fsat_count`: 7 satisfying
  assignments and, by direct enumeration of all `9^5` value tuples, 7 sections.
- `funsat`, the eight clauses on all sign patterns of `x0, x1, x2`: `funsat_unsatisfiable`,
  `funsat_no_section` (through the reduction), `funsat_count` (0 and 0), and
  `funsat_gadget_needed` (both gadget-free networks of `funsat` have sections).

## The exact event-order condition under root-set coordination (`RootSetEvents.v`)

`CoordinatedExact.v` gives the exact event-order condition when values are driven along a spanning
tree of a group-labeled graph. `RootSet.v` drives values from a root set `R` along an outward
spanning forest `F` with arbitrary (lossy) maps. This file combines the two and closes the row
"event order under root-set coordination (non-invertible driving forest)" of the regime audit,
section 12 ([LOSSY-NETWORKS.md](../../docs/LOSSY-NETWORKS.md) P6).

**The driving network of a forest** (`frule`, `fsrc`, `ffun`). A vertex `w` attached by a forest
edge `(u, w, f)` reads only `u` and takes `f (s u)`, ignoring its own value; a root keeps its own
value; registries off `R ++ verts F` are untouched (`forest_network_shape`). Non-driving edges `X`
never write: they are constraints checked on the result, or coordinated away. A forest gives every
vertex one driver, so the network is acyclic and satisfies `FederationEvents.Common`
(`forest_common`), and `FederationEventsConverse.v` applies unchanged (`forest_gc_iff`,
`forest_fed_exact`, `forest_fed_exact_full`). Consistent states of the network are exactly the
sections of `F` (`forest_cons_iff`). `forest_order`, `forest_order_set`: for duplicate-free `R`,
`R ++ targets F` is a topological order over exactly `R ++ verts F`.

Setting of the main theorems: `oforest R F`, a topological order `o` of the network over exactly
`R ++ verts F`, events `(E, reg, sig)` on those registries with any declared same-registry
independence `J`, and a consistent start `s0`.

**C1 and C2 on the forest.** `forest_c1_static`, `forest_c1r1`: C1 holds unconditionally (a driven
target is overwritten by `f (z u)` on both sides; a root's repair is the identity).
`forest_c2at_iff`: C2 at a reachable witness `s` is trivial on driven registries and, on a root
`r`, is exactly `sig e2 (sig e1 (s r)) = sig e1 (sig e2 (s r))`. `forest_c2_static_iff`: static C2
holds iff every two `J`-independent events of every root commute at every value.

**The exact condition.**

- **`forest_events_exact`**: for every consistent start `s0`,
  `TraceConv s0 <-> forall r, In r R -> RootCC r J (s0 r)`: every two `J`-independent events of
  each root `r` commute at every value reachable from `s0 r` by `r`'s own events. One independent
  condition per root.
- `forest_perm_exact`: the same for permutations (every pair declared).
- `forest_events_exact_global`, `forest_global_iff_static`: convergence from **every** consistent
  start iff every root's independent events commute at every value, iff static C1 and C2.

**Different roots do not interact.** `forest_root_run`: a root's value after a run is its start
value pushed through its own events only. `forest_run_formula`, `forest_run_single_root`: every
vertex is `p w` applied to the run of one root `rho w` (its driving root) on that root's own
events. `forest_runs_by_root`: runs with the same per-root subsequences reach the same state;
`forest_cross_commute`: events on different registries commute from every consistent state;
`forest_driven_noop`: an event on a driven registry is overwritten. A vertex reached from two roots
in the graph is still driven by one of them (the other edge is in `X`), so there is no cross-root
counterexample. The only cross-root coupling is through the kept constraints:
`forest_runs_kept`, every reached state is a section of `F`, and it is a section of `F ++ X` iff
the run's root values are a consistent root assignment (`root_set_criterion`).

**The group case recovered.** `tforest r T` turns a spanning tree of `CoordinatedCycles.v` (edges in
either direction) into an outward forest from `[r]` with the maps `tr g b` (`tforest_props`), whose
network is the tree's driving network pointwise (`dfun_ffun`, `dsrc_fsrc`; `runF_fext`).
`coordinated_events_exact_recovered` and `coordinated_events_exact_global_recovered` re-derive
`coordinated_events_exact` and `coordinated_events_exact_global` as `R = [r]`; `recovered_klein`
applies the first to the Klein tree.

**Instances** (`tw_*`, over `nat`). Roots 0 and 1, forest `[(0, 2, par); (1, 3, cap1)]` with the
lossy `par x = x mod 2` and `cap1 x = min x 1`, non-driving edge `(1, 2, par)`, so vertex 2 is
reached from both roots (`tw_root_set`: `[0; 1]` is a root set, neither root alone is). Events
Dbl (`2x`) and Clamp (`min x 5`) on root 0, Inc on root 1, Poke (write 7) on the driven vertex 2.

- `tw_converges_at_zero`: from every consistent start with root 0 at 0, every permutation
  converges (both root-0 events fix 0).
- `tw_diverges_at_three`: from root 0 at 3, Dbl and Clamp give 6 versus 5 at root 0 and 0 versus 1
  at vertex 2.
- `tw_reachable_matters`: Dbl and Clamp commute at 1, yet from root 0 at 1 the runs
  Dbl Dbl Dbl Clamp and Dbl Dbl Clamp Dbl diverge (5 versus 8), since 4 is reachable: the
  reachable-value qualifier is needed. `tw_not_global`: convergence holds from some consistent
  starts and fails from others.
- `tw_cross_roots`, `tw_poke_noop`, `tw_vertex2`: root 0 and root 1 events commute from every
  consistent start, Poke is overwritten, and vertex 2 depends on root 0's events only.
- `tw_constraint`: the cross-root constraint holds from the zero start, fails after one Inc on
  root 1, and holds again after two.

## Minimum coordination for lossy networks (`LossyMinimum.v`)

Gap 11 of `REGIME-AUDIT.md` (section 12, "Optimization: minimum coordination", none known). A
coordination deletes edges; the question is the least number of deletions that leaves a network
with a section.

**Definitions.** Edges are deleted by **position** in the edge list `G`, so parallel copies of one
edge are distinct and no equality on maps is needed. A coordination set `F` is a duplicate-free
list of positions below `|G|` (`cset G F`); the residual network `resid G F` keeps the edges whose
position is not in `F`. `F` is feasible (`lfeasible G F`) when `resid G F` has a section, and
`is_lmin G k` says that some feasible coordination set has `k` positions and every feasible one
has at least `k` (unique: `lmin_unique`).

**Exact characterization (through `RootSet.v`).**

- `lfeasible_root_set`: for **any** root set `R` and spanning forest `Fr` of the residual, `F` is
  feasible iff some root assignment `a` drives a state satisfying every residual edge
  (`root_set_criterion_graph` applied to the residual).
- `lfeasible_iff_root_set`: `F` is feasible iff the residual has a root set, a spanning forest and
  a root assignment whose driven state satisfies every residual edge (`root_set_ok`). A root set
  always exists: all vertices with the empty forest (`trivial_forest`).
- `lmin_root_set`: `k` is the minimum iff it is the least `|F|` whose residual passes that
  criterion.
- Upper bounds: `forest_residual_feasible` (an outward-forest residual is feasible) and
  `lossy_lmin_le_nontree` (with an outward forest `T` followed by extra edges `X`, the minimum is
  at most `|X|`).

**Decision procedure** (a fiber listed by `lv` with decidable equality).

- `sec_b_spec`: `sec_b` decides section existence by a search over one value per vertex.
  `lfeasible_decide_forest`: with a spanning forest of the residual, feasibility is the search over
  the product of the root domains (`root_set_decide`).
- `lmin_le_b_spec`: `lmin_le_b G k = true` iff a feasible coordination set of size at most `k`
  exists (a search over the subsets of positions).
- `lmin_b_correct`: `lmin_b G` (the least `k` with `lmin_le_b G k`) is the minimum;
  `lmin_decide`: `is_lmin G k <-> lmin_b G = k`; `lmin_exists`.

**Hardness** (through the 3-SAT network `net f` of `LossyHardness.v`).

- `lmin_zero_iff_section`: the minimum is `0` iff the network has a section.
- `lmin_zero_iff_sat`: `is_lmin (net f) 0 <-> satisfiable f` (`net_section_iff_sat`);
  `min_le_zero_iff_sat`: the same for the decision problem "minimum `<= 0`".
- `net_lmin_dichotomy`: the minimum of `net f` is `0` if `f` is satisfiable and `1` otherwise:
  deleting the pinning self-loop (position `0`) always leaves a section (`net_unpinned`,
  `net_one_suffices`, from `no_pin_trivial`).
- `lmin_reduction`: the reduction packaged: `|net f| = 6|f| + 1`,
  `is_lmin (net f) 0 <-> satisfiable f`, and `is_lmin (net f) 1 <-> ~ satisfiable f`.

So "minimum `<= k`" is NP-hard already at `k = 0`, and telling minimum `0` from minimum `1` is
NP-hard, so no efficient algorithm approximates the minimum within any factor unless P = NP. As in
`LossyHardness.v`, what is mechanized is the correctness and size of the reduction; the complexity
conclusion is the standard argument.

**Membership in NP.**

- `min_le_np_certificate`: a feasible coordination set of size at most `k` exists iff some
  certificate `(F, t)`, a list of positions and one value per residual vertex, passes
  `min_cert_ok` (a length test, a duplicate test, a range test, and one equality test per residual
  edge).
- `min_cert_size`: an accepted certificate has `|F| <= k`, `|F| <= |G|` and `|t| <= 2|G|`.
- `lmin_le_np`: for the minimum `m`, `m <= k` iff some certificate passes.

**The invertible case.** `lift Es` reads a group-labeled network as a lossy one under the regular
action (`g` acts by `x |-> g x`); `msection_lift`: sections coincide.

- `lossy_min_is_gfes`: on lifted networks the lossy minimum **is** the group feedback edge set
  minimum: the least number of deleted edges leaving a coboundary labeling (`gfes`,
  `is_gfes_min`; `lfeasible_lift_iff` via `section_iff_coboundary`).
- `lift_cycle_basis`: when the residual is a spanning tree plus extra edges, `F` is feasible iff
  every extra edge is balanced (`cycle_basis_criterion`), so in the invertible case feasibility is
  decided per fundamental cycle.
- `group_tree_lmin_zero`: a group-labeled tree has minimum `0`; `group_lmin_le_nontree`: with a
  spanning tree `T` (edges in either direction) and extra edges `X`, the minimum is at most `|X|`.

**The lossy minimum is not cycle-based.**

- `c22_lmin`: the C22 shape (constant maps `false` and `true` from `0` and `1` into `2`) is a tree
  and has minimum `1`.
- `lossy_min_exceeds_cycle_bounds`: every valid lower bound `L` on the lossy minimum that sees only
  cycles (takes the same value on every tree as on the empty network) has `L c22_es = 0 < 1`.
  `cycle_bounds_nonvacuous`: the zero bound meets both hypotheses. Edge-disjoint obstructing
  cycles (`edge_disjoint_lower_bound`) are such a bound.
- `c22_group_lmin`: the same tree with group labels has minimum `0` (`group_tree_lmin_zero`), and
  `lossy_lmin_le_nontree` needs an outward forest where `group_lmin_le_nontree` accepts any tree.

**Instances.** `c22_lmin_b`, `c22_lmin` and `c22_certificate` (the checker accepts deleting
position `1` with `k = 1` and rejects the empty set with `k = 0`); `diamond_lmin` (minimum `1`);
`two_lmin` and `scc_lmin` (minimum `0`); `tri_lmin` (a Z/2 triangle closed by a flip: lossy
minimum `1` = group feedback edge set minimum); `bow_lmin` (the bowtie: `2` both ways, matching
`bowtie_min_two`); `fsat_lmin` (`0`) and `funsat_lmin` (`1`) through the 3-SAT network.

## Signed cycles: loops versus merges, and the signed-cycle bridge to E (`SignedCycles.v`, `SignedResolver.v`)

**The separation (`SignedCycles.v`, reading A).** Walks may cross an edge backward, contributing
the inverse label (`walk`); directed paths use edges forward only (`dpath`). On a group-labeled
network under the regular action:

- `section_transport` (the lemma): a section maps `s u` to `s w` along every walk by the walk's
  label.
- `holonomy_free_section`: if every closed walk has trivial label, a section exists. This holds for
  any finite edge list, with no spanning-tree hypothesis (the proof grows a forest one component at
  a time).
- `invertible_merge_is_holonomy`: (1) two directed paths `u -> v` with different composite labels
  `h1`, `h2` close (the second reversed) into a closed walk at `u` with holonomy `h2^-1 h1`, which
  is not the identity, and no section exists; (2) a section exists iff every closed walk has trivial
  holonomy, iff walk labels are path-independent, iff the labeling is a coboundary
  (`section_iff_coboundary`).
- `fundamental_cycles_holonomy`: with a spanning tree plus extra edges, "every extra edge balanced"
  (`cycle_basis_criterion`) iff every closed walk has trivial holonomy.
- `obstruction_loop_vs_merge`: (a) invertible: every tree (`CohomologyGraph.tree`: grown leaf by
  leaf from a root, each edge in either orientation; forests are covered by
  `holonomy_free_section`) has a section and trivial holonomy (`tree_has_section`); (b) lossy: the C22 shape is a tree with no section, although each of its two
  edges alone has one, and its minimum coordination is 1 (`c22_cycle_basis_fails`,
  `c22_no_section_recovered`, `c22_lmin`). In the invertible case every obstruction is a loop; in
  the lossy case a merge of two directed paths suffices.

**Harary balance, proved.** Signed graphs are Z/2-labeled networks (`xorb`; label `true` is a
negative edge). `harary_balance`: a switching `o` (every edge `(u, v, b)` has `b = xorb (o u) (o v)`,
so reversing the order at the vertices with `o = true` makes every edge positive) exists iff no
closed undirected walk carries an odd number of negative edges. This is the Z/2 instance of
`holonomy_free_section`, for every finite signed graph (any edge list: no connectivity or
simple-graph premise, parallel edges and self-loops allowed). It is stated for closed walks; the
classical form with simple cycles (an odd closed walk contains a negative cycle) is not
mechanized. `balanced_dicycles_positive`: in a balanced
graph every directed cycle is positive; `balanced_no_positive_acyclic`: balance plus "no positive
directed cycle" leaves no directed cycle at all. Instances: `z2_triangle_merge` (an unbalanced
triangle with two directed paths of different sign), `z2_square_balanced`.

**The bridge to E (`SignedResolver.v`, reading B).** The resolver model: one value type `X` with a
partial order that has a least and a greatest element and finite height; a state exposes each
vertex of a finite list through a lens with extensionality; vertex `v` is updated by its resolver
`Fv v` from the current state (`rupd`), and runs, fairness and settling are those of
`DistributedCycles.v` (`prs`, `Fair`, `Settles`). The signed interaction graph is the **global**
graph: `Resp sg` says each resolver reads only its in-neighbors and is monotone in its positive
inputs and antitone in its negative ones, with signs fixed across all states (the in-neighbor
reading is `resp_reads_in_neighbors`). Every bridge theorem also takes `SgOn` (the endpoints of
every signed edge are vertices) and both attempts assume the greatest element. Local
(state-dependent) graphs are out of scope.

- `switched_monotone`: under `Resp` and a switching `o`, every resolver is monotone for the
  switched orders (`leo`, `le_o`).
- `signed_settlement` (attempt 1): with `slfp o` the least fixed point of the switched order
  (`DistributedCycles.Lfp` after the change of order): from every start `h0 <= slfp o` (switched
  order) every fair schedule settles at `slfp o` (`q1_below`); from every sound start
  (`h0 <= Fsync h0` in the switched order) every fair schedule settles at the least fixed point
  above `h0`
  (`q1_sound_settles`); and E holds from every start `h0 <= slfp o`: `EffectiveCanon` of
  `CanonicalExecution.v` (Settlement and CanonicalFidelity) with the canonicalizer `const (slfp o)`,
  together with the left side of `esh_exact` (Settlement, CanonAgree, CanonConv; S and H are
  trivial here because there are no events). The switching is a hypothesis;
  `signed_settlement_harary` derives it from balance (no closed walk with an odd number of negative
  edges) and concludes the switching, fair settlement and E from low starts (a subset of
  `signed_settlement`'s conclusions).
- `signed_fidelity` (attempt 2): with `Resp`, a switching and at most one fixed point, every fair
  schedule from **every** start settles at it, and E holds from every start (`q1_unique_iff` after
  the change of order; it uses the greatest element). `signed_fidelity_harary` derives the
  switching from balance. Uniqueness is a hypothesis. The global sign route to uniqueness (no
  positive directed cycle in the global graph: Aracena 2008, and the global corollary of Richard
  and Comet 2007, cited) collapses on balanced graphs to acyclicity
  (`balanced_no_positive_acyclic`), that is, to Robert (mechanized: `rb_robert_boolean`,
  [`RobertFair.v`](distributed.md#fair-schedules-on-acyclic-networks-robertfairv)). Richard and Comet's theorem is itself
  local (multivalued: no positive circuit in any local interaction graph gives at most one fixed
  point; restated as a local theorem in Richard 2010, Theorem 3); its Boolean case is
  `local_fidelity` below, which strictly extends the global route (`local_weaker_than_global`).
- Non-vacuity: `neg_chain_settles` (a negative edge and a non-trivial switching; every start is
  low), `unique_pos_cycle` (a positive directed cycle with one fixed point; every global
  certificate of it contains that cycle, `unique_pos_cycle_every_certificate`, so the "no positive
  directed cycle" condition never applies to it).

**What breaks, each a theorem.**

| Theorem | Network | Hypothesis shown needed |
|---|---|---|
| `neg2_no_fixed_point` | `x0 := not x1`, `x1 := x0` (negative 2-cycle) | balance: no switching, no fixed point, no schedule settles (compare the negation counterexample; unlike `flip_noflush`, there is no fixed point at all) |
| `copyback_ghost` | `x0 := x1`, `x1 := x0` (positive 2-cycle) | the start condition for fidelity: from the sound start `(1, 1)`, above `slfp = (0, 0)`, every schedule stays put, so CanonicalFidelity and E fail; two orders from `(0, 1)` reach both fixed points (`copyback_without_authority`, the ghost of `ghost_exact`) |
| `toggle_ghost` | `x0 := not x1`, `x1 := not x0` (balanced, switching `(false, true)`) | the same with negative edges: `slfp = (0, 1)`, the ghost is `(1, 0)` |
| `ring_needs_low_start`, `ring_low_start_E` | the positive 3-ring of `dist_ring_livelock` | the start condition for fair-schedule settlement: from `(1, 0, 0)` a fair schedule never reaches quiescence. E's Settlement half (a flush word exists) holds from every start; from `(1, 0, 0)` E fails through CanonicalFidelity (`[2; 1]` reaches the quiescent state `(1, 1, 1)`) |
| `unbalanced_unique_oscillates` | `x0 := x0`, `x1 := x0 and not x1` | balance in attempt 2: one fixed point, yet no schedule from `x0 = 1` settles |
| `flip_needs_top`, `flip_needs_top_resolver` | `flip_noflush`'s swap on `{fz < fa, fb}` | the greatest element: monotone, one fixed point, no top, no flush from `fa`; inside the resolver model every other hypothesis of `signed_fidelity` holds (lens, least element, finite height, `SgOn`, `Resp`, a switching, uniqueness) and E's Settlement fails from `fa` |
| `xor_no_certificate` | `x1 := x0 xor x1` | lossy non-monotone resolvers are rejected: every certifying graph is unbalanced |
| `cyc3_unsignable` | the 3-cycle permutation of `{t0, t1, t2}` | signability: no partial order with a least element makes it monotone or antitone, and it has no fixed point |

So the bridge is a set of sufficient certificates for E under an explicit resolver semantics (global
signs, bounded finite-height value sets, low starts or a unique fixed point), not an identity
between signed-cycle conditions and E. Statement review (#81): each exported statement above was
checked with `Check`/`About` against these descriptions; the theorems `resp_reads_in_neighbors`,
`signed_fidelity_harary`, `ring_low_start_E`, `flip_needs_top_resolver` and
`unique_pos_cycle_every_certificate` were added where the prose claimed more than a statement.

## Local interaction graphs: local fidelity and local settlement (`LocalSigned.v`)

**Setting.** The Boolean resolver model of `SignedResolver.v` (value set `bool`, a lens with
extensionality on the vertex list `js`, resolvers `Fv`, the asynchronous step `rupd`). The **local
interaction graph** `G(x)` at a state `x` is the discrete Jacobian of Remy, Ruet and Thieffry
(2008): an arc `j -> i` at `x` when flipping `x_j` changes `Fv i` (`larc`), with sign
`lneg x j i = xorb (Fv i x) (x_j)` (`true` is negative). `lneg_spec`: the arc is positive iff
raising `x_j` from `false` to `true`, the other coordinates as in `x`, raises `Fv i`, and negative
iff it lowers it. Cycles are elementary (a nonempty list of distinct vertices, `IsCycle`), and the
sign of a cycle is the xor of its arc signs (`csign`). `NoLocalPos I`, `NoLocalNeg I`,
`NoLocalCycle I`: for **every** state `x`, `G(x)` restricted to `I` has no positive cycle, no
negative cycle, no cycle at all. The global certificate of `SignedResolver.v` is `Resp sg`, with
signs fixed across all states; `SgCycle sg c b` is an elementary cycle of `sg` with sign `b`.

**Local fidelity.**

- `rrt_sub`, `local_fidelity` (Remy, Ruet and Thieffry 2008, mechanized for every `n`):
  `NoLocalPos js` implies that `Fsync` has at most one fixed point. The proof is an induction on
  subcubes: every cycle of `G(x)` at a fixed point `x` is positive (`fixed_csign`), so under the
  hypothesis `G(x)` is acyclic and has a sink `k` (`cycle_or_sink`); two fixed points that disagree
  everywhere then give, after flipping `k`, two fixed points of a smaller subcube.
- `local_fidelity_canon`: with `NoLocalPos js` and a fixed point `q`, CanonicalFidelity with the
  constant canonicalizer `q` from every start. No global sign hypothesis.
- `local_signed_fidelity`: the lift through `signed_fidelity`. `SgOn`, `Resp` and a switching of
  the global certificate, plus `NoLocalPos js` in place of the uniqueness hypothesis (now derived),
  give fair settlement from every start at the unique fixed point and E from every start.
- `local_in_global`, `local_cycle_global`, `global_to_local`: under `Resp` every local arc is an
  edge of `sg` with the same sign, so "no positive cycle in the global certificate" implies
  `NoLocalPos js` (non-vacuity: `global_to_local_instance`, the unbalanced negative 2-cycle).
- `local_weaker_than_global`: the converse fails. For `x0 := x1 && x2`, `x1 := x0 || x2`,
  `x2 := false` no `G(x)` has any cycle (arc `1 -> 0` needs `x2 = 1`, arc `0 -> 1` needs
  `x2 = 0`), yet **every** global certificate contains the positive 2-cycle `0 -> 1 -> 0`. The
  fixed point is unique, every fair schedule from every start settles at it, and E holds from every
  start. The global sign route never applies to this network.

**Local settlement.**

- `local_neg_free_no_fixed_point`: the naive local form of the negative-cycle rule is false. The
  6-vertex Boolean network `tn_F` (Tonello 2017, section 5: the Boolean conversion of Richard
  2010's multivalued Example 6, vertex `3i + h - 1` carrying "component `i` is at level at least
  `h`") has no negative cycle in any local graph and no fixed point, so no run ever settles and E's
  Settlement fails from every start. Six vertices is the least possible in the Boolean case
  (Tonello, Farcot and Chaouiya 2018, cited: up to five components a cyclic attractor forces a
  local negative cycle).
- `richard_t3` (Richard 2011, Theorem 3, mechanized for every `n` along Richard's proof:
  `claim1`, `claim2`, `partners`, `claim3`, `four_point`, `opp_core`, and Lemma 2 as
  `opp_false`): `NoDup js`, `NoLocalNeg js` and `OutDeg1 js` (every vertex of every local graph
  has out-degree at most one, which is non-expansiveness for the Hamming distance:
  `outdeg_nonexpansive`) imply that from every state some update word reaches a fixed point
  (`t3_path`). So a fixed point exists and E's Settlement holds from every start. The reachability
  form is the content of Ruet 2017, Remark 2 (no cyclic attractor).
- `richard_t4` (Richard 2011, Theorem 4, with the same reachability form): `NoLocalNeg js` and one
  vertex on every positive cycle of every local graph give a fixed point and E's Settlement from
  every start. It is proved from `rrt_sub` applied to the network with that vertex negated.
- `shih_dong_E` (Shih and Dong 2005, with paths): `NoLocalCycle js` gives a unique fixed point,
  reached from every state, and E from every start, with no global sign hypothesis.
- `shih_dong_not_fair`: fair asynchronous settlement does **not** follow, even from
  `NoLocalCycle`. For `x0 := not x1 && not x2`, `x1 := x0 || not x2 || x3`,
  `x2 := x0 && x1 && x3`, `x3 := not x0` no local graph has a cycle and E holds from every start,
  but the fair periodic schedule `2, 3, 0, 1, 3, 2, 0, 1, ...` from `(1, 1, 0, 1)` returns there
  every 8 steps and never settles. Robert's theorem (an acyclic **global** graph) does give fair
  convergence (`rb_robert_boolean`); the local hypothesis does not. An exhaustive search (not
  mechanized) over all 3-vertex networks finds no such example, so 4 vertices is the least. Relation to the
  literature: that local acyclicity does not make the asynchronous state graph acyclic is known
  (Richard 2019, attributing it to a 4-component example of Shih and Dong 2005); the fair-schedule
  form was not found in the literature searched
  ([LOSSY-NETWORKS.md, P2, novelty check](../../docs/LOSSY-NETWORKS.md#p2-rootless-convergence-in-reading-b-the-runtime-model)).
- `ring_local_conditions`: the positive 3-ring satisfies `NoLocalNeg`, `OutDeg1` and the
  Theorem 4 hypothesis (vertex 0 is on every local positive cycle), and has E's Settlement from
  every start; it has two fixed points, a fair schedule from `(1, 0, 0)` that never settles, and
  CanonicalFidelity fails there. Under either corrected local condition only E's Settlement half
  follows.

**What each local hypothesis gives** (Boolean, every `n`; "no" entries are mechanized
counterexamples).

| Local hypothesis | Fixed points | E's Settlement | CanonicalFidelity | Fair-schedule settlement |
|---|---|---|---|---|
| `NoLocalPos` | at most one (`local_fidelity`) | no (`neg2_no_fixed_point` with `global_to_local_instance`) | yes, every start (`local_fidelity_canon`) | no (same network) |
| `NoLocalPos`, plus `Resp` and a switching | exactly one | yes | yes | yes, every start (`local_signed_fidelity`) |
| `NoLocalNeg` | possibly none (`local_neg_free_no_fixed_point`) | no | vacuous | no |
| `NoLocalNeg` and `OutDeg1` | at least one (`richard_t3`) | yes | no (`ring_local_conditions`) | no (same) |
| `NoLocalNeg` and a vertex on every local positive cycle | at least one (`richard_t4`) | yes | no (`ring_local_conditions`) | no (same) |
| `NoLocalCycle` | exactly one (`shih_dong_E`) | yes | yes | no (`shih_dong_not_fair`) |
| `NoLocalCycle` and `OutDeg1` | exactly one | yes | yes | yes from every start with at most two unstable vertices (`one_token_fair_settlement`, [below](#fair-settlement-under-local-conditions-localfairsettlementv); `two_token_fair_settlement`, [below](#two-unstable-vertices-localtwotokenv)); from every start open |

**For gap 3 (rootless propagation on lossy networks).** On fidelity the local route strictly
extends the global certificates of `SignedResolver.v` (`local_weaker_than_global`: a network
outside every global sign condition, with E certified). On settlement, local conditions certify
E's Settlement half (flush words: Theorems 3 and 4, Shih and Dong) and, with `NoLocalCycle`, all of
E, but none of these local conditions alone gives fair-schedule settlement: from every start that
still needs the global switching (`local_signed_fidelity`) or a globally acyclic graph.
`NoLocalCycle` with `OutDeg1` gives it from starts with at most one unstable vertex
(`LocalFairSettlement.v`, next section) and at most two (`LocalTwoToken.v`, the section after). The certificates remain
sufficient, not an exact condition; multivalued value sets are not covered (the multivalued
local results of Richard and Comet 2007 and Richard 2010 are cited).

Decision procedure for the instances: `chk` enumerates every state and every list of distinct
vertices (`nl_complete`) and is proved sound (`chk_sound`); the 6-vertex check covers 64 states
and 1,957 vertex lists.

## Fair settlement under local conditions (`LocalFairSettlement.v`)

**Setting.** The Boolean lens model of `LocalSigned.v`. (A) is `NoLocalCycle js`; `AcyclicAt x`
is (A) at the single state `x`. (B) is `OutDeg1 js`, out-degree at most one in every local graph,
which is Hamming non-expansiveness of `Fsync` (`outdeg_nonexpansive`). `ucnt x` counts the unstable
vertices of `x` (the tokens). `orb n x` is the synchronous orbit. `NoClosedChange P` says that no
closed asynchronous run from a state in `P` changes the state: if the word `w1 ++ w2` leads from
`x` back to `x`, so does `w1`; on a finite state space this is acyclicity of the asynchronous state
graph. `Fair` and `Settles` are those of `DistributedCycles.v`, as in `LocalSigned.v`.

**Synchronous form.**

- `sync_orbit_fixed`: `NoDup js`, (B), a periodic orbit `orb (S L) x = x`, and (A) at one state
  `orb t x` of it imply `Fsync x = x`. Proof: let `U` be the vertices that flip on the orbit and `D`
  the Hamming distance on `U` between orbit points. Non-expansiveness gives
  `D (i + 1) (k + 1) <= D i k`, and periodicity turns this into equality. If some `u` in `U` had no
  out-arc into `U` in `G(orb t x)`, then flipping `u` at `orb t x` would not change `Fsync` on
  `U`, and comparing with an orbit point that differs from `orb t x` at `u` gives
  `D s t <= D s t - 1`. So `G(orb t x)` restricted to `U` has no sink, hence a cycle
  (`cycle_or_sink`), against (A) there.
- `sync_simple`: (A) and (B) give a unique fixed point `q` that every synchronous orbit reaches
  within `2^|js|` steps (`pigeon`, `nodup_states_bound`). This is the conclusion of Shih and Ho
  1999, Theorem 3.1, read in full: their hypothesis (b), `F(V(x))` inside `V(F(x))`, is (B) by
  their Lemma 4.1 (column `j` of their discrete Jacobian holds the out-arcs of `j`). Their proof
  goes through a fixed point and its von Neumann neighborhood; this one needs (A) only on the orbit.

**Tokens and the single-token case.**

- `ucnt_mono`: (B) alone, every asynchronous step: `ucnt (rupd v x) <= ucnt x` (firing `v` makes
  `v` stable unless it has a self-loop, and changes the status of at most one other vertex).
- `one_step_F`, `orbit_of_run`: with at most one unstable vertex, an asynchronous step is a no-op
  or the synchronous step, so every run from such a state stays on its synchronous orbit.
- `one_token_closed`: (B), `AcyclicAt x` and `ucnt x <= 1`: no closed asynchronous run from `x`
  changes the state. This is the report's single-token lemma, localized to one state and with no
  fixed point used.

**From acyclicity to fair settlement.**

- `fair_settles_closed`: if `P` is preserved by every asynchronous step and `NoClosedChange P`
  holds, every `Fair` schedule from every start in `P` `Settles` at a fixed point. The proof
  splits the schedule into fair rounds (`round`); a round with no change ends at a fixed point,
  and more than `2^|js|` rounds with changes would revisit a state, giving a closed run with a
  change.
- `fair_settlement_of_acyclic`: (A) and `NoClosedChange True`: every fair schedule from every
  start settles at the unique fixed point (the E-side analogue of `FairFlushR`).
- `one_token_fair_settlement`, `fair_settles_once_one_token`: (A) and (B): every fair schedule
  from a start with at most one unstable vertex settles at the unique fixed point; so does every
  fair run that ever reaches such a state.
- `rank_closed`, `rank_ok_sound`: a rank that strictly decreases along every real move certifies
  `NoClosedChange True`; on Boolean vectors it is decided by `rank_ok_b`.

**Instances.**

- `shih_ho_instance` (non-vacuity): Shih and Ho's 4-vertex example (their Section 3, item (5)),
  `x0 := not x1 || not x2 || x3`, `x1 := 1`, `x2 := 1`, `x3 := not x0 || x1 || x2`. It has (A)
  and (B), local arcs `0 -> 3` at `0000` and `3 -> 0` at `0110` (so the global interaction graph
  has a cycle and Robert's theorem does not apply; `rb_converse_fails` reads this as the failure
  of Robert's converse), an acyclic asynchronous state graph (the
  longest-path rank, checked by `rank_ok_b`), so every fair schedule from every start settles at
  `1111`; the state `0110` has exactly one unstable vertex.
- `outdeg_needed`: (B) is needed. Shih and Dong's network `sd_F` has (A) and out-degree 2 at
  `0000`, a synchronous periodic orbit of length 3 through `0110`, a closed asynchronous run that
  changes the state, and a fair schedule that never settles (`shih_dong_not_fair`).
- `no_neg_not_enough`: no local negative cycle is not enough. The positive 3-ring has (B) and no
  local negative cycle, and a fair schedule that never settles (`ring_local_conditions`).
- `no_pos_not_enough`: no local positive cycle is not enough. The negative 3-ring
  `x0 := x1`, `x1 := x2`, `x2 := not x0` has (B) and no local positive cycle, a closed
  asynchronous run `2, 1, 0, 2, 1, 0` from `000` that changes the state, and no fixed point, so no
  fair schedule settles from any start.

**What is open (gap 3 stays open).** Under (A) and (B): no closed asynchronous run whose states all
have two or more unstable vertices. With `fair_settlement_of_acyclic` that would give fair
settlement from every start. Computational evidence, not mechanized: no such run for n = 3 to 6
([research/gap3-fair-settlement](../../research/gap3-fair-settlement/README.md)); the key lemma F2
there is proved here for one token (inside `sync_orbit_fixed`). Two tokens are settled in
`LocalTwoToken.v` (next section); three or more are open. Not found in the literature searched;
Shih and Ho 1999 treat synchronous iteration only. These are sufficient conditions; an exact
condition for gap 3 is also open.

## Two unstable vertices (`LocalTwoToken.v`)

**Setting.** As in `LocalFairSettlement.v`: (A) is `NoLocalCycle js`, (B) is `OutDeg1 js`,
`ucnt x` counts the tokens. `un x t` says that `t` is unstable at `x`; `TwoTok x a c` says that
the tokens of `x` are exactly `a` and `c`. Inside the proof `p` is the unique fixed point (from
`shih_dong_E`), `dp x` is the Hamming distance from `x` to `p`, a token at `v` is good when
`x_v <> p_v` (firing it moves toward `p`) and bad otherwise, and `G1 x b v` says that the tokens
of `x` are a good `b` and a bad `v`.

**Main results.**

- `two_token_closed`: `NoDup js`, (A), (B) and `ucnt x <= 2`: no closed asynchronous run from `x`
  changes the state. `two_token_no_closed_change` is the same statement as
  `NoClosedChange (fun x => ucnt x <= 2)`.
- `two_token_fair_settlement`, `fair_settles_once_two_tokens`: (A) and (B): every fair schedule
  from a start with at most two unstable vertices settles at the unique fixed point, and so does
  every fair run that ever reaches such a state (from `fair_settles_closed`).

**The proof, in five steps.**

1. `not_both_bad`: with two tokens at least one is good. If both were bad, `Fsync x` would be two
   steps further from `p` than `x`, against non-expansiveness (`outdeg_nonexpansive`).
2. `tight`, `tight_arc`, `head_arc` (rigidity). At a `G1` state `Fsync x` is exactly as far from
   `p` as `x`. Then every `j` where `x` and `p` differ has an out-arc in `G(x)` to a vertex `i`
   with `F_i(x) <> p_i`: otherwise `Fsync (flip j x)` would be too far from `p`. So every vertex
   of `D(x)` plus the bad token `v` has an out-arc inside that set as soon as `v` points into
   `D(x)`, and `G(x)` would have a cycle (`cycle_or_sink`). Hence the bad token never points into
   `D(x)`: not at a stable vertex, and not at the good token either.
3. `G1_T`, `G1_H`, `run_bad_or_dec`. Every move that keeps two tokens keeps `G1`: the bad token
   passes to a bad receiver by step 2, and the good token passes to a good one by step 1. If no
   state of a closed two-token run is `G1`, every move fires a good token and `dp` strictly
   decreases, which is impossible; so every state of the run is `G1`.
4. `swap_TH`. At a `G1` state, "fire the good token, then the bad one" can be replaced by "fire the
   bad token, then the good one", reaching the same state with two tokens throughout: the bad
   token keeps an out-arc (`ucnt_mono` rules out losing a token), and by step 2 it does not point
   at the good token. The converse swap can fail.
5. `W_sort`, `W_main`. A closed `G1` walk (the inductive `W`, labelled by which token moves) is
   rearranged with `swap_TH`: all bad-token moves first (`H^h T^h`, `W_sort`; `W_dp` gives
   equally many of each), rotated to start between the two blocks (`T^h H^h`), and then each `H`
   is pulled forward next to a `T` (`W_pullH`), giving `(T H)^h`. From a state with tokens
   `{b, v}`, "fire `b`, then `v`" is the synchronous step (`F_two`). So the closed run yields
   `orb h z = z` with `h >= 1` at a state `z` that is not fixed, against `sync_orbit_fixed`.

**Instance.** `two_token_instance`: Shih and Ho's network `sh_F` at `1110` has exactly two
unstable vertices, `0` (bad: it agrees with the fixed point `1111`) and `3` (good), so the `G1`
case occurs, and every fair schedule from `1110` settles at `1111`.

**What is open.** Three or more tokens. For three tokens a bad token can pass to a good receiver
(a SAT witness at n = 4, [K2.md](../../research/gap3-fair-settlement/K2.md)), so the token types
are not invariant and step 3 does not hold as stated; step 4's swap fails exactly when one
token's vertex points at another token. Gap 3 stays open.

## The imbalance law (`LocalTokenBalance.v`)

**Setting.** As in `LocalTwoToken.v`, but with no acyclicity hypothesis. For any state `p`,
`ng p x` and `nb p x` count the tokens of `x` that are good (`x_t <> p_t`) and bad
(`x_t = p_t`); `ucnt_split` says that they add up to `ucnt x`.

**Main results.**

- `image_distance` (no hypothesis, any `p`): `dS (Fsync x) p + ng p x = dS x p + nb p x`, that is
  d(F x, p) = d(x, p) - g + b. `Fsync x` differs from `x` exactly at the tokens; a good token flips
  toward `p` and a bad one away.
- `bad_le_good`: `NoDup js`, (B) and `Fsync p = p`: `nb p x <= ng p x` at every state, for every
  number of tokens. Non-expansiveness with `Fsync p = p` (`outdeg_nonexpansive`) gives
  d(F x, p) <= d(x, p), and `image_distance` turns it into b <= g. Neither (A) nor the absence of
  self-loops is used.
- `bad_half`, `bad_le_half`: `2 * nb p x <= ucnt x` and `nb p x <= ucnt x / 2`: one token is good,
  two or three tokens have at most one bad, four or five at most two.
- `not_both_bad_k2`: `LocalTwoToken.not_both_bad` recovered as the case of two tokens.
- `three_token_shape`: with exactly three tokens, (g, b) is (3, 0) or (2, 1). A counting
  consequence only.

**Instance.** `token_balance_instance`: Shih and Ho's network `sh_F` with (A), (B) and the fixed
point `1111` has two tokens (1, 1) at `1110`, where the bound b <= g is attained, three tokens
(3, 0) at `0100`, and three tokens (2, 1) at `1001`.

**What is open.** Nothing here is about closed runs with three or more tokens. The structural
lemmas mined for that case, and the obstruction, are in
[K3.md](../../research/gap3-fair-settlement/K3.md). Gap 3 stays open.

## Static consistency as a CSP (`TransportCSP.v`)

**Setting.** Reading A: a network is a list of edges `(u, v, f)` with `f : D -> D` on one fiber
`D`, and a section satisfies `f (s u) = s v` on every edge (`msection`). Pinned vertices are a list
`P` of `(vertex, value)` pairs. A relation is an arity and a predicate on tuples; `rgraph f` is the
graph `{(x, f x)}` and `rpin c` the unary relation `{c}`. For a transport family `F` and pin values
`cs`, the template is `gamma F cs` (Gamma_F). `csp_of G P` is the CSP instance of the network: one
binary constraint per edge and one unary constraint per pin. Operations are `p : list D -> D`
read at an arity `k`; `preserves k p R` is the usual polymorphism condition (applied to the
columns of any `k x n` matrix whose rows lie in `R`).

**Main results (the bridge).**

- `section_iff_csp`: when `G` is labeled by `F` and the pin values lie in `cs`, `G` has a section
  agreeing with `P` iff `csp_of G P` is satisfiable, and `csp_of G P` is an instance of
  CSP(Gamma_F). `section_solution` is the pointwise form; `section_iff_csp_nopin` the unpinned one.
- `hsection_iff_csp`, `hsection_over`, `msection_as_hsection`: reading B's merges. A merge edge
  `(us, v, g)` with `g` of arity `k` is the `(k + 1)`-ary relation `hgraph k g`; reading A is the
  case `k = 1`.
- `pol_iff_commute`: `p` preserves `rgraph f` iff `f (p xs) = p (map f xs)` for every `xs` of length
  `k`. `pol_pin_iff`: `p` preserves `{c}` iff `p (c, ..., c) = c`. `pol_gamma_iff`: Pol(Gamma_F) is
  exactly the set of operations commuting with every map of `F` (the centralizer of `F`) that fix
  the pinned values.
- `pol_solutions`: a polymorphism maps `k` solutions of any instance over Gamma to a solution
  (the closure property); `section_closure` is the network form.
- `group_maltsev`, `group_pol`, `group_section_as_msection`: for a group acting on itself by left
  translation, `m (x, y, z) = x y^-1 z` commutes with every translation and satisfies
  `m (x, x, y) = y = m (y, x, x)`; the group-labeled networks of `CohomologyGraph.v` are
  translation networks, whose polynomial criterion is `section_iff_coboundary`.
- `prj_signs`, `prj_signs_eq`, `net_in_hard_family`, `hard_family_csp`: the maps `prj c p` of
  `LossyHardness.v` depend on the clause `c` only through its sign pattern, so every network
  `net f` is labeled by one fixed family of 26 maps (`hard_family`: `filt`, `pin`, and 24
  projections `sprj n1 n2 n3 p`). Section existence for that fixed family is 3-SAT on every formula
  by the existing reduction (`net_section_iff_sat`, linear size by `net_size`), so CSP(Gamma) for
  this one template is NP-complete. `hard_family_min_fails`: the family is not monotone and `min`
  is not one of its polymorphisms.

**Predicted cells.**

- `mono_min_commute`, `mono_max_commute`, `mono_median_commute`, `med_majority`, `chain_pol`: a
  monotone map on a chain commutes with `min`, `max` and the median, so for every family of
  monotone maps and every pin list, `min` and `max` (semilattice operations) and the median (a
  majority operation) are polymorphisms of Gamma_F. `chain_min_section`: the pointwise min and max
  of two sections are sections.
- `ac_exact` (monotone transports on the finite chain `{0..N}`, pinned vertices): `ac_decide N G P`
  runs arc consistency (a simultaneous revise of every domain, iterated until no domain shrinks)
  and returns `true` iff a section with values in `{0..N}` agreeing with the pins exists. The
  witness is the minimum of each arc-consistent domain (`ac_min_section`); pruning never removes a
  section's value (`run_spec`). Termination: `ac_run_some`, within `measure init + 1` passes, and
  `ac_pass_bound`: `measure init <= |vs| (N + 1)`, `vs` the vertices of `G` and the pinned
  vertices. Step bound (stated, not mechanized as a cost model): each pass examines every value of
  every domain against every edge, `O(|vs| (N + 1) |G| (N + 1))` checks, so the procedure is
  polynomial in the network and the chain length. `ac_family` states it per family.
- `ac_needs_mono`: monotonicity is needed. The negation `x |-> 1 - x` around a triangle on `{0, 1}`
  passes arc consistency with full domains and has no section.
- `diamond_join_fails`: on the diamond `0 < a, b < 1`, the lossy map `f (0) = f (a) = f (b) = 0`,
  `f (1) = 1` is monotone and does not commute with join, so join is not a polymorphism of
  Gamma_{f}; it does commute with meet (`diamond_meet_ok`). `diamond_g_fails`: the monotone map
  `a, b |-> a` (0 and 1 fixed) commutes with neither join nor meet. The chain hypothesis matters for
  the min/max argument.
- `median_family`, `median_family_not_lattice`: a non-chain family with a majority polymorphism.
  On `bool * bool`, the swap, the lossy projection `(x, y) |-> (x, x)` and the negation of the
  first coordinate commute with the coordinatewise median, a majority operation that fixes every
  pin; the lattice meet and join are not polymorphisms of this family. Tractability of section
  existence for such families is the cited bounded-width result (Jeavons, Cohen and Gyssens 1997;
  Feder and Vardi 1998); only the commutation is mechanized.

**Instances.** `ac_ex1` (a path, a lossy decrement and a parallel copy, pinned: a section),
`ac_ex2` (two paths that disagree at a merge: `ac_decide = false`, no section), `ac_ex3` (a lossy
2-cycle: the arc-consistent domains are `{3}` and the only section is 3 everywhere),
`bridge_instances` (the C22 tree as an unsatisfiable CSP instance, `two_G` of `RootSet.v` as a
satisfiable one).

**Cited, not mechanized.** The CSP dichotomy: for a finite template Gamma, CSP(Gamma) is in P or
NP-complete, decided by the polymorphisms (Bulatov, FOCS 2017; Zhuk, FOCS 2017 and J. ACM 67(5),
2020). Mal'tsev templates are tractable (Bulatov and Dalmau, SIAM J. Comput. 36(1), 2006). The
polymorphism connection and the tractable closure classes (constant, majority, semilattice,
affine): Jeavons, Cohen and Gyssens, J. ACM 44(4), 1997; Jeavons, Theoret. Comput. Sci. 200, 1998.
Bounded width: Feder and Vardi, SIAM J. Comput. 28(1), 1998. Per fixed family `F`, section
existence is therefore classified by Pol(Gamma_F); the correspondence above is what makes that
reading precise.
