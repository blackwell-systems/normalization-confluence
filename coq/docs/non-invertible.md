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
