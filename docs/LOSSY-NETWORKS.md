# Lossy networks without a spanning root: complexity, root sets, and signed cycles

**Status: research note, forward-looking.** This page grounds an open problem; the note itself
adds no theorems to the gate. Several of its claims have since been mechanized (the root-set
criterion and counting, #54; the 3-SAT reduction, #57; event order under a root set, #59;
rootless single invertible cycles, #48) and carry the mechanized tag below. Every claim carries
one of four tags:

- **[mechanized: name]**: a theorem in [`coq/`](../coq), axiom-free, passing `coq/verify.sh`.
- **[verified: source]**: a published theorem, checked against the primary source or a reliable
  restatement (named), with its hypotheses as stated there.
- **[our conjecture]**: a claim of this note. Where a proof sketch is given it is a sketch, not a
  proof; where an empirical check exists it is cited (`research/lossy/validate.py`).
- **[refuted]**: a hypothesis from the first-pass analysis that is false as stated, with the
  correct statement next to it.

The question came from [REGIME-AUDIT.md](../REGIME-AUDIT.md) section 12, whose row "General graph
(no out-arborescence, several cycles): none mechanized; none known" has since been closed by
`RootSet.v` (#54) and `LossyHardness.v` (#57), and from the categorical paper's conclusion, which
lists "a cohomological account of the non-invertible case" as open. Read this note as the
companion to [REGIMES.md](REGIMES.md) for networks the current theorems do not decide, in the same
register as [LYAPUNOV-EXTENSION.md](LYAPUNOV-EXTENSION.md). The mechanized results it led to are
described in [coq/docs/non-invertible.md](../coq/docs/non-invertible.md).

## The short version

1. "A network with lossy maps" means two different things in this repository, and the existing
   theorems split cleanly between them. In the **constraint reading** (A) every edge is an equation
   and the consistent states are the limit of the diagram; the cohomology files use it. In the
   **resolver reading** (B) every vertex is computed from all its sources jointly and the consistent
   states are fixed points of a finite discrete dynamical system; the federation files use it.
2. Reading A is binary constraint satisfaction with functional constraints. Deciding whether a
   consistent state exists is NP-complete in general (the 3-SAT reduction is mechanized:
   `net_section_iff_sat`), polynomial with one source component (`rooted_criterion` is the
   correctness core), and exponential only in the number of source components of the condensation
   (David's root sets, 1995; mechanized as `root_set_criterion_graph`). So no polynomial-time "cohomological
   account" of the general non-invertible case exists unless P = NP; the right object is the root
   set, and the right tractability theory is that of database joins.
3. Reading B is the theory of finite (Boolean and multivalued) networks. Thomas's rules, proved by
   Remy, Ruet and Thieffry, Richard and Comet, Richard, and Aracena, give signed-cycle conditions:
   no negative cycle gives a consistent state, no positive cycle gives at most one, and the number
   of consistent states is at most `2^{tau+}`. The repository's copy-back and negation
   counterexamples are exactly the positive and negative 2-cycles of that theory.
4. The bridge: over Z/2 with copy and negation labels, holonomy is cycle sign, but cohomology
   (reading A) sees **undirected** cycles and Thomas (reading B) sees **directed** ones. Off the
   invertible fragment, a total order on each fiber signs every lossy map, and "some family of
   orders makes every edge monotone" is a common generalization of trivial holonomy and of the
   monotone regime. The pieces are known; their use for federated or replicated convergence appears
   to be new.

## 1. The question

### Networks

A **network** `N = (V, E, X)` is a finite set of vertices (registries; `nat` in Coq), a finite
fiber `X_v` per vertex (the registry's shared component, or its set of normal forms), and directed
edges `(u, v, f)` with `f : X_u -> X_v` a total map. An edge is **invertible** when `f` is a
bijection and **lossy** otherwise. The Coq files put every vertex on one fiber type `V`
(`CohomologyGeneral.msection` over `@edge (V -> V)`); typed fibers embed into one fiber with a
filter gadget (section 3.2), so nothing below depends on that choice.

The **condensation** of `N` collapses each strongly connected component (SCC) to a point; its
sources are the **source components**. `N` has a **spanning root** when some vertex reaches every
vertex, that is, when the condensation has exactly one source component. "Without a spanning root"
means two or more source components.

### Reading A: the constraint reading

A state `s` (one value per vertex) is **A-consistent** when every edge holds:

```
  s in L_A(N)   iff   f (s u) = s v   for every edge (u, v, f) in E
```

This is `msection s E` in `CohomologyGeneral.v`, `is_section` in `CohomologyGraph.v` (group
labels), and `cycle_section` on a single cycle. `L_A(N)` is the limit of the diagram in finite sets
whose objects are the fibers and whose arrows are the edge maps: the equalizer of the two maps
`prod_v X_v -> prod_e X_{target e}` given by `s |-> (s (target e))_e` and
`s |-> (f_e (s (source e)))_e`. A vertex with several in-edges imposes that all of them agree; this
is the sheaf gluing condition of the categorical paper.

### Reading B: the resolver reading

Each vertex `v` has a source list `src(v)` and a local function
`F_v : prod_{u in src(v)} X_u -> X_v` (a morphism map for one source, a resolver for several;
the Coq models also let `F_v` read `v`'s own value). Vertices with no sources are free. A state is
**B-consistent** when

```
  s in L_B(N)   iff   s v = F_v (s restricted to src(v))   for every v with src(v) nonempty
```

that is, `s` is a fixed point of the global map `F`. `L_B(N)` is also a finite limit (the
equalizer of `id` and `F`), so "the consistent states form a limit" does not distinguish the two
readings; the diagrams differ. Reading B carries a dynamics: updating one vertex,
`s |-> s[v := F_v(s)]`, is `FederationOrder.step`, and the graph of all such single-vertex updates
is the **asynchronous state graph** `Gamma(F)` of discrete dynamical systems (Richard 2010,
Definition 1).

The **interaction graph** `G(F)` has an arc `u -> v` when `F_v` depends on `u`. When each fiber is
totally ordered (identified with an integer interval), the arc is **positive** (resp. **negative**)
when increasing `x_u` by one step can increase (resp. decrease) `F_v`; an arc can carry both signs.
A cycle's sign is the product of its arc signs (Richard 2010, Definitions 3 and 4).

In the Boolean-network formalism every vertex has a local function, so a free vertex (a source, or
a registry whose value nobody overwrites) is `F_v(x) = x_v`: a **positive self-loop**. This is why
the multiplicity results below count sources: each free vertex contributes its whole fiber of
consistent states. Pinning a free vertex to one value, which is what an authority root does,
removes that positive loop. Uniqueness "given the root" in `CoordinatedCycles.v` is uniqueness after
the root's positive self-loop has been pinned.

### How the readings relate

- **They coincide at in-degree at most one.** If every vertex has at most one in-edge and
  `F_v = f_e` for that edge, then `L_A(N) = L_B(N)`. Immediate from the definitions; check 7 of
  `validate.py` confirms it on 1000 random networks.
- **They differ at in-degree two or more, on the same graph and maps.** The diamond
  `u -> v` (copy), `u -> w` (copy), `w -> v` (negation) has no directed cycle and no A-consistent
  state (it forces `v = u` and `v = not u`); in reading B, with any resolver at `v`, it is acyclic
  and has exactly one consistent state per value of the free source `u`. The same holds for
  `c22_cycle_basis_fails` (a tree with constant maps 0 and 1 into one vertex): no A-section, and
  four B-fixed points with a priority resolver. (Check 6.)
- **Each existence problem reduces to the other in polynomial time** (tables given explicitly)
  **[our conjecture]**, validated by checks 8 and 9. B to A: give each vertex `v` with sources
  `u_1..u_k` a product vertex `P_v` over `X_{u_1} x ... x X_{u_k}` with projection edges
  `P_v -> u_i` and an edge `P_v -> v` carrying `F_v`; sections correspond one to one to fixed
  points. A to B: let `v` read its first in-edge, and give every further in-edge `(u_i, v, f_i)`
  a Boolean alarm vertex that keeps its value when `f_i(s u_i) = s v` and negates itself otherwise.
  The agreement constraint of reading A becomes, in reading B, a negative self-loop that is active
  exactly on disagreement.

### Which reading each existing theorem uses (H1)

**H1: verified, with one refinement.** Both readings are present, and every theorem uses exactly
one of them, except `CoordinatedCycles.v`, which drives in B and checks in A.

| Module | Reading | What it states |
|---|---|---|
| `Cohomology.v` | A | single cycle: section iff the loop composite has a fixed point (`has_section`, `fixed_point_iff_trivial_holonomy`, `flip_no_section`) |
| `CohomologyGraph.v` | A (group labels) | `section_iff_coboundary`, `cycle_basis_criterion`, `sat_iff_trivial_holonomy`, `tree_has_section`, `tree_unique`, `H1_classification`, `betti_number` |
| `CohomologyMin.v` | A | minimum coordination counts, `theta_separation` |
| `LossyMinimum.v` | A (any maps) | minimum coordination: `lfeasible_iff_root_set`, `lmin_root_set`, `lmin_decide`, `lmin_reduction`, `lossy_min_is_gfes` |
| `CohomologyGeneral.v` | A (any maps) | `thm_obstruction_general`, `thm_obstruction_reachable`, `diagnose_*`, `c15_*`, `out_tree_section`, `out_tree_unique`, `rooted_criterion`, `rooted_coordination_suffices`, `c22_cycle_basis_fails`, `c13_two_ways_not_exhaustive` |
| `Categorical.v` | B | `consistent_iff_equalizer`: `Consistent s` iff every target's shared component equals its resolver value `res s B` |
| `FederationOrder.v` | B | `run` is a sequence of single-vertex updates `f i s (s i)` reading `src i`; `order_independent` on acyclic networks |
| `FederationEvents.v`, `FederationGRS.v` | B | `f j t x` overwrites with the image of the sources (morphism or resolver); R1 is `pn_R1` (reads only `src j`); `frun_solves`, `solve_unique` |
| `Federation.v`, `Chaotic.v`, `ChaoticACC.v`, `MonotoneFederation.v`, `FederationEventsCycles.v` | B | a monotone global operator `Phi`; least fixed point and chaotic (asynchronous) iteration |
| `PaperInstances.v` (`prop_cycle_necessary`, `r1_necessary`, `r2_necessary`) | B | federated compensation as a rewrite relation; with identity local repair, `cyc_rep` is exactly `Gamma(F)` |
| `CoordinatedCycles.v` | B then A | values driven along a tree by `FederationOrder.run` (B); balanced non-tree edges checked as `is_section` constraints (A); `copyback_without_authority` runs B and checks A |

The refinement: the categorical paper's Proposition 1 ("a federation is a finite limit") is about
reading B, while its cohomology sections are about reading A. Where the papers apply cohomology
(cycles of single-source morphisms) the two agree. Resolvers appear only on acyclic targets, where
reading B always has a consistent state (Robert's theorem, section 4.1) and cohomology is not
invoked. That is why the distinction has not surfaced; it matters as soon as a network has both
cycles and multi-source targets.

## 2. What is already mechanized

For lossy maps, in reading A:

- **One cycle.** A section exists iff the loop composite `g` has a fixed point; restriction to
  vertex 0 is a bijection from sections onto `Fix(g)` [mechanized: `thm_obstruction_general`,
  `sections_are_fixed_points`]. On a finite fiber, iterating `|X|` times decides reachability from
  a seed [mechanized: `diagnose_bounded`, `diagnose_dichotomy`]; one seed is definitive only when
  fixed points are all-or-nothing [mechanized: `c15_exact_refuter`, `c15_free_definitive`,
  counterexample `c15_definitive_claim_false`].
- **A spanning root with a root-oriented tree.** For every root value the out-tree carries a unique
  section, and the whole graph has a section with that root value iff the driven state satisfies
  every non-tree edge [mechanized: `out_tree_section`, `out_tree_unique`, `rooted_criterion`].
  Deleting all non-tree edges always leaves a section [mechanized: `rooted_coordination_suffices`].
- **No root: a tree can fail.** A tree with two constant maps into one vertex has no section
  [mechanized: `c22_cycle_basis_fails`]. Balance is not static off the invertible fragment
  [mechanized: `noninvertible_balance_not_static`, `c22_rooted_instance`].
- **A root set (added since this note, #54).** Root sets are exactly the vertex sets with an
  outward spanning forest [mechanized: `root_set_iff_forest`]; for any root set and spanning
  forest, a section exists iff some root assignment drives a state satisfying every edge
  [mechanized: `root_set_criterion_graph`, `root_set_criterion_values`, agreement form
  `root_set_agreement`]; sections correspond one to one to consistent root assignments and are
  counted by them [mechanized: `root_set_bijection`, `root_set_count`, `out_forest_unique`];
  existence is a search over the product of root domains [mechanized: `root_set_decide`].
  `rooted_criterion` is recovered as the case of one root [mechanized: `rooted_criterion_recovered`].
- **Hardness (added since this note, #57).** The 3-SAT reduction of section 3.2 [mechanized:
  `net_section_iff_sat`, `net_bijection`, `net_count`, `net_size`, `np_certificate`].
- **Event order under a root set (added since this note, #59).** From a start consistent with the
  forest's driving network, interleavings converge iff each root's independent events commute at
  every value reachable from its start value [mechanized: `forest_events_exact`,
  `forest_events_exact_global`].

For invertible maps (reading A with group labels): `section_iff_coboundary`,
`cycle_basis_criterion`, `plan_exact`, `coordinated_sound`, `prop_minimal_qualified_iff`
[mechanized], with the regular action needed [mechanized: `nonfree_holonomy_counterexample`].

In reading B: on acyclic networks the consistent state exists and is unique given the free
vertices, and every topological order reaches it [mechanized: `frun_solves`, `solve_unique`,
`order_independent`]; this is Robert's theorem in the federation model (section 4.1). On cycles
with monotone maps on a lattice, the least fixed point exists and chaotic iteration reaches it
[mechanized: `kleene_lfp`, `lfp_unique`, `chaotic_reaches_lfp`, `chaotic_acc_reaches_lfp`]; it is
not the only fixed point [mechanized: `bottom_matters`]. Without an authority, two orders can reach
different consistent states [mechanized: `copyback_without_authority`], and a negation cycle has no
consistent state and repair never terminates [mechanized: `prop_cycle_necessary`]. On a single
coherently oriented cycle with invertible labels and every edge a writer (added since this note,
#48): a consistent state exists, and every state reaches one, iff the holonomy is trivial, and the
reachable one is unique iff the group is trivial [mechanized: `rootless_section_iff_holonomy`,
`rootless_nf_exists_iff`, `rootless_unique_iff`, `rootless_unique_normal_form_iff`].

What was missing when this note was written is everything between "one source component" and
"arbitrary": the regime of the audit's then-open row. For reading A it is now closed (#54, #57);
for reading B with lossy maps it is still open (REGIME-AUDIT.md gap 3).

## 3. Complexity map, reading A

### 3.1 The map

| Network (reading A) | Deciding existence of a consistent state | Status |
|---|---|---|
| General, maps given as tables | **NP-complete** | membership: [mechanized: `np_certificate`]; hardness: reduction 3.2 [mechanized: `net_section_iff_sat`, `net_size`, `net_tables`], NP-completeness by the standard argument; consistent with [verified: Cooper, Cohen, Jeavons 1994, as reported by David 1995 section 2.2] |
| In-degree at most one (each weak component has at most one cycle) | polynomial: per cycle, test `Fix(g)` | [mechanized: `thm_obstruction_general`]; the reduction to cycles is immediate |
| Every map a bijection (any graph) | polynomial, `O(|X| (|V| + |E|))`: fix one value per component, propagate, check | [verified: Khot 2010 survey, the remark that value-1 unique games are solved by propagation]; with the regular action, [mechanized: `section_iff_coboundary`] |
| One source component (a spanning root `r`) | polynomial, `O(|X_r| (|V| + |E|))`: drive each root value, check | correctness [mechanized: `rooted_criterion`, `out_tree_unique`]; algorithm [verified: Zhang and Yap 2011, Corollary 3, `O(e d^2)`] |
| `k` source components | `O(prod_i |X_{r_i}| (|V| + |E|))`: enumerate a minimum root set, drive, check | correctness [mechanized: `root_set_criterion_graph`, `root_set_iff_forest`, `root_set_decide`]; [verified: David 1995, Theorem 1 and Appendix A.1 (a minimum root set is one vertex per source SCC, computable in polynomial time)]; validated, check 4 |
| Parameterized by `k` | XP in general; FPT when fibers are bounded (`c^k`); W[1]-hard when fibers are unbounded | [our conjecture, reduction 3.4, validated] |
| Source-overlap hypergraph alpha-acyclic | polynomial (semijoin reduction) | [verified: Yannakakis 1981; Beeri, Fagin, Maier, Yannakakis 1983] via 3.3 |
| Source-overlap hypergraph of bounded hypertree width | polynomial | [verified: Gottlob, Leone, Scarcello 2002] via 3.3 |
| Classes of bounded arity / unbounded arity | tractable iff bounded treewidth of cores (bounded arity); FPT iff bounded submodular width | [verified: Grohe 2007; Marx 2013], under their complexity assumptions, via 3.3 |

**H2: verified.** Existence is NP-complete in general and in NP (the certificate is the state;
checking it is one table lookup per edge) [mechanized: `net_section_iff_sat`, `net_size`,
`np_certificate`; NP-completeness by the standard argument]. With a single source component it is polynomial in
`|X_root| x |E|`, as expected. One refinement on where the hardness lives: not in lossy maps alone,
but in lossy maps **together with** many source components. Lossy maps with one source, and many
sources with bijective maps, are both polynomial.

**H3: verified, with a priority correction.** The multi-source reduction proposed in the first pass
(condense SCCs, reduce to a CSP among source components with image-equality constraints, read it
as a join) is correct (validated, checks 3 and 4) but **not new**: it is David's root-set
decomposition (JAIR 1995). David's root set is exactly one representative per source SCC of the
directed graph of functional constraints, and "any consistent instantiation of the root set can be
linearly extended to a solution" is his Theorem 1. The single-root case is Zhang and Yap's
Corollary 3. What the repository adds is the mechanized correctness core (`rooted_criterion`, and
for a root set `root_set_criterion_graph` with the count `root_set_count`) and the placement of
these results inside the convergence theory.

### 3.2 The reduction from 3-SAT

Given a 3-CNF formula with variables `x_1..x_n` and clauses `C_1..C_m`, build:

- a **clause vertex** `C_j` with fiber the 7 assignments to its three variables that satisfy it;
- a **variable vertex** `x_i` with fiber `{0, 1}`, for each variable that occurs;
- for each occurrence of `x_i` in `C_j`, a **projection edge** `C_j -> x_i` mapping an assignment
  to its `x_i` bit.

Every clause vertex is a source (in-degree 0); every variable vertex is a multi-source target with
one in-edge per occurrence; there are no cycles. A state is A-consistent iff the clause values
agree on shared variables, iff the variable values form a satisfying assignment. In fact the map
from sections to satisfying assignments of the occurring variables is a bijection (each clause
value is determined by its three variables), so the reduction is parsimonious **[mechanized:
`net_section_iff_sat`, `net_bijection`, `net_count`]** (on the one-fiber form below).

**Matching the theory's edge semantics.** Edges are directed and carry total functions, as in
`msat`: `(u, v, f)` holds when `f (s u) = s v`. Two adjustments make the construction literal:

- *One shared fiber.* `msection` gives every vertex the same fiber `V`. Take `V = {0..7} u {P}`
  (three-bit codes plus a poison value), map any code that does not satisfy `C_j` to `P` on every
  projection edge, add a filter vertex `z` pinned to 0 by a constant self-loop `(z, z, const 0)`,
  and add an edge `x_i -> z` sending `0, 1` to `0` and everything else to `1`. Then variable values
  are forced into `{0, 1}`, which forces clause values to satisfying codes; the count of sections
  is again the number of satisfying assignments [mechanized: `LossyHardness.v` builds exactly this
  network `net f` (poison value 8): `net_section_iff_sat`, `net_count`; `6|f| + 1` edges, each a
  9-entry table: `net_size`, `net_tables`]. Both parts of the gadget are needed [mechanized:
  `no_filter_trivial`, `no_pin_trivial`].
- *Bounded degree.* Restricting the formula so that each variable occurs a bounded number of times
  keeps SAT NP-complete [verified: Tovey 1984], so hardness holds with bounded in-degree and fibers
  of size at most 9.

**Validation** (`research/lossy/validate.py`, fixed seed, output in `research/lossy/validate.out`):

| Check | Instances | Agreement |
|---|---|---|
| typed fibers: section exists iff satisfiable | 600 random 3-CNF, `n` in 4..10, `m/n` in 3..6 (437 SAT, 163 UNSAT) | 600/600 |
| typed fibers: #sections = #satisfying assignments | same 600 | 600/600 |
| one shared fiber with the filter gadget: existence | 200 | 200/200 |
| one shared fiber with the filter gadget: counts | 200 | 200/200 |

Sections were found by generic backtracking over the network (the search knows nothing about
clauses); satisfiability by enumerating all assignments.

**Membership in NP.** A consistent state has size `|V|` and is checked with `|E|` table lookups
[mechanized: `np_certificate`, `np_certificate_net`].
Maps given as circuits instead of tables keep membership (each check is a circuit evaluation).

**A single source is not hard.** If some vertex `r` reaches every vertex, enumerate `X_r`, drive
along a BFS out-tree, and check every edge; correctness is `rooted_criterion` with `out_tree_unique`
(validated against brute force on 1500 random rooted networks, check 3). The bound is polynomial in
`|X_r|`. In gsm fibers are enumerated explicitly, so this is the relevant measure; if a fiber were
given succinctly (a product of many variables), the bound would be pseudo-polynomial.

### 3.3 The join reading

Let `r_1..r_k` be a minimum root set (one vertex per source component) and, for a vertex `w`, let
`p_{i,w} : X_{r_i} -> X_w` be the composite along any path from `r_i` to `w`. Discard root values
for which the subnetwork reachable from `r_i` has no section (the single-root test). Then a section
exists iff there are root values `a_i` with `p_{i,w}(a_i) = p_{j,w}(a_j)` for every pair `i, j` and
every `w` reachable from both **[our conjecture as stated here; the existence half is David 1995,
Theorem 1; the per-edge agreement form, where every non-driving edge equates two driving-path
values, is mechanized: `root_set_agreement`]**.

Equivalently, let `R_i` be the relation over the attributes `W_i` (the vertices reachable from
`r_i` and from some other root) consisting of the tuples `(p_{i,w}(a))_{w in W_i}`; a section
exists iff the natural join of `R_1..R_k` is nonempty. That is a Boolean conjunctive query over
explicitly given relations, so the database tractability theory applies to the **source-overlap
hypergraph** (vertices: shared vertices; hyperedges: the `W_i`):

- alpha-acyclic: polynomial by a semijoin program [verified: Yannakakis 1981], and pairwise
  consistency implies global consistency exactly on acyclic schemes [verified: Beeri, Fagin, Maier,
  Yannakakis 1983]. In the theory's words: on an acyclic overlap hypergraph, checking every pair of
  sources is a complete gluing check; on a cyclic one it is not.
- bounded hypertree width: polynomial [verified: Gottlob, Leone, Scarcello 2002].
- class-level characterizations: bounded arity, polynomial iff bounded treewidth modulo homomorphic
  equivalence, assuming FPT != W[1] [verified: Grohe 2007]; unbounded arity, FPT iff bounded
  submodular width, assuming the exponential time hypothesis [verified: Marx 2013].

Evaluating conjunctive queries is NP-complete in combined complexity [verified: Chandra and Merlin
1977], which is the database face of section 3.2.

### 3.4 Hardness in the number of sources

Given a graph whose vertices are colored with `k` colors, build a source vertex `P_{ab}` for each
pair of colors `a < b`, ranging over the edges between classes `a` and `b`, and a sink `Y_c` per
color ranging over class `c`, with edges `P_{ab} -> Y_a` and `P_{ab} -> Y_b` projecting an edge to
its endpoints. Sections are exactly the multicolored `k`-cliques, and the network has `k(k-1)/2`
source components **[our conjecture]**, validated on 400 random colored graphs (check 5, 400/400).
Multicolored clique is W[1]-hard in `k` [verified: Fellows, Hermelin, Rosamond, Vialette 2009],
so reading A is W[1]-hard parameterized by the number of source components when fibers are
unbounded, and the `prod |X_{r_i}|` algorithm cannot be improved to `f(k) poly(n)` unless
FPT = W[1]. With fibers bounded by `c` it is `O(c^k poly)`, so FPT.

### 3.5 What this says about the open problem

The categorical paper's open problem is "a cohomological account of the non-invertible case". If
"account" means an invariant computable in polynomial time that decides existence of a consistent
state, then section 3.2 rules it out unless P = NP **[the reduction is mechanized:
`net_section_iff_sat`, `net_size`; NP-completeness by the standard argument]**, and section 3.4
rules out an `f(k) poly(n)` refinement unless FPT = W[1] **[our conjecture]**. What survives is
structural: the root set measures the irreducible search [mechanized: `root_set_criterion_graph`,
`root_set_count`], the rooted criterion is exact per root value, and the overlap hypergraph's
width governs tractability.
The invertible fragment is the exception because bijective constraints propagate without search
(a value at one vertex fixes its whole component), which is why `H^1` decides it.

## 4. Reading B and discrete dynamical systems

### 4.1 The published theorems (H4)

**H4: verified, with hypotheses and attributions made precise.** Statements are for a
map `F` on a product of finite sets; "Boolean" means every fiber is `{0, 1}`; "multivalued" means
every fiber is a finite integer interval. The **global** interaction graph `G(F)` has a signed arc
`u -> v` when some unit change of `x_u` changes `F_v` in that direction (arcs may carry both
signs); the **local** graph `G(F)(x)` is the same at one point `x`, from the discrete Jacobian.
A local statement is stronger than the global one, since `G(F)(x)` is a subgraph of `G(F)`.

| Result | Statement | Setting | Source |
|---|---|---|---|
| Thomas's rules (conjecture) | a positive cycle is necessary for several stable states; a negative cycle is necessary for sustained oscillation | informal | [verified: Thomas 1981] |
| Robert | `G(F)` acyclic implies a unique fixed point, reached by iteration | Boolean in the restatement; any finite fibers | [verified: Robert 1986, as restated by Bridoux et al. 2022, section 2.6]; in the federation model [mechanized: `frun_solves`, `solve_unique`, `order_independent`] |
| Shih and Dong | if no local graph `G(F)(x)` has a cycle, `F` has a unique fixed point | Boolean, local | [verified: Shih and Dong 2005, abstract (full text not accessible to us), as restated in Richard 2011, Theorem 1, and Richard 2019, Theorem 2] |
| First rule, local | two fixed points imply a positive circuit in some `G(F)(x)` | Boolean, local | [verified: Remy, Ruet, Thieffry 2008, Theorem 3.2, primary text (HAL hal-00692086)] |
| First rule, multivalued | two fixed points (or several attractors of the asynchronous dynamics) imply a positive circuit in some local interaction graph `G_F(x)`; hence no positive circuit in any local graph, and a fortiori none in the global interaction graph, implies at most one fixed point | multivalued, local | [verified: Richard and Comet 2007, as restated in Richard 2009, Theorem 1, and Richard 2010, Theorem 3 ("local version of first Thomas' conjecture")] |
| Second rule | an attractive cycle of the asynchronous dynamics implies a negative circuit in the union of the local graphs along it | Boolean | [verified: Remy, Ruet, Thieffry 2008, Theorem 4.4] |
| Second rule, multivalued, and the fixed-point corollary | a cyclic attractor of `Gamma(F)` implies a negative circuit in `G(F)`; hence **no negative circuit in `G(F)` implies a fixed point** | multivalued, global | [verified: Richard 2010, Theorem 1 and Corollary 1] |
| Aracena's duality | for a signed interaction digraph `D`: only negative cycles gives at most one fixed point; only positive cycles gives at least one; strongly connected with only negative cycles gives none; strongly connected with only positive cycles gives at least two | Boolean, global | [verified: Aracena 2008, as restated in Bridoux et al. 2022, Theorem 1] |
| Positive feedback bound | number of fixed points at most `2^{tau+}`, `tau+` the minimum number of vertices meeting every positive cycle | Boolean, global | [verified: Aracena 2008, Bridoux et al. 2022, Theorem 2]; multivalued analogue depending on `X` and the positive-circuit topology [verified: Richard 2009] |
| Local negative cycles | "no local negative circuit implies a fixed point" holds for non-expansive networks, and is **false** in general (and-nets without local negative cycles and without fixed points; antipodal attractive cycles) | Boolean, local | [verified: Richard 2011; Ruet 2017] |
| Complexity | deciding whether a Boolean network has a fixed point is NP-complete in general (dichotomies by function and graph class) | Boolean | [verified: Kosub 2008; restated by Bridoux et al. 2022] |

Attributions, made precise: Richard 2010 is the second (negative-circuit) rule, multivalued, with
the fixed-point corollary; the multivalued first rule is Richard and Comet (2007), generalized to a
fixed-point bound by Richard (2009). Aracena's existence statement ("only positive cycles gives at
least one fixed point") is for Boolean networks and the global signed graph; the multivalued
existence statement is Richard 2010's corollary. The first pass's "absence of negative cycles
implies at least one fixed point" is therefore correct for the **global** graph, and
**[refuted]** for local graphs in general (Ruet 2017), where it holds only under extra hypotheses
such as non-expansiveness (Richard 2011).

### 4.2 The correspondence with the existing counterexamples (H5)

| This repository | Reading B / Thomas | Status |
|---|---|---|
| `copyback_without_authority`: A copies B, B copies A; from `(0, 1)` the orders `[0; 1]` and `[1; 0]` reach `(1, 1)` and `(0, 0)` | the positive 2-cycle: strongly connected with only positive cycles, so at least two fixed points (Aracena); `tau+ = 1`, so at most `2^1 = 2`: the bound is attained. `Gamma(F)` from `(0, 1)` branches to both fixed points (check 6: 2 fixed-point attractors, no cyclic one) | **exact**; now an instance of the rootless single-cycle theorem [mechanized: `rootless_copyback_not_unique`, `copyback_without_authority_recovered`] |
| `prop_cycle_necessary`, `negation_one_coordinated`, `flip_no_section`: `phi_AB = 1 - x`, `phi_BA = id` | the negative 2-cycle: strongly connected with only negative cycles, so no fixed point (Aracena); `Gamma(F)` is one cyclic attractor of length 4, and `cycle_paper_trace` is that attractor, step for step | **exact** (with identity local compensation, `cyc_rep` is `Gamma(F)`); rootless form [mechanized: `rootless_negation_no_nf`] |
| Z/2 holonomy (`sat_iff_trivial_holonomy`, `xorb` labels) | sign of a cycle with copy and negation arcs | **exact for directed cycles only**: cohomology quantifies over undirected cycles (an edge traversed backward contributes its inverse), Thomas over directed cycles. The diamond of section 1 has an unbalanced undirected cycle (no A-section) and no directed cycle (a unique B-fixed point per source value) |
| acyclic federations converge (`frun_solves`, `solve_unique`, `order_independent`) | Robert's theorem | **exact** in reading B; reading A can still fail on an acyclic graph (`c22_cycle_basis_fails`, the diamond) |
| monotone regime (`kleene_lfp`, `chaotic_reaches_lfp`) | "no negative cycle" | **needs qualifiers**, see below |
| non-invertible maps, no root (audit section 12) | signed graph after choosing an order on each fiber | **new use**, see 4.3 |

**H5: modified.** The correspondences that are exact are the two 2-cycle counterexamples and the
acyclic case. "Trivial holonomy = even number of negations = positive cycle" is exact for a
directed cycle with Z/2 labels, and **[refuted]** as a statement about networks, because the two
readings see different cycles: undirected in reading A, directed in reading B (validated: at in-degree at
most one, where the two notions coincide, "section exists iff no directed cycle has an odd number
of negations" holds on 1000/1000 random networks, check 7). "The monotone regime is the
no-negative-cycle case" is **[refuted]** as an identity; the correct relation, with its qualifiers:

1. Monotone means every arc is positive for the given lattice orders, which is stronger than "no
   negative cycle" (negative arcs off every cycle are allowed by Richard's corollary).
2. The regimes conclude different things. Monotone gives a **least** fixed point reached from bottom
   by every fair order (`kleene_lfp`, `chaotic_reaches_lfp`); no-negative-cycle gives **existence**
   of a fixed point and no cyclic attractor (Richard 2010), with neither uniqueness nor a canonical
   one. `bottom_matters` and the copy-back loop (monotone, two fixed points) show the regime's
   uniqueness comes from the protocol (start at bottom), not from the network.
3. The order types differ. Richard's theorem needs totally ordered fibers (integer intervals); the
   monotone regime uses lattices. Neither contains the other.

The Z/2 picture also has a known continuous counterpart: a system is monotone for some orthant order
iff every closed undirected chain of its signed graph is positive [verified: DasGupta, Enciso,
Sontag, Zhang 2007, Lemma 3 (Kamke's condition)]. That is Z/2 balance, and their minimum number of
edges to remove for sign consistency is the Z/2 group feedback edge set the repository already
uses for minimum coordination. So reading A's Z/2 cohomology is, verbatim, "can the network be made
monotone by flipping the encoding of some vertices."

### 4.3 What reading B gives where cohomology says nothing

For lossy maps without a spanning root, cohomology is silent and reading A is NP-complete. Reading B
still has usable structure, because any finite fiber can be totally ordered, and then every
dependence has a sign:

- **Existence without an authority.** If, for some choice of orders on the fibers, `G(F)` has no
  negative circuit, a B-consistent state exists [verified: Richard 2010, Corollary 1]. The order is
  a free parameter: different orders give different signed graphs, and one good order suffices
  **[our conjecture: the search over orders is the useful object]**.
- **Uniqueness without an authority.** If `G(F)` has no positive circuit, there is at most one
  B-consistent state [verified: Richard and Comet 2007, whose theorem is local and stronger: no
  positive circuit in any local graph `G_F(x)` suffices; Boolean case mechanized as
  `local_fidelity`]. Free vertices are positive self-loops
  (section 1), so the condition applies to the network with its sources pinned. It would be the
  first condition in the theory that gives a unique consistent state on a cycle **without** naming
  a root on that cycle.
- **Counting.** In the Boolean case at most `2^{tau+}` consistent states [verified: Aracena 2008],
  so the multiplicity that `copyback_without_authority` exhibits is localized to a positive feedback
  vertex set: fixing those vertices (an authority on `tau+` registries) leaves at most one
  consistent state per fixed value (Aracena's Lemma 1, as restated by Bridoux et al. 2022).
- **Oscillation.** A cyclic attractor of the asynchronous repair needs a negative circuit
  [verified: Richard 2010, Theorem 1]; so a network whose repair can oscillate has its oscillation
  located on negative cycles, the reading-B form of `prop_cycle_necessary`.

**Monotonizability, a common generalization [our conjecture].** Call `N` *monotonizable* when there
is a total order on each fiber making every edge map monotone.

- For permutation labels on a connected graph: monotonizable iff every holonomy is the identity
  permutation, iff every root value extends to a section. Sketch: an order-preserving bijection of a
  finite chain is the identity, so monotone transports force trivial holonomy; conversely transport
  one order along a spanning tree. Under the regular action this is `H^1 = 0`
  (`section_iff_coboundary`). Validated on 500 random networks (check 10, 500/500).
- For lossy maps at in-degree at most one: monotonizable implies a section exists, since a monotone
  map of a finite chain has a fixed point (iterate from the least element). Not conversely
  (`c15`'s copy-then-swap has a section and is not monotonizable: a monotone map of a chain has no
  2-cycle). Validated: 600/600, with 60 instances that have a section without being monotonizable
  (check 11).
- In reading B with monotone resolvers, monotonizable implies a least fixed point reached by
  chaotic iteration from the bottom of the chosen orders, which is the existing monotone machinery
  (`Federation.v`, `Chaotic.v`) applied after a change of order. In reading A it does not suffice:
  `c22_cycle_basis_fails` uses constant (monotone) maps and has no section.

So monotonizability restricts to trivial holonomy on the invertible fragment, contains the monotone
regime as the case where the orders are given, and covers the Z/2 orthant case of DasGupta et al.
as the case where each order is the given one or its reverse.

## 5. Prior work and novelty (H6)

**H6: the components are known; the bridge to federated or replicated convergence appears new.**

- **Functional and bijective constraints.** Functional binary constraints and root sets: David 1995
  (pivot consistency, root sets, linear extension from a consistent root instantiation); David 1993
  (functional and bijective constraints that make a CSP polynomial); Van Hentenryck, Deville, Teng
  1992 (arc consistency for functional constraints in `O(ed)`); Zhang and Yap 2011 (variable
  substitution; a CSP solved globally when one variable reaches all others through functional
  constraints). Bijective constraints are the "One" constraints of the tractable 0/1/all class of
  Cooper, Cohen, Jeavons 1994; Carbonnel and Cooper 2016 survey the area, including functional
  instances with small root sets and the polynomial computation of a minimum root set (NP-hard for
  ternary constraints). Reading A is this problem, so its complexity map is known in substance.
- **Unique games.** Deciding whether a unique game is fully satisfiable is easy by propagation
  [verified: Khot 2010 survey]; this is the bijective (invertible) case.
- **Sheaves and contextuality.** Contextuality as an obstruction to global sections (Abramsky and
  Brandenburger 2011); Čech cohomology gives a sufficient but not necessary condition, with false
  positives (Abramsky, Mansfield, Barbosa 2012), and covers All-vs-Nothing arguments (Abramsky,
  Barbosa, Kishida, Lal, Mansfield 2015); the relational-database form of the same question
  (Abramsky 2013); approximate sections and the consistency radius (Robinson 2017). The
  "cohomology is sound but incomplete" phenomenon there is the same gap as the non-invertible case
  here, and NP-hardness of the underlying problem is the reason in both.
- **Databases.** Yannakakis 1981; Beeri, Fagin, Maier, Yannakakis 1983; Chandra and Merlin 1977;
  Gottlob, Leone, Scarcello 2002; Grohe 2007; Marx 2013.
- **Discrete dynamics and asynchronous iterations.** Thomas 1981; Robert 1986; Shih and Dong 2005;
  Remy, Ruet, Thieffry 2008; Richard and Comet 2007; Richard 2009, 2010, 2011; Aracena 2008; Ruet
  2017; Kosub 2008; Bridoux, Durbec, Perrot, Richard 2022. Üresin and Dubois 1990 give a sufficient
  condition (asynchronously contracting operators) for every asynchronous iteration over discrete
  data to converge to a unique fixed point, necessary on finite domains; it is the exact abstract
  condition for rootless convergence in reading B, without a graph characterization.
- **Monotone systems.** DasGupta, Enciso, Sontag, Zhang 2007: sign consistency as Z/2 balance, and
  the minimum inconsistent edge set (NP-hard, Goemans-Williamson style approximation).
- **Routing.** Griffin, Shepherd, Wilfong 2002: solvability of the stable paths problem is
  NP-complete; with no dispute wheel (a cyclic structure) there is a unique solution and the path
  vector protocol converges to it. This is the closest distributed-systems precedent: a
  cycle-shaped obstruction to convergence in a network of local fixed-point rules.
- **Logic programming and argumentation.** Odd and even cycles play the negative and positive roles:
  finite argumentation frameworks without odd-length attack cycles have stable extensions (Dung
  1995, stated via "limited controversial"); Datalog with negation read as a Boolean network, with
  feedback-vertex-set bounds on model counts (Trinh, Benhamou, Soliman, Fages 2025); abstract
  dialectical frameworks are Boolean networks (Heyninck, Knorr, Leite 2024).
- **CRDTs and replicated data.** Targeted searches (CRDT or eventual consistency with Boolean
  network, Thomas's rules, signed cycles, sheaf cohomology) found no work connecting replicated or
  federated convergence to Boolean-network fixed-point theory or to Thomas's rules. The categorical
  paper already records that no prior sheaf-cohomology work targets the replicated-convergence
  obstruction.

**Assessment.** New, as far as these searches reach: (a) the observation that the repository's
cohomology and its federation theorems use two different readings, with the reductions between
them; (b) the identification of the copy-back and negation counterexamples with Aracena's extremal
positive and negative 2-cycles, and of acyclic federation convergence with Robert's theorem;
(c) reading A's NP-completeness as the precise reason the non-invertible case has no cohomological
account, with the root set as the replacing invariant; (d) monotonizability as the common
generalization of trivial holonomy, the monotone regime and orthant monotonicity. Not new: every
complexity statement about functional CSPs, every Thomas-type theorem, and the join theory. The
contribution is the map between them, which is the same kind of contribution the README claims for
the existing work ("these are the tools; the conditions and theorems built with them are new").

## 6. Open problems, ranked

Ranked by value to the theory and gsm per unit of difficulty.

Status as of the current gate: P1 and P6 are done, and P4 is done in reading A (#70, closing
[REGIME-AUDIT.md](../REGIME-AUDIT.md) gap 11); P2 is open and listed there as gap 3 (sufficient signed-cycle certificates for E are now mechanized, see P2); P3 and P5 are not audit gaps (they are
research directions, not missing exact conditions for a listed regime).

### P1. The root-set criterion, mechanized, with the hardness that makes it optimal

- **Status: done**, #54 (`RootSet.v`: `root_set_iff_forest`, `root_set_criterion_graph`,
  `root_set_criterion_values`, `root_set_agreement`, `root_set_bijection`, `root_set_count`,
  `root_set_decide`), with the hardness half's reduction mechanized in #57 (`LossyHardness.v`:
  `net_section_iff_sat`, `net_bijection`, `net_count`, `net_size`, `np_certificate`;
  NP-completeness by the standard argument). It closes REGIME-AUDIT.md section 12's
  general-graph row.
- **Statement.** For a network with a minimum root set `r_1..r_k`, a section with root values
  `a_1..a_k` exists iff the state driven from those values along a forest of out-trees satisfies
  every edge; and existence is NP-complete in general (reduction 3.2).
- **Why it matters.** It closes the audit's row "general graph: none mechanized; none known" with an
  exact criterion, generalizing `rooted_criterion` from one root to a root set. The hardness half
  explains why no cheaper exact criterion exists. For gsm, it is a complete decision procedure for
  rootless lossy federations whose cost is reported up front (`prod |X_{r_i}|`), which `Build` can
  run under a budget and report as undetermined when exceeded, as `Synthesize` already does.
- **Difficulty.** Low to medium. The criterion is `rooted_criterion` per source component plus an
  agreement check at shared vertices; the minimum root set is a Tarjan condensation.
- **Mechanization needs.** An `otree`-forest generalization of `out_tree_section` and
  `out_tree_unique`; a statement over a list of roots; the reduction's correctness lemma (sections of
  the clause network correspond to satisfying assignments) is mechanizable as a finite construction,
  while NP-completeness itself stays cited.

### P2. Rootless convergence in reading B (the runtime model)

- **Status: open**, REGIME-AUDIT.md gap 3 (rootless propagation on non-invertible networks in
  the resolver reading). The invertible single-cycle case is done, #48 (`RootlessCycles.v`:
  `rootless_unique_iff`, `rootless_two_orders`, `rootless_not_unique`), which answers the
  copy-back generalization below for one coherently oriented invertible cycle; invertible
  networks beyond one cycle were gap 2, closed by #91 (`RootlessNetworks.v`:
  `net_unique_normal_form_iff`, a unique normal form iff an authority root per component, given a
  section, or a trivial group).
- **Progress: sufficient certificates for E, not an identity** (`SignedCycles.v`,
  `SignedResolver.v`). Resolver semantics made explicit: one value type with a least and a greatest
  element and finite height; each vertex updated by its resolver from the current state; fair
  asynchronous schedules as in `DistributedCycles.v`; the signed graph is the **global** interaction
  graph (`Resp`: signs fixed across all states). Proved:
  1. Harary balance for finite signed graphs (`harary_balance`, the Z/2 instance of
     `holonomy_free_section`): a switching to all-positive exists iff no closed walk carries an
     odd number of negative edges (the simple-cycle form, "no negative cycle", is classical and
     not mechanized).
  2. Attempt 1 (`signed_settlement`, `signed_settlement_harary`): balance makes every resolver
     monotone after reversing the orders at the switched vertices (`switched_monotone`); then from
     every start at or below the least fixed point of the switched order every fair schedule
     settles there, sound starts settle at the least fixed point above them, and E (Settlement and
     CanonicalFidelity of the canonical-execution kernel, canonicalizer the constant least fixed
     point) holds from every such start. The switching is a hypothesis of `signed_settlement` and
     derived from balance in `signed_settlement_harary`. The start condition is needed for
     fidelity and for fair-schedule settlement: `copyback_ghost` and `toggle_ghost` (a sound start
     above the least fixed point stays at a ghost: fidelity fails) and `ring_needs_low_start` (a
     fair schedule never settles); on that ring E's Settlement half still holds from every start,
     and E fails through fidelity (`ring_low_start_E`).
  3. Attempt 2 (`signed_fidelity`, `signed_fidelity_harary`): balance plus at most one fixed
     point gives settlement from every start and E from every start. Uniqueness is a hypothesis: on a balanced graph Thomas's
     condition "no positive directed cycle" forces an acyclic graph (`balanced_no_positive_acyclic`),
     so the cited global sign route (Aracena 2008, and the global corollary of Richard and Comet
     2007, whose theorem is local) adds nothing beyond Robert there;
     `unique_pos_cycle` is covered by the hypothesis, and every global certificate of it has a
     positive cycle (`unique_pos_cycle_every_certificate`).
  Breaks recorded as theorems: `neg2_no_fixed_point` (unbalanced, no fixed point),
  `unbalanced_unique_oscillates` (one fixed point but no balance: no settlement), `flip_needs_top`
  and `flip_needs_top_resolver` (monotone with one fixed point on a value set without a top, every
  other hypothesis of attempt 2 holding: no flush), `xor_no_certificate`
  (a non-monotone lossy resolver admits only unbalanced certificates), `cyc3_unsignable` (a
  permutation that no order with a least element signs). Still open: multivalued local
  interaction graphs, value sets without bounds, and an exact (iff) condition for E in reading B.
  The rest of the statement below stays open.
- **Progress: local (state-dependent) interaction graphs, Boolean, every `n`** (`LocalSigned.v`;
  details in [coq/docs/non-invertible.md](../coq/docs/non-invertible.md#local-interaction-graphs-local-fidelity-and-local-settlement-localsignedv)).
  The local graph `G(x)` is the discrete Jacobian: an arc `j -> i` at `x` when flipping `x_j`
  changes `F_i`, positive when raising `x_j` raises `F_i` (`lneg_spec`); cycles are elementary.
  Two separate results, not one slogan:
  1. Local fidelity. No positive cycle in any `G(x)` gives at most one fixed point (`rrt_sub`,
     `local_fidelity`: Remy, Ruet and Thieffry 2008, mechanized for every `n` by induction on
     subcubes), hence CanonicalFidelity from every start with no global sign hypothesis
     (`local_fidelity_canon`), and, with a balanced global certificate, fair settlement and E from
     every start (`local_signed_fidelity`). The local condition is implied by the global one
     (`global_to_local`) and strictly weaker: `local_weaker_than_global` has no cycle in any
     `G(x)` but a positive 2-cycle in every global certificate, and E holds.
  2. Local settlement. "No negative cycle in any `G(x)` gives a fixed point" is false: the
     6-vertex Boolean conversion of Richard's Example 6 (Tonello 2017) has no local negative cycle
     and no fixed point (`local_neg_free_no_fixed_point`). Corrected sufficient conditions,
     mechanized with the reachability form (from every state an update word reaches a fixed point,
     so E's Settlement holds from every start): no local negative cycle plus out-degree at most one
     in every `G(x)`, which is non-expansiveness for the Hamming distance (`richard_t3`,
     `outdeg_nonexpansive`; Richard 2011, Theorem 3, with Ruet 2017, Remark 2), or plus one vertex
     on every local positive cycle (`richard_t4`; Richard 2011, Theorem 4); and no local cycle at
     all gives all of E (`shih_dong_E`; Shih and Dong 2005). Fair asynchronous settlement does not
     follow: not under either corrected condition (`ring_local_conditions`: the positive 3-ring,
     two fixed points, a fair schedule that never settles), and not even with no local cycle at
     all (`shih_dong_not_fair`, 4 vertices, a fair periodic schedule of period 8 that never
     settles), in contrast with Robert's global acyclic case.
  Consequence for gap 3: on fidelity the local route strictly extends the global certificates; on
  settlement, local conditions certify E's Settlement half (and, without any local cycle, all of
  E), while fair-schedule settlement still needs the global switching or global acyclicity. The
  certificates stay sufficient, not exact. Since P2's statement asks for every fair order, the
  local results answer it only through E (Settlement in its existential, flush form: some update
  word reaches the fixed point from every reachable state), not in its fair form; that fair form
  from local conditions is open in general, with the progress below.
- **Progress: fair settlement under no local cycle plus out-degree at most one** (#92,
  `LocalFairSettlement.v`; details in
  [coq/docs/non-invertible.md](../coq/docs/non-invertible.md#fair-settlement-under-local-conditions-localfairsettlementv)).
  Write (A) for "no cycle in any local graph" and (B) for "out-degree at most one in every local
  graph" (`OutDeg1`, non-expansiveness by `outdeg_nonexpansive`). Mechanized for every `n`:
  1. Synchronous form. (B), with (A) at one state of a synchronous periodic orbit, makes the orbit
     a fixed point (`sync_orbit_fixed`): along the orbit, non-expansiveness and periodicity make
     the Hamming distance between orbit points invariant under the shift, and a vertex that flips
     on the orbit but has no out-arc into the flipped set at some orbit state would make a shifted
     distance strictly smaller; so the local graph there has a cycle. Hence (A) and (B) make every
     synchronous orbit reach the unique fixed point within `2^n` steps (`sync_simple`). This is the
     conclusion of Shih and Ho 1999 (Adv. Appl. Math. 22(1):60-102), Theorem 3.1, whose hypothesis
     (b), `F(V(x))` inside `V(F(x))`, is (B) by their Lemma 4.1 (column `j` of their discrete
     Jacobian holds the out-arcs of `j`); the proof here is different, and `sync_orbit_fixed`
     needs (A) only on the orbit.
  2. Single-token asynchronous case. (B) alone makes the number of unstable vertices
     non-increasing along asynchronous runs (`ucnt_mono`). With one unstable vertex an
     asynchronous move is the synchronous step, so a closed run is a synchronous orbit and part 1
     applies: with (A) at a state with at most one unstable vertex, no closed run through it
     changes the state (`one_token_closed`). So every fair schedule from a start with at most one
     unstable vertex, and every fair run that ever reaches such a state, settles at the unique
     fixed point (`one_token_fair_settlement`, `fair_settles_once_one_token`).
  3. Generic step. An acyclic asynchronous state graph gives fair settlement at the unique fixed
     point from every start (`fair_settles_closed`, `fair_settlement_of_acyclic`, by fair rounds
     and pigeonhole), so the open part reduces to acyclicity.
  Needed, as theorems: (B) (`outdeg_needed`: Shih and Dong's network has (A), a synchronous
  3-cycle and a fair schedule that never settles); no local positive cycle (`no_neg_not_enough`:
  the positive 3-ring has (B), no local negative cycle and a fair schedule that never settles); no
  local negative cycle (`no_pos_not_enough`: the negative 3-ring has (B), no local positive cycle,
  a closed asynchronous run, and no fixed point). Non-vacuity: `shih_ho_instance`, Shih and Ho's
  own 4-vertex example (their Section 3, item (5)), with (A), (B), local arcs `0 -> 3` and `3 -> 0`
  at different states (so the global graph has a cycle and Robert's theorem does not apply), and
  an asynchronous state graph that is acyclic (a rank certificate), so every fair schedule from
  every start settles at `1111`.
- **Progress: two unstable vertices** (#NN, `LocalTwoToken.v`; details in
  [coq/docs/non-invertible.md](../coq/docs/non-invertible.md#two-unstable-vertices-localtwotokenv)).
  Under (A) and (B), no closed asynchronous run from a state with at most two unstable vertices
  changes the state (`two_token_closed`), so every fair schedule from such a start, and every fair
  run that ever reaches such a state, settles at the unique fixed point
  (`two_token_fair_settlement`, `fair_settles_once_two_tokens`). Call a token good when its vertex
  disagrees with the fixed point p and bad otherwise. With two tokens, non-expansiveness leaves at
  least one good (`not_both_bad`); with one of each, `F(x)` is exactly as far from p as x, which
  forces every vertex of the disagreement set D(x) to have an out-arc into D(x) plus the bad token
  (`tight_arc`), so the bad token cannot point into D(x) without closing a local cycle
  (`head_arc`). Hence the token types never change on a closed two-token run, a run with two good
  tokens moves strictly toward p, and in the mixed case "good then bad" can always be swapped into
  "bad then good" (`swap_TH`). The closed run then rearranges into (good, bad) pairs (`W_sort`,
  `W_main`), each pair being the synchronous step F, which gives a synchronous periodic orbit
  through a non-fixed state against `sync_orbit_fixed`. Non-vacuity: `two_token_instance` (Shih
  and Ho's network at 1110, one good and one bad token). The same case is decided by SAT for
  n = 3 to 7 (`research/gap3-fair-settlement/K2.md`, which also lists the potentials that fail).
- **Open: three or more tokens (computational evidence, not mechanized).** Under (A) and (B), no
  closed asynchronous run whose states all have three or more unstable vertices. An exhaustive SAT
  search finds no network on n = 3, 4, 5 or 6 vertices with (A) and (B) and any cycle in its
  asynchronous state graph; with `fair_settlement_of_acyclic` this would give fair settlement from
  every start. For three tokens a bad token can pass to a good receiver (a SAT witness at n = 4),
  so the two-token argument does not apply as it stands.
  - **Cross-checks:** brute force at n = 3, two encodings, three solvers. Dropping either
    condition gives counterexamples at once.
  - **What a proof may need:** the search suggests no local cycle is needed only at the states a
    cycle visits, as in `sync_orbit_fixed`. The conjectured key lemma F2 is proved for one
    unstable vertex (part 2); two unstable vertices are settled by the route above; three or more
    are open.
  - **Literature:** not found in the literature searched (Shih and Ho 1999 treat synchronous
    iteration only; their proof maps von Neumann neighborhoods into von Neumann neighborhoods,
    which single asynchronous updates do not do).
  - **Details and scripts:** [research/gap3-fair-settlement](../research/gap3-fair-settlement/README.md).
- **Novelty check for `shih_dong_not_fair`.** The weaker fact is in the literature: Richard,
  "Positive and negative cycles in Boolean networks," J. Theoret. Biol. 463 (2019) 67-76, section
  3, records that under Shih and Dong's hypothesis (no cycle in any local graph) Robert's
  synchronous convergence and the acyclicity of the asynchronous state graph are both lost, and
  attributes this to a 4-component example in Shih and Dong 2005. So "local acyclicity does not
  make every asynchronous path reach the fixed point" is known (and the weak form, a shortest path
  to the fixed point from every state, holds: Richard, Theoret. Comput. Sci. 583 (2015) 1-26,
  Corollaries 3 and 4). What `shih_dong_not_fair` adds is the fair-schedule form: a periodic
  schedule updating every vertex twice per period of 8, every update changing the state, that
  never reaches the fixed point. That form was not found in the literature we searched; we could
  not read Shih and Dong's own 4-component example (the full text was not accessible to us), so it
  may already exhibit it. Not mechanized, a cross-check: over all 3-vertex Boolean networks (680
  have no local cycle) the asynchronous state graph is acyclic and the synchronous iteration
  converges in every case, so 4 vertices is the least for the known phenomenon and for the fair
  form. Search scope (October 2026): Shih and Ho 1999 (full text, read for #92; synchronous
  iteration only) and Shih and Dong 2005 (abstract and restatements), Remy, Ruet and Thieffry 2008, Richard 2010, 2011, 2015 and 2019, Richard and Ruet
  2013, Ruet 2016 and 2017, Tonello 2017, Tonello, Farcot and Chaouiya 2018, Melliti, Regnault,
  Richard and Sené 2013, the fixing-word papers (Gadouleau and Richard 2018; Aracena, Gadouleau,
  Richard and Salinas 2020), and web searches on fair, periodic and chaotic asynchronous iterations
  with local interaction graphs. Placement in [LANDSCAPE.md](LANDSCAPE.md#related-work-for-signed-cycles).
- **Citations checked for the local results** (statements, settings and hypotheses, from the
  papers or, where marked, the authors' own restatements):
  - Remy, Ruet and Thieffry, *Graphic requirements for multistability and attractive cycles in a
    Boolean dynamical framework*, Adv. Appl. Math. 41 (2008) 335-350, checked against the primary
    text (author version, HAL hal-00692086): Boolean; Theorem 3.2: if `F` has two fixed points `a`
    and `b`, then some `G(F)(x)` has a positive circuit, more precisely a positive circuit whose
    vertices all lie in the set of coordinates where `a` and `b` differ; so if no `G(F)(x)` has a positive circuit, `F` has at
    most one fixed point (the paper presents this as the signed counterpart of Shih and Dong, with
    a stronger hypothesis and a stronger conclusion). Theorem 4.4: an attractive cycle of the
    asynchronous dynamics forces a negative circuit in the union of the local graphs along the
    cycle, hence in the global graph. (Also restated in Richard 2011, Theorem 2, and Ruet 2017,
    section 2.4.) Mechanized here: `rrt_sub`, `local_fidelity`.
  - Richard, *Local negative circuits and fixed points in non-expansive Boolean networks*, Discrete
    Appl. Math. 159 (2011) 1085-1093 (arXiv 0910.0750): Boolean, local graphs. Theorem 3: if no
    `G(F)(x)` has a negative circuit and every vertex of every `G(F)(x)` has out-degree at most one
    (property P, equivalent to `d(F(x), F(y)) <= d(x, y)` for the Hamming distance), `F` has a
    fixed point. Theorem 4: the same conclusion if no `G(F)(x)` has a negative circuit and some
    vertex lies on every positive circuit of every `G(F)(x)`. Mechanized here: `richard_t3`,
    `richard_t4` (with reachability).
  - Ruet, *Negative local feedbacks in Boolean networks*, Discrete Appl. Math. 221 (2017) 1-17
    (arXiv 1512.01573): Boolean, local graphs. Theorem A: there are and-nets (built in dimension 12)
    with no local negative cycle and no fixed point; Theorem B: there are Boolean networks with no
    local negative cycle and an antipodal attractive cycle (asynchronous dynamics; dimension at
    least 7). Remark 2: a non-expansive network with a cyclic attractor has a local negative
    cycle. Cited; the mechanized counterexample is the smaller one below.
  - Richard and Comet, *Necessary conditions for multistationarity in discrete dynamical systems*,
    Discrete Appl. Math. 155 (2007) 2403-2413: multivalued (products of finite integer intervals);
    if no local interaction graph `G_F(x, v)` has a positive circuit, `F` has at most one fixed
    point (as restated in Richard 2009, Theorem 1, and Richard 2010, Theorem 3, which also states
    it for several attractors of the asynchronous dynamics). It is a **local** theorem, so the
    global form follows. Cited, not mechanized (Boolean only here).
  - Richard, *Negative circuits and sustained oscillations in asynchronous automata networks*, Adv.
    Appl. Math. 44 (2010) 378-392 (arXiv 0907.5096): multivalued, asynchronous; a cyclic attractor
    forces a negative circuit in the global graph (Theorem 1), hence no global negative circuit
    gives a fixed point; Example 6 (`{0, ..., 3}^2`, with Comet) has no negative circuit in any
    local graph and no fixed point.
  - Tonello, *On the conversion of multivalued to Boolean dynamics*, Discrete Appl. Math. 259
    (2019) 193-204 (arXiv 1703.06746, 2017), section 5: the 6-component Boolean conversion of
    Example 6, no local negative cycle, no fixed point (mechanized here as
    `local_neg_free_no_fixed_point`); Tonello, Farcot and Chaouiya, *Local negative circuits and
    cyclic attractors in Boolean networks with at most five components*, SIAM J. Appl. Dyn. Syst.
    18(1) (2019) 68-79 (arXiv 1803.02095, 2018): up to 5 components, a cyclic attractor forces a
    local negative circuit (by SAT; cited); a network without a fixed point has a cyclic
    attractor, so 6 is the least dimension of a Boolean counterexample.
  - Shih and Dong, *A combinatorial analogue of the Jacobian problem in automata networks*, Adv.
    Appl. Math. 34(1) (2005) 30-46: Boolean, local graphs; no cycle in any `G(F)(x)` gives a
    unique fixed point (abstract; restated in Richard 2011, Theorem 1, and Richard 2019, Theorem 2;
    the full text was not accessible to us). Conjectured by Shih and Ho, *Solution of the Boolean
    Markus-Yamabe problem*, Adv. Appl. Math. 22(1) (1999) 60-102. Mechanized here, with paths
    (`sd_path`), as `shih_dong_E`.
  - Shih and Ho, *Solution of the Boolean Markus-Yamabe problem*, Adv. Appl. Math. 22(1) (1999)
    60-102 (full text read for #92): Theorem 3.1, no cycle in any local graph plus
    `F(V(x))` inside `V(F(x))` (out-degree at most one in every local graph, their Lemma 4.1;
    Hamming non-expansiveness, their Lemma 4.3) makes the synchronous iteration reach the unique
    fixed point from every start; Theorem 3.2, without the second condition this holds for
    `n <= 3` only. Synchronous iteration only. The conclusion of Theorem 3.1 is mechanized here, by
    a different proof, as `sync_simple` (`sync_orbit_fixed` needs the first condition only on the
    orbit); their 4-vertex example of Section 3, item (5), is `shih_ho_instance`.

  P2 is part of the cyclic frontier: the acyclic case is
  Robert's theorem, and what is open is the cyclic one, an instance of the question of what
  additional structure makes the composition layer P exact on cycles
  ([REGIME-AUDIT.md, the cyclic frontier](../REGIME-AUDIT.md#the-cyclic-frontier);
  [THEORY.md](THEORY.md#canonical-execution)).
- **Statement.** For a cyclic network in reading B, characterize when every fair asynchronous order
  from a given initial state reaches the same consistent state, without an authority root. Known:
  necessary conditions from Thomas's rules (a positive cycle for multiplicity, a negative cycle for
  oscillation), the exact abstract condition of Üresin and Dubois (asynchronously contracting
  operators on finite domains), and Robert for the acyclic case. Wanted: a sufficient condition
  stated on the signed graph for lossy maps, and the generalization of `copyback_without_authority`:
  does having two fixed points always give one initial state from which two orders reach different
  ones?
- **Why it matters.** gsm's cyclic runtime is reading B. Today a non-monotone cycle is rejected or
  coordinated from a root; a signed-graph condition would accept some rootless cycles with a proof,
  and Aracena's `tau+` names the smallest set of registries whose values must be pinned.
- **Difficulty.** Medium for the Boolean case (much is in the literature), large for multivalued
  lossy maps with resolvers.
- **Mechanization needs.** `Gamma(F)` as a relation (it is `FederationOrder.step` restricted to
  changing updates), attractors as terminal SCCs, Robert (already present as `frun_solves`), and the
  proofs of Aracena's duality and Richard's corollary; all finite and constructive, so in reach of
  the axiom-free gate.

### P3. Monotonizability

- **Status: open** (not an audit gap).
- **Statement.** Decide whether a network admits a total (or lattice) order on each fiber making
  every edge map, and every resolver, monotone; prove that in reading B this gives a least
  consistent state reached by chaotic iteration, and that on permutation labels it is equivalent to
  trivial holonomy.
- **Why it matters.** It would be the order-theoretic replacement for `H^1` off the invertible
  fragment: exact where cohomology is exact, sufficient where cohomology is silent, and it reuses the
  monotone machinery that gsm already runs (`AllowMonotoneCycles`). gsm could search for orders
  instead of requiring the user to supply a lattice.
- **Difficulty.** Medium for the theorems; the complexity of deciding monotonizability is unknown to
  us (it is a constraint problem over permutations, and we expect NP-hardness in general and
  tractability for in-degree at most one or for bounded fibers along a tree).
- **Mechanization needs.** Total orders as rank functions on finite fibers; the chain
  fixed-point lemma; an instance of `Federation.v` after relabeling; the permutation-case
  equivalence via `sat_iff_trivial_holonomy`.

### P4. Minimum coordination for lossy networks

- **Status: done in reading A**, #70 (`LossyMinimum.v`), closing REGIME-AUDIT.md gap 11. Exact
  characterization through the root-set criterion: a deletion set is feasible iff its residual
  passes it (`lfeasible_iff_root_set`), and the minimum is the least such deletion
  (`lmin_root_set`), decided on finite fibers (`lmin_decide`). Hardness: the 3-SAT network of 3.2
  has minimum 0 iff the formula is satisfiable and 1 otherwise (`lmin_reduction`,
  `net_lmin_dichotomy`), so even telling 0 from 1 is NP-hard and no efficient algorithm
  approximates the minimum within any factor unless P = NP (standard argument); membership in NP
  by a checkable certificate (`min_le_np_certificate`). On group-labeled networks it is the group
  feedback edge set minimum (`lossy_min_is_gfes`); in general it is not cycle-based
  (`lossy_min_exceeds_cycle_bounds`: the C22 tree has minimum 1, which every cycle-only lower
  bound misses). The invertible plan-model form is `plan_min_exact` (`CoordinationMinimum.v`,
  #72). Still open: the reading-B variants below (signed-cycle feedback sets), which build on
  P2's signed-cycle machinery.
- **Statement.** The minimum number of edges whose deletion leaves an A-section (or, in reading B,
  makes every remaining cycle non-negative so a fixed point is guaranteed, or non-positive so it is
  unique). Before #70 the audit listed the non-invertible minimum as "none known".
- **Why it matters.** It is the lossy analogue of the group feedback edge set result and would give
  gsm's `CoordinationPlan` a target beyond "cut every cycle".
- **Difficulty.** Medium to large. NP-hardness is inherited from the Z/2 case; the signed variants
  are feedback problems on signed digraphs, whose complexity has been studied (Montalva, Aracena,
  Gajardo 2008) and should be checked before claiming anything.
- **Mechanization needs.** Reading A done as above (feasibility over `msection`, deletion by
  position). Reading B needs the signed-digraph feedback notions and the P2 machinery.

### P5. Structural tractability, stated in the theory's terms

- **Status: open** (not an audit gap; `root_set_agreement` is the per-edge agreement form it
  would refine).
- **Statement.** Translate 3.3 into a theorem about networks: if the source-overlap hypergraph is
  alpha-acyclic, pairwise agreement of sources is a complete gluing check, and existence is decided
  by a semijoin program.
- **Why it matters.** It is the exact condition under which the per-pair checks gsm can afford are
  complete for rootless lossy networks, which is the same shape as R1/R2 being the gluing axiom.
- **Difficulty.** Low on paper (Beeri et al.), medium to mechanize (join trees, GYO reduction).

### P6. Uniqueness and event order under a root set

- **Status: done.** Uniqueness given root values, #54 (`out_forest_unique`, `root_set_bijection`);
  event order, #59 (`RootSetEvents.v`: `forest_events_exact`, `forest_perm_exact`,
  `forest_events_exact_global`, `forest_global_iff_static`), closing REGIME-AUDIT.md gap 4. As
  predicted below, the driving network is acyclic and `fed_exact` instantiates
  (`forest_fed_exact`); commuting at the start value alone is not enough (`tw_reachable_matters`).
- **Statement.** Given root values, the section is unique (the `out_tree_unique` generalization);
  state the event-order condition (C1/C2 analogue) for root-driven lossy networks.
- **Why it matters.** Closes the audit's "uniqueness and event order with non-invertible coordination:
  none mechanized".
- **Difficulty.** Low to medium, since the driving network is acyclic and `fed_exact` should
  instantiate, as for `CoordinatedCycles.v`.

## 7. A proposed first paper

**Title.** *Lossy Federations: Root Sets, Signed Cycles, and the Limits of Cohomology.*

**Contributions.**

1. Two readings of a lossy federation (constraint and resolver), the polynomial reductions between
   them, and the classification of the existing mechanized results by reading.
2. The complexity map of the constraint reading: NP-completeness (parsimonious from 3-SAT, bounded
   degree), polynomial with one source component, the root-set algorithm with W[1]-hardness in the
   number of sources, and join-width tractability; with the root-set criterion mechanized (P1).
   Positioned explicitly as an application of David 1995 and Zhang and Yap 2011, not as new CSP
   theory.
3. The consequence for the categorical paper's open problem: no polynomial cohomological account of
   the non-invertible case unless P = NP; the root set as the replacing invariant.
4. The resolver reading as a discrete dynamical system: the copy-back and negation counterexamples
   as Aracena's extremal 2-cycles, acyclic convergence as Robert's theorem, and authority-free
   existence and uniqueness from Thomas-type conditions, with the directed versus undirected cycle
   distinction made precise.
5. Monotonizability as the common generalization of trivial holonomy, the monotone regime and
   orthant monotonicity (P3), with the permutation-case equivalence mechanized.

**Venue options.**

- *PaPoC* (Workshop on Principles and Practice of Consistency for Distributed Data): the replicated
  data audience, a fast first exposure for contributions 1, 3 and 4.
- *OPODIS* or *DISC*: distributed computing, if the paper leads with rootless convergence and
  minimum coordination.
- *CP* (Principles and Practice of Constraint Programming): if it leads with the complexity map and
  the root-set criterion; the reviewers will know David and Zhang and Yap.
- *ITP* or *CPP*: if the mechanization (P1, P3 and the Thomas-type results of P2) is the center.
- *Logical Methods in Computer Science*: the journal version combining all five.

## 8. References

*Functional constraints and CSP tractability.*
P. David, "When functional and bijective constraints make a CSP polynomial," Proc. IJCAI 1993,
pp. 224-229.
P. David, "Using pivot consistency to decompose and solve functional CSPs," Journal of Artificial
Intelligence Research 2 (1995) 447-474.
P. Van Hentenryck, Y. Deville, C.-M. Teng, "A generic arc-consistency algorithm and its
specializations," Artificial Intelligence 57(2-3) (1992) 291-321.
Y. Zhang, R. H. C. Yap, "Solving functional constraints by variable substitution," Theory and
Practice of Logic Programming 11(2-3) (2011) 297-322 (arXiv:1006.3215; preliminary version
Y. Zhang, R. H. C. Yap, C. Li, S. Marisetti, "Efficient algorithms for functional constraints,"
ICLP 2008).
M. C. Cooper, D. A. Cohen, P. G. Jeavons, "Characterising tractable constraints," Artificial
Intelligence 65(2) (1994) 347-361.
C. Carbonnel, M. C. Cooper, "Tractability in constraint satisfaction problems: a survey,"
Constraints 21 (2016) 115-144.
M. R. Fellows, D. Hermelin, F. Rosamond, S. Vialette, "On the parameterized complexity of
multiple-interval graph problems," Theoretical Computer Science 410(1) (2009) 53-61.
C. A. Tovey, "A simplified NP-complete satisfiability problem," Discrete Applied Mathematics 8(1)
(1984) 85-89.
S. Khot, "On the power of unique 2-prover 1-round games," Proc. STOC 2002, pp. 767-775; and "On the
Unique Games Conjecture," invited survey, Proc. IEEE CCC 2010.

*Databases and conjunctive queries.*
M. Yannakakis, "Algorithms for acyclic database schemes," Proc. VLDB 1981, pp. 82-94.
C. Beeri, R. Fagin, D. Maier, M. Yannakakis, "On the desirability of acyclic database schemes,"
Journal of the ACM 30(3) (1983) 479-513.
A. K. Chandra, P. M. Merlin, "Optimal implementation of conjunctive queries in relational data
bases," Proc. STOC 1977, pp. 77-90.
G. Gottlob, N. Leone, F. Scarcello, "Hypertree decompositions and tractable queries," Journal of
Computer and System Sciences 64(3) (2002) 579-627.
M. Grohe, "The complexity of homomorphism and constraint satisfaction problems seen from the other
side," Journal of the ACM 54(1) (2007), Article 1.
D. Marx, "Tractable hypergraph properties for constraint satisfaction and conjunctive queries,"
Journal of the ACM 60(6) (2013), Article 42.

*Sheaves and contextuality.*
S. Abramsky, A. Brandenburger, "The sheaf-theoretic structure of non-locality and contextuality,"
New Journal of Physics 13 (2011) 113036.
S. Abramsky, S. Mansfield, R. Soares Barbosa, "The cohomology of non-locality and contextuality,"
Proc. QPL 2011, EPTCS 95 (2012) 1-14 (arXiv:1111.3620).
S. Abramsky, R. Soares Barbosa, K. Kishida, R. Lal, S. Mansfield, "Contextuality, cohomology and
paradox," Proc. CSL 2015, LIPIcs 41, pp. 211-228.
S. Abramsky, "Relational databases and Bell's theorem," in In Search of Elegance in the Theory and
Practice of Computation, LNCS 8000, Springer, 2013.
S. Abramsky, G. Gottlob, P. G. Kolaitis, "Robust constraint satisfaction and local hidden variables
in quantum mechanics," Proc. IJCAI 2013, pp. 440-446.
M. Robinson, "Sheaves are the canonical data structure for sensor integration," Information Fusion
36 (2017) 208-224.

*Boolean and discrete networks.*
R. Thomas, "On the relation between the logical structure of systems and their ability to generate
multiple steady states or sustained oscillations," in Numerical Methods in the Study of Critical
Phenomena, Springer Series in Synergetics 9, Springer, 1981, pp. 180-193.
F. Robert, *Discrete Iterations: A Metric Study*, Springer Series in Computational Mathematics 6,
1986.
F. Robert, *Les systèmes dynamiques discrets*, Mathématiques et Applications 19, Springer, 1995.
M.-H. Shih, J.-L. Ho, "Solution of the Boolean Markus-Yamabe problem," Advances in Applied
Mathematics 22(1) (1999) 60-102.
M.-H. Shih, J.-L. Dong, "A combinatorial analogue of the Jacobian problem in automata networks,"
Advances in Applied Mathematics 34(1) (2005) 30-46.
E. Remy, P. Ruet, D. Thieffry, "Graphic requirements for multistability and attractive cycles in a
Boolean dynamical framework," Advances in Applied Mathematics 41(3) (2008) 335-350 (author
version: HAL hal-00692086).
A. Richard, J.-P. Comet, "Necessary conditions for multistationarity in discrete dynamical
systems," Discrete Applied Mathematics 155(18) (2007) 2403-2413.
A. Richard, "Positive circuits and maximal number of fixed points in discrete dynamical systems,"
Discrete Applied Mathematics 157(15) (2009) 3281-3288.
A. Richard, "Negative circuits and sustained oscillations in asynchronous automata networks,"
Advances in Applied Mathematics 44(4) (2010) 378-392 (arXiv:0907.5096).
A. Richard, "Local negative circuits and fixed points in non-expansive Boolean networks," Discrete
Applied Mathematics 159(11) (2011) 1085-1093 (arXiv:0910.0750).
J. Aracena, "Maximum number of fixed points in regulatory Boolean networks," Bulletin of
Mathematical Biology 70(5) (2008) 1398-1409.
P. Ruet, "Local cycles and dynamical properties of Boolean networks," Mathematical Structures in
Computer Science 26(4) (2016) 702-718.
P. Ruet, "Negative local feedbacks in Boolean networks," Discrete Applied Mathematics 221 (2017)
1-17 (arXiv:1512.01573).
A. Richard, "Fixed point theorems for Boolean networks expressed in terms of forbidden
subnetworks," Theoretical Computer Science 583 (2015) 1-26 (arXiv:1302.6346).
A. Richard, "Positive and negative cycles in Boolean networks," Journal of Theoretical Biology 463
(2019) 67-76 (arXiv:2201.08600).
E. Tonello, "On the conversion of multivalued to Boolean dynamics," Discrete Applied Mathematics
259 (2019) 193-204 (arXiv:1703.06746).
E. Tonello, E. Farcot, C. Chaouiya, "Local negative circuits and cyclic attractors in Boolean
networks with at most five components," SIAM Journal on Applied Dynamical Systems 18(1) (2019)
68-79 (arXiv:1803.02095).
S. Kosub, "Dichotomy results for fixed-point existence problems for Boolean dynamical systems,"
Mathematics in Computer Science 1(3) (2008) 487-505.
F. Bridoux, A. Durbec, K. Perrot, A. Richard, "Complexity of fixed point counting problems in
Boolean networks," Journal of Computer and System Sciences 126 (2022) 138-164 (arXiv:2012.02513).
M. Montalva, J. Aracena, A. Gajardo, "On the complexity of feedback set problems in signed
digraphs," Electronic Notes in Discrete Mathematics 30 (2008) 249-254.

*Asynchronous iterations, routing, monotone systems.*
A. Üresin, M. Dubois, "Parallel asynchronous algorithms for discrete data," Journal of the ACM
37(3) (1990) 588-606.
T. G. Griffin, F. B. Shepherd, G. Wilfong, "The stable paths problem and interdomain routing,"
IEEE/ACM Transactions on Networking 10(2) (2002) 232-243.
B. DasGupta, G. A. Enciso, E. Sontag, Y. Zhang, "Algorithmic and complexity results for
decompositions of biological networks into monotone subsystems," Biosystems 90(1) (2007) 161-178
(arXiv:q-bio/0509040).

*Logic programming and argumentation.*
P. M. Dung, "On the acceptability of arguments and its fundamental role in nonmonotonic reasoning,
logic programming and n-person games," Artificial Intelligence 77(2) (1995) 321-357.
V.-G. Trinh, B. Benhamou, S. Soliman, F. Fages, "On the Boolean network theory of Datalog¬,"
arXiv:2504.15417, 2025.
J. Heyninck, M. Knorr, J. Leite, "Abstract dialectical frameworks are Boolean networks," Proc.
LPNMR 2024, LNCS 15245 (arXiv:2407.02055).

## Where this sits

- Proven: the two papers and [`coq/`](../coq) (this note's mechanized results are in
  [coq/docs/non-invertible.md](../coq/docs/non-invertible.md)); the regimes are
  [REGIMES.md](REGIMES.md), and their status is [REGIME-AUDIT.md](../REGIME-AUDIT.md).
- This note: the rootless lossy direction. Its constructions are checked by
  [`research/lossy/validate.py`](../research/lossy/validate.py) (13 checks, all agreeing; recorded
  output in [`research/lossy/validate.out`](../research/lossy/validate.out)), which is evidence that
  they are stated correctly, not a proof.
- The headline consequence for the theory: off the invertible fragment the obstruction to a
  consistent state is computationally hard in the constraint reading, so the right generalization
  of `H^1` is structural (root sets, overlap width, orders on fibers), and the resolver reading,
  which is gsm's runtime, has its own exact language in signed cycles.
