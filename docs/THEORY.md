# Theory overview

The theory in one page: the regime it adds, what is new and what is not, the key concepts, how
the three convergence regimes nest, and where the theory sits in pure mathematics
([Mathematical structure](#mathematical-structure)). "What's new here" marks each item mechanized,
paper or implemented. For the
headline and its precision paragraph see the [front page](../README.md); for what is proved in each
regime see [REGIME-AUDIT.md](../REGIME-AUDIT.md); for the full statements see the papers and
[coq/README.md](../coq/README.md).

## Overview

Traditional approaches to coordination-free convergence require either:
1. **Operation commutativity** (CRDTs) - operations must be designed to commute
2. **Invariant confluence** - operations must preserve invariants in all orderings

This research identifies a third regime: **normalization confluence**, where operations may be non-commutative and may violate invariants, yet systems converge through compensation. Convergence is a property of the normalization rewrite system (event application + invariant repair), not the operations themselves.

This repository contains theoretical foundations, proofs, and companion verification tools.

## What's new here

Each item is marked **[mechanized]** (axiom-free in [`coq/`](../coq)), **[paper]** (proved in the
papers, not mechanized), or **[implemented]** (in [gsm](https://github.com/blackwell-systems/gsm)).
[CATEGORICAL-STRUCTURE.md](CATEGORICAL-STRUCTURE.md) and [coq/README.md](../coq/README.md) give the
exact split.

1. **A third convergence regime.** Operations may conflict and break invariants; convergence comes
   from compensation. Two new conditions, WFC and CC; CC is strictly weaker than operation
   commutativity and shown necessary by counterexample. Together they give convergence via Newman's
   lemma, with a complexity bound and a verification calculus that reduces CC to per-pair checks.
   The condition is exact: with canonical repair, every configuration from a start has a unique
   normal form iff CC holds on the states reachable from it, and for any enabledness the exact
   condition is joinability of critical pairs at reachable configurations (JC). The WFC potential may
   take values in any well-founded order, so the state space need not be finite; finiteness is only
   what makes gsm's exhaustive check decidable. Duplicate delivery is absorbed for idempotent governed
   steps and diverges otherwise.
   CRDTs embed as its compensation-free case, and the inclusion is strict on the same transition
   representation. Under causal delivery, where only concurrent events must commute, convergence
   still holds and the compensation-free fragment is exactly the CmRDT commutativity regime; under
   unordered at-least-once delivery it is exactly commutative-idempotent state evolution on
   reachable states, and with a finite event range and decidable state equality the CvRDT
   semilattice regime on reachable states (one theorem, `crdt_boundary`).
   - [mechanized] Newman's lemma and the convergence theorem, with a non-vacuity instance
     (`Newman.v`, `Governance.v`, `Defensibility.v`); the calculus's footprint-disjointness path
     (`Gsm.v`); the strict CRDT embedding (`CRDT.v`) and the boundary theorem with the sharpened
     witness (`CRDTBoundary.v`); convergence under causal delivery, standard
     op-based CRDTs, and the exactness theorem (`CausalReplay.v`), and the rewrite-system theorem
     with CC1 only for co-enabled events (`GovernanceCausal.v`); WFC over any well-founded order,
     with an infinite instance on `Z` (`GovernanceWF.v`); the exact converses `cc_exact_from`,
     `jc_exact` and `causal_exact`, with counterexamples to the naive converses
     (`GovernanceConverse.v`); at-least-once delivery (`AtLeastOnce.v`).
   - [paper] The necessity counterexamples, the complexity bound, and the rest of the calculus
     (strong absorption, decomposable repair, product composition).
2. **Federations.** An authority argument and resolution operators give convergence on any acyclic
   network, and monotone repair on any topology; acyclicity and M1 are shown necessary. Normal forms
   are a limit, so compositionality is a corollary; certificates form a sheaf whose gluing axiom is
   R1/R2; the obstruction on cycles is `H^1` holonomy. Coordinating a cycle basis suffices, the exact
   minimum is a group-feedback-edge-set number, and abelianized sizing is provably unsound (`S_3`).
   Driving values along a spanning tree from an authority root, checking balanced non-tree edges and
   coordinating unbalanced ones gives non-monotone cycles a normal form that is unique given the root.
   Event interleavings across registries converge iff C1 and C2 hold at reachable witnesses (acyclic)
   or the global condition GC holds (monotone cycles).
   - [mechanized] Order-independence and the retraction for arbitrary acyclic federations
     (`FederationOrder.v`, `Categorical.v`); the monotone least fixed point and chaotic iteration
     (`Federation.v`, `Chaotic.v`), and under the ascending chain condition instead of finite height
     (`ChaoticACC.v`); event interleavings across registries, with C1 and C2 exact at reachable
     witnesses and GC exact on monotone cycles (`FederationEvents.v`, `FederationEventsConverse.v`,
     `FederationEventsCycles.v`); soundness of the coordination plan for non-monotone cycles
     (`CoordinatedCycles.v`); the limit (an equalizer) and compositionality in its fold-append
     form (`Categorical.v`); the gluing counterexample; in the invertible fragment, the section
     criterion, the cycle-basis criterion, `H^1` as a quotient with `|E| - |V| + 1` generators, and
     the sufficiency of coordinating a cycle basis (`Cohomology.v`, `CohomologyGraph.v`); the `S_3`
     separation (`CohomologyMin.v`).
   - [paper] The authority and resolution theorems as stated, the necessity of acyclicity and M1,
     R1/R2 as the gluing axiom and the sheaf assembly over the full cover, the rank on the nerve as
     a 2-complex, the non-invertible case (a fixed-point condition on the loop composite), and the
     group-feedback-edge-set complexity (cited from the literature).
   - [implemented] The loop-composite diagnostic, as `Federation.DiagnoseCycle`.
3. **Synthesis.** An exhaustive search finds a convergent repair or, when it completes, a witness
   that none exists.
   - [implemented] `Registry.Synthesize` in gsm. The search is budget-bounded and can return
     undetermined; it is not mechanized.
4. **Trust.** Axiom-free Rocq proofs, CI-checked on three prover versions (Coq 8.18, Coq 8.20,
   Rocq 9.3). Every registry machine gsm returns (from `Build`, `SynthesizeWith`, and
   `BuildCompositional` per footprint component) is re-certified in process by a checker generated
   from the proof, with optimized variants proved to give the same results.
   - [mechanized] The checkers' soundness and the equality of the optimized variants
     (`TableFast.v`, `TableFn.v`, `AstTables.v`, `AstCompact.v`).
   - [implemented] The in-process gate in gsm.

**What isn't new.** Convergence by confluence (Newman, Meseguer), repair to a legitimate state
(Dijkstra), Knaster-Tarski and chaotic iteration, `H^1` theory and balance (Hatcher, Harary,
Zaslavsky), and group-feedback-edge-set complexity. These are the tools; the conditions and
theorems built with them are new. See [LANDSCAPE.md](LANDSCAPE.md) for the placement against prior
work.

## Key Concepts

### Normalization Confluence

A coordination-free convergence regime where:
- **Operations may violate invariants** (unlike invariant confluence)
- **Operations need not commute** (unlike CRDTs)
- **Compensation restores validity** after each operation
- **Compensated results commute** even though operations don't

Under two conditions - well-founded compensation (WFC) and compensation commutativity (CC) - all processors consuming the same events converge to the same valid state regardless of application order.

### Registry-Governed Streams

A **registry** is any authoritative definition of validity external to the stream processor: policy engines, constraint services, schema validators, compliance controllers. The registry provides:
- **Invariant predicates** defining valid states
- **Compensation operator** repairing violations deterministically

Events are applied in any order; the registry normalizes states after each event. The governance rewrite system interleaves event application with compensation.

### Federated Registries

Multiple registries connected by **morphisms** encoding cross-organizational constraints. A manufacturer's specifications constrain supplier capabilities; a regulator's rules constrain bank behavior.

For **tree-shaped networks** (directed forests where each non-root has one incoming morphism), federated convergence follows from component convergence + morphism validity preservation. The **authority argument** eliminates nondeterminism: source normal forms deterministically control target shared components.

The tree restriction is then removed. A target with **multiple sources** carries a **resolution operator** - a source-determined, validity-preserving merge of its incoming constraints (priority, conjunction, most-restrictive-wins) - generalizing the authority function. Under these two decidable conditions, convergence holds on **any acyclic network**, with the tree case as the single-source special case. Because the merge encodes domain policy, the guarantee is verified by finite enumeration rather than assumed.

Finally, when shared domains are ordered (lattices) and repair is **monotone**, acyclicity is unnecessary: the repair operator has a least fixed point (Knaster-Tarski) reached order-independently by chaotic iteration, so convergence holds on **any cyclic graph**. Both halves of this (least-fixed-point existence and asynchronous order-independent convergence) are machine-checked in [`coq/`](../coq). This reveals two independent routes to federated confluence:

| Regime | Repair requirement | Permissible topologies | Convergence guarantee |
|---|---|---|---|
| **Monotone** | Monotone on a lattice order (join *or* meet); validity-preserving | **Any**: cyclic meshes, DAGs, trees | Least fixed point `lfp(⊥)` under any *fair* asynchronous order |
| **Non-monotone** | May reverse the order (toggles, negation, cancellations); validity-preserving | **Acyclic** coordination-free; multi-source targets need resolution operators. Cycles only with a computed coordination | Deterministic one-shot normal form; on a coordinated cycle, unique given the authority root (`CoordinatedCycles.v`) |

Monotonicity and acyclicity are orthogonal: either alone suffices. Validity preservation is required in both. State-based CRDTs are the compensation-free special case of the monotone regime.

## Three Regimes of Coordination-Free Convergence

| Regime | Requirement | Guarantees | Design Space |
|--------|-------------|------------|--------------|
| **Operation Commutativity** (CRDTs) | Operations commute algebraically | Convergence without coordination | Commutative operations only |
| **Invariant Confluence** | Operations preserve invariants in all orderings | Convergence without repair | Invariant-preserving operations only |
| **Normalization Confluence** | Compensated results commute (operations need not) | Convergence through repair | Non-commutative, invariant-violating operations |

Normalization confluence occupies the gap between CRDTs (requires commutativity) and I-confluence (requires invariant preservation). It permits operations that satisfy neither, provided compensation commutes.

These regimes are **nested, not merely adjacent**. CRDTs are the *compensation-free* corner: operations designed so repair is never needed. Drop that restriction, keep the convergence guarantee, and you have normalization confluence, so every CRDT is a governed machine whose max repair depth is zero, and the inclusion is **strict** on the same transition representation (there are convergent governed machines whose raw transitions, without compensation, satisfy no CRDT convergence condition; the claim is about representations, since such a machine's governed behavior can itself be a CRDT). This is not informal: it is machine-checked, axiom-free, in [`coq/CRDT.v`](../coq/CRDT.v) (`cmrdt_SEC`, `cvrdt_SEC`) and [`coq/CRDTBoundary.v`](../coq/CRDTBoundary.v) (the boundary theorem `crdt_boundary`, the witnesses `witness_ops_not_commute`, `witness_not_cvrdt_order`, `witness_not_cvrdt_exact`, and the qualifier `witness_governed_constant`), and stated in full in [SUBSUMPTION.md](SUBSUMPTION.md). The relationship also holds under causal delivery, where only concurrent operations must commute: standard op-based CRDTs converge as an instance, and the compensation-free fragment is *exactly* the op-based CRDTs ([`coq/CausalReplay.v`](../coq/CausalReplay.v): `causal_cmrdt_SEC`, `compensation_free_exact`), with the full rewrite-system theorem in [`coq/GovernanceCausal.v`](../coq/GovernanceCausal.v). So "a third regime alongside CRDTs" is the entry framing; the sharper claim the proofs support is that normalization confluence is the general regime and CRDTs are its compensation-free fragment.

## Mathematical structure

In one line: a local-to-global theory of canonical forms, built from convergent rewriting,
fixed-point theory, categorical descent and cohomological obstruction, with the boundary of each
stated exactly. This section places the theory in pure mathematics and says, area by area, what is
mechanized and what is classical or paper-only. A name in backticks is a Coq theorem in
[`coq/`](../coq), checked by the axiom-free gate in `coq/verify.sh` unless the text says otherwise.
Status per regime is in [REGIME-AUDIT.md](../REGIME-AUDIT.md); where the two differ, the audit
wins.

### Two engines

Canonical forms come from two different sources, and the split is mathematical, not an
implementation detail: rewriting finds the canonical form as the end of a well-founded descent that
local confluence makes unique; fixed-point theory finds it as the least fixed point of a monotone
operator, an extremal point of an order rather than the end of a descent.

- **Well-founded rewriting.** A single registry is an abstract rewriting system. WFC makes it
  terminating (the potential may take values in any well-founded order), CC makes it locally
  confluent, and Newman's lemma gives unique normal forms (`newman_on`, `governance_confluent`,
  `governance_wf_confluent`). The conditions are exact at the states that matter: every event
  buffer from `s0` has a unique normal form iff CC1 and CC2 hold at the states reachable from `s0`
  (`cc_exact_from`); for any enabledness, confluence is joinability of critical pairs at reachable
  configurations (`jc_exact`), and when a compensation step can disable an event, its localized
  form `JCg` (`jcg_exact`).
- **Monotone fixed-point theory.** On a cycle the authority argument fails (every registry is
  downstream of itself), so the canonical form comes from order instead: the least fixed point of
  a monotone repair operator on a lattice. Classical: Knaster-Tarski, Kleene iteration, and
  chaotic iteration (Cousot). Mechanized: a stabilized Kleene iterate is the least fixed point and
  that point is unique (`kleene_lfp`, `lfp_unique`); Kleene iteration stabilizes under the
  ascending chain condition (`kleene_acc_lfp`); chaotic iteration from bottom can always reach the
  least fixed point, and every schedule that runs to quiescence ends there
  (`chaotic_reaches_lfp`, `chaotic_limit_unique`, `chaotic_acc_reaches_lfp`).
  `MonotoneExact.v` makes two further questions exact: under R2 with valid locals, a least fixed
  point reached by iteration (or any, under ACC) is valid iff some Kleene iterate is
  (`lfp_valid_iff_reached`, `lfp_valid_exact`), and it is reached in finitely
  many steps iff the Kleene chain is eventually constant iff there is no infinite strict ascent
  along it (`kleene_reach_exact`, `chaotic_reach_exact`). Knaster-Tarski itself, on a complete
  lattice without ACC, is outside the axiom-free gate by design (gap 8).

### Category theory: normalization as a retraction

A normalizer `rho : S -> S` is idempotent, so it is a retraction of `S` onto its image, and its
image is its fixed-point set (`image_iff_fixed`, `retract_into_fixed`). That set is
`Fix(rho) = Eq(id, rho)`, the equalizer of the identity and `rho`, so the canonical states form a
limit (`fixed_is_equalizer`). For an acyclic federation the same holds one level up: on the product
of the components' valid sets, the federated canonical states `L_F` are the equalizer of two maps
(`cat_prop_one`), and the federated normalizer is a retraction onto `L_F` whose image and fixed
points are exactly `L_F` (`cat_thm_one_sound`, `cat_thm_one_complete`, `cat_thm_one_idempotent`,
`cat_thm_one_image`, `cat_thm_one_fixed`). Compositionality is a corollary of this one fact.

On an ordered state space, a map that is monotone, extensive and idempotent is a closure operator
(classical). The federated repair is not automatically one: a sub-federation's repair can fail to
be monotone even when its repair operator `Phi_J` is monotone and the component satisfies WFC
(`fed_rem_convexity_refuted`); the corrected hypothesis is `fed_rem_convexity_corrected`.

### Sheaves: local to global

The federated question has the shape of a gluing problem. Local normal forms are sections over
registries, and agreement on shared components is the compatibility condition on overlaps; the
papers state R1/R2 (source-determinacy and validity preservation) as the gluing axiom. The positive
sheaf assembly over the full cover is paper only (open gap 13). The negative half is mechanized:
two normalizers that agree on every valid state still glue to an order-dependent system on the
shared state (`gluing_order_dependent`), so local agreement alone does not glue.

### Cohomology and topology

When transports are invertible (labels in a group `G`, with `G` acting on itself, the regular or
torsor action), the obstruction to a global section is holonomy along cycles. Classical: the
fundamental group of a connected graph is free of rank `|E| - |V| + 1`, so `H^1(graph; G)` is
`Hom(pi_1, G)` up to conjugation, that is `G^k` up to simultaneous conjugation with
`k = |E| - |V| + 1`. Mechanized combinatorially, without constructing `pi_1`: the non-tree edges of
a spanning tree number `|E| - |V| + 1` (`betti_number`), and two tree-fixed labelings are
cohomologous iff their non-tree labels are simultaneously conjugate (`H1_classification`).

A global section exists iff the labeling is a coboundary, that is, iff its class in `H^1` is
trivial (`section_iff_coboundary`, any graph, any group), iff every fundamental cycle of a spanning
tree has trivial holonomy (`cycle_basis_criterion`). With the regular action and an authority
root, `H^1 = 0` iff, for
every root value, the coordination-free network has a unique consistent state reached by every
propagation order (`prop_minimal_qualified_iff`). Each qualifier is proved necessary:

- the regular action: for a non-free action a non-identity holonomy can still leave a consistent
  state (`nonfree_holonomy_counterexample`);
- the authority root: without one, two propagation orders reach different consistent states
  (`copyback_without_authority`), and the root chosen decides which (`root_choice_matters`);
- for a rootless, coherently oriented invertible cycle on at least two registries with trivial
  holonomy, the reachable consistent state is unique iff `G` is trivial (`rootless_unique_iff`).

### Non-abelian obstruction

Abelianizing the labels loses information, and it can undercount. On a theta graph labeled in
`S_3`, the minimum number of edges to coordinate is 2 over `S_3` and 1 over its abelianization
(`theta_separation`). The general direction is a bound: the minimum over `G` is at least the
minimum over any homomorphic image of `G`, in particular `G^ab` (`min_G_ge_min_image`). So
abelianized sizing gives a lower bound only, and it can be strictly too small.

### Minimal surgery

When the obstruction is nonzero, the question becomes how little to coordinate. Coordinating every
non-tree edge of a spanning tree always suffices (`tree_has_section`). For invertible labels the
minimum set of edges whose removal leaves a section is the group feedback edge set number of the
labeled graph; it is NP-hard even in the abelian case, a result cited from the literature and not
mechanized. Mechanized pieces: `edge_disjoint_lower_bound`, `edge_disjoint_min`,
`min_G_ge_min_image`, `theta_separation`. Linking this minimum to the plan model (tree, root,
coordinated set) is open (gap 10); the minimum for lossy transports is open (gap 11).

### Beyond groups: the lossy side

Without inverses there is no group, no torsor and no `H^1`. Each edge is then an equation
`f(s(u)) = s(v)` with `f` an arbitrary map on a fiber, and consistency is a constraint-satisfaction
question. On a network without a spanning root, existence is NP-complete: the 3-SAT reduction is mechanized in `LossyHardness.v` (a
network built from a 3-CNF has a section iff the formula is satisfiable, `net_section_iff_sat`;
sections correspond one to one to satisfying assignments, `net_bijection`; the construction is
linear, `net_size`; a section is an edge-by-edge checkable certificate, `np_certificate`), and
NP-completeness follows by the standard argument. The exact criterion is mechanized in
`RootSet.v`: for any root set and spanning forest, a section exists iff some root assignment
drives a state satisfying every edge (`root_set_criterion_graph`), and sections are counted by the
consistent root assignments (`root_set_count`). On a single cycle the test is the loop composite:
a section exists iff the loop composite has a fixed point reachable from some seed
(`thm_obstruction_reachable`), and on a finite fiber a bounded number of iterations decides it
(`diagnose_bounded`, `diagnose_dichotomy`). So the obstruction theory has a proved boundary: cohomology where maps are
invertible, provable hardness where they are not. The research note on lossy networks,
`LOSSY-NETWORKS.md`, is in progress (PR #52).

### Monoids and traces

Event sequences are words in the free monoid `E*`, and running them is an action of `E*` on states.
Order independence up to a declared independence relation `I` means that this action factors
through the trace monoid `E*/~I` (Mazurkiewicz traces, a partially commutative monoid): if every
`I`-pair commutes on the relevant domain, trace-equivalent words act identically (`run_tequiv`).
Under causal delivery, any two causally consistent orders are trace-equivalent with concurrency as
`I` (`causal_tequiv`). When every pair is independent, trace equivalence is permutation
(`perm_tequiv_total`): free commutation is the free commutative monoid case.

### Repair confluence and event confluence, mathematically

The two convergence notions are different mathematical properties. Repair confluence is the
existence of a retraction onto the canonical states. Event confluence is the statement that the
governed action of `E*` (an event, then repair) factors through the trace quotient. Repair
confluence holds, under each regime's hypotheses, on acyclic federations and on monotone cycles,
and it does not imply event confluence: a two-registry acyclic federation with C2 and local CC, but not C1, sends two event
orders to different states (`audit_counterexample`); a tree with component WFC, CC and M1 has one
start and one event buffer with two distinct normal forms (`fed_thm_fed_convergence_refuted`); and
on a monotone cycle whose repair is the least fixed point, two trace-equivalent sequences diverge
(`cyc_counterexample`). The exact event conditions are separate theorems: C1 and C2 at reachable
witnesses on acyclic federations (`fed_exact_full`), and the global condition GC on monotone cycles
(`cyc_events_converge_iff`, `net_events_converge_iff`).

### The four questions

| Question | Mathematical form | Answer |
|---|---|---|
| **Existence** | A global section (`H^0` non-empty) | Invertible: exact, the class in `H^1` is trivial (`section_iff_coboundary`, `cycle_basis_criterion`). Lossy: exact by root sets (`root_set_criterion_graph`), and NP-complete without a spanning root (`net_section_iff_sat`, `np_certificate`) |
| **Convergence** | Repair: a retraction onto the canonical states. Events: the `E*` action factors through the trace monoid | Repair: `cc_exact_from`, `jc_exact` (one registry), `cat_thm_one_sound` and `cat_thm_one_fixed` (acyclic), `chaotic_reaches_lfp` (monotone cycles), `prop_minimal_qualified_iff` (invertible cycles with a root). Events, separately: `fed_exact_full` (acyclic), `cyc_events_converge_iff` (monotone cycles); not implied by repair (`audit_counterexample`, `cyc_counterexample`) |
| **Obstruction** | What blocks a section | Invertible: holonomy, the class in `H^1` (`cycle_basis_criterion`, `H1_classification`). Lossy: a loop composite with no reachable fixed point (`thm_obstruction_reachable`, `diagnose_dichotomy`) |
| **Surgery** | The least coordination that removes the obstruction | Invertible: the group feedback edge set number, NP-hard (cited), with mechanized bounds (`edge_disjoint_lower_bound`, `min_G_ge_min_image`, `theta_separation`); its link to the plan model is open (gap 10). Lossy: open (gap 11), with the upper bound `rooted_coordination_suffices` |

[REGIME-AUDIT.md](../REGIME-AUDIT.md) asks these questions of every regime: existence and
convergence are its convergence rows, surgery its optimization rows, and the obstruction is what
its exact conditions name. For each it records the exact condition, the hardness result, or the
open gap.

### Continuous analogue

Discrete well-founded descent plus confluence has a continuous counterpart: a Lyapunov function
plus contraction. Both ask whether every trajectory reaches one canonical state regardless of
order, so the question is structurally the same, but the answers are different theorems in
different branches of mathematics, not one theorem with two instances. Nothing continuous is
proved here; [LYAPUNOV-EXTENSION.md](LYAPUNOV-EXTENSION.md) maps the direction.

### Calibration

Each area is classical: Newman's lemma, Knaster-Tarski and chaotic iteration, equalizers and
retractions, sheaves, graph cohomology and gain-graph balance, Mazurkiewicz traces, and the
complexity of group feedback edge sets and of 3-SAT. The contribution is the combination: the
exact boundaries between the areas, the non-abelian and lossy results, and the mechanization. See
[LANDSCAPE.md](LANDSCAPE.md) for the placement against prior work.
