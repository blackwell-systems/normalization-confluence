# Theory overview

The theory in one page: the regime it adds, what is new and what is not, the key concepts, how
the three convergence regimes nest, the decomposition through which six exact convergence results
are rederived ([Canonical execution](#canonical-execution)), and where the theory sits in pure
mathematics ([Mathematical structure](#mathematical-structure)). "What's new here" marks each item
mechanized, paper or implemented. For the
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
     (`GovernanceConverse.v`); at-least-once delivery (`AtLeastOnce.v`); the necessity
     counterexamples (`thm_necessity`, `prop_cc_necessary`, `PaperInstances.v`); the per-event and
     total step bounds (`base_thm_complexity_per_event`, `base_thm_complexity_comp_total`,
     `RhoStar.v`); and the rest of the calculus, strong absorption (`base_thm_strong_absorption`),
     decomposable repair (`calc_decomp_normalizer`), product composition (`base_thm_product`) and
     the corrected footprint theorem (`calc_footprint_cc1_iff`; the paper's v1 statement is refuted,
     `base_thm_footprint_cc1_refuted`) (`Calculus.v`).
   - [paper] The asymptotic cost model of `thm:complexity` (`O(n)`, `O(n log n)` with a priority
     queue), which concerns data structures rather than the step bound.
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
     separation (`CohomologyMin.v`); `H^1` on the nerve as a 2-complex (`CohomologyNerve.v`); sheaf
     gluing over sub-federation covers (`SheafGluing.v`); the non-invertible case
     (`CohomologyGeneral.v`, `RootSet.v`, `LossyHardness.v`); minimum coordination, tied to the
     plan model on invertible networks and through root sets on lossy ones, with its hardness
     reductions (`CoordinationMinimum.v`, `LossyMinimum.v`).
     The authority and resolution theorems in their corrected (v2) form (`fed_lem_authority_a`,
     `fed_lem_authority_b`, `fed_lem_authority_c_corrected`, `fed_lem_resolved_termination`,
     `fed_thm_fed_convergence_corrected`, `fed_thm_resolved_convergence_corrected`,
     `FederationGRS.v`) and the necessity of acyclicity and M1 (`prop_cycle_necessary`,
     `prop_m1_necessary`, `PaperInstances.v`).
   - [paper] The sheaf assembly on the variable-level and monotone-overlap site, and the cited
     complexity results (NP-completeness of 3-SAT and Max-Cut; fixed-parameter, planar and
     approximation results for group feedback edge sets).
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

## Canonical execution

> A system is canonical exactly when every ambiguity its execution model can expose is either
> eliminated by canonicalization or proved semantically irrelevant; in acyclic compositions, those
> obligations can be checked locally.

That sentence states the framework through which six of the repository's exact convergence
results are rederived as short corollaries (below). It is mechanized axiom-free in
`CanonicalExecution.v` (the kernel), `CanonicalInstances.v` (the single-system instances) and
`CanonicalLocality.v` (composition), all in the `coq/verify.sh` gate. Full statements,
per-theorem qualifiers and the statement review are in
[coq/docs/canonical-execution.md](../coq/docs/canonical-execution.md). Where
[Mathematical structure](#mathematical-structure) places the theory area by area, this section
gives a decomposition that cuts across the rewriting, trace and federation areas. Status per
regime stays in [REGIME-AUDIT.md](../REGIME-AUDIT.md); nothing here changes a row there.

### The decomposition: E, S, H and P

An execution model can expose three kinds of ambiguity: which configuration the dynamics settles
in, which representative of a state an event acts on, and which of several equivalent histories
was run. Each layer below is the obligation that removes one of them; P says when the obligations
of a composite can be checked on its parts.

- **E, effective canonicalization.** The dynamics settles (Settlement), and the settled
  configurations it reaches are the canonical ones designated by an idempotent canonicalizer `N`
  (canonical fidelity). This eliminates the settling ambiguity by canonicalization.
- **S, state descent (state coherence).** An event's canonical outcome does not depend on whether
  it acts on a raw state or on its canonical form: `N (act e s) = N (act e (N s))`. Equivalently,
  every event respects `N x = N y` (`state_descent_iff_respects_canon`), and then a raw run and the
  governed run agree after canonicalization (`normalization_descent`). With `N := rho*` from WFC,
  state descent is CC2 in its all-events form (`state_descent_iff_cc2`).
- **H, history descent (history coherence).** The canonical semantics is constant on the semantic
  equivalence classes of admissible executions. Under presentation adequacy (the semantic
  equivalence is generated by a set of edges between admissible executions), this holds iff it
  holds across each generator edge (`history_descent_exact`). This proves the history ambiguity
  semantically irrelevant.
- **Peaks.** For a rewrite presentation, under termination from the start, confluence is
  joinability of the peaks at reachable configurations (`peak_exact`, Newman's lemma localized),
  split by any complete classifier into state peaks and history peaks (`classified_peak_exact`).
- **E, S and H together.** Under Settlement, every settled run agrees with the canonical semantics
  and settled runs with equivalent histories agree iff canonical fidelity, state descent at every
  reachable configuration and history descent hold (`canonical_execution_exact`). `esh_exact` is
  the same statement with Settlement carried on both sides; `esh_sufficient` is the backward
  direction, with no Settlement.
- **P, composition.** Two theorems, kept separate.
  - Interaction locality, `factor_exact`: global ambiguities decompose into local ambiguities
    (inside one component) and interface ambiguities (across the composition boundary). Under
    locality completeness `LC` (components of an exposed global ambiguity are exposed, and an
    exposed global ambiguity whose components are resolved is resolved) and `Realizable` (every
    exposed local or interface ambiguity is forced by an exposed global one), global resolution
    holds iff local and interface resolution hold. Each of the three premises is needed
    (`factor_needs_sound`, `factor_needs_exposed`, `factor_needs_realizable`). In the acyclic
    federation the interface ambiguities have the S shape (C1R1: pointwise state descent of a
    target's local canonicalizer) and the local ambiguities the H shape (C2R: the one-swap
    condition of a local governed run); `LC` is the model's locality and topological-solving
    argument (`fed_lc_sound`, `fed_reflects`), and `fed_factor_supply` discharges every premise on
    the supply chain.
  - State gluing, `SheafGluing.v`: local canonical states glue on a cover, for every federation
    satisfying R1, iff the cover refines the constraints (`sheaf_iff_refines`, `gluing`).
  - The shared hypothesis: the locality behind `LC` in the federation (a repair reads only its
    sources, `c_local`) is equivalent to R1 at fixed target values (`c_local_iff_r1`; `common_r1`
    is the direction from the federation's hypotheses). On an acyclic federation the two halves
    hold together as a conjunction, `fed_state_and_interaction`; neither is used to prove the
    other.
  - An observation, not a theorem: state gluing reads as descent of objects (canonical states
    along a cover) and interaction locality as descent of morphisms (commutation of steps along a
    composition boundary). No combined descent statement is formalized.

### Symmetry and state descent

The symmetry reduction (`SymmetryCutoff.v`, [ROADMAP.md](ROADMAP.md) item 8) is a small instance
of the decomposition. In a collection of independent, identically governed items, a peak between
two events on the same item is a peak of the one-item registry (`same_item_reduces`). A peak
between events on different items is two S obligations, one per item, `N (e (N s)) = N (e s)` with
`N = rho*` (`cross_item_reduces`): no condition relates the two items. State descent of the item
(its CC2) discharges them (`cc2_star`), and at valid states they hold with no hypothesis
(`cross_valid_commute`). Invariance under permutations of the keys makes every item the same check,
so unique normal forms have a cutoff of one item (`un_cutoff`), while CC1 taken without CC2 needs
two (`cc1_cutoff`, `cc1_cutoff_tight`): its cross-item peaks are exactly the S obligation it leaves
out. An aggregate invariant breaks the decomposition at S: its repair must change items that are
valid on their own, so the canonicalizer is not a product of item canonicalizers, and the
collection diverges while the single item converges (`aggregate_diverges`).

Abstraction (`AbstractionCutoff.v`) is the same move on value relations instead of item keys.
For rules that compare and copy values and declared constants, two states with the same order
type relative to the constants are related by an order isomorphism that the rules commute with
(`OrdInv`), so every condition gives them the same answer (`cc1_order_type`, `cc2_order_type`). The
quotient by order type is a state descent the checker can use: each condition over all integers
is decided over a finite set of representatives (`cc1_abs`, `un_abs`). The equivalence fails for
additive rules, where states of one order type can differ on `x + y < z` (`triangle_diverges`).
There the reduction is to the validity of one formula per condition (`lin_exact`), not to a finite
quotient.

### Scope

- **Exact for single systems:** E, S and H.
- **Exact for acyclic composition:** P, through `factor_exact` and its federation instance.
- **On cycles, P has the soundness direction only.** On the monotone-cycle model, local and
  interface resolution give commutation of every independent pair at every normal form
  (`cyc_factor_sound`) and the global condition GC from every normal form
  (`cyc_factor_sound_gc`), through a static decomposition whose realizability is not proved.
  Locality itself fails without acyclicity: on a two-registry copy cycle every exposed local and
  interface ambiguity is resolved, yet two declared-independent events diverge, so `LCSound`, and
  hence `LC`, fails (`cyclic_lc_sound_fails`; the divergence alone is `cyclic_lc_fails`). The
  cyclic open convergence problems are the question this leaves: what additional structure makes P exact
  on cycles ([REGIME-AUDIT.md, the cyclic frontier](../REGIME-AUDIT.md#the-cyclic-frontier)).
- **A canonicalizer chosen by the dynamics.** E does not have to use the least fixed point. In the
  no-reset distributed model on monotone cycles, convergence among quiescent interleavings alone is
  exact with the quiescent state propagation settles in as the canonical state, a ghost allowed
  (`conv_quiet_exact`, `DistributedConvergenceExact.v`): fidelity becomes "every reachable state
  flushes to at most one quiescent state", and S and H are state descent and history descent for
  that flush. `flush_fed_iff` is the case where the flush is `Lfp` (`agree_conv_noghost`: agreement
  with the FedMachine is convergence plus `NoGhostR`). The flush is a relation, not a function, so
  this is proved directly rather than as an instance of `esh_exact`, whose canonicalizer is a
  function; an axiom-free choice of a flush for every state is not available.

### Evidence: six exact results as short corollaries

Each existing exact theorem below is rederived through the kernel with the same exported statement
(premises up to order), with two exceptions. `flush_fed_iff_kernel` has `flush_fed_iff`'s
conclusion with none of its order, rank or cover premises. `stream_exact_free` is reread, not
rederived: the kernel proves its history half, `stream_free_hd_iff_pcc` (history descent over
duplicate-free reorderings iff PCC, with no use of `stream_exact_free`). Line counts are proof
bodies, as checked in the statement review.

| | Existing result | Rederivation (proof-body lines) | Kernel route |
|---|---|---|---|
| A | `jc_exact`, `jcg_exact` (single registry) | `jc_exact_kernel` (14), `jcg_exact_kernel` (12) | `classified_peak_exact`: event/compensation peaks are state peaks, distinct event/event peaks history peaks |
| B | `causal_exact` (causal delivery) | `causal_exact_kernel` (4) | `history_descent_exact`; generators are adjacent concurrent swaps, whose edge condition is CCR |
| C | `alo_exact`, `causal_alo_exact`, `causal_alo_exact_idem` (at-least-once) | `alo_exact_kernel` (5), `causal_alo_exact_kernel` (3), `causal_alo_exact_idem_kernel` (3) | `history_descent_exact`; swaps plus one duplicate generator at its legal landing point (`gen_idem`, `gen_abs`). The cost is adequacy, about 250 lines of semantics-free word combinatorics |
| D | `fed_exact`, `fed_exact_full`, `gc_iff_reach`, `reach_commute_iff` (acyclic federation, event order) | `fed_exact_P` (6), `gc_iff_reach_P` (2), `reach_commute_iff_P` (16), `fed_exact_full_P` (14) | H then P: `history_descent_exact`, then `factor_exact` and `factor_pointwise`; instance glue about 85 lines, with `LC` the model's locality lemma |
| E | `pjc_exact`, `stream_exact` (stream processors); the history half of `stream_exact_free` | `pjc_exact_kernel` (10), `stream_exact_kernel` (15); `stream_free_hd_iff_pcc` | `classified_peak_exact` with an empty state-peak class; `history_descent_exact` for the free-delivery history half, whose swap edge condition is PCC |
| F | `flush_fed_iff` and the ghost family (distributed model, monotone cycles, no resets) | `flush_fed_iff_kernel` (5) | `esh_exact`: Settlement is `FlushR`, canonical fidelity `NoGhostR`, state descent `XUcR`, history descent `FMConv`; `flip_esh`, `ghost_esh`, `copy_xu_esh` and `fm_conv_esh` each fail one layer, `conv_ghost_esh` holds H without E, and `raise_only_esh` holds all three |

### Absent laws, explained

The framework also says why some laws are absent from the published exact conditions.

- **Streams have no state-descent condition.** A stream processor normalizes before every event,
  so an event never acts on a raw invalid state, and the state-peak class of the stream classifier
  is empty (`stream_state_peaks_empty`, with completeness `st_complete`). Confluence is then the
  history-peak condition PJC alone. The statement is about that classification: peak kinds are
  labels, and no theorem shows the S layer itself vacuous for streams.
- **Causal at-least-once needs `AbsorbAt`, not plain idempotence.** In the history kernel a
  redelivery is a generator, and the generator has to sit at its legal landing point: a copy at
  the end of an exactly-once causal run that holds the event and none of its causal successors.
  Its edge condition is exactly `AbsorbAt` (`gen_abs`); a copy right after the first delivery has
  edge condition exactly `IdemAt` (`gen_idem`). A naive `aa = a` generator at every prefix does
  not reproduce the published condition: its edge condition is idempotence at prefixes that
  already contain duplicates.

### The missing compositional ingredient

The first validation run rederived the history layer of `fed_exact` (`fed_exact_kernel`, 7 lines)
and then stopped: splitting a cross-registry swap into a state-descent obligation (C1R1) and a
history obligation (C2R) needed locality (an event on registry `j` changes nothing outside `j` and
its downstream registries) and topological solving (the re-normalized state is the unique solution
of the component equations). Neither is expressible in E, S or H; both say how a global
canonicalizer decomposes into local canonicalizers along a dependency order. That diagnosis named
P, and `factor_exact` supplied it with `LC` as a named obligation, after which D passes. The same
diagnosis locates the cyclic frontier: on a cycle an event's own write comes back through its
sources, so the environment of a local canonicalizer is not fixed by the event's registry, and that
is where `LC` fails (`cyclic_lc_sound_fails`).

### Qualifiers

- `esh_exact` (with `canonical_execution_exact` and `esh_sufficient`) assumes every event is
  admissible after every admissible word, so its reachability is under unrestricted event
  delivery. Regimes that restrict event order (B, C) go through `history_descent_exact`, whose
  admissibility predicate expresses causal delivery; of the six results only F instantiates
  `esh_exact`.
- `state_descent_iff_cc2` is the all-events form of CC2 (every event at every invalid state), not
  the paper's Axiom CC2, which asks it only for enabled events.
- C1R1 is pointwise state descent with a point-dependent canonicalizer (`c1r1_state_descent`): the
  canonicalizer `f j z` depends on the environment `z` after the other event, and it is idempotent
  only on valid target values. It is not state descent at every reachable configuration for one
  fixed `N`.
- `stream_free_hd_iff_pcc` is the kernel rederivation of `stream_exact_free`'s history half.
  `stream_free_history` rewrites by `stream_exact_free` itself, so it is a restatement, not a
  rederivation.
- `factor_exact` is logically thin by design: `LCSound` and `Realizable` are its two directions
  stated per ambiguity, so its content is its premises. The composition argument lives in each
  instance's proof of `LC`.

### Quotients for checking

Every proved semantic quotient is also a potential verification quotient. State descent (S) says
which states an event's canonical outcome cannot tell apart; the same equivalence lets a checker
visit one representative instead of every state, which is what the symmetry and abstraction
reductions of [ROADMAP.md](ROADMAP.md) item 8 do. History descent (H) says which histories reach the
same canonical state; the same equivalence lets a checker follow one order per class, which is
partial-order reduction. "Potential" carries the qualification: a quotient is usable for a check
only when that check's condition respects it, and each reduction is to be stated with a soundness
theorem for the condition it serves. Partial-order reduction itself is classical (Mazurkiewicz
traces; persistent, stubborn and ample sets); the point here is that the reduction relation is the
one the convergence proofs already establish.

### What it is not yet

The framework has rederived the six existing exact results and explained the absent laws above.
Its decomposition shaped one new exact result: gap 14, convergence alone in the no-reset cyclic
distributed model, is E, S and H relative to the quiescent state propagation settles in
(`conv_quiet_exact`, above under Scope). Read through it, `conv_ghost_esh`'s "H without E" becomes
all three layers for the dynamics' canonicalizer (`conv_ghost_instance`). That result needed a
different canonicalizer, not P. The open test is still the cyclic frontier: a structure that makes
P exact on cycles would settle the remaining open gaps.

## Mathematical structure

In one line: a local-to-global theory of canonical forms, built from convergent rewriting,
fixed-point theory, categorical descent and cohomological obstruction, with the boundary of each
stated exactly. This section places the theory in pure mathematics and says, area by area, what is
mechanized and what is classical or paper-only. The decomposition that rederives six exact
convergence results (E, S, H and P) is the previous section,
[Canonical execution](#canonical-execution). A name in backticks is a Coq theorem in
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
papers state R1/R2 (source-determinacy and validity preservation) as the gluing axiom. Mechanized
in `SheafGluing.v` on the registry-level site (open sets are sub-federations, sections over `U`
are the states consistent on `U`): separation holds with no hypothesis (`separation`), and under
R1 a compatible family of local sections glues, uniquely, when every constraint inside the union
lies inside one member of the cover (`gluing`, `sheaf_exact`). That condition is exact, uniformly
in the data: gluing holds on a cover for every R1 federation on the graph iff the cover refines the
constraints (`sheaf_iff_refines`). It is a condition on members, not overlaps (`chain_glues`), and
each hypothesis is needed (`triangle_fails`, `r1_failure`). Certificates (the federated normalizer
restricted to a sub-federation) glue on covers closed under sources (`cert_sheaf`), restriction is
exact exactly for such sub-federations (`cert_restrict_iff`), and SC, not validity preservation,
is what makes a certificate land in its sections (`cert_needs_sc`). The negative half: two
normalizers that agree on every valid state still glue to an order-dependent system on the shared
state (`gluing_order_dependent`, wrapped as `gluing_cex_overlap`), so local agreement alone does
not glue. Still paper only (gap 13, narrowed): the companion paper's variable-level site and its
monotone-overlap regime.

### Cohomology and topology

When transports are invertible (labels in a group `G`, with `G` acting on itself, the regular or
torsor action), the obstruction to a global section is holonomy along cycles. Classical: the
fundamental group of a connected graph is free of rank `|E| - |V| + 1`, so `H^1(graph; G)` is
`Hom(pi_1, G)` up to conjugation, that is `G^k` up to simultaneous conjugation with
`k = |E| - |V| + 1`. Mechanized combinatorially, without constructing `pi_1`: the non-tree edges of
a spanning tree number `|E| - |V| + 1` (`betti_number`), and two tree-fixed labelings are
cohomologous iff their non-tree labels are simultaneously conjugate (`H1_classification`).

On the nerve as a 2-complex, each 2-cell (a triangle, or any closed walk) adds a relation: its
holonomy must be trivial. Mechanized in `CohomologyNerve.v`: for any group, `H^1(K; G)` is the
assignments of the non-tree generators satisfying every cell's relation word, up to simultaneous
conjugation, that is `Hom(<X | relation words>, G)` modulo conjugation (`nerve_H1_classification`;
abelian `G`: no quotient, `nerve_H1_abelian`). There is no rank for non-abelian `G`; the
classification replaces it. Over Z/2 the count is exact: `2^((|E| - |V| + 1) - rank)` classes, the
rank being the number of independent cell relations (`nerve_H1_Z2_count`); with no cells it is
`2^(|E| - |V| + 1)` (`nerve_Z2_no_cells`), and the cells lower it exactly when they impose a
relation (`nerve_Z2_full_iff`). The cells change the count, never existence: a section exists iff
the labeling is a coboundary, independent of the cells (`nerve_section_iff_coboundary`). Classical
and not mechanized: that the presented group is the fundamental group of the complex.

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
  holonomy, the reachable consistent state is unique iff `G` is trivial (`rootless_unique_iff`);
  on any finite rootless network the root reappears as structure: the reached consistent state is
  unique iff (given `H^1 = 0`) every weakly connected component contains a registry no other
  registry writes, or `G` is trivial (`net_unique_iff`), and a unique normal form from every start
  holds iff `H^1 = 0` and that registry can be chosen upstream of the whole component, an authority
  root, or `G` is trivial (`net_unique_normal_form_iff`).

The same criterion holds on walks, with no spanning tree. In `SignedCycles.v` a walk may cross an
edge backward with the inverse label, and a section transports along every walk
(`section_transport`). On any finite edge list, with no spanning-tree or connectivity premise, a
section exists iff every closed walk has trivial holonomy, iff walk labels are path-independent,
iff the labeling is a coboundary; and two directed paths `u -> v` with different labels `h1`, `h2`
close into a closed walk with holonomy `h2^-1 h1`, which rules out a section
(`invertible_merge_is_holonomy`, `holonomy_free_section`). At Z/2 this is **Harary's balance
theorem, proved** (not cited): a finite signed graph, parallel edges and self-loops allowed, has a
switching to all-positive iff no closed walk carries an odd number of negative edges
(`harary_balance`). The mechanized form is stated for closed walks; the classical form with simple
cycles (an odd closed walk contains a negative cycle) is not mechanized.

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
labeled graph, and it is exactly what the coordination plan achieves at its best: on a connected
network, some plan rooted at `r` coordinates at most `k` edges iff some feasible coordination
deletes at most `k` edges, for every root (`plan_min_exact`, `plan_min_attained`,
`plan_min_root_independent`). It is NP-hard already over Z/2: Max-Cut reduces to it, with the
reduction mechanized (`maxcut_reduction`, `maxcut_plan_reduction`) and Max-Cut's NP-completeness
cited. Earlier bounds: `edge_disjoint_lower_bound`, `edge_disjoint_min`, `min_G_ge_min_image`,
`theta_separation`. For lossy transports the minimum is the least deletion whose residual passes
the root-set criterion (`lmin_root_set`, decided by `lmin_decide`); on group-labeled networks it is
the group feedback edge set minimum (`lossy_min_is_gfes`), but in general it is not cycle-based:
a tree of two constant maps needs one deletion, which every cycle-only lower bound misses
(`lossy_min_exceeds_cycle_bounds`). Telling minimum 0 from minimum 1 is NP-hard, by the 3-SAT
reduction (`lmin_reduction`), so no efficient approximation within any factor exists unless
P = NP; the problem is in NP (`min_le_np_certificate`).

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
invertible, provable hardness where they are not.

**Loops versus merges, as a theorem pair** (`obstruction_loop_vs_merge`). Invertible: every tree
has a section and trivial holonomy, so every obstruction is a loop. Lossy: the C22 tree (two
constant maps, `false` and `true`, into one vertex) has no section although each of its two edges
alone has one, and its minimum coordination is 1: two directed paths merge with images that
disagree, and no loop is involved.

**Signed certificates for E** (`SignedResolver.v`, reading B). With an explicit resolver semantics
(one value set with a least and a greatest element and finite height, per-vertex resolvers, fair
asynchronous schedules) and a signed **global** interaction graph that certifies the resolvers
(monotone in positive and antitone in negative inputs, signs fixed across all states), balance
makes every resolver monotone after reversing the order at the switched vertices
(`switched_monotone`). Then E of the canonical-execution framework (Settlement and
CanonicalFidelity, canonicalizer the switched least fixed point) holds from every start at or below
that point (`signed_settlement`), and from every start when there is at most one fixed point
(`signed_fidelity`). These are sufficient certificates, not an exact characterization; each
hypothesis is shown needed by a counterexample (`neg2_no_fixed_point`, `copyback_ghost`,
`ring_low_start_E`, `unbalanced_unique_oscillates`, `flip_needs_top_resolver`,
`xor_no_certificate`, `cyc3_unsignable`). On a balanced graph Thomas's sign condition for
uniqueness (no positive directed cycle) leaves no directed cycle at all
(`balanced_no_positive_acyclic`), so uniqueness is a hypothesis rather than a sign condition.

**Local interaction graphs** (`LocalSigned.v`, Boolean value set, every `n`). The local graph
`G(x)` is the discrete Jacobian at a state `x`: an arc `j -> i` when flipping `x_j` changes the
resolver of `i`, signed by the direction of the change. Local fidelity: no positive cycle in any
`G(x)` gives at most one fixed point (`rrt_sub`, `local_fidelity`; Remy, Ruet and Thieffry 2008)
and CanonicalFidelity from every start, with no global sign hypothesis (`local_fidelity_canon`).
This strictly extends the global route: the global condition implies the local one
(`global_to_local`), and a 3-vertex network with no cycle in any `G(x)` has a positive 2-cycle in
every global certificate (`local_weaker_than_global`). Local settlement: no negative cycle in any
`G(x)` does not give a fixed point (`local_neg_free_no_fixed_point`, 6 vertices, the least
possible by Tonello, Farcot and Chaouiya), but together with non-expansiveness or with one vertex
on every local positive cycle it gives, from every state, an update word reaching a fixed point
(`richard_t3`, `richard_t4`; Richard 2011, Theorems 3 and 4), and no cycle in any `G(x)` gives a
unique fixed point reachable from every state, hence all of E (`shih_dong_E`; Shih and Dong 2005).
The Settlement certified is E's existential (flush) form. Fair-schedule settlement does not
follow from any of these local conditions: a 4-vertex network with no local cycle has a fair
schedule of period 8 that never settles (`shih_dong_not_fair`), while Robert's theorem gives fair
convergence when the global graph is acyclic (mechanized: `rb_robert_boolean`,
`coq/RobertFair.v`). Under no local cycle plus out-degree at most one (`LocalFairSettlement.v`),
every synchronous orbit reaches the unique fixed point (`sync_simple`, the conclusion of Shih and
Ho 1999, Theorem 3.1; `sync_orbit_fixed` needs the local acyclicity only on the orbit), and every
fair schedule from a start with at most two unstable vertices settles there
(`one_token_fair_settlement`; `two_token_fair_settlement` in `LocalTwoToken.v`). What stays open
(REGIME-AUDIT gap 3): fair settlement from local conditions from every start (under those two
conditions, runs with three or more unstable vertices at every state), multivalued local graphs, value sets without bounds, and an exact
condition. The research note on lossy networks,
[LOSSY-NETWORKS.md](LOSSY-NETWORKS.md), develops this side: the constraint and resolver
readings, root sets, and signed-cycle (Thomas-type) conditions.

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
| **Convergence** | Repair: a retraction onto the canonical states. Events: the `E*` action factors through the trace monoid | Repair: `cc_exact_from`, `jc_exact` (one registry), `cat_thm_one_sound` and `cat_thm_one_fixed` (acyclic), `chaotic_reaches_lfp` (monotone cycles), `prop_minimal_qualified_iff` (invertible cycles with a root), `net_unique_normal_form_iff` (rootless invertible networks: an authority root per component, or a trivial group); rootless lossy resolver networks, sufficient only: signed certificates for E on the global interaction graph (`signed_settlement`, `signed_fidelity`), and on Boolean local interaction graphs (`local_fidelity_canon`, `richard_t3`, `richard_t4`, `shih_dong_E`), whose Settlement is existential, not fair-schedule (`shih_dong_not_fair`). Events, separately: `fed_exact_full` (acyclic), `cyc_events_converge_iff` (monotone cycles); not implied by repair (`audit_counterexample`, `cyc_counterexample`) |
| **Obstruction** | What blocks a section | Invertible: holonomy, the class in `H^1` (`cycle_basis_criterion`, `H1_classification`; on the 2-complex, `nerve_H1_classification`, `nerve_H1_Z2_count`), equivalently a closed walk with non-trivial holonomy on any edge list (`invertible_merge_is_holonomy`); at Z/2, Harary balance (`harary_balance`). Lossy: a loop composite with no reachable fixed point (`thm_obstruction_reachable`, `diagnose_dichotomy`), and also a merge with no loop at all (`obstruction_loop_vs_merge`) |
| **Surgery** | The least coordination that removes the obstruction | Invertible: the group feedback edge set number, which the best coordination plan attains (`plan_min_exact`); NP-hard by a mechanized Max-Cut reduction (`maxcut_reduction`). Lossy: the least deletion passing the root-set criterion (`lmin_root_set`, `lmin_decide`), not cycle-based (`lossy_min_exceeds_cycle_bounds`); NP-hard even to tell 0 from 1 (`lmin_reduction`) |

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
retractions, sheaves, graph cohomology and gain-graph balance (Harary's theorem is proved here at
Z/2, `harary_balance`), Mazurkiewicz traces, and the
complexity of group feedback edge sets and of 3-SAT. The contribution is the combination: the
exact boundaries between the areas, the non-abelian and lossy results, and the mechanization. See
[LANDSCAPE.md](LANDSCAPE.md) for the placement against prior work.
