# Theory overview

The theory in one page: the regime it adds, what is new and what is not, the key concepts, and how
the three convergence regimes nest. "What's new here" marks each item mechanized, paper or
implemented. For the
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
