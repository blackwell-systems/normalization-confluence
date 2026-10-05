# Normalization Confluence

[![Blackwell Systems™](https://raw.githubusercontent.com/blackwell-systems/blackwell-docs-theme/main/badge-trademark.svg)](https://github.com/blackwell-systems)

Research on coordination-free convergence in distributed systems through normalization confluence - a third structural regime alongside operation commutativity (CRDTs) and invariant confluence.

**A complete, mechanized map of when governed concurrent state converges, with exact conditions in every regime and a checker for the practical ones.**

The idea is **convergence by compensation**: operations may conflict and break invariants, and
replicas still converge because repair is well-founded and commutes with events. CRDTs are the
special case with no compensation, and under causal delivery they are exactly that fragment.

For networks of registries the map separates two properties. **Repair confluence**, a unique
federated normal form, composes freely on acyclic networks and on monotone cycles. **Event
confluence**, the same result for every event order, costs two local checks per edge (C1 and C2),
which are exact at reachable states and also suffice on monotone cycles. Non-monotone cycles
converge under a computed coordination, to a normal form that is unique given the authority root.

Scope: discrete, deterministic governed state (continuous state is out of scope; see
[LYAPUNOV-EXTENSION.md](LYAPUNOV-EXTENSION.md)). The exact conditions (JC for a single registry,
CCR under causal delivery, GC for event interleavings in a federation) quantify over reachable
states, so checking them means exploring the reachable state space. The cheap sufficient
conditions (CC for a registry, C1 and C2 for a federation, acyclic or monotone-cyclic) imply them,
and they are what [gsm](https://github.com/blackwell-systems/gsm) checks (its single-registry check
is re-certified by an oracle extracted from the proof; the federation-level checks are not yet, see
[ROADMAP.md](ROADMAP.md) item 5). These conditions, and the implications between them, are
mechanized axiom-free in [`coq/`](coq) (729 theorems at the time of writing; `coq/verify.sh` is
the source of truth).

**Dayna Blackwell** | dayna@blackwell-systems.com

---

## Overview

Traditional approaches to coordination-free convergence require either:
1. **Operation commutativity** (CRDTs) - operations must be designed to commute
2. **Invariant confluence** - operations must preserve invariants in all orderings

This research identifies a third regime: **normalization confluence**, where operations may be non-commutative and may violate invariants, yet systems converge through compensation. Convergence is a property of the normalization rewrite system (event application + invariant repair), not the operations themselves.

This repository contains theoretical foundations, proofs, and companion verification tools.

New here? A few pointers orient you:
- [LANDSCAPE.md](LANDSCAPE.md): where this sits relative to CRDTs, consensus, invariant confluence, and the saga pattern, and what it changes.
- [SUBSUMPTION.md](SUBSUMPTION.md): the machine-checked proof that, under causal delivery, op-based CRDTs are exactly the compensation-free fragment of normalization confluence, that state-based CRDTs embed as the semilattice case, and that the inclusion is strict.
- [REGIMES.md](REGIMES.md): a decision table and flowchart for when a given (possibly federated, possibly cyclic) governed network converges.
- [ROADMAP.md](ROADMAP.md): the caveats removed so far (finite state, exactly-once delivery, sufficiency-only conditions, non-monotone cycles), the qualifiers found, what remains open, and which caveats are fundamental limits.
- [LYAPUNOV-EXTENSION.md](LYAPUNOV-EXTENSION.md): a forward-looking research note (nothing proven) mapping the discrete conditions to a continuous state space, WFC as a Lyapunov function and CC as contraction, with the convex-gradient sweet spot where the collapse survives and the multi-basin boundary where it provably does not.
- [LOSSY-NETWORKS.md](LOSSY-NETWORKS.md): a forward-looking research note on lossy (non-invertible) networks without a spanning root: the constraint and resolver readings, NP-completeness and root sets in the first, Thomas's signed-cycle rules in the second.
- [coq/](coq): the machine-checked, axiom-free proof (CI-gated; reproduce it in one command). It is also the source of the verified checkers gsm runs as an in-process, fail-closed gate: a checker over emitted step tables and a checker over the rules themselves, the latter also certifying the compensation-free (CRDT-fragment) classification. See [coq/extraction/](coq/extraction).

---

## What's new here

Each item is marked **[mechanized]** (axiom-free in [`coq/`](coq)), **[paper]** (proved in the
papers, not mechanized), or **[implemented]** (in [gsm](https://github.com/blackwell-systems/gsm)).
[CATEGORICAL-STRUCTURE.md](CATEGORICAL-STRUCTURE.md) and [coq/README.md](coq/README.md) give the
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
   CRDTs embed as its compensation-free case, and the inclusion is strict. Under causal delivery,
   where only concurrent events must commute, convergence still holds and the compensation-free
   fragment is exactly the op-based CRDTs.
   - [mechanized] Newman's lemma and the convergence theorem, with a non-vacuity instance
     (`Newman.v`, `Governance.v`, `Defensibility.v`); the calculus's footprint-disjointness path
     (`Gsm.v`); the strict CRDT embedding (`CRDT.v`); convergence under causal delivery, standard
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
   from the proof, with optimized variants proved to give the same verdicts.
   - [mechanized] The checkers' soundness and the equality of the optimized variants
     (`TableFast.v`, `TableFn.v`, `AstTables.v`, `AstCompact.v`).
   - [implemented] The in-process gate in gsm.

**What isn't new.** Convergence by confluence (Newman, Meseguer), repair to a legitimate state
(Dijkstra), Knaster-Tarski and chaotic iteration, `H^1` theory and balance (Hatcher, Harary,
Zaslavsky), and group-feedback-edge-set complexity. These are the tools; the conditions and
theorems built with them are new. See [LANDSCAPE.md](LANDSCAPE.md) for the placement against prior
work.

---

## Publications

### The Categorical Structure of Federated Convergence: Limits, Sheaves, and Minimal Coordination

**Companion paper: the structure under the federated regimes**

Answers when a federation must coordinate at all, and how little coordination suffices. A federation's convergent states are a limit and its federated normalizer is the retraction onto that limit, so compositionality is a corollary of one structural fact. Convergence certificates form a sheaf whose gluing condition is exactly the source-determinacy and validity-preservation hypotheses (R1/R2) the federation already certifies, so the obstruction to a global convergent state is cohomological: `H^0` is the convergent states and `H^1` is the holonomy of the morphism cycles. The two federated regimes become one picture: an acyclic network has no cycles and `H^1` vanishes, while a monotone cycle collapses the obstruction to a least fixed point. The obstruction is computable as a loop composite over the shared subspace, implemented in gsm as a cycle diagnostic. When the obstruction is nonzero, coordinating a cycle basis suffices to converge, localizing the global verdict of CALM and invariant confluence into a mixed-consistency partition; the exact minimum is the group feedback edge set number of the labeled nerve (NP-hard even in the abelian case, fixed-parameter tractable in the coordinated core's size, polynomial on planar or edge-disjoint nerves). The structural core (limit, retraction, compositionality, order-independence) and the cohomological layer (the completion on arbitrary graphs, the cycle-basis criterion, `H^1` as a quotient with its rank, and the `S_3` separation) are mechanized axiom-free in Coq/Rocq. Working notes: [CATEGORICAL-STRUCTURE.md](CATEGORICAL-STRUCTURE.md).

**Files:**
- `categorical_structure_of_federated_convergence.pdf` - Full paper
- `categorical_structure_of_federated_convergence.tex` - LaTeX source (829 lines)

### Normalization Confluence in Federated Registry Networks

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18677400.svg)](https://doi.org/10.5281/zenodo.18677400)

**Extended version with federated systems**

Extends normalization confluence to multi-organizational environments where registries are connected by morphisms encoding cross-organizational semantic constraints. For tree-shaped morphism networks (directed forests), proves federated convergence requires only validity preservation of the morphisms - all other conditions derive from network acyclicity via an authority argument: the source's unique normal form deterministically fixes the target's shared component. The tree restriction is then lifted to any acyclic network: multi-source targets carry a validity-preserving, source-determined resolution operator generalizing the authority function.

Shows both conditions are necessary: acyclicity and validity preservation under shared-component overwrite (M1), each by counterexample. Removes the acyclicity requirement for monotone repair: when shared domains are lattices and repair is monotone, convergence holds on any network, including cycles (Knaster-Tarski, with order-independence as chaotic iteration). Proves compositional collapse: a convex, internally convergent sub-federation collapses to a single effective registry, so the outer network converges iff the collapsed one does. The single-registry base theorem, order-independence on acyclic networks, the monotone least fixed point, and chaotic-iteration convergence are mechanized axiom-free in [`coq/`](coq), together with event interleavings across registries and the coordinated non-monotone cycle.

Includes self-contained treatment of single-registry model (governance rewrite system, convergence theorem via Newman's Lemma, necessity results, complexity analysis, and verification calculus).

**Files:**
- `normalization_confluence_in_federated_registry_networks.pdf` - Full paper
- `normalization_confluence_in_federated_registry_networks.tex` - LaTeX source (2513 lines)

**Citation:**
```bibtex
@techreport{blackwell2026federated,
  title   = {Normalization Confluence in Federated Registry Networks},
  author  = {Blackwell, Dayna},
  year    = {2026},
  doi     = {10.5281/zenodo.18677400},
  note    = {Technical Report},
  license = {CC-BY-4.0}
}
```

### Normalization Confluence for Registry-Governed Stream Processing

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18671870.svg)](https://doi.org/10.5281/zenodo.18671870)

**Core single-registry foundation**

Identifies normalization confluence as a third regime for coordination-free convergence in distributed systems. Formalizes registry-governed stream processing, proves termination and confluence under well-founded compensation (WFC) and compensation commutativity (CC), and develops a verification calculus for practical CC checking. Shows uniformly bounded compensation (UBC) yields constant per-event overhead matching conventional stream processing.

**Files:**
- `normalization_confluence_2026.pdf` - Core paper
- `normalization_confluence_2026.tex` - LaTeX source (1758 lines)

**Citation:**
```bibtex
@techreport{blackwell2026normalization,
  title   = {Normalization Confluence for Registry-Governed Stream Processing},
  author  = {Blackwell, Dayna},
  year    = {2026},
  doi     = {10.5281/zenodo.18671870},
  note    = {Technical Report},
  license = {CC-BY-4.0}
}
```

---

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

Finally, when shared domains are ordered (lattices) and repair is **monotone**, acyclicity is unnecessary: the repair operator has a least fixed point (Knaster-Tarski) reached order-independently by chaotic iteration, so convergence holds on **any cyclic graph**. Both halves of this (least-fixed-point existence and asynchronous order-independent convergence) are machine-checked in [`coq/`](coq). This reveals two independent routes to federated confluence:

| Regime | Repair requirement | Permissible topologies | Convergence guarantee |
|---|---|---|---|
| **Monotone** | Monotone on a lattice order (join *or* meet); validity-preserving | **Any** — cyclic meshes, DAGs, trees | Least fixed point `lfp(⊥)` under any *fair* asynchronous order |
| **Non-monotone** | May reverse the order (toggles, negation, cancellations); validity-preserving | **Acyclic** coordination-free; multi-source targets need resolution operators. Cycles only with a computed coordination | Deterministic one-shot normal form; on a coordinated cycle, unique given the authority root (`CoordinatedCycles.v`) |

Monotonicity and acyclicity are orthogonal — either alone suffices. Validity preservation is required in both. State-based CRDTs are the compensation-free special case of the monotone regime.

---

## Companion Tools

### gsm - Governed State Machines

[![Go Reference](https://pkg.go.dev/badge/github.com/blackwell-systems/gsm.svg)](https://pkg.go.dev/github.com/blackwell-systems/gsm)

**Go library for building verified convergent state machines**

- Build-time WFC/CC verification via exhaustive state-space enumeration
- O(1) runtime event application through precomputed lookup tables
- Fluent builder API for defining state machines in Go code
- Portable JSON export for multi-language runtime support
- An in-process, fail-closed gate: no machine is returned unless the proof-generated checker certifies it (on `Build`, `SynthesizeWith`, and `BuildCompositional` per footprint component). The table oracle, generated as Go from the axiom-free extraction in [coq/](coq), runs on every success path; a second extracted oracle recomputes convergence straight from the rules. A bug in gsm's own verification cannot hand back a non-convergent machine

```go
machine, report, err := builder.Build()
// Convergence: GUARANTEED (verified exhaustively)

s = machine.Apply(s, "ship_item") // O(1) table lookup
```

Repository: [github.com/blackwell-systems/gsm](https://github.com/blackwell-systems/gsm)

### nccheck - Normalization Confluence Verifier

**YAML-based verification tool for finite-state registry specifications**

Reference implementation proving the verification procedure from the paper is mechanizable. Exhaustively checks WFC and CC for registry specs, provides counterexamples when convergence fails.

```bash
nccheck examples/disjoint.yaml      # PASS - independent subsystems
nccheck examples/permissions.yaml   # FAIL - cross-variable invariants
```

Repository: [github.com/blackwell-systems/nccheck](https://github.com/blackwell-systems/nccheck)

---

## Three Regimes of Coordination-Free Convergence

| Regime | Requirement | Guarantees | Design Space |
|--------|-------------|------------|--------------|
| **Operation Commutativity** (CRDTs) | Operations commute algebraically | Convergence without coordination | Commutative operations only |
| **Invariant Confluence** | Operations preserve invariants in all orderings | Convergence without repair | Invariant-preserving operations only |
| **Normalization Confluence** | Compensated results commute (operations need not) | Convergence through repair | Non-commutative, invariant-violating operations |

Normalization confluence occupies the gap between CRDTs (requires commutativity) and I-confluence (requires invariant preservation). It permits operations that satisfy neither, provided compensation commutes.

These regimes are **nested, not merely adjacent**. CRDTs are the *compensation-free* corner: operations designed so repair is never needed. Drop that restriction, keep the convergence guarantee, and you have normalization confluence, so every CRDT is a governed machine whose max repair depth is zero, and the inclusion is **strict** (governed machines exist that no CRDT can express). This is not informal: it is machine-checked, axiom-free, in [`coq/CRDT.v`](coq/CRDT.v) (`cmrdt_SEC`, `cvrdt_SEC`, and the witnesses `witness_not_cmrdt` / `witness_leaves_valid_space`), and stated in full in [SUBSUMPTION.md](SUBSUMPTION.md). The relationship also holds under causal delivery, where only concurrent operations must commute: standard op-based CRDTs converge as an instance, and the compensation-free fragment is *exactly* the op-based CRDTs ([`coq/CausalReplay.v`](coq/CausalReplay.v): `causal_cmrdt_SEC`, `compensation_free_exact`), with the full rewrite-system theorem in [`coq/GovernanceCausal.v`](coq/GovernanceCausal.v). So "a third regime alongside CRDTs" is the entry framing; the sharper claim the proofs support is that normalization confluence is the general regime and CRDTs are its compensation-free fragment.

---

## License

All papers: CC-BY-4.0

All code (tools): MIT License
