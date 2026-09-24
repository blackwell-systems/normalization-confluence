# Normalization Confluence

[![Blackwell Systems™](https://raw.githubusercontent.com/blackwell-systems/blackwell-docs-theme/main/badge-trademark.svg)](https://github.com/blackwell-systems)

Research on coordination-free convergence in distributed systems through normalization confluence - a third structural regime alongside operation commutativity (CRDTs) and invariant confluence.

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
- [SUBSUMPTION.md](SUBSUMPTION.md): the machine-checked proof that CRDTs are exactly the compensation-free fragment of normalization confluence, and that the inclusion is strict.
- [REGIMES.md](REGIMES.md): a decision table and flowchart for when a given (possibly federated, possibly cyclic) governed network converges.
- [coq/](coq): the machine-checked, axiom-free proof (CI-gated; reproduce it in one command). It is also the source of verified differential oracles for gsm: a checker over emitted step tables and a checker over the rules themselves, the latter also certifying the compensation-free (CRDT-fragment) classification. See [coq/extraction/](coq/extraction).

---

## Publications

### Normalization Confluence in Federated Registry Networks

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18677400.svg)](https://doi.org/10.5281/zenodo.18677400)

**Extended version with federated systems**

Extends normalization confluence to multi-organizational environments where registries are connected by morphisms encoding cross-organizational semantic constraints. For tree-shaped morphism networks (directed forests), proves federated convergence requires only validity preservation of the morphisms - all other conditions derive from network acyclicity via an authority argument: the source's unique normal form deterministically fixes the target's shared component. The tree restriction is then lifted to any acyclic network: multi-source targets carry a validity-preserving, source-determined resolution operator generalizing the authority function.

Includes self-contained treatment of single-registry model (governance rewrite system, convergence theorem via Newman's Lemma, necessity results, complexity analysis, and verification calculus).

**Files:**
- `normalization_confluence_in_federated_registry_networks.pdf` - Full paper (1939 lines)
- `normalization_confluence_in_federated_registry_networks.tex` - LaTeX source

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
- `normalization_confluence_2026.pdf` - Core paper (1581 lines)
- `normalization_confluence_2026.tex` - LaTeX source

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
| **Non-monotone** | May reverse the order (toggles, negation, cancellations); validity-preserving | **Acyclic only**; multi-source targets need resolution operators | Deterministic one-shot normal form; feedback loops structurally excluded |

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
- Differential testing against two verified oracles extracted from [coq/](coq): one re-certifies the emitted step tables, the other recomputes convergence straight from the rules, so a bug in gsm's own verification cannot pass a non-convergent machine

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

These regimes are **nested, not merely adjacent**. CRDTs are the *compensation-free* corner: operations designed so repair is never needed. Drop that restriction, keep the convergence guarantee, and you have normalization confluence, so every CRDT is a governed machine whose max repair depth is zero, and the inclusion is **strict** (governed machines exist that no CRDT can express). This is not informal: it is machine-checked, axiom-free, in [`coq/CRDT.v`](coq/CRDT.v) (`cmrdt_SEC`, `cvrdt_SEC`, and the witnesses `witness_not_cmrdt` / `witness_leaves_valid_space`), and stated in full in [SUBSUMPTION.md](SUBSUMPTION.md). So "a third regime alongside CRDTs" is the entry framing; the sharper claim the proofs support is that normalization confluence is the general regime and CRDTs are its degenerate, compensation-free fragment.

---

## License

All papers: CC-BY-4.0

All code (tools): MIT License
