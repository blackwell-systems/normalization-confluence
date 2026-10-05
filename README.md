# Normalization Confluence

[![Blackwell Systems™](https://raw.githubusercontent.com/blackwell-systems/blackwell-docs-theme/main/badge-trademark.svg)](https://github.com/blackwell-systems)

Research on coordination-free convergence in distributed systems through normalization confluence - a third structural regime alongside operation commutativity (CRDTs) and invariant confluence.

**An exact regime map of governed concurrent state: in every regime, a machine-checked exact condition, a hardness result showing no efficient one exists, or a gap stated in the open, with a checker for the practical ones.**

The idea is **convergence by compensation**: operations may conflict and break invariants, and
replicas still converge because repair is well-founded and commutes with events. CRDTs are the
special case with no compensation, and under causal delivery they are exactly that fragment.

For networks of registries the map separates two properties. **Repair confluence**, a unique
federated normal form, composes freely on acyclic networks and on monotone cycles. **Event
confluence**, the same result for every event order, costs two local checks per edge (C1 and C2),
which are exact at reachable states and also suffice on monotone cycles. Non-monotone cycles
converge under a computed coordination, to a normal form that is unique given the authority root.

Scope: discrete, deterministic governed state (continuous state is out of scope; see
[LYAPUNOV-EXTENSION.md](docs/LYAPUNOV-EXTENSION.md)). The exact conditions (JC for a single registry,
CCR under causal delivery, GC for event interleavings in a federation) quantify over reachable
states, so checking them means exploring the reachable state space. The cheap sufficient
conditions (CC for a registry, C1 and C2 for a federation, acyclic or monotone-cyclic) imply them,
and they are what [gsm](https://github.com/blackwell-systems/gsm) checks (its single-registry check
is re-certified by an oracle extracted from the proof; the federation-level checks are not yet, see
[ROADMAP.md](docs/ROADMAP.md) item 5). These conditions, and the implications between them, are
mechanized axiom-free in [`coq/`](coq) (1370 theorems at the time of writing; `coq/verify.sh` is
the source of truth).

"Machine-checked" in the line above applies to the exact conditions. Of the hardness results,
deciding consistency of a lossy network without a spanning root is NP-complete: the 3-SAT
reduction is machine-checked (correct in both directions, parsimonious, linear in size, with a
checkable certificate; `coq/LossyHardness.v`), and NP-completeness follows from it by the standard
argument. NP-hardness of minimum coordination is cited from the literature. The gaps still open are
the distributed propagation model on monotone cycles without reset epochs, where the exact
condition is mechanized under `LowR` and otherwise only relative to two reachable hypotheses
(`FlushR`, `NoGhostR`; the acyclic model and cycles with reset epochs are exact), rootless
networks beyond a single invertible cycle, rootless propagation on lossy networks, and cyclic
monotone collapse (paper only); least fixed points without ACC are a design exclusion, and minimum
coordination, the `H^1` rank on the 2-complex and sheaf gluing are open optimization and structure
questions.
[REGIME-AUDIT.md](REGIME-AUDIT.md) gives each regime's status with its Coq theorem.

**Dayna Blackwell** | dayna@blackwell-systems.com

---

## Start here

**Practitioners: does my system converge?** Start with the field guide,
[docs/REGIMES.md](docs/REGIMES.md): find your situation (one registry, causal or at-least-once
delivery, a network of registries, cycles, a distributed deployment) and read off whether it
converges and which theorem says so. [gsm](https://github.com/blackwell-systems/gsm) checks the
cheap sufficient conditions at build time (see [Companion Tools](#companion-tools)).

**Researchers: what is new, and against what?** The [papers](#publications), then
[docs/THEORY.md](docs/THEORY.md) (the theory overview: the third regime, what is new and what is
not, each item marked mechanized, paper or implemented, and the key concepts),
[docs/LANDSCAPE.md](docs/LANDSCAPE.md) (placement against prior work),
[docs/SUBSUMPTION.md](docs/SUBSUMPTION.md) (CRDTs as the compensation-free fragment) and
[docs/CATEGORICAL-STRUCTURE.md](docs/CATEGORICAL-STRUCTURE.md) (working notes for the companion
paper).

**Proof readers: what exactly is machine-checked?** [coq/](coq): the machine-checked, axiom-free
proof (CI-gated; reproduce it in one command). It is also the source of the verified checkers gsm
runs as an in-process, fail-closed gate: a checker over emitted step tables and a checker over the
rules themselves, the latter also certifying the compensation-free (CRDT-fragment) classification.
See [coq/extraction/](coq/extraction). Start at [coq/README.md](coq/README.md), the module index
grouped by regime with each module's headline theorems and a page of full results per regime;
`cd coq && bash verify.sh` reproduces the axiom-free gate that CI runs.

**Auditors: is the headline accurate?** [REGIME-AUDIT.md](REGIME-AUDIT.md) checks it regime by
regime: for each question, the exact condition with its Coq theorem, the hardness result, or the
open gap, and what gsm checks. [docs/ROADMAP.md](docs/ROADMAP.md) says what is next, and
[CHANGELOG.md](CHANGELOG.md) records each change.

Every page, with its role in one line: [docs/README.md](docs/README.md).

---

## Publications

### The Categorical Structure of Federated Convergence: Limits, Sheaves, and Minimal Coordination

**Companion paper: the structure under the federated regimes**

Answers when a federation must coordinate at all, and how little coordination suffices. A federation's convergent states are a limit and its federated normalizer is the retraction onto that limit, so compositionality is a corollary of one structural fact. Convergence certificates form a sheaf whose gluing condition is exactly the source-determinacy and validity-preservation hypotheses (R1/R2) the federation already certifies, so the obstruction to a global convergent state is cohomological: `H^0` is the convergent states and `H^1` is the holonomy of the morphism cycles. The two federated regimes become one picture: an acyclic network has no cycles and `H^1` vanishes, while a monotone cycle collapses the obstruction to a least fixed point. The obstruction is computable as a loop composite over the shared subspace, implemented in gsm as a cycle diagnostic. When the obstruction is nonzero, coordinating a cycle basis suffices to converge, localizing the global verdict of CALM and invariant confluence into a mixed-consistency partition; the exact minimum is the group feedback edge set number of the labeled nerve (NP-hard even in the abelian case, fixed-parameter tractable in the coordinated core's size, polynomial on planar or edge-disjoint nerves). The structural core (limit, retraction, compositionality, order-independence) and the cohomological layer (the completion on arbitrary graphs, the cycle-basis criterion, `H^1` as a quotient with its rank, and the `S_3` separation) are mechanized axiom-free in Coq/Rocq. Working notes: [CATEGORICAL-STRUCTURE.md](docs/CATEGORICAL-STRUCTURE.md).

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

## License

All papers: CC-BY-4.0

All code (tools): MIT License
