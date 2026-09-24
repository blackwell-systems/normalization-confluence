# CRDTs are the compensation-free fragment of normalization confluence

This note states, and points at the machine-checked proof of, the relationship between
conflict-free replicated data types (CRDTs) and normalization confluence. The claim is precise and
scoped:

> As a convergence mechanism, every CRDT is a governed state machine whose operations were designed
> so that compensation is never needed. Normalization confluence keeps the convergence guarantee
> after dropping that restriction, and the inclusion is strict.

Everything below is mechanized in `coq/CRDT.v`, axiom-free, and gated by `coq/verify.sh`.

## Background in one paragraph

A CRDT achieves convergence by staying inside a structure that cannot conflict. Op-based CRDTs
(CmRDT) require that concurrent operations commute. State-based CRDTs (CvRDT) require that states
form a join-semilattice and that replicas merge by least upper bound. In both cases an operation
can never produce a state that violates an invariant, because there is no invariant to violate:
the design burden is to encode every intent as a commuting operation or a monotone join.
Normalization confluence removes that burden. Events may violate a declared invariant, and a
compensation repairs the violation; convergence is recovered from two properties (well-founded
compensation and compensation commutativity) via Newman's lemma.

## The four results

### 1. Op-based CRDT: strong eventual consistency is a corollary (`cmrdt_SEC`)

Model a CmRDT as a state type `S`, operations `Op`, and `apply : Op -> S -> S`, with the defining
hypothesis that operations commute. Strong eventual consistency, that replicas which delivered the
same set of operations in any order reach the same state, is exactly `run_perm_invariant` from
`coq/Checker.v`: commuting steps applied over any permutation of the same list give the same
result. The CmRDT's central guarantee is therefore a one-line instance of a theorem the governance
development already proved.

### 2. The embedding is faithful (`cmrdt_governed_SEC`)

Placing a CmRDT inside a governed machine is not a metaphor. Take the trivial invariant (every
state is valid) and the identity compensation. Then well-founded compensation is trivial
(normalization is the identity, terminating in zero steps), the governed step (apply, then
compensate) equals the raw operation, and compensation commutativity reduces to the operations
commuting. Convergence follows from the same order-independence lemma. So a CmRDT is literally the
`invariant = true`, `compensation = identity` corner of the governed model.

### 3. State-based CRDT: the semilattice special case (`cvrdt_SEC`, `cvrdt_absorbs_duplicates`)

Model a CvRDT by a join that is commutative, associative, and idempotent. Merging received states
is then order-independent (again the same lemma) and absorbs duplicate delivery (merging the same
state twice equals once). Idempotence is the one extra property a CvRDT bundles in, to tolerate
at-least-once delivery; normalization confluence does not require it in general. The join order is
a semilattice and merge is monotone in it, which is the monotone regime already mechanized for
federated networks in `coq/Federation.v` and `coq/Chaotic.v`.

### 4. The inclusion is strict (`witness_converges`, `witness_not_cmrdt`, `witness_leaves_valid_space`)

Embedding alone would only show CRDTs are *at most* as expressive. The witness in `CRDT.v` shows
the containment is proper: a concrete governed machine that converges yet is neither CRDT. Its
state is a single boolean where only `false` is valid; its events are `settrue` and `flip`; its
compensation resets to `false`. Three facts are proven:

- `witness_converges`: the governed steps commute, so every ordering of the same events agrees.
- `witness_not_cmrdt`: the raw operations do not commute, so they cannot be the concurrent
  operations of an op-based CRDT.
- `witness_leaves_valid_space`: an event maps a valid state to an invalid one, whereas a
  state-based CRDT's operations keep the state inside the semilattice and never produce a state
  that needs repair.

The machine converges only because compensation repairs the violation. No CRDT can represent it.

## What this claim does not say

The result is about the convergence principle, not about CRDT engineering as a whole. CRDTs also
address concerns this theorem does not subsume:

- duplicate delivery via idempotence (captured for the CvRDT case as
  `cvrdt_absorbs_duplicates`, not assumed in general),
- causal delivery and the metadata that enforces it (version vectors, dotted contexts),
- garbage collection of tombstones and history.

The defensible statement is the one at the top: as a way to *guarantee convergence*, a CRDT is a
governed machine whose operations were built so compensation is never needed, and there are
convergent governed machines that are no CRDT. "CRDTs are obsolete" is neither claimed nor needed.

## Where the proof lives

- `coq/CRDT.v`: the four results above, axiom-free.
- `coq/Checker.v`: `run_perm_invariant`, the order-independence lemma every part reuses.
- `coq/verify.sh`: gates on `cmrdt_SEC`, `cmrdt_governed_SEC`, `cvrdt_SEC`, `witness_converges`,
  `witness_not_cmrdt`, and `witness_leaves_valid_space` being `Closed under the global context`.
