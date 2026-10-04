# CRDTs are the compensation-free fragment of normalization confluence

This note states, and points at the machine-checked proof of, the relationship between
conflict-free replicated data types (CRDTs) and normalization confluence. The claim is precise and
scoped:

> As a convergence mechanism, every CRDT is a governed state machine whose operations were designed
> so that compensation is never needed. Under causal delivery the compensation-free fragment of
> normalization confluence is EXACTLY the op-based CRDTs, state-based CRDTs embed as the
> semilattice case, and the inclusion is strict.

Everything below is mechanized axiom-free and gated by `coq/verify.sh`: the all-pairs results in
`coq/CRDT.v`, and the causal results (standard op-based CRDTs, exactness, the bridge to trace
equivalence, and the rewrite-system theorem) in `coq/CausalReplay.v` and `coq/GovernanceCausal.v`.

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
at-least-once delivery; normalization confluence does not require it in general. Where duplicates
can occur, `coq/AtLeastOnce.v` gives the governed counterpart: duplicates of an event whose governed
step is idempotent are absorbed (`alo_commuting_converges`, and `causal_alo_converges` under causal
delivery), and a duplicated non-idempotent event diverges (`non_idempotent_diverges`). The join order is
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

## Causal delivery and exactness (`CausalReplay.v`, `GovernanceCausal.v`)

The results above use the strong op-based definition: every pair of operations commutes, in every
order. The literature's op-based CRDTs only require *concurrent* operations to commute, because
delivery is causal: an operation is applied after the operations it depends on. Read against that
definition, the all-pairs results would cover only part of the class. The causal results close the
gap.

- `causal_convergence`: if governed steps commute for every **concurrent** pair, any two causally
  consistent delivery orders of the same events reach the same state. Causally ordered pairs never
  need to commute.
- `causal_cmrdt_SEC`: standard op-based CRDTs (concurrent operations commute, causal delivery)
  converge, as an instance.
- `compensation_free_exact`: for a compensation-free system (normalization is the identity), the
  causal convergence condition holds **if and only if** the system is an op-based CRDT. With the
  embedding, the compensation-free fragment is exactly the op-based CRDTs.
- `witness_causal_not_cmrdt`: strictness under causal delivery. A governed system that converges
  but is not an op-based CRDT.
- `witness_beyond_all_pairs`: new reach. A system whose operations do not all commute (an add, a
  causally later remove, and an independent counter), which the all-pairs results cannot cover, but
  which converges under causal delivery.
- `causal_tequiv`: any two causally consistent orders are trace-equivalent under concurrency. This
  connects causal delivery to `Trace.v`'s `run_tequiv`, the theorem behind gsm's declared
  `Independent` pairs.
- `causal_governance_confluent` (`GovernanceCausal.v`): the full rewrite-system Convergence
  Theorem, with compensation interleaving, holds with CC1 required only for distinct events that
  are enabled together. Under causal delivery, causally ordered events are never enabled together.
  The witness `cw_confluent` / `cw_violates_all_pairs_cc1` satisfies the weakened hypothesis while
  violating the original one.

All of these use the bubbling argument (an event is moved to the front past concurrent events), so
the connectivity of linear extensions is never assumed.

The causal condition is also exact. `causal_exact` (`GovernanceConverse.v`): causal convergence
from `s0` holds iff every concurrent pair commutes after every causally consistent prefix that can
deliver it, and `causal_convergence_exact` (with happens-before irreflexive) is the converse of
`causal_convergence` over all starts. Reachability of the state alone is not enough
(`naive_causal_converse_fails`).

## What this claim does not say

The result is about the convergence principle, not about CRDT engineering as a whole. CRDTs also
address concerns this theorem does not subsume:

- duplicate delivery via idempotence (captured for the CvRDT case as
  `cvrdt_absorbs_duplicates`, and for governed machines by `AtLeastOnce.v` when the duplicated
  governed steps are idempotent; not assumed in general),
- the metadata that enforces causal delivery (version vectors, dotted contexts). The convergence
  principle *under* causal delivery is covered (`CausalReplay.v`); how a system achieves causal
  delivery is not,
- garbage collection of tombstones and history.

The defensible statement is the one at the top: as a way to *guarantee convergence*, a CRDT is a
governed machine whose operations were built so compensation is never needed, and there are
convergent governed machines that are no CRDT. "CRDTs are obsolete" is neither claimed nor needed.

## Where the proof lives

- `coq/CRDT.v`: the four results above, axiom-free.
- `coq/Checker.v`: `run_perm_invariant`, the order-independence lemma every part reuses.
- `coq/CausalReplay.v`: causal convergence, standard op-based CRDTs, exactness, the causal
  witnesses, and the bridge to trace equivalence.
- `coq/GovernanceCausal.v`: the rewrite-system Convergence Theorem under causal delivery.
- `coq/GovernanceConverse.v`: the converse (exactness) of causal convergence.
- `coq/AtLeastOnce.v`: duplicate delivery for governed machines.
- `coq/verify.sh`: gates on all of the above being `Closed under the global context`.
