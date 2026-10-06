# CRDTs are the compensation-free fragment of normalization confluence

This note states, and points at the machine-checked proof of, the relationship between
conflict-free replicated data types (CRDTs) and normalization confluence. The claim is precise and
scoped:

> Normalization confluence strictly generalizes the standard CRDT convergence regimes. Under
> causal exactly-once delivery, its compensation-free fragment is exactly the CmRDT
> commutativity regime (`causal_convergence_exact`). Under unordered at-least-once delivery, its
> compensation-free fragment is exactly commutative-idempotent state evolution on reachable
> states (`merge_action_exact`) and, with a finite event range and decidable state equality,
> exactly the CvRDT semilattice regime on reachable states (`cvrdt_on_iff`). Nontrivial
> normalization strictly extends these compensation-free regimes on the same transition
> representation.

Put shortly: remove compensation and CRDT algebra is exactly the convergence condition that
remains; restore it and the class becomes strictly larger.

The whole statement is one theorem, `crdt_boundary` in `coq/CRDTBoundary.v`, assembled from the
exact theorems of `coq/GovernanceConverse.v` and `coq/CvRDTExact.v` and a sharpened strictness
witness. Everything below is mechanized axiom-free and gated by `coq/verify.sh`.

## Background in one paragraph

CRDTs obtain convergence algebraically. A state-based CRDT (CvRDT) keeps state evolution
monotone in a join-semilattice and merges replicas by least upper bound; an op-based CRDT (CmRDT)
requires delivered effects to commute wherever delivery leaves them concurrent. Normalization
confluence lets raw transitions leave the normal-form region and recovers convergence through a
terminating, locally confluent normalization (well-founded compensation and compensation
commutativity, via Newman's lemma). The distinction is the convergence mechanism, not whether the
application has semantic invariants: CRDT-backed applications may have invariants independently,
and whether those invariants survive coordination-free execution is a separate question (invariant
confluence, Bailis et al., [arXiv:1402.2237](https://arxiv.org/abs/1402.2237)).

## The boundary theorem (`crdt_boundary`)

Setting. An event `e` has a raw transition `act e : S -> S`, a normalization `normalize : S -> S`
repairs the result, and the governed step is `gstep act normalize e s = normalize (act e s)`
(`CausalReplay.gstep`). The system is compensation-free when `normalize s = s` for every `s`.

`crdt_boundary` states, for every `S`, `E`, `act` and `normalize` with `normalize = id`:

- **(a) Causal exactly-once delivery.** For every irreflexive happens-before relation `hb`:
  the governed steps converge causally from every start state (any two causally consistent orders
  of the same events reach the same state) **iff** concurrent raw operations commute at every
  state (`causal_cmrdt act hb`). This is `causal_convergence_exact` instantiated at the governed
  step, composed with `compensation_free_exact` (`cf_causal_boundary`).
- **(b) Unordered at-least-once delivery.** For every event range `X` (with decidable event
  equality) and start `s0`: every two deliveries over `X` with the same set of events, in any
  order and with any duplication, reach the same state from `s0` (`MergeConv`) **iff** the raw
  actions are commutative and idempotent at every state reachable from `s0`
  (`merge_action_exact`, through `cf_merge_boundary`).
- **(b') The semilattice form.** If moreover `X` is finite and state equality is decidable:
  `MergeConv` from `s0` **iff** the raw actions have a join-semilattice representation on the
  states reachable from `s0` (`CvRDTOn`: some `j` is a join-semilattice there and every event acts
  as `act e s = j s (act e s0)`), through `cvrdt_exact_all` (`cf_cvrdt_boundary`).

and, for the witness machine on `bool` (below):

- **(c) With compensation.** The witness's governed steps (raw `settrue` and `flip`, compensation
  to `false`) converge under causal exactly-once delivery from every start and under unordered
  at-least-once delivery from every start, while the conditions of (a) and (b) fail for its raw
  operations: they are not a causal CmRDT, the compensation-free system built from them diverges
  causally, they are neither commutative nor idempotent at a reachable state from any start, the
  compensation-free system diverges under duplication from every start, and they have no
  semilattice representation on the reachable states.

**Qualifier.** Part (c) is strictness relative to a fixed transition representation. The
governed composite `gstep wraw fixb` is itself the constant map to `false`, so it is a CmRDT and a
CvRDT on `bool` (`witness_governed_constant`). The theorem says that no compensation-free system
using these raw transitions satisfies the CRDT convergence conditions; it does not say that the
observable governed behavior escapes every CRDT. Read the strictness claim as a statement about
representations, not about observable behavior.

Non-vacuity (`boundary_nonvacuous`): the hypotheses of (a), (b) and (b') hold for the witness's
events (irreflexive `hb`, a finite range, decidable equality on events and states); with the raw
witness operations both sides of each iff are false, and with the constant action both sides are
true.

## The exact theorems behind it

The boundary rests on behavioral exact theorems, each an iff about runs:

- `causal_exact` (`GovernanceConverse.v`): causal convergence from `s0` iff every concurrent pair
  commutes after every causally consistent prefix that can deliver it (CCR). Reachability of the
  state alone is not enough (`naive_causal_converse_fails`).
- `causal_convergence_exact` (`GovernanceConverse.v`): with `hb` irreflexive, causal convergence
  from every start iff governed steps commute on every concurrent pair at every state. It is the
  converse of `causal_convergence` (`CausalReplay.v`); irreflexivity is needed.
- `merge_action_exact` (`CvRDTExact.v`): convergence under every order and every duplication from
  `s0` iff the action is commutative and idempotent at every reachable state; equivalently
  `alo_exact`'s conditions (`merge_conv_alo_exact`).
- `cvrdt_on_iff` and its packaged form `cvrdt_exact_all` (`CvRDTExact.v`): with a finite event
  range and decidable state equality, that convergence iff a join-semilattice representation on
  the reachable states. The backward direction `cvrdt_on_conv` needs no qualifier. The older
  `cvrdt_on_exact` states the same iff inside its section, but as exported it also takes the
  section hypothesis `MergeConv s0` as a premise, so its standalone statement is weaker than its
  name suggests; `cvrdt_on_iff`, `cvrdt_exact_all` and `crdt_boundary` (b') state the iff with
  only the finite range and decidable equality as hypotheses (`cvrdt_on_iff_nonvacuous`: both
  sides true for one finite instance, both false for another).
- `cvrdt_on_inflationary` (`CvRDTExact.v`): in that representation every event is inflationary
  in the join order.

`compensation_free_exact` (`CausalReplay.v`) is a structural equivalence, not a behavioral one:
once `normalize = id`, the governed step is the raw operation pointwise, so "governed steps commute
on concurrent pairs" and "concurrent raw operations commute" (`causal_cmrdt`) are the same
condition, and the proof is a rewrite. Its behavioral content comes from composing it with
`causal_convergence_exact`, which is what `crdt_boundary` (a) does.

The qualifiers of the state-based side are machine-checked as counterexamples in `CvRDTExact.v`:
the naive iff with a join-semilattice on all of `S` is false (`naive_cvrdt_iff_fails`),
reachability is needed (`clamp_reach_qualifier`), and both the commutation and the idempotence
clauses are needed (`lww_not_conv`, `add_cc_not_alo`).

## Strictness: what the witness shows

The witness (`CRDT.v`, section StrictInclusion; sharpened in `CRDTBoundary.v`) is a single
boolean where only `false` is valid, two events with raw transitions `settrue` (`s := true`) and
`flip` (`s := negb s`), and compensation that resets to `false`. Its governed steps converge
(`witness_converges`, `witness_governed_converges`). Its raw operations fail every CRDT
condition, each stated as a specific theorem:

- `witness_ops_not_commute`: `flip (settrue false) = false` while `settrue (flip false) = true`,
  and the two orders differ at every state. (The older `witness_not_cmrdt` quantifies over all
  functions `bool -> bool`; it is kept, and this is the specific pair.)
- `witness_raw_not_causal`: with the two events concurrent, the compensation-free system on these
  raw transitions diverges under causal exactly-once delivery from every start;
  `witness_causal_not_cmrdt` (`CausalReplay.v`) is the same failure of the op-based condition.
- `witness_not_cvrdt_order`: there is no partial order on `bool` under which both raw operations
  are inflationary. `settrue false = true` forces `false <= true`, `flip true = false` forces
  `true <= false`, and antisymmetry gives `true = false`; `witness_not_inflationary_antisym` needs
  only antisymmetry. So the raw operations are not monotone state evolution in any
  join-semilattice on `bool`.
- `witness_not_cvrdt_exact`: as merge actions, from every start state, the raw operations are not
  commutative and not idempotent (`flip` is not) at a reachable state, so by `merge_action_exact`
  they do not converge under unordered at-least-once delivery (`witness_duplicate_diverges`
  computes one divergence), and by `cvrdt_on_conv` they have no semilattice representation on the
  reachable states.
- `witness_leaves_valid_space` (`CRDT.v`): an event maps the valid state to an invalid one.

The conclusion: no compensation-free system using these raw state transitions satisfies the
corresponding CRDT convergence condition, yet the governed system converges. It converges because
compensation repairs the violation. By `witness_governed_constant` the governed behavior is itself
trivially representable (the state after any nonempty delivery is `false`, and the governed steps
are a CvRDT with join `andb`), so the claim is about representations, not observable behavior.

## The embedding (sufficient direction)

- `cmrdt_SEC` (`CRDT.v`): an op-based CRDT whose operations all commute reaches the same state
  from any permutation of the same operations, as a one-line instance of `run_perm_invariant`
  (`Checker.v`).
- `cmrdt_governed_SEC` (`CRDT.v`): the embedding is faithful. With the trivial invariant and the
  identity compensation, well-founded compensation is trivial, the governed step equals the raw
  operation, and compensation commutativity reduces to the operations commuting.
- `cvrdt_SEC`, `cvrdt_absorbs_duplicates` (`CRDT.v`): a commutative, associative, idempotent join
  makes merge order-independent and absorbs duplicate delivery. `CvRDTExact.v` recovers both
  through the exact theorems (`cvrdt_SEC_recovered`, `cvrdt_absorbs_duplicates_recovered`) and
  shows the delivered state is the least upper bound of `s0` and the payloads (`cvrdt_lfp`): a
  state-based CRDT is the compensation-free monotone case.

## Causal delivery (`CausalReplay.v`, `GovernanceCausal.v`)

The all-pairs results above use the strong op-based definition (every pair commutes). The
literature's op-based CRDTs only require concurrent operations to commute, because delivery is
causal.

- `CausalReplay.v` formalizes happens-before, concurrency (distinct and unordered by `hb`) and
  causal linearizations (duplicate-free orders in which every `hb`-earlier event comes first). It
  proves `causal_convergence` (governed steps that commute on concurrent pairs converge on every
  causally consistent order), `causal_cmrdt_SEC` (standard op-based CRDTs converge, as an
  instance), `compensation_free_exact` (the structural equivalence above), the witnesses
  `witness_causal_not_cmrdt` and `witness_beyond_all_pairs` (an add, a causally later remove and
  an independent counter: not all operations commute, yet causal delivery converges), and
  `causal_tequiv` (causally consistent orders are trace-equivalent under concurrency, connecting
  causal delivery to `Trace.v`'s `run_tequiv`, the theorem behind gsm's declared `Independent`
  pairs).
- `GovernanceCausal.v` is the co-enabled-events theorem for the rewrite system:
  `causal_governance_confluent` proves the full Convergence Theorem, with compensation
  interleaving, with CC1 required only for distinct events that are enabled together. Causal
  delivery is an important instance (causally ordered events are never enabled together), not
  the theorem's hypothesis. The witness `cw_confluent` / `cw_violates_all_pairs_cc1` satisfies the
  weakened hypothesis while violating the all-pairs one.

## Relation to the CRDT literature

- CmRDT and CvRDT are used in the sense of Shapiro, Preguiça, Baquero and Zawirski, "A
  comprehensive study of Convergent and Commutative Replicated Data Types" (INRIA Research Report
  RR-7506, January 2011, [inria.hal.science/inria-00555588](https://inria.hal.science/inria-00555588)) and
  "Conflict-free Replicated Data Types" (SSS 2011, LNCS 6976, pp. 386-400,
  [doi:10.1007/978-3-642-24550-3_29](https://doi.org/10.1007/978-3-642-24550-3_29)): a CvRDT is a
  state-based object whose states form a join-semilattice with inflationary updates and
  least-upper-bound merge; a CmRDT is an op-based object whose concurrent operations commute under
  causal delivery. `crdt_boundary` (a) and (b') are the exact versions of those two sufficient
  conditions for a compensation-free system, on reachable states.
- Delta-state CRDTs (Almeida, Shoker and Baquero, "Delta State Replicated Data Types", Journal of
  Parallel and Distributed Computing 111, 2018, [arXiv:1603.01529](https://arxiv.org/abs/1603.01529))
  ship join-decompositions of state changes rather than whole states, but deltas are still joined
  into a join-semilattice; they stay in the semilattice regime of (b'), with smaller messages.
- Invariant confluence (Bailis et al., [arXiv:1402.2237](https://arxiv.org/abs/1402.2237)) asks
  whether invariants survive coordination-free merging; it is orthogonal to the convergence
  mechanism this note classifies (see [LANDSCAPE.md](LANDSCAPE.md) for the placement).

## What this claim does not say

The result is about the convergence principle, not about CRDT engineering as a whole. CRDTs also
address concerns this theorem does not subsume:

- the metadata that enforces causal delivery (version vectors, dotted contexts). The convergence
  principle under causal delivery is covered (`CausalReplay.v`, `GovernanceConverse.v`); how a
  system achieves causal delivery is not;
- garbage collection of tombstones and history;
- the observable behavior of a governed machine. As `witness_governed_constant` shows, a governed
  machine's composite steps can themselves be a CRDT; strictness is about using the raw
  transitions without compensation.

Duplicate delivery is covered exactly for compensation-free systems (`crdt_boundary` (b)) and for
governed machines by `AtLeastOnceExact.v` (`alo_exact`, `causal_alo_exact`). "CRDTs are obsolete"
is neither claimed nor needed.

## Where the proof lives

- `coq/CRDTBoundary.v`: `crdt_boundary`, its parts `cf_causal_boundary`, `cf_merge_boundary`,
  `cf_cvrdt_boundary`, the sharpened witness theorems and `boundary_nonvacuous`.
- `coq/CRDT.v`: the embedding (`cmrdt_SEC`, `cmrdt_governed_SEC`, `cvrdt_SEC`,
  `cvrdt_absorbs_duplicates`) and the original witness.
- `coq/CvRDTExact.v`: the state-based exact theorems and their counterexamples.
- `coq/CausalReplay.v`: happens-before, concurrency, causal linearizations, causal convergence,
  `compensation_free_exact` and the causal witnesses.
- `coq/GovernanceConverse.v`: `causal_exact`, `causal_convergence_exact`.
- `coq/GovernanceCausal.v`: the co-enabled-events Convergence Theorem for the rewrite system.
- `coq/AtLeastOnce.v`, `coq/AtLeastOnceExact.v`: duplicate delivery for governed machines.
- `coq/Checker.v`: `run_perm_invariant`.
- `coq/verify.sh`: gates all of the above on being `Closed under the global context` (2974
  theorems at the time of writing; `verify.sh` is the source of truth).
