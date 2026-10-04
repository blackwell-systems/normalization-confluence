# Roadmap: removing the remaining caveats

Goal: a theory in which every remaining caveat is either a deliberate design exclusion or a
fundamental limit, and nothing is merely unproven. This page lists each caveat the development
still carries, what removing it would prove, how, what it depends on, and when it counts as done.

Status of the gate at the time of writing: 135 theorems, all axiom-free (`coq/verify.sh`), CI on
Coq 8.18, Coq 8.20 and Rocq 9.3. Nothing on this page is claimed proven until it lands in a module
and passes the gate.

## In flight

| Item | Where | Status |
|---|---|---|
| Event interleaving for **monotone cyclic** federations | `mech/federation-events-cycles-converse` | in progress |
| **General converse** for C1 and C2 (necessary, not only sufficient) | same branch | in progress |
| gsm check for **C2** (same-target event pairs, repair in between) | gsm, after the current merge sequence | queued |
| gsm `EmbedCertified` executes the **certified tables** instead of live closures | gsm | queued |

The cyclic result works through the federated normalizer `N` (the unique least fixed point from
`Federation.v` and `Chaotic.v`): each governed step is `N` after the event, and `Trace.run_tequiv`
gives convergence when steps commute on reachable states. In a cycle that condition is global, not
per edge, so a gsm check for it explores the federated state space.

## Removable caveats, high value

Each item below lists the theorem it would add, the approach, and the acceptance criterion. They
are independent of one another and can run in parallel; item 5 builds on the others.

### 1. "Finite state" becomes a statement about checking only

- **Today.** The single-registry convergence theorem (`Governance.v`) already quantifies over any
  state type, but its termination potential is natural-number valued (`Phi : State -> nat`). The
  monotone results assume finite height (`Chaotic.v`, `rank`). The paper's infinite-domain
  corollary (convergence is domain-independent) is proved on paper only.
- **Target.** Termination from any well-founded relation (ordinals, lexicographic products), and
  the monotone regime under the ascending chain condition instead of finite height.
- **Approach.** Restate WFC over an arbitrary well-founded order and rerun the termination proof;
  replace `rank` with well-foundedness of the strict order's converse in the chaotic-iteration
  proof.
- **Done when.** The generalized theorems pass the gate, a non-vacuity instance on an infinite
  domain (for example an unbounded integer counter with a floor repair) discharges every hypothesis,
  and the existing finite theorems are recovered as corollaries.
- **Effect.** "Finite" stops being a condition of the theory. It remains only what makes gsm's
  exhaustive check decidable.

### 2. "Exactly-once delivery" becomes a checked property

- **Today.** Convergence assumes every replica sees each event exactly once. A non-idempotent event
  delivered twice diverges.
- **Target.** Convergence under at-least-once delivery for the events whose governed step is
  idempotent, and a counterexample for any event that is not.
- **Approach.** Model delivery as a multiset of events and prove that duplicates of an idempotent
  governed step are absorbed, extending the order-independence results; this mirrors how state-based
  CRDTs absorb duplicates (`cvrdt_absorbs_duplicates`).
- **Done when.** The theorem passes the gate with a witness of divergence for a non-idempotent
  event. gsm's next release reports non-idempotent events (`Report.NotIdempotent`, gsm PR #24), so the
  documentation can say exactly which events need deduplication.

### 3. "Sufficient, not necessary" becomes "if and only if"

- **Today.** The convergence conditions are proven sufficient; necessity is shown by
  counterexamples (the paper's necessity results, the CC counterexamples, the C1 and C2
  counterexamples). The general converse for C1 and C2 is in flight.
- **Target.** General converses for the single-registry CC condition and for causal delivery: if
  CC fails at a reachable state, two event orders diverge; if a non-commuting pair can arrive out of
  causal order, a divergent run exists.
- **Approach.** Construct the diverging runs from the failure witness, with reachability as an
  explicit hypothesis. If the naive converse is false, prove the strongest true form and record the
  counterexample to the naive one.
- **Done when.** Each core result reads "converges if and only if," with any qualifier stated in
  the theorem.

### 4. Non-monotone cycles converge under a computed coordination

- **Today.** Non-monotone cyclic federations have no unique normal form and are rejected (or
  coordinated by gsm's `CoordinationPlan`, which cuts every cycle). The holonomy-minimal plan in
  gsm's `HOLONOMY-COORDINATION-DESIGN.md` has a stated soundness condition but no theorem.
- **Target.** Soundness of the holonomy-minimal plan: with values driven along a spanning tree from
  a designated authority root, balanced non-tree edges kept as checked constraints, and unbalanced
  edges externally coordinated, the federation has a unique normal form.
- **Approach.** Compose the acyclic federation results (the tree is acyclic) with
  `tree_has_section`, `tree_unique`, `keep_balanced_suffices` and `unbalanced_blocks` from
  `CohomologyGraph.v`; the authority root fixes the constant that `tree_unique` leaves free.
- **Done when.** The soundness theorem passes the gate, with the copy-back loop (balanced, accepted
  with zero coordination) and the negation loop (unbalanced, one edge coordinated) as instances.
- **Effect.** Every cyclic case is covered: monotone cycles converge, and non-monotone cycles
  converge given the computed coordination.

### 5. Federation-level checks become oracle-certified

- **Today.** gsm's single-registry builds pass a fail-closed oracle gate extracted from the proof.
  The federation-level checks (M1, R1/R2, acyclicity, monotone cycles, cross-registry order) are
  gsm's Go code and are not oracle-certified.
- **Target.** An extracted federation checker, proven sound against the federation theorems, run by
  gsm in-process on `Federation.Build`.
- **Approach.** A decidable checker over the federation's emitted tables (morphism and resolver
  tables, component step tables), proven to imply the hypotheses of the federation theorems
  (including C1, C2 and items 1 to 4 as they land), extracted the same way as the table and rules
  oracles. This is also the outstanding item in gsm's `CERTIFICATE-DESIGN.md`.
- **Done when.** gsm's federation report states that the federated composition is oracle-certified,
  with differential tests against the Go checks.

## Removable caveats, lower value

- **Non-invertible cycles, mechanized criterion.** A global section around a cycle exists if and
  only if the loop composite has a reachable fixed point. This is what gsm's `DiagnoseCycle`
  computes; mechanizing it backs the diagnostic with a theorem.
- **Distributed model for cycles.** `FederationEvents.v` proves a distributed model (local events
  and separate propagation steps) for acyclic federations; extend it to monotone cycles.
- **Rank of `H^1` on the full nerve.** The mechanized rank is for the graph (the nerve's
  1-skeleton). Triangles add relations that can lower it. Rarely matters in practice.
- **Complexity results.** NP-hardness and fixed-parameter tractability of the minimum coordination
  are cited from the group feedback set literature; they are not this work's results.

## Fundamental limits (stated, not removable)

- **Continuous state.** Convergence of continuous dynamics needs a different argument (contraction,
  see `LYAPUNOV-EXTENSION.md`). Multi-basin landscapes have no unique attractor.
- **Eventual delivery.** A replica that never receives an event cannot converge with one that did.
- **Purity of Go closures.** gsm can verify combinator rules exactly; arbitrary Go closures can be
  tested, not proven pure.
- **Trust base.** The extracted checkers rely on Rocq's extraction, the Go code generator and the Go
  toolchain.

## Sequencing

Items 1, 2, 3 and 4 are independent proofs and can run in parallel. Item 5 is engineering that
consumes their statements, so it starts once their theorem statements are fixed. The in-flight work
(cycles and the C1/C2 converse) feeds items 3 and 5.

When items 1 to 5 land, every remaining caveat on this page is either a design exclusion
(non-monotone cycles without coordination) or a fundamental limit.
