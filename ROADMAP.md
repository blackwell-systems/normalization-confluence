# Roadmap: removing the remaining caveats

Goal: a theory in which every remaining caveat is either a deliberate design exclusion or a
fundamental limit, and nothing is merely unproven. This page lists each caveat the development
still carries, what removing it would prove, how, what it depends on, and when it counts as done.

Status of the gate: 254 theorems, all axiom-free (`coq/verify.sh`), CI on Coq 8.18, Coq 8.20 and
Rocq 9.3 (135 when this page was first written). Items 1 to 4, the monotone-cycle event result and
the C1/C2 converse have landed; item 5 is open. Nothing on this page is claimed proven until it lands
in a module and passes the gate.

## Done

| Item | Module | Headline theorems | PR |
|---|---|---|---|
| 1. Finite state only for checking | `GovernanceWF.v`, `ChaoticACC.v` | `governance_wf_confluent`, `causal_governance_wf_confluent`, `zw_confluent` (infinite instance on `Z`); `chaotic_acc_reaches_lfp`, `kleene_acc_lfp`, `ole_no_rank` | #23 |
| Event interleaving for monotone cyclic federations | `FederationEventsCycles.v` | `gc_iff`, `gc_image`, `cyc_events_converge_iff`, `cyc_instance`, `bottom_matters`, `cyc_counterexample` | #24 |
| Exact converse of C1 and C2 (acyclic) | `FederationEventsConverse.v` | `fed_exact`, `fed_exact_full`, `acyclic_gc_iff`, `static_c1_c2_gc`, `naive_converse_fails` | #24 |
| 2. At-least-once delivery | `AtLeastOnce.v` | `alo_commuting_converges`, `causal_alo_converges`, `non_idempotent_diverges`, `late_duplicate_diverges` | #25 |
| 3. Exact converse of CC and of causal convergence | `GovernanceConverse.v` | `cc_exact_from`, `cc_exact_global`, `jc_exact`, `causal_exact`, `causal_convergence_exact` | #26 |
| 4. Non-monotone cycles under a computed coordination | `CoordinatedCycles.v` | `coordinated_sound`, `coordinated_unique_nf`, `plan_exact`, `coordination_needed`, `coordinated_events_converge`, `copyback_zero_coordination`, `negation_one_coordinated` | #27 |
| gsm check for **C2** (same-target event pairs, repair in between) | gsm | gsm PR #26 | gsm |

Still in flight: gsm `EmbedCertified` executing the **certified tables** instead of live closures
(gsm PR #27, open).

### Qualifiers found

Each item reads "if and only if" or "converges" only with the qualifier stated in the theorem. The
naive statements are false, and each has a mechanized counterexample:

- **C1/C2 converse.** The exact converse needs witnesses realized by reachable states. Static C1 can
  fail while every interleaving from every valid consistent start converges
  (`naive_converse_fails`). Static C1 and C2 are sufficient, and necessary only at reachable
  witnesses.
- **CC converse.** Needs canonical repair (`rho_star` returns a valid state): with the identity as
  `rho_star`, CC1 fails yet normal forms are unique (`rho_star_qualifier`). Under causal or guarded
  enabledness CC1 is not necessary (`masked_cc1`); the exact condition is joinability of critical
  pairs at reachable configurations (`jc_exact`).
- **Causal converse.** Reachability of the state is not enough; the non-commuting concurrent pair
  must be deliverable after a causally consistent prefix (`naive_causal_converse_fails`).
- **At-least-once.** Idempotence of each duplicated event is not enough under causal delivery: the
  redelivery must itself be causally consistent (`late_duplicate_diverges`).
- **Coordinated cycles.** The normal form is unique given the authority root, not absolutely: the
  result depends on the root (`root_choice_matters`), and without a root two orders reach different
  consistent states (`copyback_without_authority`). Balance is a static property of an edge only for
  invertible transports (`noninvertible_balance_not_static`), and the strong form of
  `unbalanced_blocks` needs the regular action (`nonfree_holonomy_counterexample`).

### Exact versus checked

The exact conditions (JC, CCR and GC) quantify over reachable states or prefixes, so checking them
means exploring the reachable state space (on a cycle, the federated state space). The cheap
sufficient conditions (CC for a registry, C1 and C2 for an acyclic federation) are what gsm checks;
they imply the exact ones (`cc_reach_jc`, `static_c1_c2_gc`). Scope throughout: discrete,
deterministic governed state.

The cyclic result works through the federated normalizer `N` (the unique least fixed point from
`Federation.v` and `Chaotic.v`): each governed step is `N` after the event, and `Trace.run_tequiv`
gives convergence when steps commute on reachable states. In a cycle that condition is global, not
per edge, so a gsm check for it explores the federated state space.

## Removable caveats, high value

Each item below lists the theorem it would add, the approach, and the acceptance criterion. Items 1
to 4 are done; the "Today" paragraphs record the state before they landed. Item 5 is open.

### 1. "Finite state" becomes a statement about checking only

**Status: done (#23).** `GovernanceWF.v` (WFC over any well-founded order, with the infinite
withdrawal registry on `Z` as instance and the nat-valued theorems as corollaries) and
`ChaoticACC.v` (chaotic and Kleene iteration under the ascending chain condition, with
`option nat` as an ACC lattice that provably has no rank into `nat`).

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

**Status: done (#25).** `AtLeastOnce.v`: duplicates of idempotent governed steps are absorbed
(`alo_absorbed`, `alo_commuting_converges`, `causal_alo_converges`), and a non-idempotent duplicate
diverges (`non_idempotent_diverges`, `inc_duplicate_diverges`). Qualifier: under causal delivery the
redelivery must be causally consistent (`late_duplicate_diverges`).

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

**Status: done (#24, #26).** `GovernanceConverse.v`: `cc_exact_from` (unique normal forms from `s0`
iff CC on the states reachable from `s0`, with canonical repair), `jc_exact` (any enabledness),
`causal_exact` and `causal_convergence_exact`. `FederationEventsConverse.v`: `fed_exact`,
`fed_exact_full`, `acyclic_gc_iff`. Qualifiers and counterexamples to the naive converses are listed
under "Qualifiers found" above.

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

**Status: done (#27).** `CoordinatedCycles.v`: `coordinated_sound` and `coordinated_unique_nf`
(unique normal form given the authority root), `plan_exact`, `coordination_needed`,
`coordinated_events_converge`, with `copyback_zero_coordination` and `negation_one_coordinated` as
the two acceptance instances. Qualifiers: `root_choice_matters`, `copyback_without_authority`,
`noninvertible_balance_not_static`, `nonfree_holonomy_counterexample`.

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

**Status: open.**

- **Today.** gsm's single-registry builds pass a fail-closed oracle gate extracted from the proof.
  The federation-level checks (M1, R1/R2, acyclicity, monotone cycles, cross-registry order) are
  gsm's Go code and are not oracle-certified.
- **Target.** An extracted federation checker, proven sound against the federation theorems, run by
  gsm in-process on `Federation.Build`.
- **Approach.** A decidable checker over the federation's emitted tables (morphism and resolver
  tables, component step tables), proven to imply the hypotheses of the federation theorems
  (including C1, C2 and the now-landed items 1 to 4), extracted the same way as the table and rules
  oracles. This is also the outstanding item in gsm's `CERTIFICATE-DESIGN.md`.
- **Done when.** gsm's federation report states that the federated composition is oracle-certified,
  with differential tests against the Go checks.

## Removable caveats, lower value

- **Non-invertible cycles, mechanized criterion.** A global section around a cycle exists if and
  only if the loop composite has a reachable fixed point. This is what gsm's `DiagnoseCycle`
  computes; mechanizing it backs the diagnostic with a theorem.
- **Distributed model for cycles.** `FederationEvents.v` proves a distributed model (local events
  and separate propagation steps) for acyclic federations; extend it to monotone cycles.
- **C2 converse over all valid starts in general networks.** The C2 converse applies when some
  valid consistent state realizes the witness pair `(z, b)` (for example a two-registry federation
  whose source has no repair); a general statement quantifying over all valid starts is open.
- **Cost of checking GC.** On a cycle the exact condition GC has no per-edge reduction, so a check
  enumerates reachable normal forms (or the image of `N`) and tests every independent pair. A
  cheaper sufficient check, or a bound on that exploration, is open.
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

Items 1 to 4, the monotone-cycle event result and the C1/C2 converse have landed, so their theorem
statements are fixed and item 5 can start. When item 5 lands, every remaining high-value caveat on
this page is either a design exclusion (non-monotone cycles without coordination) or a fundamental
limit; the lower-value items above remain open.
