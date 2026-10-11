# Paper outline: normalization confluence

Working title: *Normalization confluence: an exact, mechanized theory of when repair can replace
commutativity*.

A section-by-section outline for the planned paper ([ROADMAP.md](ROADMAP.md#planned-paper-normalization-confluence)),
built from the roadmap's three claim tiers, the adversarial review's surviving claims and evidence
set ([research/paper-argument.md](../research/paper-argument.md#part-3-what-survives)) and the
tests of the framework. Every name in backticks is a gated theorem in `coq/*.v`. No prose yet; each
section lists its purpose, its claims, the results that carry them, and its source pages.

Venue plan (from the roadmap): arXiv first, then a journal that takes long mechanized work (for
example Logical Methods in Computer Science). Target length for the main text: about 30 pages, with
the regime map and the full recovery tables in appendices.

## The argument in four sentences

1. Replicas that repair their invariants after every event may differ raw, and what must agree is
   the result after repair; the paper gives exact conditions for that at one event, over finite
   histories and over infinite runs, and proves how the three relate.
2. Repair strictly enlarges which operations can be used, though not which behaviors converge: a
   convergent system is a CRDT on its repaired steps, and normalization confluence is an exact way
   to build one from operations that do not commute.
3. Three layers (execution, consistent states, long-run behavior) and three proved interfaces
   organize the results across the regimes, with normalization confluence derived from them without
   circularity.
4. The framework was tested where it could fail: frozen, it recovers classical theorems from outside
   the repository, and it made a prediction committed before its test, which passed.

## Abstract (sketch, to be written last)

Four or five sentences following the argument above, with the numbers: the gate count, the number
of regimes in the map, the outside theorems recovered, the prediction's outcome.

## 1. Introduction

- **Purpose.** The question and why it matters: networks deliver events in different orders,
  businesses have rules, and repair after every event is what systems do in practice (sagas,
  compensation, constraint repair).
- **Example.** The shelf: capacity 5, stock 4, "add 3" and "remove 1", two orders, two results
  (OVERVIEW.md, site).
- **The gap.** CRDTs avoid repair by design; invariant confluence checks invariants without
  repairing them; compensation in practice has no exact convergence condition.
- **Contributions,** one line each:
  1. exact conditions at three scales, as a proved hierarchy (section 3);
  2. the relation to CRDTs stated precisely: strict for operations, not for behaviors (section 4);
  3. a three-layer framework with proved interfaces, from which normalization confluence is
     derived (sections 5 to 9);
  4. tests of the framework: outside theorems recovered with it frozen, and a preregistered
     prediction (section 10);
  5. a regime map with exact conditions, hardness results and listed open problems, all
     mechanized axiom-free, and a checker that runs the practical conditions at build time
     (sections 11 and 12).
- **Scope sentence.** "Exact" is relative to the model each result states; the mathematical tools
  are classical and credited.
- Source: THEORY.md (main result), OVERVIEW.md, README.md.

## 2. Setting

- Events with raw transitions, a repair `N` (idempotent, terminating where stated), the governed
  step `N (act e s)`, delivery models (free, causal, at-least-once, declared independence).
- Reachable states; what "converges" means at each scale.
- Notation table.
- Source: THEORY.md (main result), `GovernanceConverse.v`, `CausalReplay.v`.

## 3. The main result: three conditions and how they relate

- **Purpose.** State the exact condition at each scale and the hierarchy.
- **State descent** (one event): `N (e (N x)) = N (e x)`, the definition `DescendsOn`; convergence
  requires it (`cc_exact`, `state_descent_iff_cc2`).
- **History descent** (finite histories): every allowed reordering gives the same result after
  repair; `history_from_descent` turns the raw question into the repaired one given state descent.
- **Canonical recurrence** (infinite runs): every fair run eventually stays on one repaired result
  (`C1_closed`); `canon_settles_quotient_invariant` reads `N` only through its result.
- **The hierarchy.** Not one equation: `descent_not_history`, `history_not_descent`,
  `trajectory_needs_descent`; together with terminating repair, state and history descent are
  exactly normalization confluence on one registry (`nd_derived_from`).
- **Figure 1.** The three conditions and the proved relations between them (site, "How the
  conditions relate").
- Source: THEORY.md (Descent at three scales), `LayerInterfaces.v` Part 3, `NormalizationDerived.v`.

## 4. CRDTs, invariant confluence and what repair adds

- **Purpose.** Place the result against the two closest bodies of work, precisely.
- **CRDTs are the case where repair does nothing.** `crdt_boundary` (a), (b), (b'): without
  compensation, the conditions are exactly the CmRDT and CvRDT conditions on reachable states.
- **Two readings of "strictly generalizes."** Operations: strict (`crdt_boundary` (c), the witness).
  Behavior: not strict; `causal_exact` and `merge_action_exact` hold for any step, so a convergent
  governed system is a CRDT on its governed steps (`witness_governed_constant` is one instance).
- **What normalization confluence adds:** a way to build such systems from operations that need not
  commute and a repair, with an exact check (section 12).
- **Invariant confluence.** A different question: the invariant is checked, never repaired. Its
  exact form as a polymorphism of the reachable valid states (`iconf_iff_pol_reach`, `uq_not_pol`)
  and `repair_enlarges`, with the caveat that the repair compensates a committed write.
- Source: SUBSUMPTION.md, LANDSCAPE.md, `CRDTBoundary.v`, `CvRDTExact.v`, `InvariantConfluence.v`.

## 5. Layer A: execution

- **Purpose.** One theorem pair proves the exact history results.
- **Kernel.** `local_exact` (P1), `closure_exact` (P2).
- **Recoveries,** each with its original predicates and its adequacy cost: `causal_exact_recovered`,
  `alo_exact_recovered`, `det_live_recovered`, `amodm_closure_recovered`; three of these are not
  trace monoids.
- **Where the local check stops.** `hw_seeds_insufficient`.
- **Table 1.** Recovery, original theorem, bridge size, adequacy cost.
- Source: THEORY.md (Layer A), `PresentedExecution.v`.

## 6. Layer C: long-run behavior

- **Purpose.** One fair-lasso kernel proves the settlement results on finite state spaces and
  classifies how runs fail.
- **Kernel.** `C1_closed`, `C1_nn`, `C2`, `C2_loops`; refutation on any state space (`C1_refutes`,
  `bad_lasso_refutes`).
- **A positive bridge.** `signed_settlement_lasso`.
- **Classification of failures.** `lasso_classification`, `semantic_oscillation`: oscillation,
  livelock, settling on the wrong state.
- **Boundaries.** Finite state for the exact form; `lpo_leak` for the constructive one.
- Source: THEORY.md (Layer C), `CanonicalRecurrence.v`.

## 7. Layer B: consistent states

- **Purpose.** The fixed points of repair are the solutions of a constraint problem, which places
  consistency in known constraint-satisfaction algebra.
- **Results.** `edge_fixed_iff_csp`, `section_iff_csp`, `pol_gamma_iff`; one tractable and one hard
  family (`ac_exact`, `dnet_iff_sat`), described as recovering known boundaries (Jeavons and Cooper
  1995; Larose and Zadori 2006).
- Source: THEORY.md (Layer B), `TransportCSP.v`, `TransportCSPHard.v`.

## 8. The interfaces

- **A to B.** Consistency must be respected only after repair: `xu_iff_respects`;
  `strict_not_necessary`, `natural_converse_fails`.
- **B to C.** One consistent state and still never reached: `flip2_unique_solution_livelock`;
  `settled_canon_exact`, `no_solution_canon_settles`.
- **A to C.** Newman under termination (`newman_bridge`); where fairness falls short
  (`four_point_fair_not_confluent`) and why (`fair_starves`, `fair_sn_exact`); where it stops
  (`drop_starved_confluent`).
- **Figure 2.** The three layers around `N`, with each interface labeled by its theorem and its
  stopping counterexample.
- Source: THEORY.md (Interfaces between the layers), `LayerInterfaces.v`.

## 9. The compensation-commutativity theorem as the base case

- **Purpose.** The single-registry theorem derived from the framework, without circularity.
- **Results.** `nd_derived_from`, `nd_cc_exact`; the dictionary: the one-event condition is state
  descent and the commutation condition is history descent.
- **The non-circularity check.** 46 of the file's 47 theorems still prove with the original
  theorems admitted as axioms; the one exception only shows the two forms agree.
- **Stated as a derivation, not a prediction:** the framework was built after the theorem.
- Source: THEORY.md (The compensation-commutativity theorem as the base case), `NormalizationDerived.v`.

## 10. Testing the framework

- **Purpose.** Separate compression from reach, and reach from prediction.
- **10.1 Outside theorems, framework frozen.** The protocol: every existing file frozen, the pass
  criterion fixed in advance, every leak recorded.
  - Dijkstra's self-stabilization (layer C, passed): `stab_fair_from` (one line from `C1_closed`),
    `ring_fair_selfstab`, `ring_unfair_selfstab`, `unfair_exact`, `ring_bound_matters`.
  - Invariant confluence (layer B, passed): `pol_iconfluent`, `iconf_iff_pol_reach`, `uq_not_pol`,
    `replica_exact`.
  - CRDT strong eventual consistency (layer A, partial; the weakest test, since CRDT results
    predate the framework): `opsec_exact`, `gomes_convergence`, `cvrdt_sec`, `crdt_sec_strict`.
  - **Table 2.** Theorem, layer, outcome, bridge size, leaks.
- **10.2 What the leaks share.** The kernels follow one state through time: no merge of two replica
  states, no simultaneous moves; a system that never quiesces needs an adapter. Recorded as
  boundaries, not repaired.
- **10.3 A preregistered prediction.** The freeze (hashes checked in CI), the protocol, the
  candidates considered, P2 as committed (claim, criteria, timestamp), the literature check made
  before commitment, and the outcome: passed. A 3 by 3 market with exactly one stable matching and a
  pair-fair cycle (`p2_unique_stable`, `p2_bad_lasso`, `p2_refutes_settlement`, `p2_pass`); the
  exhaustive counts (2 by 2: none; 3 by 3: 3,240 of 34,080; 4 by 4: 17,655,840,000 of
  65,867,261,184); the independent check; and, outside the scored claim, the same result under
  strong fairness.
- **What this section may claim:** one correct preregistered prediction, a bet on which side of a proved distinction (`q1_unique_iff` against `flip2_unique_solution_livelock`) a new system falls; not that the framework computed the answer. A computed prediction about real software (P3) is in preparation.
- Source: THEORY.md (Testing the framework and the outside-theorem subsections),
  research/predictions/.

## 11. The regime map

- **Purpose.** The evidence base, summarized: in every regime, an exact condition, a hardness
  result, or a listed open problem.
- **Figure 3.** The Convergence Atlas.
- **Content.** Exact regimes by family; hardness (NP-complete consistency without a spanning root;
  minimum coordination NP-hard); the open gaps and the cyclic frontier; design exclusions.
- Source: REGIME-AUDIT.md, COVERAGE.md, docs/atlas/.

## 12. gsm: the conditions at build time

- **Purpose.** The practical use: what gsm checks, how it scales (footprints, collections,
  abstraction, federations), and the extracted oracles that re-certify its tables.
- **Example.** The shelf in gsm and the build's counterexample (site).
- **Stated limits.** gsm's static checks are sufficient forms of reachable-state conditions, not
  exact.
- Source: gsm README and docs/theory.md, `coq/extraction/`, `coq/goextract/`.

## 13. Related work

By community, from LANDSCAPE.md: CRDTs and CALM; invariant confluence; rewriting (Newman, Huet,
Klop); trace theory; Boolean and discrete networks (Robert, Thomas, Richard, Shih and Ho); fixed
points (Knaster-Tarski, Bekic); CSP algebra (Abramsky, Jeavons, Bulatov, Zhuk, Larose and Zadori);
fair cycles and fair termination (Emerson and Lei, Vardi and Wolper, Lehmann, Pnueli and Stavi,
Francez); self-stabilization (Dijkstra, Dolev, earlier mechanizations in PVS and Coq); routing
algebras where relevant to the prediction candidates.

## 14. Limitations and what is not claimed

From the review's "claims the paper should not make", restated for the reader: no new mathematics in
the tools; the three layers are not one principle; layer C is exact on finite state spaces; the
recoveries compress, they do not confirm; a unique solution does not give convergence; gsm's checks
are sufficient, not exact; no "new" or "first" without a recorded literature check.

## 15. Conclusion

What is settled, what the tests showed, and the open problems that matter most (composition on
cycles; layer C beyond finite state; a merge in layer A).

## Appendices

- A. Method: every cited name read as a statement; the axiom-free gate on three Coq versions; how to
  reproduce.
- B. Module index by regime (coq/README.md).
- C. The full recovery tables, with adequacy costs.
- D. The regime audit summary and the coverage matrix.
- E. The prediction protocol and the committed text of P2, verbatim.

## Before drafting

- Fill in section 10.3 from the P2 outcome.
- Decide whether the CRDT relation (section 4) moves before the layers, as here, or after.
- Check every figure against the site's versions.
- Read every cited name in the Coq source once more against the sentence that cites it.
