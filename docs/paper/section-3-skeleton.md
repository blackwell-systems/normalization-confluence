# Section 3 skeleton: the main result

Writing notes for section 3 of the paper ([PAPER-OUTLINE.md](../PAPER-OUTLINE.md#3-the-main-result-three-conditions-and-how-they-relate)).
Each paragraph lists what it must say, the formal statement it carries, and the Coq name behind it.
No prose: the prose is written from these notes. Statements are read from the Coq source; the
paper's notation may differ, but the content must not.

Target length: 4 to 5 pages, one figure, one example.

## 3.0 Opening (one paragraph)

Must say:
- The question in one sentence: replicas apply the same events in different orders and repair after
  each one; when do they end in the same state?
- The answer's shape: raw states may differ; what must agree is the result after repair. One exact
  condition at each of three scales: one event, finite histories, infinite runs.
- The three are not one equation: they form a proved hierarchy (3.4).

## 3.1 One event: state descent

Paragraph 1, the definition.
- Repair `N : X -> X`. An event `e : X -> X` descends on a set `P` when
  `forall x, P x -> N (e (N x)) = N (e x)`.
- Coq: `DescendsOn` (`LayerInterfaces.v`).
- Plain reading: applying the event to a state or to its repaired form gives the same result after
  repair. Repairing early loses nothing the event can see.

Paragraph 2, the example (the shelf).
- Capacity 5, stock 4, events "add 3" and "remove 1", repair caps at 5.
- Raw state 7 (after "add 3"): `N(e(N 7)) = N(remove1(5)) = 4`, but `N(e(7)) = N(6) = 5`. State descent
  fails for "remove 1" at 7, and the two delivery orders end at 4 and 5.
- Keep the arithmetic in the text; it is the reader's first concrete case.

Paragraph 3, why it is necessary.
- In the single-registry setting, state descent is exactly the second commutation condition CC2:
  `state_descent_iff_cc2` (`CanonicalExecution.v`): with repair `rho*` built from a terminating
  repair step (`Phi (rho s) < Phi s` off the valid states),
  `StateDescent rho* apply <-> forall s e, ~ valid s -> rho* (apply e s) = rho* (apply e (rho s))`.
- And CC2 is forced by convergence (3.3).

## 3.2 Finite histories: history descent

Paragraph 1, the definition.
- A delivery model says which reorderings of a history count as the same (free: all permutations;
  causal: those consistent with happens-before; at-least-once: also duplicates; declared
  independence: swaps of declared pairs).
- History descent: every reordering the model allows gives the same result after repair.

Paragraph 2, the transfer lemma.
- `history_from_descent` (`LayerInterfaces.v`): if every event descends, then for any equivalence
  `EqH` on histories and any start `s0`,
  `(forall h k, EqH h k -> N (rawrun h s0) = N (rawrun k s0)) <->`
  `(forall h k, EqH h k -> grun h (N s0) = grun k (N s0))`,
  where `grun` repairs after every event.
- Plain reading: given state descent, asking whether raw runs agree after repair is the same as
  asking whether the repaired runs agree. This is what lets a checker work on repaired states only.

Paragraph 3, the exact condition per delivery model.
- Point forward: section 5 gives one theorem pair that decides history descent for every delivery
  model above (`local_exact`, `closure_exact`). Here only state the free-delivery case through 3.3.

## 3.3 The single-registry theorem (compensation commutativity)

Paragraph 1, the statement.
- `cc_exact` (`GovernanceConverse.v`), relative to a start `s0`, with `gov e = rho* o apply e` and
  terminating repair:
  every configuration over a state reachable from `s0` has a unique normal form
  `<->` (CC1) `forall sigma e1 e2, reach s0 sigma -> gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)`
  and (CC2) `forall sigma e, reach s0 sigma -> ~ valid sigma -> gov e sigma = gov e (rho sigma)`.
- Plain reading: replicas converge exactly when repaired events commute (CC1) and an event does not
  care whether repair ran first (CC2), at the states they can reach.

Paragraph 2, in terms of the two descents.
- `nd_derived_from` (`NormalizationDerived.v`): every run from `s0` has one result `<->` free-history
  descent from `N s0` and state descent on the states reachable from `s0`. CC1 is history descent,
  CC2 is state descent.
- Section 9 shows this is derived from the framework's kernels without circularity; here it only
  reads the theorem in the section's vocabulary.

Paragraph 3, the proof idea and its standing (be plain about it).
- Sufficiency: Newman's lemma on the reachable set, with a case split on the two kinds of critical
  peak (two events; event and repair).
- Necessity: two small runs, two events in both orders (CC1), one event before and after repair
  (CC2); both ends are normal forms because repair always reaches a valid state.
- Standing: this is the critical-pair theorem (Knuth and Bendix; Huet 1980) specialized to a system
  whose critical pairs are already normal forms, which is why "joinable" becomes "equal" and the
  converse is free. The contribution is the condition and its necessity at reachable states, not the
  proof technique.
- Counterexamples that fix the qualifiers: reachability is needed (`rho_star_qualifier`), and the
  naive converse fails without it (`masked_cc1`).

## 3.4 Infinite runs: canonical recurrence

Paragraph 1, the setting.
- When repair may never stop (networks with cycles), ask about long-run behavior: a run settles on a
  repaired result `c` if `N` of the state is eventually always `c`.
- Fair schedules: every action is named infinitely often.

Paragraph 2, the condition.
- `C1_closed` (`CanonicalRecurrence.v`): on a finite state space, if the fiber `N^{-1}(c)` is closed
  under the steps, every fair run from `s0` settles on `c` `<->` there is no bad fair lasso from `s0`
  (a fair loop with a state outside the fiber).
- Plain reading: settling fails exactly through a fair loop that leaves the target result.
- Scope: exact on finite state spaces; refutation (`C1_refutes`) holds on any state space.

Paragraph 3, it reads repair only through its result.
- `canon_settles_quotient_invariant` (`LayerInterfaces.v`): if the dynamics respect `N`, settling is
  a property of the quotient dynamics; two systems with the same `N`-image behave the same.

## 3.5 The hierarchy (Figure 1)

Paragraph 1, the claim.
- The three conditions are not one equation. State descent and history descent are independent;
  together with terminating repair they are exactly convergence of the single registry (3.3);
  terminating repair links them to settlement (Newman, section 8).

Paragraph 2, the proved separations (one sentence each):
- `descent_not_history`: state descent without history descent. With `N` the identity every event
  descends, and two events that do not commute separate a reordering.
- `history_not_descent`: history descent without state descent. One event, so every reordering is
  trivial, while the event does not respect what repair identifies (`N` maps 0 and 1 together).
- `trajectory_needs_descent`: at infinite runs, two dynamics whose steps have the same image under
  `N` can settle on different results (one on `true`, the other on `false`) when they do not respect
  `N`; reading settlement through the quotient needs descent.

Figure 1: three boxes (one event, sequences, infinite runs), "neither implies the other" between the
first two, "with terminating repair" from the second to the third, and the bracket "together:
exactly the single-registry theorem". Use the site's version as the draft.

## 3.6 Closing (one paragraph)

Must say:
- Every condition is exact: necessary and sufficient, each hypothesis shown needed by a
  counterexample.
- Forward pointers: section 4 (what this says about CRDTs), sections 5 to 8 (the layers and
  interfaces that organize these results across the regimes).

## Checks before the prose is final

- Read each cited name in the Coq source again against the sentence that cites it.
- Keep one notation for repair throughout (`N` in this section; say once that `rho*` in 3.3 is `N`).
- Verify the shelf arithmetic once more in the final text.
