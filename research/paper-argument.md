# Adversarial review for the paper "Convergence as descent"

The roadmap lists this review as the step before drafting ([ROADMAP.md, "Before
drafting"](../docs/ROADMAP.md#before-drafting)). It argues the case against the paper as a skeptical
reviewer would, then answers each objection with the smallest set of results from the repository, or
concedes it and says how the paper should state the claim instead.

Scope. No theorem is added, removed or renamed, and no claim in an existing page changes. Every name
in backticks is a `Theorem`, `Lemma` or `Corollary` in `coq/*.v`; the statements quoted are read
from the Coq files. Prior work is as recorded in [LANDSCAPE.md](../docs/LANDSCAPE.md); nothing here
adds a literature search.

The claim under review, from [THEORY.md](../docs/THEORY.md#main-result): in every regime the
repository covers, a system converges exactly when its behavior does not depend on anything the
repair map `N` throws away, read at one transition, over finite histories and over infinite runs,
with three layers (A, execution; B, constraints; C, settlement) and three interfaces between them.

Outcomes in brief:

| | Objection | Outcome |
|---|---|---|
| O1 | Descent is compatibility with a congruence | Partly answered: shape conceded, necessity answered |
| O2 | Layer A is Mazurkiewicz traces plus Newman | Partly answered |
| O3 | Layer B is Abramsky's global sections plus Jeavons | Conceded as mathematics; placement answered |
| O4 | Layer C is Emerson-Lei fair cycles | Conceded for the kernel; compression answered |
| O5 | The interfaces are definitional | Partly answered |
| O6 | The "predictions" are known results | Conceded |
| O7 | Recovering the repository's own theorems is circular | Partly answered; since answered in part by outside recoveries (A7, update) |
| O8 | The finiteness and LPO leaks remove the cases that matter | Partly conceded |
| O9 | The framework has predicted nothing not already known | Conceded in part: two preregistered predictions passed, P2 as a bet and P3 as a model computation checked against running software (A9, updates) |
| O10 | The distributed application is a change of vocabulary | Partly answered |
| O11 | "One principle at three scales" is not a theorem | Conceded in part; the paper must restate it |
| O12 | "Exact" is cheap: the author picks the model and quantifies over reachable states | Partly answered |

## Part 1. The objections

Each objection is written as a reviewer from the named community would write it.

### O1. Descent is compatibility with a congruence (universal algebra)

`DescendsOn P N e` says `N (e (N x)) = N (e x)` on `P`. With `N` idempotent and `P` closed under
`N`, the repository itself proves this is the same as `e` respecting the kernel of `N` and as `N o
e` factoring through `N` (`descends_iff_respects`, `descends_iff_factors`). That is the definition
of an operation compatible with an equivalence relation, in chapter II of any universal algebra
text. Calling it "descent" borrows a word from Grothendieck that the repository then has to
disclaim. A condition every algebraist checks when forming a quotient cannot be the main result of a
paper. Listing the regimes where it shows up (CC2, XU, C1, state descent) shows that the author
wrote the same compatibility condition four times, not that four problems share a principle.

### O2. Layer A is Mazurkiewicz traces plus Newman (rewriting and trace theory)

The execution algebra quotients words by swaps of independent events. That is the trace monoid of
Cartier and Foata and of Mazurkiewicz, and `swap_peq_perm` and the declared-pairs row (a trace
monoid of `I`) say so. P1 (`local_exact`) and P2 (`closure_exact`) say that a semantics is invariant
on the generated equivalence iff it agrees on the generators, with or without whiskering. For a
monoid action this is the standard fact that an action factors through a quotient by a congruence
iff it is constant on the generating pairs (Howie). `ppc_iff_whisk` shows the "continuation closure"
of P2 is just the set of whiskered generator pairs, so P2 says: a function is constant on the
classes of an equivalence closure iff it agrees on the relation being closed. Confluence of the
governed rewrite system is Newman's lemma. Nothing here needs a name of its own.

### O3. Layer B is Abramsky's global sections plus Jeavons (CSP algebra)

Global sections as CSP solutions is Abramsky and coauthors (2011 to 2017; Abramsky, Barbosa, de
Silva and Zapata 2017, Proposition 13). That polymorphisms of the graph of a map are the operations
commuting with it is clone theory (Machida 2010; Machida and Rosenberg). Arc consistency deciding
monotone constraints on a chain is Jeavons and Cooper 1995, in the semilattice form of Jeavons,
Cohen and Gyssens 1997. Mal'tsev for group translations is Bulatov and Dalmau 2006. The diamond
hardness follows from Larose and Zádori 2006, and the three-element boundary from Broniek 2006.
LANDSCAPE.md concedes all of this. Layer B is a well-known theory applied to one family of
instances, and the classification is a cited, unmechanized dichotomy (Bulatov 2017; Zhuk 2017,
2020).

### O4. Layer C is Emerson-Lei fair cycles (model checking)

C1 and C2 say that on a finite state space every fair run eventually stays in a set iff no fair
lasso has a loop state outside it. That is the fair-cycle characterization of Clarke, Emerson and
Sistla 1986, Emerson and Lei 1986 and Vardi and Wolper 1986, which every LTL model checker
implements as Büchi emptiness. A fair lasso is an accepting cycle. The file says so in its header.
Re-proving it in Coq and then re-reading some settlement results through it is engineering, not a
contribution to the theory of convergence.

### O5. The interfaces are definitional

B-C: an edge repair `s[b := f (s_a)]` fixes `s` iff `f (s_a) = s_b` (`erep_fixed_iff`); so "fixed
points of repair are sections" holds by unfolding, and "sections are CSP solutions" is O3. A-C: the
bridge is Newman's lemma (`newman_bridge` from `peak_exact`), and its converses (`cr_peaks`,
`cr_unf`) are textbook. A-B: "a natural family maps sections to sections" (`natural_maps_sections`)
is naturality. An interface theorem that holds because both sides were defined to match is not
evidence that the layers belong to one theory. The objection the repository set out to test (three
classical theories stapled together) is not refuted by stapling them with three more classical
facts.

### O6. The "predictions" are known results

THEORY.md says the algebra "predicts" the hard cell for monotone maps off the chain, and
`TransportCSP.v` files the chain cell under "predicted cells". Both cells are in the literature: the
chain side is Jeavons and Cooper 1995, the diamond follows from Larose and Zádori 2006 through the
square encoding, and every three-element poset is covered by Broniek 2006. A prediction whose answer
was published twenty years earlier is a recovery. The computational search over small posets
confirms known facts.

### O7. Recovering the repository's own theorems is circular

The recovered results (`causal_exact`, `tconv_exact`, `alo_exact`, `det_live_exact`,
`amodm_closure_exact`, `chaotic_reaches_lfp`, `signed_settlement`, `signed_fidelity`, the flip2 and
ghost examples) were proved in the same repository, by the same author, over definitions the same
author chose. The kernels (P1, P2, C1, C2) were written after those results were known, with the
targets in view. A kernel designed to fit a list of theorems will fit them. "Eight results
recovered" measures how well the author knows the author's own development, not whether the
framework explains anything. At worst it is tautological: if a recovered theorem's proof calls the
original, nothing is recovered.

### O8. The finiteness and LPO leaks remove the cases that matter

Every layer C recovery assumes a listed, finite state type. The originals assume finite height,
which allows infinitely many states, so the recoveries are of the finite fragments only, and
`chaotic_reaches_lfp` also needs a finite component list. The strong form of C1 is not constructive
in general (`lpo_leak`). The A-C exact replacement (`fair_sn_exact`) also needs a finite state type.
Real replicated state (counters, logs, integer balances) is not finite. So layer C does not cover
the systems the paper's title is about, and the claimed unification holds only where every question
is decidable by enumeration anyway.

### O9. The framework has predicted nothing not already known

A unifying theory earns its place by saying something about a case its author had not already
solved. LANDSCAPE.md records that the canonical-execution decomposition has not yet produced an
exact result for a regime not already studied. The three-layer version has recovered existing
results and placed known CSP results. It has not stated a condition for an unstudied system and then
had it proved. Without that, "unification" is a filing system.

### O10. The distributed application is a change of vocabulary

Replace "registry" by "algebra", "repair" by "retraction", "event order" by "word in a trace
monoid", "settlement" by "Büchi emptiness", and the distributed-systems content disappears. CRDTs
are already known to converge because their operations commute or their merges form a semilattice;
the CALM and invariant-confluence lines already characterize coordination-freedom. Writing the same
conditions over a "governed state" does not make them results about distributed systems.

### O11. "One principle at three scales" is not a theorem

The repository's own documents concede that descent unifies only at the transition level. Across
scales the uses "form a hierarchy", the levels are independent (`descent_not_history`,
`history_not_descent`), layer C uses `N` as an observation rather than a map the steps pass through,
and descent "neither implies canonical settlement nor is implied by it". Layer B "is not a descent
condition" (THEORY.md). So one of the three layers is descent, one is a constraint problem and one
is recurrence. A paper titled "Convergence as descent" claims more than the mechanized results show.

### O12. "Exact" is cheap

Each exact condition is relative to a model the author defined, and many quantify over reachable
states (`cc_exact`: CC1 and CC2 at the states reachable from `s0`; `fed_exact_full`: C1R and C2R at
reachable witnesses). A condition of the form "every reachable peak joins" is close to a restatement
of "every order converges", and it is not a static check: to verify it you must explore the
reachable states, which is what convergence checking already does. Necessary-and-sufficient
conditions are easy to obtain when the condition may mention the reachable set.

## Part 2. The answers

For each objection: the answer with the smallest set of results that carries it, or the concession,
and how the paper should state the claim. "Direction" says which half of an exact result does the
work.

### A1. Descent is compatibility with a congruence: partly answered

**Conceded.** The shape is the textbook one. The repository states this before the objection can:
`descends_iff_respects` and `descends_iff_factors` (with `N` idempotent and `P` closed under `N`,
descent, respecting the kernel of `N` and factoring through `N` are equivalent), credited to Burris
and Sankappanavar in [coq/docs/interfaces.md](../coq/docs/interfaces.md). The word "descent" is the
repository's earlier usage (factoring through a quotient), not Grothendieck's.

**Answered.** The content is not the shape but two facts about it in each regime: which `N` and
which `P`, and that the condition is necessary there, not only sufficient. A congruence condition an
algebraist checks is a hypothesis chosen to make a quotient exist; here it is forced by convergence.

- `cc_exact` (single registry): unique normal forms for every event buffer at every state reachable
  from `s0` iff CC1 at reachable states and CC2, `rho_star (apply e sigma) = rho_star (apply e (rho
  sigma))` at every reachable invalid `sigma`. In its all-states form CC2 is descent along
  `rho_star` (`state_descent_iff_cc2`, `cc2_is_descends`). **Direction: necessary.** Convergence
  forces the descent conjunct; sufficiency is the older Newman argument.
- `dist_collapse_iff` (distributed model, a block `J` collapsed to one atom): the network converges
  iff the collapsed network converges and XU holds at every reached state, half-propagated states
  included. `dist_collapse_refuted` shows the descent conjunct cannot be dropped: XU fails at a
  reached state, the collapsed network converges, the original does not. **Direction: necessary.**
- `strict_not_necessary`: on the supply federation, XU (descent, `xu_is_descends`) holds, strict
  commutation (`Candidate`, the obvious strengthening, `candidate_is_commutes`) fails, and every
  reordering of events converges. With `candidate_implies_xu`, the quotient condition sits strictly
  between the naive sufficient condition and convergence.

**How the paper should state it.** "The condition is the standard compatibility of an operation with
the kernel of `N`. The results are which `N` and `P` each regime needs and that the condition is
necessary there." Do not present `DescendsOn` itself as a result.

### A2. Layer A is Mazurkiewicz traces plus Newman: partly answered

**Conceded.** In the commutation case layer A is the trace monoid: `swap_peq_perm` (adjacent swaps
generate `Permutation`) and the declared-pairs instance (`dg_tequiv_peq`, `dg_peq_tequiv`: the
generated equivalence is trace equivalence for `I`). P1 and P2 are elementary. `seeds_necessary`
needs no hypothesis, and `ppc_iff_whisk` makes P2 (`closure_exact`) the statement that a semantics
is invariant iff it agrees on the whiskered generator pairs with both sides admissible. THEORY.md
already credits Cartier and Foata, Mazurkiewicz, Burroni and Squier, Otto and Kobayashi, and uses
only the generated relation.

**Answered, in two places.**

- Not every instance is a trace monoid. The at-least-once generator `[a; a] ~ [a]` changes length,
  so its quotient is not a partially commutative monoid (`alo_exact_recovered`,
  `causal_alo_idem_recovered`). The live switch uses squares `[LA a; LS] ~ [LS; LT a]` that relabel
  letters across typed phases, and needs P1 with a nontrivial `Q` (past the switch), because the
  migration does not respect A's future (`det_live_recovered`, through `lv_seeds_live`).
  Admissibility (causal consistency, legal landings, typed phases) is not a property of a free or
  trace monoid either.
- The case where the generator check at a point fails. For a monoid action compatible with the
  observation, checking generators suffices (Howie). When the observation is not compatible with
  the steps it does not: `hw_seeds_insufficient` has every swap seed observationally equal at every
  point and invariance false, `hw_not_resp` shows the compatibility hypothesis `RespOn` is what
  fails, and `hw_closure_witness` is the separating pair (a seed continued by the reveal). This is
  the barrier's A-modulo-M case (`amodm_closure_recovered`), where the migration `M` is not
  compatible with A's steps.

Newman's lemma is not part of layer A; it is the A-C interface (`newman_bridge`), and the CC1 peak
part of `cc_exact` is not recovered by layer A at all (THEORY.md, layer A).

**Direction.** Both halves of P1 are proved, but the sufficient half carries the weight: a check on
seeds at their points suffices for invariance, under `RespOn` (`local_exact`) or with the
continuation closure (`closure_exact`). The necessary half (`seeds_necessary`) is a two-line proof.

**How the paper should state it.** "Layer A is a presented admissible path system in the sense of
string rewriting. P1 and P2 are elementary. What is done here is the presentation of each delivery
model (admissibility and generators), the proof that each presentation is adequate, and the
counterexample that fixes where the local check stops."

### A3. Layer B is Abramsky's global sections plus Jeavons: conceded as mathematics

**Conceded.** Every mathematical ingredient of layer B is prior work, as LANDSCAPE.md records in its
constraint-layer section: `section_iff_csp` is the specialization of Abramsky, Barbosa, de Silva
and Zapata 2017 to networks of maps; `pol_iff_commute` and `pol_gamma_iff` are the clone-theoretic
centralizer; `ac_exact` is a mechanized instance of Jeavons and Cooper 1995; `group_maltsev` is the
standard Mal'tsev term; `dnet_iff_sat` and `pol_dfam_iff` follow from Larose and Zádori 2006; the
three-element boundary is Broniek 2006. The dichotomy is cited, not mechanized.

**What remains, and it is placement, not mathematics.**

- The repository's section-existence question, for both section notions (reading A edges, reading B
  merges, with pins), is CSP(Gamma_F) for one template per transport family, proved against the
  definitions the rest of the development uses (`section_iff_csp`, `hsection_iff_csp`), so the
  general NP-complete cell (`net_section_iff_sat`) and the tractable cells sit in one classification
  indexed by the centralizer of the family (`pol_gamma_iff`).
- Layer B connects to convergence through the B-C interface, not on its own: a store is fixed by
  every edge repair iff it is a section iff it solves the CSP (`edge_fixed_iff_section`,
  `edge_fixed_iff_csp`), and the same for resolver repairs (`rupd_fixed_iff_csp`). That is what
  makes the CSP solutions the settled states of layer C (A5 below).
- The join-preserving line: transports that preserve join keep join as a polymorphism on any lattice
  (`semilattice_pol`, `joinhom_pol`), while monotone maps off the chain can have only projections
  (`pol_dfam_iff`). This is a reading of known facts in CRDT terms, not a result.

**How the paper should state it.** "Layer B applies the algebraic theory of CSP to the repository's
transport networks. It recovers known boundaries and contributes no tractability or hardness
result." Keep the LANDSCAPE.md sentence that the application of CSP algebra to replicated or
federated state was not found in the searches recorded there, as a search result.

### A4. Layer C is Emerson-Lei fair cycles: conceded for the kernel

**Conceded.** C1 (`C1_closed`, `C1_nn`, `C1_classical`) and C2 (`C2`, `C2_loops`) are the classical
fair-cycle characterization; `CanonicalRecurrence.v` says so in its header and makes no claim for
them.

**Answered for what was tested.** The experiment was compression, under a criterion stated before
the bridges were written ([coq/docs/recurrence.md](../coq/docs/recurrence.md): PASS if one kernel
gives short bridges for five named targets and the lasso language classifies oscillation, livelock
and ghosts; FAIL if regimes need obstruction notions that are not fair lassos). The originals were
proved by rank and monotonicity arguments, not by lassos. Result:

- One kernel proves the settlement statements of `chaotic_reaches_lfp`, `signed_settlement`,
  `signed_fidelity` and `FairFlushR` (`chaotic_reaches_lfp_lasso`, `signed_settlement_lasso`,
  `signed_fidelity_lasso`, `fairflush_lasso`, `fairflushR_lasso`), with no-bad-lasso arguments of 5
  to 11 lines over a shared toolkit of about 60 lines (`loop_floor`, `infl_loop_fixed`, `pigeon`).
- One notion classifies the failures (`lasso_classification`): the negation cycle (a bad
  non-singleton lasso, bad for every target), flip2 (`flip2_fair_lasso`, a bad fair lasso although
  the repair has one fixed point), the ghost (`copyback_ghost_lasso`, a settled singleton in the
  wrong fiber), multistability, and a fair raw oscillation inside one fiber where C2 fails and C1
  holds (`semantic_oscillation`).
- Fairness is what separates the cases: a bad cycle that never names one label refutes nothing
  (`nonfair_cycle_not_refuting`).

**How the paper should state it.** "C1 and C2 are the classical fair-cycle characterization. The
claim is that the repository's settlement results, proved by rank arguments, are instances of it in
their finite fragments, and that one notion (a bad fair lasso) covers every long-run failure met."

### A5. The interfaces are definitional: partly answered

**Conceded.** The positive halves are close to definitional. `erep_fixed_iff` is an unfolding;
`edge_fixed_iff_section` lifts it over a network; `newman_bridge` is `peak_exact` (Newman,
localized) plus `NFDec` for the unique-normal-forms half; `cr_peaks`, `cr_unf` and
`natural_maps_sections` are textbook.

**Answered.** The content of each interface is where it stops and what replaces it there, and those
parts are not definitional.

- A-C. Fair settlement does not replace termination in Newman's lemma
  (`four_point_fair_not_confluent`: Klop's four-point system in C's form, every peak joins, every
  fair run settles, two normal forms below `kb`). The exact replacement: under C2 every reachable
  moving loop starves a label (`fair_starves`, no finiteness used), so on a finite state type
  termination is exactly the absence of a reachable starved loop (`fair_sn_exact`), and then Newman
  applies (`fair_newman`, non-vacuous by `or_fair_newman`). The condition is exact for termination,
  not confluence (`drop_starved_confluent`). **Direction:** the sufficient half of `fair_sn_exact`
  (no starved loop gives termination) is the one `fair_newman` uses; the content is `fair_starves`.
- B-C. A unique B-solution does not give settlement (`flip2_unique_solution_livelock`). Under C2,
  canonical settlement at `c` holds iff every reachable B-solution lies in the fiber of `c`
  (`settled_canon_exact`). No B-solution refutes raw settlement (`no_solution_no_settlement`) but
  not canonical settlement (`no_solution_canon_settles`). **Direction:** the necessary half
  (`canon_needs_solutions`, hence `ghost_refutes` and `multistable`) needs no C2 and carries the
  refutations; the sufficient half needs C2.
- A-B. Strict naturality is not necessary for a fixed network (`natural_converse_fails`), is
  necessary edge by edge off self-loops (`natural_iff_edgewise`), and fails to be necessary on a
  self-loop (`selfloop_square_not_necessary`). The canonicalized form is the one convergence needs:
  XU is exactly that the event passes to the quotient by the repair (`xu_iff_respects`), and strict
  commutation is unnecessarily strong (`strict_not_necessary`).

**How the paper should state it.** "Three bridges, each with the counterexample that marks where it
stops." Present the A-C condition (`fair_starves`, `fair_sn_exact`) as the only interface with a
non-obvious exact condition, and say that its relation to the fair-termination literature (Lehmann,
Pnueli and Stavi 1981; Francez 1986) has not been checked at theorem level (Part 4).

### A6. The "predictions" are known results: conceded

**Conceded.** The chain cell is Jeavons and Cooper 1995; the diamond cell follows from Larose and
Zádori 2006 through the square encoding; every three-element poset is Broniek 2006 (LANDSCAPE.md,
"Monotone transports off the chain"). The search in
[research/predicted-hard-cell](predicted-hard-cell/search.py) and `TransportCSPHard.v`
(`dnet_iff_sat`, `pol_dfam_iff`, `dfam_minimal`) confirm and mechanize known results. Arriving at
a known result from the framework's side is a consistency check, not a prediction.

What is not covered by the literature found: the general statement that the monotone maps of a
finite poset give a tractable CSP exactly when the poset is a chain. It is neither proved here nor
found in the literature; the search table is evidence for the posets it lists. That is an open
question (Part 4), not a prediction the paper can claim.

**How the paper should state it.** Replace "predicts" by "places" or "recovers" for every known
cell, as the roadmap's item 3 already does.

### A7. Recovering the repository's own theorems is circular: partly answered

**Answered: not tautological.** Two checks, made on the Coq files for this review.

- Same statements. Each recovered theorem states the original's conclusion over the original
  module's own predicates. For example `causal_exact_recovered` in `PresentedExecution.v` is
  `GovernanceConverse.CausalConv step hb s0 <-> GovernanceConverse.CCR step hb s0`, which is
  `causal_exact`; `det_live_recovered` is `det_live_exact`'s `DLive <-> PermB (M s0) /\ DS1`;
  `tconv_exact_recovered` and `alo_exact_recovered` match `tconv_exact` and `alo_exact` the same
  way. The layer C bridges state the originals' conclusions with a finiteness hypothesis added (A8).
- Different proofs. In `PresentedExecution.v` the names of the original exact theorems occur only in
  comments; the recovered proofs go through `local_exact`, `local_exact_all` or `closure_exact`. In
  `CanonicalRecurrence.v` the settlement bridges do not call `chaotic_reaches_lfp`,
  `signed_settlement` or `signed_fidelity`; they go through C1 and C2. One bridge uses its original
  for a fact about the example, not for the settlement claim: `copyback_ghost_lasso` reads the
  least fixed point's value from `copyback_ghost`. The recoveries do reuse shared infrastructure,
  the adequacy lemmas of the earlier kernel (for example `CanonicalInstances.causal_adequate`) and
  word lemmas such as `GovernanceConverse.causal_prefix`; THEORY.md puts the adequacy cost for
  at-least-once at about 250 lines.

**Conceded.**

- The kernels were written after the targets were known, by the same author. Recovery shows that one
  development compresses into two kernels; it is not independent confirmation, and it adds no
  evidence that the original theorems are true (they were already proved).
- Layer C was run against a criterion stated in advance (A4). The repository does not record a
  comparable advance criterion for layer A.
- The roadmap's "recovers separately proved exact results as instances of one theorem" is accurate
  only with the adequacy work counted: the generic theorem is short, the per-model presentation is
  not.

**How the paper should state it.** "One theorem pair proves these statements, which were earlier
proved directly, with the per-model cost shown." Give bridge sizes and leaks in a table. Do not
count recoveries as evidence of explanatory power beyond compression, and do not write "explains".

**Update (2026-10-11).** Outside theorems have since been recovered with every existing file frozen
and a pass criterion fixed in advance: Dijkstra's self-stabilization (layer C, passed,
`SelfStabilization.v`), invariant confluence (layer B, passed, `InvariantConfluence.v`) and CRDT
strong eventual consistency (layer A, partial: operation-based passed, state-based needs a merge of
two replica states, `CRDTRecovery.v`). The CRDT test is the weakest of the three, because the
repository already had CRDT regimes before the kernels were written. These answer the circularity
objection in part: some of the structure transports beyond the results it was built from. They are
still recoveries of known results.

### A8. The finiteness and LPO leaks remove the cases that matter: partly conceded

**Conceded.** Every layer C recovery assumes a listed state type; the originals assume finite height
and allow infinitely many states, so the recoveries are of the finite fragments
([coq/docs/recurrence.md](../coq/docs/recurrence.md), "Leaks"). `chaotic_reaches_lfp_lasso` also
takes a finite label list. `fair_sn_exact` and `fair_newman` need a finite state type. The strong
form of C1 is not provable axiom-free in general: `lpo_leak` gives a four-state instance with no bad
fair lasso on which strong settlement implies LPO. Infinite networks are a design exclusion (X4),
and continuous state is a fundamental limit (ROADMAP.md).

**Answered, for the half that refutes.** Every refutation in layer C needs no finiteness:
`bad_lasso_refutes` and `C1_refutes` hold on any state type, so flip2, the ghost, the negation cycle
and multistability are refutations of convergence on any state space. `fair_starves` needs no
finiteness either. The constructive leak does not reach the recoveries, whose targets are fixed
points and so closed under the steps (`C1_closed`). **Direction:** the necessary direction (a bad
fair lasso refutes settlement) holds in general; the sufficient direction (no bad lasso gives
settlement) is the one that needs finiteness and, in the strong form for a fiber not closed under
the steps, classical logic.

The objection's last point, that real replicated state is infinite, applies to layer C only. Layers
A and B and the single-registry results are not restricted to finite state (`cc_exact` and the
well-founded variant in `GovernanceWF.v` allow infinite state spaces; the layer A recoveries carry
no finiteness hypothesis).

**How the paper should state it.** "Layer C is exact on finite state spaces. On finite-height
lattices with infinitely many states the original rank arguments remain the proofs; the lasso kernel
covers their finite fragments. Refutations hold on any state space."

### A9. The framework has predicted nothing not already known: conceded

**Conceded.** No statement about a regime the repository had not already studied has come out of the
three-layer framework and then been proved. LANDSCAPE.md records the same for the earlier
canonical-execution decomposition. The nearest case is `conv_quiet_exact` (gap 14): THEORY.md ("What
it is not yet") says the E, S and H decomposition shaped it, in a regime the repository had already
studied, with a different canonicalizer, not with A, B and C. The interface results
(`fair_sn_exact`, `settled_canon_exact`, `strict_not_necessary`) came out of the framework, but they
are statements about the framework's own interfaces, and `fair_sn_exact` has not been checked
against the fair-termination literature.

**How the paper should state it.** Make no predictive claim. State the framework as a compression of
the repository's exact results and a classification of its failures, and list the absence of an
outside prediction as an open question (Part 4).

**Update (2026-10-11).** Still conceded. The kernels are frozen until one prediction, committed
before its proof, is tested; the protocol and the recorded boundaries are in
[research/predictions/README.md](predictions/README.md).

**Update (2026-10-11, P2 scored).** Conceded in part. One prediction, committed before any test
([P2.md](predictions/P2.md)), passed: in the marriage market, a unique stable matching does not
stop blocking-pair dynamics from cycling under a pair-fair schedule (`p2_pass`, a 3 by 3 instance;
about 27% of 4 by 4 markets with a unique stable matching cycle). The framework supplied the
question (the B to C distinction between `q1_unique_iff` and `flip2_unique_solution_livelock`), the
reason for the bet (the update is not monotone) and the refutation tool (`bad_lasso_refutes`); the
answer came from an exhaustive search and a proof of one instance. So the paper may say that the
framework made one correct preregistered prediction, a bet on which side of a proved distinction
a new system falls, and must not say that the framework computed the answer.

**Update (P3 scored).** A second prediction, of a different kind, passed ([P3.md](predictions/P3.md)):
a model of CouchDB's and PouchDB's revision handling, built through the at-least-once exact theorem
and state descent, computed on which delivery orders a deleted document comes back, and the running
software matched on all 216 scored observations. The paper may say the framework made two correct
preregistered predictions, a bet (P2) and a model computation checked against running software (P3),
and must still not say that it derives answers by theorem alone. An unscored scenario found a model
error, recorded in the outcome.

### A10. The distributed application is a change of vocabulary: partly answered

**Conceded.** The mathematical form of each condition is classical (A1 to A4). Read as mathematics,
a regime result is a statement about a quotient, a CSP or a fair cycle.

**Answered.** The distributed content is in the model: which `N`, which states, which reorderings,
and these move the boundary, which a change of vocabulary cannot.

- The right condition is not the one the vocabulary suggests: strict commutation of an event with
  repair (`Candidate`) fails on the supply federation, yet every reordering converges, and descent
  holds (`strict_not_necessary`).
- Convergence of repair does not give convergence of events: `audit_counterexample` (two registries,
  C2 and local CC hold, C1 fails, two event orders give different states) and `cyc_counterexample`
  (on a monotone cycle whose repair is the least fixed point, two trace-equivalent sequences
  diverge).
- Composition fails in ways specific to the execution model: two blocks that each converge compose
  into one that does not (`compose_isolated_refuted`), and collapsing a block is exact only with
  descent at half-propagated states (`dist_collapse_iff`, `dist_collapse_refuted`).
- The CRDT relation is exact on the same transition representation: the compensation-free fragment
  is exactly the CRDT conditions, and the inclusion is strict (`crdt_boundary`,
  `compensation_free_exact`).

**How the paper should state it.** State each regime result as an exact theorem about a specified
execution model. Do not claim that the mathematics is specific to distributed systems; claim that
the models and the necessity counterexamples are.

### A11. "One principle at three scales" is not a theorem: conceded in part

**Conceded.** One definition covers the uses of `N` at one transition (`state_descent_is_descends`,
`cc2_is_descends`, `xu_is_descends`, `c1_is_descends`). Across scales there is no single theorem:

- transition to finite histories: descent of every event makes history descent of the raw runs the
  same question as history descent of the governed runs (`history_from_descent`,
  `path_history_from_descent`), and neither level implies the other (`descent_not_history`,
  `history_not_descent`);
- to infinite runs: C reads `N` only through one fiber (`canon_settles_fiber`); descent gives a
  reduction, the `N`-trajectory depends only on the `N`-image of the dynamics
  (`canon_settles_quotient_invariant`), and without descent that fails (`trajectory_needs_descent`);
- layer B is not a descent condition; it fixes the states A and C range over.

**What the evidence does support.** The roadmap's three tiers already put "a common principle" in
tier 2 (interpretation). The mechanized statement is narrower: one condition at the transition
level, a hierarchy with proved independence across scales, and a quotient-invariance link to layer
C.

**How the paper should state it.** In the main result, use "descent" only for the transition and
finite-history uses; say that layer C is linked by quotient invariance, not an instance; put the
three-scale reading in the interpretation tier, in those words. If the title keeps "Convergence as
descent", the abstract must say in its second sentence that descent unifies the transition-level
conditions and that the scales form a hierarchy.

### A12. "Exact" is cheap: partly answered

**Conceded.**

- "Exact" is relative to the model each result states (the roadmap's "Scope in every claim").
- Several exact conditions quantify over reachable states (`cc_exact`, `fed_exact_full`), so they
  are not static checks. The static forms gsm checks (per-state CC, XU) are sufficient conditions,
  not exact ones, and the paper must say so.

**Answered.** The exact conditions are not restatements of convergence, for two reasons.

- They are local where convergence is global. Convergence quantifies over all orders, all histories
  or all fair runs; the exact conditions quantify over one generator at its point (`local_exact`),
  one peak (`newman_bridge`, `cc_exact`), or one lasso (`C2_loops`). The reduction from the global
  to the local quantifier is the sufficient direction, and it carries the weight.
- Each hypothesis that makes the local check enough is shown needed by a counterexample:
  `hw_seeds_insufficient` (`RespOn`), `four_point_fair_not_confluent` (termination),
  `drop_starved_confluent` (the limit of `fair_sn_exact`), `natural_converse_fails` (strict
  squares), `lpo_leak` (the closed-fiber or classical premise), `no_solution_canon_settles` (raw
  versus canonical settlement).

The models are not chosen to make conditions exact: the delivery models (causal, at-least-once,
declared independence) are the standard ones, and where an earlier statement was wrong the
repository records the correction (for example `base_thm_footprint_cc1_refuted`).

**How the paper should state it.** Write "exact relative to the stated model" once, early, and give
for each core result the model, the reachable-state or static form, and the counterexample per
hypothesis.

## Part 3. What survives

### Claims the paper can make

Each survives every objection above when stated in these words.

1. **One transition-level condition, necessary where it appears.** One definition, `DescendsOn`,
   covers state descent, CC2, XU and C1 (`state_descent_is_descends`, `cc2_is_descends`,
   `xu_is_descends`, `c1_is_descends`); it is the textbook compatibility with the kernel of `N`
   (`descends_iff_respects`). It is forced by convergence in the single registry (`cc_exact`, with
   `state_descent_iff_cc2`) and in distributed collapse (`dist_collapse_iff`,
   `dist_collapse_refuted`), and the strict form is sufficient and not necessary
   (`candidate_implies_xu`, `strict_not_necessary`).
2. **Layer A compresses the history results.** One theorem pair (`local_exact`, `closure_exact`)
   proves the statements of the exact history results with their original predicates, including
   three outside the trace monoid (`alo_exact_recovered`, `det_live_recovered`,
   `amodm_closure_recovered`), at a stated per-model adequacy cost; the hidden-write example fixes
   where the local check stops (`hw_seeds_insufficient`, `hw_not_resp`, `hw_closure_witness`).
3. **Layer C compresses the settlement results in their finite fragments.** One fair-lasso kernel
   (`C1_closed`, `C1_nn`, `C2`, `C2_loops`) proves the settlement statements with short bridges
   (`chaotic_reaches_lfp_lasso`, `signed_settlement_lasso`, `signed_fidelity_lasso`), classifies
   every long-run failure met (`lasso_classification`, `semantic_oscillation`), refutes on any state
   space (`C1_refutes`, `bad_lasso_refutes`), and has a stated constructive boundary (`lpo_leak`).
4. **Layer B places section existence in known CSP algebra and ties it to settlement.** Sections are
   CSP(Gamma_F) solutions with Pol(Gamma_F) the centralizer of the family (`section_iff_csp`,
   `hsection_iff_csp`, `pol_gamma_iff`); known boundaries are mechanized as instances (`ac_exact`,
   `dnet_iff_sat`); the solutions are exactly the fixed points of the repair dynamics
   (`edge_fixed_iff_csp`, `rupd_fixed_iff_csp`).
5. **Three interfaces, each with its stopping counterexample.** A-C: `newman_bridge`,
   `four_point_fair_not_confluent`, `fair_starves`, `fair_sn_exact`, `drop_starved_confluent`. B-C:
   `settled_canon_exact`, `flip2_unique_solution_livelock`, `no_solution_canon_settles`. A-B:
   `xu_iff_respects`, `strict_not_necessary`, `natural_converse_fails`.
6. **A hierarchy across scales, with proved independence.** `history_from_descent`,
   `descent_not_history`, `history_not_descent`; layer C linked by quotient invariance
   (`canon_settles_quotient_invariant`), not by instance (`trajectory_needs_descent`).
7. **Method.** Every cited name is a statement read in the Coq source; every result is axiom-free in
   the gate on three Coq versions. (Not a theorem; a property of the evidence.)

### Claims the paper should not make

- That descent, P1, P2, C1, C2, the CSP correspondence or the interfaces are mathematically
  original. They are classical or elementary, and credited.
- That the three layers are three instances of one principle. Only the transition-level uses are
  one definition; B is not a descent condition; C uses `N` as an observation.
- That the framework predicts. The "predicted" cells are known (A6), and no outside prediction has
  been made (A9).
- That the recoveries confirm anything or explain the originals. They compress them.
- That layer C covers the originals in full generality. It covers their finite fragments.
- That a unique solution or a unique fixed point gives convergence
  (`flip2_unique_solution_livelock`), or that arc consistency decides existence without the chain
  and monotonicity hypotheses (`ac_needs_mono`).
- That the static checks gsm runs are exact. They are sufficient forms of reachable-state
  conditions.
- "New", "first" or "novel" anywhere, without a literature check recorded in LANDSCAPE.md.

### The main text's evidence set, against the roadmap's five items

The roadmap's list ([ROADMAP.md](../docs/ROADMAP.md#the-core-evidence-the-main-text)) is close to
right. Recommended changes, each tied to an objection:

1. **Descent at one transition.** Keep. **Add** `cc_exact` (with `state_descent_iff_cc2`) as the
   necessity anchor; without it the item shows only that four conditions have one shape, which is
   O1. **Add** the scale limits (`descent_not_history`, `history_not_descent`,
   `canon_settles_quotient_invariant`, `trajectory_needs_descent`), because O11 is answered only by
   stating the hierarchy precisely. `dist_collapse_iff` can go to supporting material.
2. **Layer A.** Keep `local_exact`, `closure_exact`, `causal_exact_recovered`,
   `amodm_closure_recovered`, `det_live_recovered` and the hidden-write counterexample (name it:
   `hw_seeds_insufficient`). **Replace** `tconv_exact_recovered` by `alo_exact_recovered`: the
   declared-pairs case is a trace monoid and adds nothing against O2 that the causal case does not,
   while the duplicate landing is the clearest instance outside the trace monoid. Show the adequacy
   cost next to each recovery (O7).
3. **Layer B.** Keep `edge_fixed_iff_csp`, `section_iff_csp`, `ac_exact`, `dnet_iff_sat`. **Add**
   `pol_gamma_iff` (the centralizer is what indexes the classification). **Move** `pol_dfam_iff` to
   supporting material: it strengthens a known hardness result and does not change the argument.
4. **Layer C.** Keep. **Add** one positive bridge (`signed_settlement_lasso`): the roadmap's item
   lists only the kernel and failure examples, so it does not show the compression that answers O4.
   **Add** `C1_refutes`, so the finiteness leak is stated against the half that does not need
   finiteness (O8).
5. **The interfaces.** Keep. **Add** `fair_starves` (the content of the A-C interface, with no
   finiteness), `drop_starved_confluent` (where it stops) and `settled_canon_exact` (the exact B-C
   statement under C2); the roadmap names the counterexamples but not these.

**Order.** Descent (1), layer A (2), layer C (4), layer B (3), interfaces (5). Layers A and C carry
the compression evidence; layer B is mostly recovery of known CSP results and enters the argument
through the B-C interface, so it reads best directly before the interfaces. The central figure is
unchanged.

## Part 4. Open questions the review raised

These are questions the repository cannot answer now. None is a proposal to start a proof.

1. **An outside prediction.** Is there a regime not yet studied here for which the framework states
   a condition before it is proved, and the condition then turns out exact? Nothing in the
   repository is of that kind (A9). Since: the kernels are frozen and a prediction protocol is in place
   ([research/predictions](predictions/README.md)); two predictions have been scored and passed: P2, a bet, and P3, a model computation checked against running software (A9); a prediction derived by theorem alone is still open.
2. **An outside recovery.** Every recovery is of a theorem proved in this repository. Whether the
   kernels prove a published convergence theorem from outside it, with that theorem's own
   definitions, has not been tried.
   Since tried for CRDT strong eventual consistency with the kernels frozen (`CRDTRecovery.v`): op-based
   SEC (Shapiro et al. 2011, Gomes et al. 2017) is a short bridge with `N = id`; state-based SEC is
   recovered, but the binary merge of two replica states leaks out of the kernels (PARTIAL).

   Tried since for invariant confluence (Bailis et al. 2014), kernels frozen: the polymorphism
   direction, the exact reachable form and Theorem 1 in a replica model are recovered; necessity
   for an arbitrary system leaks (`coq/InvariantConfluence.v`, THEORY.md).

   definitions, has not been tried. Since tried: Dijkstra's self-stabilization, recovered with the
   kernels frozen (PASS on its preregistered criterion; the unfair daemon needs a generic adapter
   outside the kernels): `coq/SelfStabilization.v`, [THEORY.md](../docs/THEORY.md#an-outside-theorem-self-stabilization).
3. **Fair termination.** Is `fair_sn_exact` (under fair settlement on a finite state type,
   termination iff no reachable loop starves a label) stated in the fair-termination literature
   (Lehmann, Pnueli and Stavi 1981; Francez 1986)? Not checked at theorem level.
4. **The poset boundary.** Do the monotone maps of a finite poset give a tractable CSP exactly when
   the poset is a chain? Search evidence for small posets and Broniek 2006 at size three; for
   arbitrary finite posets, neither a statement in the literature nor a proof (LANDSCAPE.md).
5. **Layer C beyond finite state.** Can a lasso-style kernel cover finite-height state spaces with
   infinitely many states, the generality of the originals, or is the rank argument needed there?
6. **A combined statement across scales.** The independence results rule out implication between
   the levels tested. Whether some conditional statement links all three scales, or the hierarchy is
   the most that holds, is open.
7. **Peaks in layer A.** The CC1 part of `cc_exact` is a peak of a rewrite system with compensation
   steps and is not recovered by layer A. Whether it belongs to layer A, or only to the A-C
   interface, is not settled.
8. **The cyclic frontier.** The framework locates where composition fails on cycles
   (`cyclic_lc_sound_fails`) but does not say what structure makes it exact there; this is the
   repository's open convergence question
   ([REGIME-AUDIT.md](../REGIME-AUDIT.md#the-cyclic-frontier)).
9. **CSP algebra and replicated state.** LANDSCAPE.md's searches found no prior application of the
   algebraic theory of CSP to replicated or federated state. That is a search result; the paper can
   report it only as such.
