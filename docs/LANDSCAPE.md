# Where normalization confluence sits (and what it moves)

If you already know CRDTs, consensus, or the saga pattern, this page places normalization
confluence relative to what you know: what problem it shares with them, what it does differently,
and which older ideas it connects. It is the "why is this new" companion to the papers and to
[REGIMES.md](REGIMES.md) (which is the "what applies to my system" lookup).

Role of this page: prior work, and where this work sits against it. What is proved per regime is
[REGIME-AUDIT.md](../REGIME-AUDIT.md); what is next is [ROADMAP.md](ROADMAP.md). The map of all
pages is [README.md](README.md).

## The shared problem: agreement without coordinating on every step

Many systems need replicas or processors that receive the same events, possibly in different
orders, to end up in the same state. The field has three broad ways to get there.

| Approach | How it prevents disagreement | Business invariants? | Coordination-free? | The catch |
|---|---|---|---|---|
| **Consensus** (Paxos, Raft, 2PC) | Agree on a total order before acting | Yes (you can reject) | No (a round trip per decision) | Latency; availability under partition |
| **CRDTs** (state/op-based) | Operations are designed to **commute** for all states | No | Yes | Cannot express "reject the overdraft": commutativity forbids operations that conflict |
| **Invariant confluence** (I-confluence) | Only run operation sets whose **every** ordering preserves the invariant | Yes, but only when free | Yes when I-confluent, else coordinate | Binary: an operation that can violate the invariant falls back to coordination |
| **Normalization confluence** (this work) | Operations **may violate** invariants; **compensation repairs**, and repaired results are order-independent (WFC + CC) | Yes | Yes | Repairs must terminate (WFC) and their results must commute (CC); you design the compensation |

The one-line difference: CRDTs make convergence work by forbidding operations that conflict;
I-confluence makes it work by forbidding orderings that would break the invariant; normalization
confluence lets operations conflict and break the invariant, then repairs, and proves the
repaired outcomes agree regardless of order.

## The gap it fills

CRDT operation-commutativity and I-confluence's "no repair needed" leave a gap: operations that
individually violate a business invariant (ship before pay, overdraw an account, exceed a cap)
but whose *repaired* results are order-independent. That gap is exactly where real business rules
live, and it is the space normalization confluence occupies. CRDTs are recovered as the special
case where compensation is never needed (a join-semilattice merge is monotone and validity is
trivial), so this is a strict generalization, not a competitor.

This recovery is now machine-checked, not just asserted: `coq/CRDT.v` proves (axiom-free) that an
op-based CRDT's strong eventual consistency is an instance of the same order-independence lemma the
governance proof uses, that a state-based CRDT is the semilattice special case, and that the
inclusion is strict on the same transition representation: a convergent governed machine whose
raw transitions are provably neither kind of CRDT (its governed behavior is itself trivially a
CRDT, `witness_governed_constant`, so the separation is about representations). See
[SUBSUMPTION.md](SUBSUMPTION.md) for the precise statement and its scope.

## Precisely: CALM, I-confluence, and where compensation adds reach

The two landmark characterizations of coordination-freedom are CALM and I-confluence. Normalization
confluence relates to each precisely, and the relationship is cleanest stated through its own
lattice: the compensation-free fragment at the floor (see [SUBSUMPTION.md](SUBSUMPTION.md)) and the
CC-satisfiability frontier at the ceiling.

**CALM (Hellerstein's conjecture; Ameloot, Neven, Van den Bussche).** *A program has a
coordination-free, eventually-consistent implementation if and only if it is monotone* (adding an
input never retracts an output). The mechanism behind the "if" is that a monotone map on a lattice
has a least fixed point reached order-independently. NC's monotone regime
(`Federation.AllowMonotoneCycles`) is exactly that mechanism: a monotone repair/morphism operator
on an ordered shared domain whose least fixed point is the federated normal form, reached by any
fair schedule (Knaster-Tarski plus chaotic iteration). So NC's monotone regime *is* the CALM
monotone case, carrying business invariants on top. Two scoping notes: CALM is an iff for a
relational/Datalog computational model, whereas NC's monotone regime is a sufficient mechanism on
lattice-valued state; and CALM says nothing about compensation, which is where NC goes past it.

*Dissolving the apparent paradox (since CALM is an iff).* How can NC converge non-monotone,
invariant-violating operations coordination-free when CALM says coordination-free implies monotone?
Because the two "coordination-free" predicates guard different guarantees, so no iff is violated.
CALM's monotonicity is necessary and sufficient for computing a correct output INCREMENTALLY under
partial, obliviously-distributed input: for a non-monotone query a node cannot finalize an output
without knowing whether more input is still coming, and detecting that needs coordination. NC makes
no incremental-output claim. Its model is the CRDT model: every replica eventually receives the same
event set, and NC guarantees strong eventual consistency of STATE, all replicas reach the same valid
normal form for that set, order-independently (CC), with validity restored by compensation. NC
tolerates transient invalidity (states between an offending event and its repair) and requires full
eventual delivery; it never emits a finalized partial output. So CALM's obstruction, finalizing a
non-monotone output under partial input, does not arise in NC's model. NC is therefore not
coordination-free "in CALM's sense on a broader class"; it lives on a different axis (state
convergence, the CRDT axis) and offers a guarantee that is weaker in timing (eventual, full-delivery,
transiently invalid) in exchange for admitting the non-monotone compensable operations monotonicity
excludes. The two coincide exactly at the monotone regime, where NC's least-fixed-point mechanism is
literally CALM's. So the precise placement is orthogonality, not subsumption: NC completes the
CRDT/state-convergence axis (compensation-free CRDTs at the floor, compensable convergence above);
CALM classifies the query-computation axis; they meet at monotone-merge CRDTs.

**I-confluence (Bailis et al.).** *A set of operations is safely coordination-free under invariant
I if and only if it is I-confluent*: the operations preserve I and merges of I-valid states stay
I-valid. This is a necessary-and-sufficient characterization for the case where operations never
drive the state invalid. In NC's terms an I-confluent operation set is a machine that is
**compensation-free with a nontrivial invariant**: repair never fires because the invariant is
never violated (max repair depth 0). That puts I-confluence on NC's floor, next to CRDTs, with one
distinction that matters. In NC's replay model, compensation-free convergence is exactly the
op-based CRDTs: under causal delivery, a compensation-free system converges iff its concurrent
operations commute (`compensation_free_exact`, machine-checked). An I-confluent operation set whose
operations also commute is therefore in that fragment. One whose operations do not commute converges
by *merging* divergent states, a different mechanism that NC's replay model does not use. So the
floor is "repair never needed" (which `compensationFree` decides), its replay-convergent part is
exactly the op-based CRDTs, and I-confluence reaches the rest of it through merge rather than
replay.

**Where compensation adds reach.** NC's own contribution is the region *above* that floor:
operations that DO violate the invariant, made convergent by a repair that terminates (WFC) and
commutes (CC). Neither prior characterization reaches it. CALM-monotonicity cannot (the canonical
divergence counterexample, antitone negation, is exactly non-monotone), and I-confluence excludes
invariant-violating operations by definition. NC reaches it by two routes that match its topology
results: monotone repair converges on any graph (the CALM overlap), and non-monotone but compensable
repair converges on acyclic networks with resolvers, and on cycles under a computed coordination
(unique given an authority root, `coq/CoordinatedCycles.v`). The condition is exact, with a cost:
with canonical repair, unique normal forms from a start hold iff CC holds on the states reachable
from it (`cc_exact_from`), and for any enabledness iff critical pairs are joinable at reachable
configurations (`jc_exact`, `coq/GovernanceConverse.v`). These exact conditions quantify over
reachable states; the per-state CC that gsm checks is the cheap sufficient form. Whether some
compensation satisfies CC at all is CC-satisfiability, decided constructively by
`Registry.Synthesize` (the impossibility witness), rather than a closed-form logical property like
monotonicity or I-confluence.

**One-line placement.** Coordination-free convergence is achievable by monotonicity (CALM), by
invariant preservation (I-confluence), or by compensable repair (this work). The first two are the
compensation-free floor that NC recovers; NC's contribution is the compensating region above it, up
to the frontier where no repair converges and only coordination remains.

## Related systems: coordination-free invariant enforcement

CALM and I-confluence are the theory. A line of *systems* work attacked the same wall CRDTs hit in
practice (you cannot enforce uniqueness, a balance floor, or referential integrity with
commutativity alone) by adding invariants to eventually-consistent replication. Normalization
confluence is the verified relative of this lineage, and each system maps onto a piece of its
structure.

- **RedBlue consistency** (Li et al., OSDI 2012). Label each operation *blue* (commutes, runs
  coordination-free) or *red* (needs a global order). This is the floor/ceiling distinction drawn
  by hand: blue is the compensation-free, commutable region; red is above the CC-satisfiability
  frontier. gsm turns the labeling into a decision, `compensationFree` certifies the blue region
  and `Synthesize`'s impossibility witness certifies the red, both machine-checked. Where RedBlue
  asks the programmer to classify, gsm classifies and proves.

- **Explicit consistency: Indigo and IPA** (Balegas et al., EuroSys 2015; VLDB 2019) and **escrow
  transactions** (O'Neil, 1986). This is the closest prior art, and it must be positioned precisely
  rather than waved off. Indigo already includes invariant *repair*, an operation runs unrestricted
  and a repair restores the invariant afterward, alongside reservation/escrow as the pessimistic
  alternative. So the distinction is not "reservation versus compensation" (Indigo offers both); it
  is the convergence argument. Indigo and IPA ground correctness in operation *commutativity* plus
  invariant preservation: they require, or transform operations to be, commutative and invariant-
  valid, so convergence is the CRDT / I-confluence route. Normalization confluence instead admits
  genuinely *non-commutative*, invariant-*violating* operations and proves convergence by Newman's
  lemma on the *compensated* rewrite system, compensation commutativity (CC) is local confluence, not
  operation commutativity. That is the technical delta, together with the axiom-free mechanization,
  the synthesis of a convergent repair with an impossibility witness, and the federated cohomological
  obstruction, none of which appear in that line. (A prior-art sweep confirms it: Indigo, IPA, and the
  machine-checked CRDT strong-eventual-consistency framework of Gomes, Kleppmann, Mulligan and
  Beresford, 2017, contain no use of Newman's lemma or a rewriting-confluence convergence argument.)
  Reservation-style enforcement remains a candidate avoidance strategy for gsm where a lossy
  after-the-fact repair is unacceptable.

- **Bayou** (Terry et al., SOSP 1995). The earliest system with application-supplied repair: each
  write carries a dependency check (a query and its expected result) and a merge procedure that runs
  when the check fails. Its convergence argument is not the repair, though. In the paper's words, two
  features give eventual consistency: writes "are performed in the same, well-defined order at all
  servers", and "the conflict detection and merge procedures are deterministic". The order is fixed by
  a primary server that commits writes; tentative writes are undone and re-executed when a newly
  received write lands earlier in the log. So Bayou converges by agreeing on one order, which is
  coordination, and merge procedures need no property beyond determinism. The paper names the
  alternative and sets it aside: writes known to commute could run in any order, but "because Bayou's
  Write operations include arbitrary merge procedures, it is effectively impossible either to
  determine whether two Writes commute or to transform two Writes so they can be reordered".
  Normalization confluence is that determination for governed state: the conditions under which
  every order of events with their repairs reaches one state (CC1 and CC2, exact at reachable states),
  decided on gsm's finite combinator rules, so no primary and no rollback are needed when they hold.
  For rules written as arbitrary Go closures the determination stays out of reach, as Bayou said;
  gsm tests closures and does not prove them (see the fundamental limits in the roadmap).

- **IceCube** (Kermarrec, Rowstron, Shapiro and Druschel, PODC 2001). Reconciliation of divergent
  replica logs by search: the application classifies pairs of actions (safe to reorder, possibly
  conflicting, unsafe) and states preconditions, and the system explores candidate schedules,
  simulates them against the state, and selects one. Like Bayou, it makes the outcome
  order-independent by choosing an order; normalization confluence asks when the choice does not
  matter. Its pairwise classification is close in spirit to gsm's per-pair checks and declared
  independence, with the difference that gsm decides the classification instead of taking it from the
  application.

- **Operational transformation** (Ellis and Gibbs, SIGMOD 1989; Ressel, Nitsche-Ruhland and
  Gunzenhäuser, CSCW 1996). The collaborative-editing route: an incoming operation is transformed
  against the concurrent operations already applied, so that transformed operations commute. The
  standard correctness conditions are TP1 (two concurrent operations commute after transformation)
  and TP2 (transforming against two operations does not depend on their order), stated as sufficient
  for convergence. TP1 is a critical-pair condition on the transformed system, the same shape as CC1.
  The conditions proved hard to get right: the original dOPT algorithm was refuted by counterexample
  (Cormack, 1995), and establishing TP2 for published transformation functions became its own line of
  work, including machine-checked attempts (Imine, Molli, Oster and Rusinowitch, ECSCW 2003) and
  their later corrections. The difference in route: OT changes the operations so they commute;
  normalization confluence keeps the operations, lets them conflict, and requires the repair to make
  the outcome order-independent, with conditions that are necessary as well as sufficient.

- **ECROs** (De Porre et al., EuroSys 2021) and **Hamsaz** (Houshmand & Lesani, POPL 2019). Given a
  sequential data type and its invariants, use an SMT solver to find which operation pairs conflict
  and synthesize the coordination or restriction needed. This is the close cousin of
  `Registry.Synthesize`, which searches for a convergent compensation or proves none exists. The
  lesson gsm takes is concrete: these systems show an SMT backend makes the search practical at
  scale, exactly the extension gsm flags as future work (its current search is backtracking with
  forward-checking, decidable but worst-case exponential).

- **Katara** (Laddad et al., PLDI 2022). Synthesizes a CRDT from a sequential specification with
  verified lifting. Adjacent to gsm's synthesis but on the compensation-free floor: Katara produces
  a commuting design, gsm produces a compensating one (or reports impossibility).

**The through-line.** This lineage established that invariants can be enforced coordination-free,
using solvers and, in Hamsaz and Katara, machine-checked soundness for specific steps.
Normalization confluence's distinction is not that capability but the shape of its guarantee: an
axiom-free, end-to-end mechanized convergence theorem, a build-time exhaustive certification of a
concrete machine, and an extracted oracle that re-checks the implementation independently of the Go
that produced it. The claim to stake against this neighborhood is both function (non-commutative,
invariant-violating operations converge, proved by confluence) and provenance of trust.

**Foundational method, and the precise instantiation.** Two older bodies of work are the method-roots,
and naming them keeps the novelty claim precise. *Rewriting logic* (Meseguer; the Church-Rosser and
coherence theory of Duran and Meseguer, with Maude's Church-Rosser and Coherence Checker) is the
general framework in which a concurrent system is a rewrite theory and correctness is confluence plus
coherence, tool-checked. NC's governance rewrite system (event application plus invariant repair) is
an instance of that framework; convergence-by-confluence is not a new method here but that
established program specialized to the coordination-free-replication-with-compensation problem, which
rewriting logic did not itself target. NC's contribution over the framework is the specialization:
the WFC and CC conditions, the placement of CRDTs and I-confluence as its compensation-free floor,
and the federated cohomological obstruction. *Self-stabilization* (Dijkstra, 1974) is the root of
convergence to a legitimate state by local repair, and CRDTs were first presented at a
self-stabilization venue (SSS 2011). NC's repair to a valid normal form is in that spirit, but the
guarantees differ: self-stabilization converges from an arbitrary (faulted) state under a scheduler,
a recovery property over executions, whereas NC's guarantee is order-independence of a fixed event
set's application, a confluence property over orderings. So the precise placement is that NC inherits
its confluence method from rewriting logic and its repair intuition from self-stabilization, and its
own contribution is the specialization: that method applied to coordination-free replicated
convergence with non-commutative compensation, through the new conditions WFC and CC, with CC shown
necessary by counterexample and exact on reachable states; a verification calculus that reduces CC to per-event-pair checks;
CRDTs and I-confluence subsumed as the compensation-free floor; federation (the authority argument,
resolution operators on acyclic networks, monotone repair on any topology, and the necessity of
acyclicity and M1); the federation's normal forms as a limit, with compositionality as a corollary;
the federated cohomological obstruction; and minimal coordination, where a cycle basis suffices (invertible fragment)
and the exact minimum is a group feedback edge set number. The base theorem, the CRDT subsumption, the
limit and compositionality core, the cohomological criterion in the invertible fragment, the exact
converses (CC, causal delivery, and C1/C2 for event interleavings), at-least-once delivery, and the
soundness of coordinating non-monotone cycles from an authority root are mechanized end to end. So
are the paper's necessity counterexamples for acyclicity and M1 (`prop_cycle_necessary`,
`prop_m1_necessary`), the calculus beyond footprint disjointness (`base_thm_strong_absorption`,
`calc_decomp_normalizer`, `base_thm_product`), and minimum coordination with its hardness
reductions (`plan_min_exact`, `maxcut_reduction`; `lmin_root_set`, `lmin_reduction`). Cited, not
mechanized: the NP-completeness of 3-SAT and Max-Cut, and the fixed-parameter and planar results
for group feedback edge sets.

## Related work for the cohomological layer

The federated layer ([CATEGORICAL-STRUCTURE.md](CATEGORICAL-STRUCTURE.md), sections 10 and 10.1)
uses sheaf gluing, Čech `H^1`, holonomy, and a cycle basis of `|E| - |V| + 1` loops. The following
work uses the same mathematics or studies related objects.

- **Fundamental groups of graphs.** For a connected graph with a maximal tree `T`, `π_1` is free
  with one generator per edge outside `T` (Hatcher, *Algebraic Topology*, Cambridge University
  Press, 2002, Proposition 1A.2), and a finite connected graph has `π_1` of rank `|E| - |V| + 1`
  (ibid., Section 1.A, Exercise 3). `G`-labelings of the edges modulo relabeling at the vertices
  correspond to `Hom(π_1, G)` modulo conjugation, the holonomy classification of flat `G`-bundles.

- **Gain graphs and balance.** Zaslavsky ("Biased graphs. I. Bias, balance, and gains," *J. Combin.
  Theory Ser. B* 47(1), 1989, 32-52, Lemma 5.3) shows that a gain graph is balanced (every cycle has
  identity gain) iff it is switching-equivalent to the all-identity labeling. The `Z/2` case is
  Harary's balance of signed graphs ("On the notion of balance of a signed graph," *Michigan Math.
  J.* 2(2), 1953, 143-146). Both are now mechanized here in closed-walk form, not only cited:
  Harary's theorem for every finite signed graph, parallel edges and self-loops allowed
  (`harary_balance`: a switching to all-positive exists iff no closed walk carries an odd number
  of negative edges), and the gain-graph criterion for any group under the regular action, on any
  finite edge list with no spanning-tree premise (`holonomy_free_section`,
  `invertible_merge_is_holonomy`). The classical form with simple cycles is not mechanized.

- **Cohomology of global-section obstructions.** Abramsky and Brandenburger ("The sheaf-theoretic
  structure of non-locality and contextuality," *New J. Phys.* 13, 113036, 2011) characterize
  contextuality as the absence of a global section of a presheaf of local data. Abramsky, Mansfield
  and Barbosa ("The cohomology of non-locality and contextuality," QPL 2011, EPTCS 95, 2012, 1-14)
  give a Čech cohomology witness over an abelian presheaf, whose non-vanishing is sufficient for
  contextuality.

- **Topology in distributed computing.** Herlihy and Shavit ("The topological structure of
  asynchronous computability," *J. ACM* 46(6), 1999, 858-923), Borowsky and Gafni ("Generalized FLP
  impossibility result for t-resilient asynchronous computations," STOC 1993, 91-100), and Saks and
  Zaharoglou ("Wait-free k-set agreement is impossible: the topology of public knowledge," STOC
  1993, 101-110; *SIAM J. Comput.* 29(5), 2000) characterize wait-free task solvability through
  simplicial complexes. Herlihy, Kozlov and Rajsbaum (*Distributed Computing Through Combinatorial
  Topology*, Morgan Kaufmann, 2013) is the textbook account; Felber, Hummes Flores and Rincon
  Galeana ("A sheaf-theoretic characterization of tasks in distributed systems," arXiv:2503.02556,
  2025) recast task solvability with cellular sheaves.

- **Cycle consistency and group synchronization.** Singer ("Angular synchronization by
  eigenvectors and semidefinite programming," *Appl. Comput. Harmon. Anal.* 30(1), 2011, 20-36)
  recovers group elements from noisy pairwise offsets. Zach, Klopschitz and Pollefeys
  ("Disambiguating visual relations using loop constraints," CVPR 2010, 1426-1433) and Huang and
  Guibas ("Consistent shape maps via semidefinite programming," *Comput. Graph. Forum* 32(5), SGP
  2013) use the condition that maps composed around a cycle return the identity.

- **Applied sheaf theory.** Goguen ("Sheaf semantics for concurrent interacting objects," *Math.
  Struct. Comput. Sci.* 2, 1992, 159-191) models object behaviours as sheaves and composes them by
  limits. Ghrist (*Elementary Applied Topology*, CreateSpace, 2014) and Hansen and Ghrist ("Toward a
  spectral theory of cellular sheaves," *J. Appl. Comput. Topol.* 3, 2019, 315-358) develop cellular
  sheaves and their cohomology. Robinson ("Sheaves are the canonical data structure for sensor
  integration," *Inf. Fusion* 36, 2017, 208-224) uses sheaf cohomology to measure consistency
  between data sources.

- **Formalizations.** mathlib's Nielsen-Schreier development proves that the vertex group of a free
  groupoid is freely generated by the arrows outside a spanning arborescence (`endIsFree`), and
  mathlib proves a finite tree's edge count (`SimpleGraph.IsTree.card_edgeFinset`). A standalone
  Lean 4 development, not part of mathlib (`github.com/Arthur742Ramos/finite-graph-fundamental-group`),
  proves that `π_1` of a finite connected graph is free of rank `|E| + 1 - |V|`. A search of mathlib,
  the Rocq graph-theory library (Doczkal and Pous) and the HoTT library found no formalization of
  the gain-graph balance criterion or of `H^1` as tuples of fundamental holonomies modulo
  simultaneous conjugation (a search result, not a proof of absence). This repository now
  mechanizes both: `H1_classification` and, for balance, `harary_balance` and
  `holonomy_free_section`.

**What the cohomological layer contributes.** The topology underneath is classical and credited as
such: `π_1` of a connected graph is free of rank `|E| - |V| + 1` (Hatcher), and a group-labeled graph
is balanced, switching-equivalent to the identity labeling, iff every cycle has trivial holonomy
(Harary for `Z/2`; Zaslavsky for an arbitrary gain group; both proved here in closed-walk form,
`harary_balance`, `holonomy_free_section`). On that base, this work contributes the
following. Labels refer to the companion paper,
[`categorical_structure_of_federated_convergence.tex`](../categorical_structure_of_federated_convergence.tex).

1. **The application to federated convergence.** Sections are convergence certificates of
   normalizers over subsystem overlaps, and the sheaf's gluing axiom is exactly the resolver
   conditions R1 (source-determinacy) and R2 (validity preservation) (`prop:gluing`). The
   counterexample showing that agreement on valid values does not suffice is mechanized
   (`gluing_order_dependent`, `coq/Cohomology.v`).
2. **The obstruction theorem for cyclic federations.** A global convergent section around a cycle
   exists iff the cycle's loop composite has a reachable fixed point, and the composite is the
   witness when it does not (`thm:obstruction`). gsm implements it as `Federation.DiagnoseCycle`.
3. **Minimal coordination.** In the invertible fragment, coordinating a cycle basis suffices for a
   convergent implementation that stays coordination-free everywhere else (`prop:minimal`), and the
   exact minimum is the group feedback edge set number of the holonomy-labeled nerve, which the best
   coordination plan attains (`plan_min_exact`); NP-hardness is a mechanized reduction from Max-Cut
   (`maxcut_reduction`), and the fixed-parameter and planar results are cited. The companion paper reports finding no prior work that
   localizes the coordination requirement to a cycle basis. Soundness of the holonomy-minimal plan
   (drive along a spanning tree from an authority root, keep balanced non-tree edges as checks,
   coordinate the unbalanced ones) is mechanized: a unique normal form given the root
   (`coordinated_sound`, `coq/CoordinatedCycles.v`).
4. **The `S_3` separation.** On the theta graph the non-abelian minimum is 2 and the abelianized
   minimum is 1, so sizing coordination by an abelianized invariant is unsound: it under-provisions.
   Mechanized end to end (`theta_separation`, `coq/CohomologyMin.v`).
5. **Axiom-free mechanization in the invertible fragment.** The criterion and the classification
   are machine-checked on an arbitrary finite group-labeled graph, abelian or not: a section exists
   iff the labeling is a coboundary, iff every fundamental cycle has trivial holonomy; `H^1` is the
   tuples of fundamental holonomies modulo simultaneous conjugation, with `|E| - |V| + 1`
   generators (`coq/Cohomology.v`, `coq/CohomologyGraph.v`, `coq/CohomologyMin.v`).

These results sit on a convergence framework whose extracted, axiom-free checker re-certifies, in
process, every registry machine gsm returns (from `Build`, `SynthesizeWith`, and `BuildCompositional`
per footprint component; a federation's components are each built by `Build`). Scope: the
cohomological classification is for the invertible fragment. Since mechanized: sheaf gluing on the
registry-level site (`sheaf_iff_refines`, `cert_sheaf`), `H^1` on the nerve as a 2-complex with the
triangle relations (`nerve_H1_classification`, `nerve_H1_Z2_count`), and the non-invertible case,
where `thm:obstruction` is a fixed-point condition rather than group cohomology
(`thm_obstruction_general`, `root_set_criterion_graph`). Still at the paper level: `prop:gluing` on
the companion paper's variable-level and monotone-overlap site. Cited: the complexity results for
group feedback edge sets.

## Related work for the constraint layer

Layer B of the theory ([THEORY.md](THEORY.md#static-consistency-as-csp)) asks whether a transport
network has a consistent state at all. `TransportCSP.v` states the answer as a constraint
satisfaction problem: each edge `(u, v, f)` is the binary relation `{(x, f x)}`, each pinned vertex
a unary relation `{c}`, a k-ary resolver merge the `(k+1)`-ary graph of the merge map, and the
sections of the network are exactly the solutions of the instance over the template Gamma_F of
the transport family `F` (`section_iff_csp`, `hsection_iff_csp`). An operation is a polymorphism
of the graph of `f` iff it commutes with `f` (`pol_iff_commute`), so Pol(Gamma_F) is the set of
operations commuting with every map of `F` and fixing the pins (`pol_gamma_iff`). The file then
places three families at known points of the CSP classification: group translations (Mal'tsev,
`group_maltsev`), the 26-map family of the 3-SAT reduction (NP-complete, `hard_family_csp`), and
monotone maps on a finite chain (semilattice and majority polymorphisms, `chain_pol`; arc
consistency decides, `ac_exact`). The question for this section is how much of this was already
connected in the literature. Every work below was checked at least at its abstract. Theorem-level
claims were read in the paper for the Abramsky papers of 2013 to 2017, Ó Conghaile 2022, Ghrist and
Riess 2022, Huntsman, Robinson and Huntsman 2024, Deville and Van Hentenryck 1991, Jeavons, Cohen
and Gyssens 1997, Jeavons, Cohen and Cooper 1998, Cohen and Jeavons 2006, Machida 2010 and Stevens
2020; Jeavons and Cooper 1995 is described through those restatements, and the classical results
already cited elsewhere in this file are described as the literature states them.

**Global sections and CSP solutions: the sheaf-theoretic contextuality line.** This is the closest
prior connection, and it is more than a decade old.

- Abramsky and Brandenburger ("The sheaf-theoretic structure of non-locality and contextuality,"
  *New J. Phys.* 13, 113036, 2011), already cited above, read an empirical model as a presheaf of
  local data over a cover of measurement contexts and contextuality as the absence of a global
  section. Abramsky ("Relational databases and Bell's theorem," in *In Search of Elegance in the
  Theory and Practice of Computation*, LNCS 8000, Springer, 2013, 13-35) identifies a global section
  of a possibilistic model with a universal relation of a database instance. Abramsky ("Contextual
  semantics: from quantum mechanics to logic, databases, constraints, and complexity," *Bull.
  EATCS* 113, 2014, 137-163, footnote 10) notes that a Kochen-Specker model over a finite outcome
  set is a constraint satisfaction problem and that contextuality means it has no solution.
- Abramsky, Barbosa, Kishida, Lal and Mansfield ("Contextuality, cohomology and paradox," CSL 2015,
  LIPIcs 41, 211-228) list constraint satisfaction as one instance of the same picture (local data
  are the constraints; no global section is no solution), and treat the Liar cycle as the Boolean
  equations `x1 = x2, ..., x(n-1) = xn, xn = not x1`: any `n - 1` of them are consistent and all `n`
  are not. That is a `Z/2`-labeled cycle with odd holonomy, the shape of `ac_needs_mono`'s negation
  triangle and of Harary balance (`harary_balance`). Their All-vs-Nothing arguments are local
  consistency and global inconsistency of linear equations over a ring, witnessed by Čech
  cohomology.
- Abramsky, Barbosa, de Silva and Zapata ("The quantum monad on relational structures," MFCS 2017,
  LIPIcs 83, 35:1-35:19, Propositions 11 to 13) state the correspondence as a theorem: CSP solutions
  correspond one to one with homomorphisms between the associated structures, and the consistent
  global assignments of an empirical model correspond one to one with the solutions of a CSP built
  from its support tables, so strong contextuality is unsatisfiability. This is the closest prior
  statement to `section_iff_csp`.
- Abramsky, Gottlob and Kolaitis ("Robust constraint satisfaction and local hidden variables in
  quantum mechanics," IJCAI 2013, 440-446) use constraint satisfaction to show that deciding
  whether a relational model has a local hidden-variable model is NP-complete (for `n >= 2`
  parties), through a "robust" variant of CSP (every compatible partial assignment of a given size
  extends to a solution). Abramsky, Dawar and Wang ("The pebbling comonad in finite model theory,"
  LICS 2017, 1-12, Section 8) relate strong k-consistency to contextuality, with a system of `Z/2`
  equations that is locally consistent and globally inconsistent.
- Polymorphisms enter this line only for quantum relaxations. Atserias, Kolaitis and Severini
  ("Generalized satisfiability problems via operator assignments," *J. Comput. System Sci.* 105,
  2019, 171-198) classify the Boolean constraint languages for which satisfiability by operator
  assignments differs from Boolean satisfiability, in Schaefer's framework; Ciardo ("Quantum
  advantage and CSP complexity," LICS 2024, Article 23) proves that quantum advantage for
  homomorphism problems is governed by a minion, the structure that captures polymorphism
  identities.

How close: the statement "global sections are CSP solutions" is in this line in general form, with
arbitrary relations on arbitrary contexts. `section_iff_csp` is its specialization to one kind of
presheaf, a network of maps over a graph (contexts are edges, the local relation on an edge is the
graph of its map, pins are unary relations), and that specialization is what turns the template
into Gamma_F, one fixed template per transport family, whose polymorphisms are the operations
commuting with the family. The contextuality papers do not single out functional constraints as a
class (the Liar cycle is one example of them) and, apart from the quantum-relaxation work, do not
use the polymorphism side. What `TransportCSP.v` adds here: the specialization to this repository's
two section notions (reading A edges and reading B merges), proved in Coq. It does not add a
contextuality result or a more general form of the correspondence.

**CSP as global sections, and cohomological local consistency.**

- Ó Conghaile ("Cohomology in constraint satisfaction and structure isomorphism," MFCS 2022,
  LIPIcs 241, 75:1-75:16) shows that CSP itself is the existence of a global section of a presheaf
  `H_k(A, B)` of local homomorphisms, that k-consistency computes a greatest sub-presheaf, and that
  a Čech-cohomological refinement of k-consistency solves systems of equations over every finite
  ring. Abramsky ("Notes on presheaf representations of strategies and cohomological refinements of
  k-consistency and k-equivalence," arXiv:2206.12156, 2022) represents positional k-pebble
  strategies as presheaves, the same objects as the Abramsky-Brandenburger models.
- How close: this is the converse direction (any CSP read as a sheaf problem), in full generality.
  It parallels this repository's split, cohomology where transports are invertible and local
  consistency on monotone chains, but the parallel is at the level of method, not of results:
  `TransportCSP.v` contributes nothing to cohomological k-consistency, and its group case is the
  classical binary-translation case where the `H^1` test is already exact
  (`section_iff_coboundary`).

**Cellular sheaves and lattice-valued sections.** A transport network is a cellular sheaf of sets
on its graph (stalk `D` on every vertex and edge, restriction `f` from the tail of an edge and the
identity from its head), and a section is a global section, `H^0`. The cellular-sheaf work cited
above (Hansen and Ghrist 2019; Robinson 2017; Felber, Hummes Flores and Rincon Galeana 2025) uses
that language; none of it uses polymorphisms.

- Ghrist and Riess ("Cellular sheaves of lattices and the Tarski Laplacian," *Homology Homotopy
  Appl.* 24(1), 2022, 325-345, Theorem 3.1 and Theorem 3.2) take sheaves valued in lattices with
  Galois-connection restriction maps, show that the global sections are exactly the fixed points of
  `id ∧ L` for their Tarski Laplacian `L`, and that on finitely many cells with stalks satisfying the
  descending chain condition the iteration reaches a section in finitely many steps, with consensus
  and distributed optimization as applications. This is the closest sheaf-side analogue of
  `ac_exact` (a monotone fixed-point computation whose limit is a section), but the settings differ:
  their iteration acts on one lattice value per cell, needs restriction maps with adjoints, and on
  complete stalks always has a section; `ac_exact` acts on sets of chain values, allows pins, and
  decides existence, which can fail. We have not derived `ac_exact` from their theorems.
- Huntsman, Robinson and Huntsman ("Prospects for inconsistency detection using large language
  models and sheaves," arXiv:2401.16713, 2024, Section 3.1) sketch a cellular sheaf of a CNF formula
  whose global sections are its satisfying assignments, and attribute the remark that the solutions
  of a CSP form a sheaf to Srinivas ("A sheaf-theoretic approach to pattern matching and related
  problems," *Theoret. Comput. Sci.* 112(1), 1993, 53-97; not read here beyond the citation).

**Constraint networks and local consistency.**

- Montanari ("Networks of constraints: fundamental properties and applications to picture
  processing," *Inform. Sci.* 7, 1974, 95-132) introduces networks of binary constraints; Mackworth
  ("Consistency in networks of relations," *Artificial Intelligence* 8(1), 1977, 99-118) gives arc
  consistency; Freuder ("A sufficient condition for backtrack-free search," *J. ACM* 29(1), 1982,
  24-32) shows that arc consistency makes search backtrack-free on tree-structured networks. A
  pinned transport network is a binary constraint network in Montanari's sense, and
  `section_iff_csp` is, mathematically, the unfolding of that observation: a section is a
  homomorphism from the network to the template.
- Deville and Van Hentenryck ("An efficient arc consistency algorithm for a class of CSP problems,"
  IJCAI 1991, 325-330) and Van Hentenryck, Deville and Teng ("A generic arc-consistency algorithm
  and its specializations," *Artificial Intelligence* 57(2-3), 1992, 291-321) give `O(ed)` arc
  consistency for "functional" constraints (at most one support in each direction, a partial
  bijection on the domain) and "monotonic" ones (`C(v, w)` implies `C(v', w')` for `v' <= v`,
  `w' >= w`), and prove that arc consistency with node consistency decides CHIP's basic constraints
  (domain constraints and `aX != b`, `aX = bY + c`, `aX <= bY + c`, `aX >= bY + c` with nonnegative
  constants). The graph of a lossy monotone map is neither functional nor monotonic in their sense,
  so their theorem does not cover `ac_exact` directly.
- Jeavons and Cooper ("Tractable constraints on ordered domains," *Artificial Intelligence* 79(2),
  1995, 327-339) identify the max-closed constraints on a totally ordered domain as tractable.
  Jeavons, Cohen and Gyssens ("Closure properties of constraints," *J. ACM* 44(4), 1997, 527-548,
  Theorem 5.13 and Example 5.15) generalize this to any semilattice (ACI) polymorphism `u`: after
  local consistency is enforced, either a domain is empty or assigning `u(D(v))` to every variable
  is a solution; the proof uses only that each constraint, restricted to the remaining domains,
  supports every remaining value, and the paper notes that the CHIP basic constraints are max-closed. Cohen and Jeavons
  ("The complexity of constraint languages," in Rossi, van Beek and Walsh (eds.), *Handbook of
  Constraint Programming*, Elsevier, 2006, Chapter 6, Proposition 37 and Example 39) state the
  result in the form used here: a semilattice polymorphism means generalised arc consistency
  decides the instance, max-closed constraints included. The graph of a monotone map on a chain is
  min-closed and max-closed (`chain_pol`), so **`ac_exact` is a mechanized instance of this
  classical result** (the binary, min-closed case, with pins as unary constraints and the minimum
  of each arc-consistent domain as the witness), not a new tractability result. Its pass bound
  (`ac_pass_bound`) is the usual counting argument for arc consistency, and `ac_needs_mono` (a
  negation triangle on `{0, 1}` that passes arc consistency and has no section) is the classical
  example that arc consistency is incomplete in general.
- Jeavons, Cohen and Cooper ("Constraints, consistency and closure," *Artificial Intelligence*
  101(1-2), 1998, 251-265, Corollary 3.6) show that a near-unanimity polymorphism of arity `r` makes
  strong `r`-consistency decide the instance; a majority polymorphism is the case `r = 3`. This is
  the cited source of tractability for `median_family`, of which only the commutation is
  mechanized.

**Groups, gain graphs and permutation constraints.**

- Under the regular action, a group-labeled network is a gain graph (Zaslavsky 1989; Harary 1953
  for `Z/2`, both above) and a section is a switching to the identity labeling. In CSP terms each
  edge relation is the graph of a left translation, and `x y^-1 z` is a Mal'tsev polymorphism of all
  of them (`group_maltsev`), which is the standard Mal'tsev term of a group. Feder and Vardi ("The
  computational structure of monotone monadic SNP and constraint satisfaction: a study through
  Datalog and group theory," *SIAM J. Comput.* 28(1), 1998, 57-104) identify group-theoretic
  ("subgroup") problems as one of the two known sources of tractability, and Bulatov and Dalmau ("A
  simple algorithm for Mal'tsev constraints," *SIAM J. Comput.* 36(1), 2006, 16-27) solve every
  Mal'tsev template in polynomial time.
- Goldmann and Russell ("The complexity of solving equations over finite groups," *Inform. and
  Comput.* 178(1), 2002, 253-262) show that systems of general equations over a fixed finite group
  are NP-complete when the group is non-abelian and polynomial otherwise. Translation networks use
  only equations `x_v = g x_u`, two variables and one constant, which stay polynomial for every
  group; the hardness needs equations outside this form, so it does not apply to the invertible
  fragment.
- Khot ("On the power of unique 2-prover 1-round games," STOC 2002, 767-775) defines unique games,
  whose constraints are permutations; deciding whether such an instance is fully satisfiable is easy
  by propagation (the [LOSSY-NETWORKS.md](LOSSY-NETWORKS.md) survey records this). Invertible transports on a finite
  fiber are instances of that problem, so the existence half of the invertible fragment is classical
  as a decision problem; the repository's contribution there is the obstruction theory and the
  mechanization, recorded in the cohomological section above.

**Polymorphisms of graphs of maps: clone theory.** For an operation `g` and a unary map `f`, `g`
preserves the graph of `f` exactly when `g` and `f` commute, and the centralizer `F*` of a set `F`
(the operations commuting with every member) is the intersection of the polymorphism clones of the
graphs of the members of `F`. This is standard in clone theory; Machida ("Commutation and
centralizers in clone theory," *RIMS Kôkyûroku* 1712, 2010, 101-110) records it in this form
(`{s}* = Pol s^□`) and surveys the centralizers of monoids of unary maps studied with Rosenberg
(Machida and Rosenberg, "On the centralizers of monoids in clone theory," ISMVL 2003, 303-308).
`pol_iff_commute` and `pol_gamma_iff` are this fact, mechanized, with pins as unary constant
relations; Pol(Gamma_F) is the centralizer of the monoid generated by `F` cut down to the
operations fixing the pins.

**Homomorphism problems for templates built from maps.**

- Feder and Vardi (1998, above) recast every CSP(Gamma) as homomorphism to a fixed structure; a
  transport network is a homomorphism problem into `(D; graph of f for f in F; {c} for each pin)`.
  Hell and Nešetřil ("On the complexity of H-coloring," *J. Combin. Theory Ser. B* 48(1), 1990,
  92-110) settle the undirected binary case (polynomial if `H` is bipartite or has a loop,
  NP-complete otherwise); graphs of maps are directed, so their theorem does not classify Gamma_F.
- Feder, Madelaine and Stewart ("Dichotomies for classes of homomorphism problems involving unary
  functions," *Theoret. Comput. Sci.* 314(1-2), 2004, 1-43; abstract read, full text not) study
  templates given by unary functions: one function gives a problem that is L-complete or trivial,
  two functions already reflect the full computational significance of CSPs on relational
  structures, and a pair of mutually inverse functions gives a P versus NP-complete dichotomy. So
  restricting templates to maps does not, in general, make classification easier than the general
  dichotomy, and the per-family question for Gamma_F is decided only by the cited dichotomy (Bulatov
  2017; Zhuk 2017, 2020). `hard_family_csp` is one explicit NP-complete family of this kind,
  extracted from the 3-SAT reduction; it is a concrete instance, not a new kind of hardness.

**Consistency of networks of models and replicated state.**

- Stevens ("Maintaining consistency in networks of models: bidirectional transformations in the
  large," *Softw. Syst. Model.* 19(1), 2020, 39-65) studies networks of models joined by binary
  consistency relations, treats a unidirectional transformation `f` as the consistency relation
  `n = f(m)`, introduces authority sets (models that must not change) and orientations of the edges,
  and relates the multiary-to-binary question to constraint networks in CSP (dual and
  hidden-variable encodings), noting that CSP asks for any solution while bidirectional
  transformations care how consistency is restored. This is the closest systems-side precedent: a
  network of maps with authoritative vertices whose consistent states are CSP solutions. It does not
  use polymorphisms or classify complexity per family.
- Replicated data. Targeted searches (October 2026) combining CRDTs, eventual consistency,
  invariant confluence or replicated data with constraint satisfaction, polymorphisms or clones
  found no work relating replica or federation consistency to the algebraic theory of CSP.
  Invariant confluence (Bailis et al., above) decides coordination-freedom per invariant and
  operation set; it is not a CSP classification.
- Mechanization. Polymorphisms have been mechanized before in another setting: Dvořák's Lean 4
  thesis ("Pursuit of truth and beauty in Lean 4: formally verified theory of grammars,
  optimization, matroids," arXiv:2602.12891, 2026) proves that a valued CSP template with symmetric
  fractional polymorphisms of all arities has a tight basic LP relaxation, and Manrique and Szeider
  ("LeanCSP: a framework for certifying constraint reformulation and solving in Lean,"
  arXiv:2607.28459, 2026) certify CSP reformulations in Lean. We did not search proof-assistant
  libraries exhaustively for a mechanized semilattice or max-closed arc-consistency theorem.

Search scope (October 2026): the papers named above, read as stated; web and arXiv searches for
sheaves, cellular sheaves or presheaves with constraint satisfaction, polymorphisms or clones;
contextuality with polymorphisms; max-closed, semilattice and functional constraints with arc
consistency; equations over groups; unary-function templates; and replicated or federated
consistency (CRDT, eventual consistency, invariant confluence, bidirectional transformations) with
constraint satisfaction. A search result, not a proof of absence.

**What the constraint layer contributes, given this literature.** The identification of global
sections with CSP solutions is Abramsky's line (2011 to 2017; the closest statement is Abramsky,
Barbosa, de Silva and Zapata 2017, Proposition 13), its converse for arbitrary CSPs is Ó Conghaile
2022, the polymorphisms of graphs of maps are the clone-theoretic centralizer, `ac_exact` is a
mechanized instance of Jeavons and Cooper 1995 (in the semilattice form of Jeavons, Cohen and
Gyssens 1997), the group case is Mal'tsev (Feder and Vardi 1998; Bulatov and Dalmau 2006) and
unique-games propagation, and classification per family is the cited dichotomy. What
`TransportCSP.v` contributes is narrower: the specific identification of this repository's
transport networks (reading A sections and reading B merges, with pins) with CSP(Gamma_F), stated
and proved in Coq against the same definitions the rest of the development uses; the reading of
REGIME-AUDIT.md's lossy existence cell per transport family, so that the NP-completeness of the
general cell (`net_section_iff_sat`) and the polynomial cases sit in one classification indexed by
the centralizer of the family; and three mechanized anchor points of known classes (Mal'tsev for
groups, the reduction's NP-complete 26-map family, monotone chains decided by arc consistency),
with mechanized counterexamples marking where the chain and monotonicity hypotheses are needed
(`diamond_join_fails`, `diamond_g_fails`, `ac_needs_mono`). It does not contribute a tractability or
hardness result for any constraint language, a mechanization of the dichotomy, of Mal'tsev
tractability or of bounded width, or a general sheaf-theoretic treatment of CSP. The application of
the algebraic CSP theory to replicated or federated state was not found in the searches above; that
is the extent of the claim.

## Related work for canonical execution

The canonical-execution framework ([THEORY.md](THEORY.md#canonical-execution)) splits canonicity
into E (effective canonicalization), S (state descent), H (history descent) and P (composition).
Each layer has a classical ancestor.

- **Newman's lemma, localized.** Newman ("On theories with a combinatorial definition of
  'equivalence'," *Ann. of Math.* 43(2), 1942, 223-243) proves that a terminating, locally
  confluent relation is confluent; Huet ("Confluent reductions: abstract properties and
  applications to term rewriting systems," *J. ACM* 27(4), 1980, 797-821) gives the abstract proof
  by well-founded induction and the critical-pair analysis. The framework's peak layer is that
  lemma localized to the configurations reachable from a start (`peak_exact`), and its split of
  peaks into state peaks and history peaks (`classified_peak_exact`) is a classification of
  critical pairs.
- **Rewriting modulo an equivalence (Church-Rosser modulo).** Huet (ibid.) also proves
  Church-Rosser theorems modulo an equivalence relation, and Peterson and Stickel ("Complete sets
  of reductions for some equational theories," *J. ACM* 28(2), 1981, 233-264) and Jouannaud and
  Kirchner ("Completion of a set of rules modulo a set of equations," *SIAM J. Comput.* 15, 1986,
  1155-1194) build completion modulo equations on it. History descent has the same shape: the
  canonical semantics must be constant on equivalence classes of executions, and under
  presentation adequacy it is checked one generator edge at a time (`history_descent_exact`), as
  Church-Rosser modulo is checked through local coherence with the equivalence.
- **Trace theory.** Cartier and Foata (*Problèmes combinatoires de commutation et
  réarrangements*, Lecture Notes in Mathematics 85, Springer, 1969) introduce partially commutative
  monoids; Mazurkiewicz ("Concurrent program schemes and their interpretations," DAIMI PB-78,
  Aarhus University, 1977) reads them as concurrent executions; Diekert and Rozenberg (eds., *The
  Book of Traces*, World Scientific, 1995) is the standard reference. Under causal delivery the
  framework's history generators are adjacent swaps of concurrent events, so the history quotient
  is a trace monoid (`run_tequiv`, `causal_tequiv`). The at-least-once instance adds a duplicate
  generator at its legal landing point, which leaves the trace setting.
- **Quotient monoid actions.** A monoid action factors through the quotient by a congruence
  exactly when it is constant on the congruence classes, and for a congruence generated by a
  relation it suffices to check the generating pairs (standard semigroup theory; Howie,
  *Fundamentals of Semigroup Theory*, London Mathematical Society Monographs, New Series 12,
  Oxford University Press, 1995). History descent under presentation adequacy is this fact for
  the run semantics, restricted to admissible executions; state descent
  (`state_descent_iff_respects_canon`) is the same fact one level down, for the kernel of the
  canonicalizer on states.
- **Descent.** Grothendieck's descent asks when local data, with gluing data, come from global
  data; Janelidze and Tholen ("Facets of descent, I," *Appl. Categ. Structures* 2, 1994, 245-281)
  give an elementary account. The framework uses the word in a weaker sense: state and history
  descent say that canonical outcomes descend along quotient maps (a raw state to its canonical
  form, an execution to its class), and state gluing (`sheaf_iff_refines`) is descent of objects
  along a cover. Reading interaction locality as descent of morphisms is an observation in
  THEORY.md, not a formalized descent theorem.

**What is new.** Not the ingredients. New: the E/S/H/P decomposition as one exact statement for
single systems (`canonical_execution_exact`, `esh_exact`); presentation adequacy as the named
hypothesis that makes history descent checkable per generator (`history_descent_exact`); and
locality completeness (`LC`) as the named hypothesis under which composition is exact
(`factor_exact`, each premise shown needed by `factor_needs_sound`, `factor_needs_exposed` and
`factor_needs_realizable`). The validation is that six existing exact results are rederived
through it as short corollaries (THEORY.md, "Evidence"), and that it locates the open problems:
locality fails on cycles (`cyclic_lc_sound_fails`), which is the cyclic frontier of
[REGIME-AUDIT.md](../REGIME-AUDIT.md#the-cyclic-frontier). It has not yet produced a new exact
result for an unstudied regime.

## Related work for signed cycles

`SignedCycles.v` and `SignedResolver.v` take the signed-graph view of rootless networks: the
constraint reading (sections, reading A) through balance, and the resolver reading (dynamics,
reading B) through Thomas-type conditions. The research note
[LOSSY-NETWORKS.md](LOSSY-NETWORKS.md) has the full survey with theorem numbers.

- **Balance and gain graphs.** Harary (1953) and Zaslavsky (1989), above. Proved here for finite
  signed graphs and, under the regular action, for any group, in closed-walk form (`harary_balance`,
  `holonomy_free_section`, `invertible_merge_is_holonomy`).
- **Thomas's rules.** Thomas ("On the relation between the logical structure of systems and their
  ability to generate multiple steady states or sustained oscillations," in *Numerical Methods in
  the Study of Critical Phenomena*, Springer Series in Synergetics 9, 1981, 180-193) proposed that
  a positive circuit is necessary for several steady states and a negative circuit for sustained
  oscillations. Proofs: Remy, Ruet and Thieffry ("Graphic requirements for multistability and
  attractive cycles in a Boolean dynamical framework," *Adv. in Appl. Math.* 41(3), 2008, 335-350)
  for Boolean networks with local interaction graphs; Richard and Comet ("Necessary conditions for
  multistationarity in discrete dynamical systems," *Discrete Appl. Math.* 155(18), 2007,
  2403-2413) for the multivalued first rule, also in local form (no positive circuit in any local
  interaction graph gives at most one fixed point); Richard ("Negative circuits and sustained oscillations
  in asynchronous automata networks," *Adv. in Appl. Math.* 44(4), 2010, 378-392) for the
  multivalued second rule, with the corollary that no negative circuit gives a fixed point; and
  Aracena ("Maximum number of fixed points in regulatory Boolean networks," *Bull. Math. Biol.*
  70(5), 2008, 1398-1409) for a bound on the number of fixed points by the fewest vertices meeting
  every positive cycle. The local negative-circuit form of the fixed-point statement holds under
  extra hypotheses (Richard, "Local negative circuits and fixed points in non-expansive Boolean
  networks," *Discrete Appl. Math.* 159(11), 2011, 1085-1093) and fails in general: Ruet
  ("Negative local feedbacks in Boolean networks," *Discrete Appl. Math.* 221, 2017, 1-17) gives
  and-nets without local negative cycles and without fixed points.
- **Robert's theorem.** Robert (*Discrete Iterations: A Metric Study*, Springer Series in
  Computational Mathematics 6, 1986): an acyclic interaction graph gives a unique fixed point,
  reached by iteration; Robert also shows (*Les systèmes dynamiques discrets*, Mathématiques et
  Applications 19, Springer, 1995) that the asynchronous state graph is then acyclic, so every
  asynchronous path, and hence every fair schedule, ends at the fixed point (as restated in
  Richard 2019, Theorem 1, below). In the federation model the unique fixed point and its runs in
  topological order are mechanized (`frun_solves`, `solve_unique`, `order_independent`), and so is
  the asynchronous half (`coq/RobertFair.v`, closing REGIME-AUDIT.md gap 16 (d)): in the distributed
  propagation model every fair schedule from every valid start settles at the run of one
  topological order (`rb_robert_fair`), within depth plus one rounds (`rb_rounds`), and every
  propagation word makes fewer than `2^n` effective steps (`rb_effective`, `rb_closed`); in the
  resolver model a unique fixed point is reached by every fair schedule (`rb_lens_robert`); for a
  Boolean network with an acyclic global graph the asynchronous state graph is acyclic and the
  fixed point unique (`rb_robert_boolean`, through `fair_settlement_of_acyclic`). The theorem is
  Robert's; the mechanization is what is added. Acyclicity cannot be dropped (`rb_neg2_cycle`,
  `rb_copyback_cycle`) and is not necessary (`rb_converse_fails`, Shih and Ho's network).
- **Local interaction graphs** (`LocalSigned.v`: Boolean, every `n`; the local graph is the
  discrete Jacobian at a state). Placements, each checked against the paper or the authors' own
  restatement:
  - Shih and Dong ("A combinatorial analogue of the Jacobian problem in automata networks," *Adv.
    in Appl. Math.* 34(1), 2005, 30-46): no cycle in any local graph gives a unique fixed point,
    conjectured by Shih and Ho ("Solution of the Boolean Markus-Yamabe problem," *Adv. in Appl.
    Math.* 22(1), 1999, 60-102) as a Boolean analogue of the Jacobian conjecture. Mechanized as
    `shih_dong_E`, with the path form `sd_path` (from every state an update word reaches the fixed
    point; the geodesic form is Richard, "Fixed point theorems for Boolean networks expressed in
    terms of forbidden subnetworks," *Theoret. Comput. Sci.* 583, 2015, 1-26, Corollary 4, under a
    hypothesis that generalizes Shih and Dong's).
  - Remy, Ruet and Thieffry 2008, above (checked against the primary text, HAL hal-00692086,
    Theorem 3.2): two fixed points force a positive cycle in some local graph, so no positive cycle
    in any local graph gives at most one fixed point. Mechanized as `rrt_sub`, `local_fidelity`.
  - Richard 2011, above: Theorem 3 (no negative cycle in any local graph and out-degree at most one
    everywhere, equivalently non-expansive for the Hamming distance, gives a fixed point) and
    Theorem 4 (no local negative cycle and one vertex on every local positive cycle gives a fixed
    point). Mechanized as `richard_t3` (with `outdeg_nonexpansive`) and `richard_t4`, both in the
    stronger reachability form (some update word reaches a fixed point from every state).
  - Tonello ("On the conversion of multivalued to Boolean dynamics," *Discrete Appl. Math.* 259,
    2019, 193-204; arXiv 1703.06746, 2017): a 6-component Boolean version of Richard's
    multivalued Example 6 (Richard 2010, above) with no local negative cycle and no fixed point.
    Mechanized as `local_neg_free_no_fixed_point`. Tonello, Farcot and Chaouiya ("Local negative
    circuits and cyclic attractors in Boolean networks with at most five components," *SIAM J.
    Appl. Dyn. Syst.* 18(1), 2019, 68-79; arXiv 1803.02095, 2018): by a SAT encoding, up to five
    components a cyclic attractor forces a local negative circuit, so six is the least dimension of
    such a counterexample. Cited, not mechanized.
  - Asynchronous convergence under local acyclicity. Richard ("Positive and negative cycles in
    Boolean networks," *J. Theoret. Biol.* 463, 2019, 67-76, section 3) records that under Shih
    and Dong's hypothesis Robert's synchronous convergence and the acyclicity of the asynchronous
    state graph are both lost, attributing this to a 4-component example of Shih and Dong 2005
    (we could not access that paper's full text, so the example itself was not read). So it is
    known that local acyclicity, unlike global acyclicity, does not force every asynchronous path
    to the fixed point. `shih_dong_not_fair` is the fair-schedule form: a 4-vertex network with no
    local cycle and a periodic schedule, every vertex updated twice per period of 8, along which
    every update changes the state and the fixed point is never reached. A fair-schedule
    statement of this kind was not found in the literature we searched (scope below); it may
    coincide with Shih and Dong's own example, which we could not check. An exhaustive check over
    all 3-vertex Boolean networks (680 have no local cycle; not mechanized) finds an acyclic
    asynchronous state graph and a convergent synchronous iteration in every case, so 4 vertices
    is the least for both the known phenomenon and its fair form.
  - Shih and Ho 1999 (read in full for #92): Theorem 3.1, no cycle in any local graph plus
    `F(V(x))` inside `V(F(x))` (out-degree at most one in every local graph, their Lemma 4.1;
    Hamming non-expansiveness, their Lemma 4.3) makes the synchronous iteration reach the unique
    fixed point from every start, within `2^n` steps; Theorem 3.2, without the second condition
    only for `n <= 3`. The paper treats synchronous iteration only. Its conclusion is mechanized
    here, by a different proof, as `sync_simple` (`LocalFairSettlement.v`; `sync_orbit_fixed`
    needs the local acyclicity only on the orbit), and its 4-vertex example is `shih_ho_instance`.
    The asynchronous counterpart, fair settlement under the same two conditions, is mechanized for
    starts with at most one unstable vertex (`one_token_fair_settlement`, #92) and at most two
    (`two_token_fair_settlement`, `LocalTwoToken.v`, #93: a closed two-token run rearranges into a
    synchronous orbit) and open in general (for n <= 6 there is computational evidence, not
    mechanized); it was not found in the literature searched (Shih and Ho 1999 treat synchronous
    iteration only).

  Search scope for the last two items (October 2026): Shih and Ho 1999 (full text, read for #92)
  and Shih and Dong 2005 (abstract and restatements; full text not accessible), Remy, Ruet and Thieffry 2008, Richard 2010,
  2011, 2015 and 2019, Richard and Ruet 2013, Ruet 2016 and 2017, Tonello 2017, Tonello, Farcot and
  Chaouiya 2018, Melliti, Regnault, Richard and Sené 2013 (global graphs without negative cycles),
  the fixing-word papers (Gadouleau and Richard 2018; Aracena, Gadouleau, Richard and Salinas 2020,
  where a word fixes a network if it reaches a fixed point from every state), and web searches for
  fair, periodic and chaotic asynchronous iterations with local interaction graphs.

**What is new.** Not balance, the Thomas-type necessary conditions, Robert's theorem or the local
fixed-point theorems (Shih and Dong; Remy, Ruet and Thieffry; Richard's Theorems 3 and 4), which
are classical; here they are mechanized for every `n` and tied to E. New, and mechanized:
sufficient signed certificates for effective canonicalization (E) of rootless resolver networks,
on the global interaction graph: with a switching, every fair schedule from a low start settles at
the switched least fixed point (`signed_settlement`), and with at most one fixed point it does so
from every start (`signed_fidelity`), each hypothesis shown needed by a counterexample; the
global-sign collapse, that on a balanced graph Thomas's sign condition for uniqueness (no positive
directed cycle) leaves no directed cycle at all (`balanced_no_positive_acyclic`), so the sign
route to uniqueness reduces there to Robert's acyclic case; the loop-versus-merge separation
(`obstruction_loop_vs_merge`): invertible obstructions are always loops, while a lossy obstruction
can be a merge on a tree with no loop at all; and, on local graphs, the reading of the classical
theorems as certificates for E's two halves (CanonicalFidelity from `local_fidelity_canon`,
existential Settlement from `richard_t3`, `richard_t4` and `shih_dong_E`), with the split between
existential and fair-schedule settlement made explicit (`shih_dong_not_fair`,
`ring_local_conditions`); and, under no local cycle plus out-degree at most one, the synchronous
conclusion of Shih and Ho 1999 with the local condition needed only on the orbit
(`sync_orbit_fixed`) and fair settlement from starts with at most one unstable vertex
(`one_token_fair_settlement`). Not claimed: an exact condition, fair-schedule settlement from
local conditions from every start, or multivalued local graphs; those are open (REGIME-AUDIT gap
3).

## The ideas it connects (and makes rigorous)

- **Term rewriting / Newman's Lemma.** Convergence is reframed as *confluence of a rewrite
  system*: events and compensation are rewrite rules, and "same result regardless of order" is
  the Church-Rosser property. This is why the proof is Newman's Lemma (termination + local
  confluence implies global confluence), and why it is mechanizable (see `coq/`).
- **Abstract interpretation / chaotic iteration.** In the monotone regime, "converges regardless
  of application order" is precisely the order-independent convergence of chaotic iteration in
  dataflow analysis (Cousot). The federated repair operator is a monotone map on a lattice; its
  least fixed point is the federated normal form, reached by any fair schedule. So the cyclic
  federation case inherits worklist scheduling and widening from that literature.
- **CALM / monotonicity.** The monotone-cycles result is the invariant-carrying cousin of CALM
  (monotone repair converges coordination-free on any topology); the precise relationship, and how
  it differs from I-confluence, is spelled out in the section above.
- **The saga pattern.** Compensation is folklore in sagas and long-running transactions, used to
  undo partial work. Normalization confluence gives that folklore a *convergence theory*: exactly
  when compensations make concurrent orderings agree on the same valid state, rather than merely
  rolling back one transaction.

## What it moves in the landscape

1. **A third coordination-avoidance regime.** Beyond commutativity (CRDTs) and
   invariance-preservation (I-confluence), there is now compensation-based convergence: keep the
   business rule, allow the violation, repair deterministically.
2. **A bridge between three fields.** Distributed convergence, term-rewriting confluence, and
   abstract-interpretation fixpoints are shown to be the same phenomenon under different names.
3. **Where to coordinate: a cycle basis, not a global yes/no.** When a federation cannot converge
   coordination-free, coordinating a cycle basis of its morphism network suffices (proved in the
   invertible fragment, with the authority-rooted plan's soundness mechanized), refining CALM and
   I-confluence from a global yes-or-no into a localized one.
4. **From folklore to guarantee.** Saga-style compensation gains a checkable condition (WFC + CC)
   and a machine-checked proof, so "our compensations converge" becomes something you verify at
   build time rather than hope for.

## Where it lives in a stack

- **The theory**: the three papers in this repository, with a machine-checked Coq/Rocq proof in
  [`coq/`](../coq) (axiom-free, CI-gated).
- **The engine**: [`gsm`](https://github.com/blackwell-systems/gsm) verifies WFC and CC for a
  concrete registry at build time (globally, or per footprint component for large machines) and
  gives an O(1) runtime.
- **An application**: durable AI agents whose governance tier uses gsm, so multiple agents sharing
  governed state converge without a coordinator.

## What it does not claim

It does not remove the need to design a correct compensation; it tells you when the one you wrote
converges, or (via synthesis) searches for one, or reports that none exists. It does not replace
consensus where you genuinely need a single total order (uniqueness, linearizable reads of a
counter). And the guarantee is convergence to a unique valid normal form, not that the normal
form is the one a human would have preferred: a converged repair can still be a bad repair, so
inspect it. It does not give CALM-style incremental correctness under partial input: NC assumes every
replica eventually sees the same event set and converges then, tolerating transient invalidity
between an event and its repair. If you must act on a non-monotone output before all events have
arrived, that is exactly the coordination CALM characterizes, and NC does not remove it. See
[REGIMES.md](REGIMES.md) for exactly which conditions your system must meet.
