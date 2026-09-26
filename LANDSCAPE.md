# Where normalization confluence sits (and what it moves)

If you already know CRDTs, consensus, or the saga pattern, this page places normalization
confluence relative to what you know: what problem it shares with them, what it does differently,
and which older ideas it connects. It is the "why is this new" companion to the papers and to
[REGIMES.md](REGIMES.md) (which is the "what applies to my system" lookup).

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
inclusion is strict via a convergent governed machine that is provably neither CRDT. See
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
never violated (max repair depth 0). That puts I-confluence, alongside CRDTs, on NC's floor: CRDTs
are the compensation-free fragment reached by commutativity, I-confluence the compensation-free
fragment reached by invariant preservation, and both are the same "repair never needed" corner that
`compensationFree` decides (machine-checked).

**Where compensation adds reach.** NC's own contribution is the region *above* that floor:
operations that DO violate the invariant, made convergent by a repair that terminates (WFC) and
commutes (CC). Neither prior characterization reaches it. CALM-monotonicity cannot (the canonical
divergence counterexample, antitone negation, is exactly non-monotone), and I-confluence excludes
invariant-violating operations by definition. NC reaches it by two routes that match its topology
results: monotone repair converges on any graph (the CALM overlap), and non-monotone but compensable
repair converges on acyclic networks with resolvers. The price of leaving the characterized floor is
that WFC + CC is a *sufficient* mechanism, not an iff: its boundary is CC-satisfiability, decided
constructively by `Registry.Synthesize` (the impossibility witness), rather than a closed-form
logical property like monotonicity or I-confluence.

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

- **Explicit consistency / Indigo** (Balegas et al., EuroSys 2015) and **escrow transactions**
  (O'Neil, 1986). Keep an invariant coordination-free by handing each replica a local *reservation*
  (a budget it may spend without asking). This is a different mechanism from compensation:
  reservation is pessimistic (prevent the violation up front), compensation is optimistic (allow
  it, repair after). They are complementary, not competing, and reservation-style invariants are a
  candidate repair strategy for gsm where a lossy after-the-fact repair is unacceptable.

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
that produced it. The claim to stake against this neighborhood is provenance of trust, not novelty
of function.

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
3. **From folklore to guarantee.** Saga-style compensation gains a checkable condition (WFC + CC)
   and a machine-checked proof, so "our compensations converge" becomes something you verify at
   build time rather than hope for.

## Where it lives in a stack

- **The theory**: the two papers in this repository, with a machine-checked Coq/Rocq proof in
  [`coq/`](coq) (axiom-free, CI-gated).
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
