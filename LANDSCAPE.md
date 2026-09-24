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
- **CALM / monotonicity.** The monotone-cycles result is the invariant-carrying cousin of CALM:
  monotone repair converges coordination-free on any topology, and adds business invariants on
  top of what monotone logic alone provides.
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
inspect it. See [REGIMES.md](REGIMES.md) for exactly which conditions your system must meet.
