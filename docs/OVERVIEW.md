# Overview

## The problem

Replicas hold copies of the same state, such as the stock on a shelf or the bookings on a flight.
Networks delay, reorder and retry messages, so events reach replicas in different orders. After
each event, every replica runs the same repair to restore its invariants (stock never exceeds the
shelf's capacity). Do replicas that have seen the same events end in the same state?

Not always. A shelf holds 5 items and has 4 in stock. Two events arrive, "add 3" and "remove 1",
and repair caps the stock at 5.

- Replica A applies "add 3" (7), repairs (5), then "remove 1": 4.
- Replica B applies "remove 1" (3), then "add 3" (6), repairs: 5.

Same events, same repair, different stock.

## Convergence by compensation

Here events may conflict and may break invariants, and a deterministic repair (compensation)
restores the invariants. The question is when every delivery order still ends in the same repaired
state, with no coordination between replicas.

CRDTs design operations so that order never matters; they are the case where repair never has anything to do. With repair, operations that do not
commute can still converge, some only because of the repair, although the resulting behavior is
itself a CRDT on the repaired steps.
Invariant confluence lets replicas merge without coordination when no merge of valid states can
break an invariant; it forbids violations, while convergence by compensation allows them and
repairs them.

## The main result

Write `N` for the repair: it takes any state to its repaired form. Raw states may differ along the
way; what has to agree is the result after repair. The theory proves a condition at each of three scales:
necessary at one event when events can arrive mid-repair, exact for a single registry when combined with the condition on sequences, and exact for infinite runs on finite state spaces. They are not one equation: they form a proved hierarchy, each level with counterexamples
showing where it stops.

**One event.** Applying an event to a state, or to that state's repaired form, gives the same result
after repair. The shelf fails: from a raw stock of 7, "remove 1" gives 4 if repair runs before it
and 5 if repair runs after, because removal sees the overflow that repair discards. A flight
passes if repair moves overflow bookings to a waitlist ordered by request id and cancellations
promote from it: the repaired state depends only on which requests are active, and no event can see
more than that.

**A sequence of events.** Every reordering the delivery model allows gives the same result after
repair. Under causal delivery a cancellation never arrives before its booking, so that pair never
has to commute. Under at-least-once delivery a retry is one more reordering: a retried "reserve seat
12A" is absorbed, because applying it twice equals applying it once, while a retried "add 1 to
stock" counts twice and the replicas diverge.

**An infinite run.** On a network with cycles, repair may never stop on its own, so the question is
whether every run eventually stays on one repaired result. Two services that each copy an "alarm
raised" flag from the other fail: a short alarm sets both flags, each then holds the other's up, and
the run settles where the intended repair (flags down once the alarm clears) never goes.

On a network of registries without cycles, the condition becomes two local checks per edge: an
event gives the same result whether or not the edge's repair has run (the one-event condition, at
the edge), and two independent events on one registry commute after that repair.

## What "exact" means

Every condition is necessary and sufficient: if it holds the system converges, and if it fails
some order does not. Each hypothesis also has a counterexample showing it cannot be dropped.
The shelf's repair terminates, and the shelf still diverges, so commutation is needed. Two
registries, each valid on its own and linked by validity-preserving maps, repair each other around
the cycle (0,0), (0,1), (1,1), (1,0), (0,0) forever. Two blocks that each converge alone can stop
converging when one feeds the other.

The exact conditions range over every reachable state; cheaper sufficient conditions (per state,
per pair of events, per edge) are proved to imply them. Where no efficient exact condition can
exist unless P = NP, there is a hardness proof instead: consistency of a lossy network with no root is
NP-complete, by reduction from 3-SAT.

All of it is machine-checked in Coq (Rocq) with no axioms. The gate in `coq/verify.sh` checks 4797
theorems, and CI runs it on every pull request.

## Has the framework been tested?

The framework that organizes these results was built from them, so re-deriving them proves little.
The stricter test is to freeze it and recover theorems from outside the repository. Dijkstra's
self-stabilization (1974) and invariant confluence (Bailis and others, 2015) both came through with
no framework file edited. CRDT convergence came through for operation-based CRDTs; state-based CRDTs
need a merge of two replica states, which the framework cannot express. The framework stays frozen
while predictions, written down before anyone tries to prove them, are tested. The first passed: a
matching market with exactly one stable matching can still cycle forever when every pair gets its
turn. The second also passed: a model of CouchDB's revision handling predicted exactly on which
delivery orders a deleted document comes back, and the real database matched ([research/predictions](../research/predictions/README.md)).

## What is still open

Seven convergence questions are open, most on cyclic networks: rootless networks with lossy
transports, the distributed model off its current hypotheses, a cyclic block whose propagation
interleaves with outer events, reconfiguration with propagation in flight, and versioned channels
on networks with several sources or with cycles. The audit states the cyclic ones as one question:
what makes composition exact on cycles. Each gap, with what is already proved, is in
[REGIME-AUDIT.md](../REGIME-AUDIT.md#the-open-gaps).

## What gsm does with it

[gsm](https://github.com/blackwell-systems/gsm), a Go library, checks the cheap conditions at build
time by enumerating the finite state space: repair terminates and commutes for a single registry,
and the two per-edge checks for a federation. It returns no machine unless the check passes. For a
single registry, a checker generated from the Coq proof re-certifies the result in process; the
federation checks are not re-certified yet. At run time an event is a table lookup.

## Where to go next

- **Building a system:** [REGIMES.md](REGIMES.md), the field guide by situation.
- **Research:** [THEORY.md](THEORY.md#main-result), then [prior work](LANDSCAPE.md).
- **Proofs:** [coq/README.md](../coq/README.md), the module index by regime; `cd coq && bash
  verify.sh` reruns the gate.
- **Status:** [REGIME-AUDIT.md](../REGIME-AUDIT.md), every regime with its theorem or open gap.
