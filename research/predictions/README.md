# Predictions against the frozen framework

Every test of the framework so far recovers a result that was already known: normalization
confluence (`NormalizationDerived.v`), Dijkstra's self-stabilization (`SelfStabilization.v`), CRDT
strong eventual consistency (`CRDTRecovery.v`) and invariant confluence (`InvariantConfluence.v`).
Those show that the framework compresses known results and that some of its structure transports to
theorems outside the repository. They do not show that it can say something true before the answer
is known. This directory holds that test.

## The freeze

Frozen on 2026-10-11 at commit `5be01a7` on main: the eight kernel files listed with their SHA-256
hashes in [frozen.sha256](frozen.sha256).

- `CanonicalExecution.v`, `CanonicalRecurrence.v`, `DistributedCycles.v`, `LayerInterfaces.v`,
  `NormalizationDerived.v`, `PresentedExecution.v`, `TransportCSP.v`, `TransportCSPHard.v`.
- `python3 docs/atlas/check.py` fails if any of them changes, so CI enforces the freeze. To check by
  hand: `shasum -a 256 -c research/predictions/frozen.sha256`.
- The freeze holds while the predictions below are being tested; P2 is scored (passed). Regime work in new files continues; it
  cannot change the kernels.

## Recorded boundaries

The outside tests found these limits of the frozen kernels. They are recorded as boundaries, not
repaired. A later version of the framework that addresses them is judged on outside theorems that
were not used to design it, not on these.

| Boundary | Found by |
|---|---|
| No merge of two replica states: layer A applies events to one state | CRDTs, state-based (`CRDTRecovery.v`) |
| The A to C termination interface speaks of settled states; a system that never quiesces needs an adapter outside the kernels | Dijkstra, arbitrary daemon (`SelfStabilization.v`) |
| One label moves per step: simultaneous moves cannot be stated | Dijkstra, distributed daemon (`SelfStabilization.v`) |
| No model of arbitrary protocols under partitions, so necessity of Bailis et al.'s Theorem 1 holds only in a replica model | Invariant confluence (`InvariantConfluence.v`) |
| The layer B bridge covers merges that act item by item | Invariant confluence (`InvariantConfluence.v`) |
| The kernels need a listed finite state type | Dijkstra (`SelfStabilization.v`) |

## The protocol

1. **Candidates.** Two or three candidate predictions about regimes whose answer is not known, each
   derived from the frozen kernels only, in [candidates.md](candidates.md). Each states the claim (a
   theorem, or a specific counterexample), the kernel results it follows from and why, a literature
   check showing the answer is not already known, the pass and fail criteria, and what a refutation
   would look like. No proof attempts at this stage.
2. **Choice and commitment.** One candidate is chosen and copied, unchanged, to `P1.md`. The commit
   that adds `P1.md` is its timestamp. The claim and its criteria are not edited after that commit.
3. **Test.** A separate run tries both to prove the claim and to refute it, with the kernels still
   frozen.
4. **Score.** The outcome is scored against the committed criteria and recorded in `P1.md`, whatever
   it is.

## Committed predictions

| File | Claim | Committed | Outcome |
|---|---|---|---|
| [P2.md](P2.md) | A unique stable matching does not stop fair blocking-pair dynamics (some market with at most 4 men and 4 women cycles under a pair-fair schedule) | 2026-10-11 | PASS at `n = 3`: a unique stable matching and a round-robin fair cycle ([outcome](P2.md#outcome), [coq/StableMatchingP2.v](../../coq/StableMatchingP2.v), [search](p2/)) |
| [P3.md](P3.md) | CouchDB and PouchDB resurrect a deleted document on exactly the computed delivery orders (6 of 24 in CouchDB, none with per-update pruning off, 12 of 24 in PouchDB) | 2026-10-11 | PASS on all three claims: every scored order matched, 3 repetitions, none nondeterministic ([outcome](P3.md#outcome), [results](route2/results/)); unscored S2 runs found an error in the CouchDB model, recorded in the outcome |

P1 is reserved for the routing candidate, reshaped after the literature check; not committed.
