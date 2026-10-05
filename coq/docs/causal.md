# Causal delivery

Detailed results for the causal-delivery modules: convergence when only concurrent events must
commute. Each module's one-line summary is in the [module index](../README.md#modules-by-regime);
the status of each question in this regime is in
[REGIME-AUDIT.md](../../REGIME-AUDIT.md#2-causal-delivery-replay-model), section 2.

## Causal delivery (`CausalReplay.v`, `GovernanceCausal.v`)

The all-pairs results (CC1 in `Governance.v`, the op-based model in `CRDT.v`) require every pair of events to commute. Under causal delivery only
**concurrent** events (neither happened before the other) can arrive in either order, so only they
need to commute. Axiom-free:

- `causal_convergence`: governed steps that commute for every concurrent pair make any two causally
  consistent delivery orders of the same events reach the same state.
- `causal_cmrdt_SEC`: standard op-based CRDTs (concurrent operations commute) converge.
- `compensation_free_exact`: a compensation-free system satisfies the causal condition iff it is an
  op-based CRDT, so the compensation-free fragment is exactly the op-based CRDTs.
- `witness_causal_not_cmrdt` (strictness) and `witness_beyond_all_pairs` (an add, a causally later
  remove, and an independent counter: not all operations commute, yet the system converges).
- `causal_tequiv`: causally consistent orders are trace-equivalent under concurrency, connecting
  causal delivery to `Trace.v`'s `run_tequiv`.
- `causal_governance_confluent` (`GovernanceCausal.v`): the rewrite-system Convergence Theorem with
  CC1 required only for distinct events enabled together; the witness `cw_confluent` /
  `cw_violates_all_pairs_cc1` meets the weakened hypothesis and violates the original.

Each ordering proof bubbles an event to the front past concurrent events, so the connectivity of
linear extensions is never assumed.
