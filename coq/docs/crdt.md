# CRDT fragment

Detailed results for the CRDT modules: CRDTs as the compensation-free fragment, and state-based
merges through the exact theorems. Each module's one-line summary is in the [module
index](../README.md#modules-by-regime); the status of each question in this regime is in
[REGIME-AUDIT.md](../../REGIME-AUDIT.md#4-crdt-fragment), section 4.

## CRDTs as a special case (`CRDT.v`)

`CRDT.v` machine-checks that conflict-free replicated data types are the compensation-free
fragment of this theory: a CRDT buys convergence by restricting to operations that can never
violate an invariant, so no repair is ever needed, and normalization confluence keeps convergence
after dropping that restriction. Four results, all axiom-free:

- `cmrdt_SEC`: an op-based CRDT's strong eventual consistency (replicas that delivered the same
  operations in any order agree) is a one-line instance of `run_perm_invariant`. Its commuting-
  operations requirement is exactly the order-independence hypothesis that lemma already assumes.
- `cmrdt_governed_SEC`: the embedding is faithful. A CmRDT is a governed machine with the trivial
  invariant (every state valid) and identity compensation; then WFC is trivial, the governed step
  equals the raw operation, and convergence follows again.
- `cvrdt_SEC` / `cvrdt_absorbs_duplicates`: a state-based CRDT is the semilattice special case. A
  commutative, associative, idempotent join makes merge order-independent (the same lemma) and
  absorbs duplicate delivery (the extra property a CvRDT bundles in for at-least-once delivery,
  which normalization confluence does not require in general).
- Strict inclusion (`witness_converges`, `witness_not_cmrdt`, `witness_leaves_valid_space`): a
  concrete governed machine that converges yet is neither CRDT. Its raw operations do not commute
  (so it is no CmRDT), and an event drives a valid state to an invalid one (so its operations are
  not the structure-preserving endomaps of a CvRDT). It converges only because compensation repairs
  the violation.

The claim is scoped to the convergence principle, not to CRDT engineering as a whole: version
vectors, the mechanisms that achieve causal delivery, and garbage collection are operational
concerns this result does not subsume. See [`SUBSUMPTION.md`](../../docs/SUBSUMPTION.md) for the full statement and caveats.

## State-based CRDTs, exact (`CvRDTExact.v`)

`CRDT.v` proves the sufficient direction for a state-based CRDT (`cvrdt_SEC`,
`cvrdt_absorbs_duplicates`). `CvRDTExact.v` places that model under the exact theorems of the single
registry and of at-least-once delivery, and proves the exact converse. Setting: a
compensation-free registry (every state valid, identity repair), so the governed step of an event
`e` is its action `act e`; a CvRDT is the instance with payload states as events and
`act x s = join s x`. `X` is the set of events in range, `s0` the start state, and `Reach s0 s`
means `s` is reached from `s0` by some delivery over `X`, duplicates allowed.

**The registry's exact theorem, compensation-free.** `cf_cc_exact_from` (through
`canonical_cc_exact_from`) and `cf_cc_exact_from_wfc` (through `cc_exact_from`): every buffer from
`s0` has a unique normal form iff the actions commute at every state reachable from `s0`; CC2 is
vacuous. `cf_reach_iff`: those reachable states are the runs from `s0`. `cf_star_run`,
`cf_un_perm`: unique normal forms give order independence of permuted deliveries.

**The exact converse.** `MergeConv s0`: every two deliveries over `X` with the same set of events
(any order, any duplication) reach the same state from `s0`.

- `mergeconv_alo`, `merge_conv_alo_exact`: `MergeConv s0` is `AtLeastOnceExact.ALOConv`, so it is
  equivalent to `alo_exact`'s conditions (commutation at reachable exactly-once states,
  idempotence at reachable first deliveries).
- **`merge_action_exact`**: `MergeConv s0` iff the action is commutative and idempotent at every
  reachable state: `act y (act x s) = act x (act y s)` and `act x (act x s) = act x s` for
  `Reach s0 s`, `X x`, `X y`. The actions of `X`, restricted to the reachable states, are an
  action of the free semilattice on `X`.
- `CvRDTOn s0` makes "is a state-based CRDT" precise: some `j` is a join-semilattice on the
  reachable states (closed, commutative, associative, idempotent there) and every event in range
  acts as a join with a fixed state, `act e s = j s (act e s0)` for reachable `s`.
  `cvrdt_on_conv`: `CvRDTOn s0 -> MergeConv s0`. `conv_cvrdt_on`: the converse, when `X` is finite
  and state equality is decidable (the join is computed without choice: `j s t` merges into `s` the
  events of a subset of `X` that reaches `t`). **`cvrdt_on_exact`**: under those qualifiers,
  `MergeConv s0 <-> CvRDTOn s0`; `cvrdt_exact_all` states both iffs. So a compensation-free
  registry converges under every order and every duplication exactly when, on its reachable
  states, it is a state-based CRDT with payload `e` read as the state `act e s0`.
  `cvrdt_on_inflationary`: in that representation every event is inflationary in the join order.

**The CvRDT instance.** For a commutative, associative, idempotent `join`: `cvrdt_action`
(commutative and idempotent at every state), `cvrdt_merge_conv` (through `merge_action_exact`),
`cvrdt_alo` (through `alo_exact`), `cvrdt_cc` and `cvrdt_unique_normal_forms` (through
`cf_cc_exact_from`), `cvrdt_on_join` (`CvRDTOn` with `j = join`, for every `s0` and `X`, no
finiteness). Recovered: `cvrdt_SEC_via_cc` and `cvrdt_SEC_recovered` (`CRDT.cvrdt_SEC`, through the
registry's theorem and through `MergeConv`), `cvrdt_set_SEC` (same event set, any duplication:
stronger than a permutation), `cvrdt_absorbs_duplicates_recovered` (through `alo_idem_reachable`).
`cvrdt_causal_cmrdt`, `cvrdt_compensation_free`: the merges also meet the op-based condition of
`CausalReplay.compensation_free_exact`.

**The monotone regime.** With `le a b := join a b = b`, merges are inflationary and monotone
(`merge_inflationary`, `merge_monotone`), and a delivery reaches the least upper bound of `s0` and
the delivered payloads (`run_upper`, `run_least`), equivalently the least common fixed point above
`s0` of the delivered merges (`cvrdt_lfp`): the least-fixed-point characterization of the
monotone regime, with nothing to repair. A state-based CRDT is the compensation-free monotone
case.

**Counterexamples.**

- `naive_cvrdt_iff_fails`: "converges under every order and duplication iff the merge is a
  join-semilattice on the whole state space" is false. `ignore_conv`, `ignore_not_comm`: the merge
  `m s x = s` converges from every `s0` for every `X` and is not commutative (it is still
  `CvRDTOn`, `ignore_cvrdt_on`: its reachable set is `{s0}`). `zero_conv`, `zero_not_idem`: `m s x = 0`
  converges and is not idempotent. The semilattice laws of the merge are sufficient, not necessary.
- `clamp_reach_qualifier`: the reachability qualifier is needed. On `nat` with `X = {x <= 5}`,
  `act x s = max s x` for `s <= 5` and `s + x` above: `MergeConv` holds from 0, the action is not
  idempotent at the unreachable 6, and `MergeConv` fails from 6. `clamp_cvrdt_on`: from 0 it is a
  state-based CRDT on its reachable states (through `conv_cvrdt_on`), though not a semilattice on
  `nat`.
- `add_cc_not_alo`: the idempotence clause is needed and is not implied by the registry's exact
  condition. The counter `act x s = s + x` has unique normal forms for every buffer from every
  state, yet a duplicate diverges.
- `lww_not_conv`: the commutation clause is needed. Overwrite (`act x s = x`) is idempotent at every
  state and diverges.

**Non-vacuity.** `maxreg_exact` (max-register), `gcounter_exact` (a two-replica G-Counter, pointwise
max on `nat * nat`), `gset_exact` (a grow-only set as a bitset, union `Nat.lor`), each with
`MergeConv`, `CvRDTOn`, at-least-once convergence and unique normal forms for every `X` and `s0`
(`cvrdt_all`), and computed duplicate deliveries `maxreg_dup`, `gcounter_dup`, `gset_dup`.
