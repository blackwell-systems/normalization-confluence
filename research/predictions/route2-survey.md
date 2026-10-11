# Route 2: a survey of real systems for a computed prediction

P2 ([P2.md](P2.md)) was a bet: the framework posed a question and leaned one way. This survey looks
for a prediction of another kind. The framework computes an answer about real, running software
from a model of its code, and the running software then checks that answer. The mathematics is
exact. The risk is whether the model matches the system.

This file does not commit a prediction. It ranks candidates, writes up the top two, and drafts a P3
in the protocol's form ([README.md](README.md)). The owner chooses.

**Preregistration hygiene.** No target software was run. I read source code and documentation
(GitHub API), transcribed the relevant functions into Python models, and ran computations on those
models only: exhaustive enumeration in Python and one `gsm` build on a generated registry. No
smoke test of CouchDB or PouchDB was run either; Docker is installed but was not used. The
harnesses in [route2/](route2/) have not been run.

## Contents

- [What the framework can decide](#what-the-framework-can-decide)
- [(a) Ranked candidates](#a-ranked-candidates)
- [(b1) CouchDB: replicated revisions under revs_limit](#b1-couchdb-replicated-revisions-under-revs_limit)
- [(b2) PouchDB: the same model, implemented separately](#b2-pouchdb-the-same-model-implemented-separately)
- [(c) Draft P3](#c-draft-p3)
- [Files](#files)

## What the framework can decide

The theorems this survey uses, read for a deterministic step function `g_e` on states (the
*governed step*: apply event `e`, then repair):

- **Free delivery, exactly once.** All orders of the same events reach one state from `s0` iff the
  governed steps commute after every reachable prefix (`causal_exact` with no causal order, CCR;
  `cc_exact_from` in the registry form with CC1 and CC2).
- **At-least-once delivery.** All deliveries with duplicates reach the exactly-once result iff the
  steps commute at reachable states and every event is idempotent at each reachable state where it
  is delivered for the first time (`alo_exact`). Per event: `needs_dedup_exact`, `safe_free_iff_idem`.
- **Declared independence** (`tconv_exact`, `dalo_exact`) for per-origin FIFO systems.
- **State descent.** If the repair `N` descends along every event, `N (e (N s)) = N (e s)`, then
  repairing after every step gives the same result as one repair at the end of the raw run
  (`normalization_descent`; `state_descent_iff_cc2`). A failure at a reachable `s` is already a
  one-event counterexample.
- **Compensation-free fragment.** Merges with identity repair converge under any order and
  duplication iff they commute and are idempotent at reachable states (`merge_action_exact`); the
  boundary to repair is `crdt_boundary`.
- **Layer C.** For reconcile loops: fair settlement iff no bad fair lasso (`C1_closed`, `C2`,
  `bad_lasso_refutes`).

`gsm` decides the single-registry case (WFC, CC) by enumeration when the state type is finite.

## (a) Ranked candidates

Fidelity: can events, state and repair be modeled from the code, finitely, without guessing.
Testability: can the real software be driven through chosen orders, cheaply and deterministically.

| Rank | System | Repair or reconcile, where | Delivery that really happens | Model fidelity | Theorem that computes the answer | Testability | Main risk |
|---|---|---|---|---|---|---|---|
| 1 | **CouchDB** revision trees with `revs_limit` | `couch_key_tree:stem/2` after every replicated merge (`couch_db_updater.erl`, `maybe_stem_full_doc_info`), with `repair_tree` when keys repeat; leaf filter in `couch_db.erl` `prep_and_validate_replicated_updates` | Replication delivers revisions with their histories in any order, with duplicates and retries, and with histories cut short by the source's own stemming | High: pure Erlang functions, about 250 lines, transcribed; same code in 3.5.3 and `main` | `alo_exact` (CCR plus idempotence), state descent with `stem_interactive_updates` as the raw run, `merge_action_exact` for the raw fragment | Very high: one container, `_bulk_docs` with `new_edits=false` injects any revision with any history; deterministic, sequential | Transcription error; read path; cluster read repair if `n > 1` |
| 2 | **PouchDB** (`pouchdb-merge`) | `merge` stems every root-to-leaf path and re-merges (`merge.js`); `revExists` filter (`updateDoc.js`) | Same as CouchDB (it replicates with CouchDB) | High: about 300 lines of JS, transcribed | Same as CouchDB, plus a cross-implementation comparison | Very high: Node, memory adapter, `bulkDocs` with `new_edits: false` | Browser adapters (`indexeddb`) use other code; scope to Node |
| 3 | **pgEdge Spock** (multi-master Postgres) | Conflict resolution in `spock_conflict.c`: last update wins by commit timestamp and origin; delta-apply columns; update on a missing row | FIFO per origin, any interleaving across origins | Medium: per-row model; commit timestamps must be controlled | `tconv_exact` and `dalo_exact` with origins as the declared independence; CCR | Medium: three Postgres nodes, pause and resume subscriptions to fix orders | Clock and timing; large C surface; config variants |
| 4 | **cr-sqlite** | Merge of `crsql_changes` rows: per-column last writer wins with deterministic tie breaks, causal length for delete and resurrect | Any order, duplicates (designed for it) | High (Rust) | `merge_action_exact` (compensation-free) | Very high: SQLite extension, inject change rows in any order | Low payoff: no repair; convergence is the documented claim; unmaintained since 2024 |
| 5 | **Kubernetes controllers** (ReplicaSet adoption with overlapping selectors; HPA against manual scaling) | Reconcile loops (`replica_set.go`, `controller_ref_manager.go`) | Informer events, requeues, rate limits | Low: caches, expectations, timing | Layer C: `C1_closed`, `C2`, `bad_lasso_refutes` | Medium: kind or envtest | Timing nondeterminism; documented as unsupported |
| 6 | **Couchbase Lite** (LiteCore revision trees, `maxRevTreeDepth` pruning) | Pruning after insert | As CouchDB | Medium: C++, moving to version vectors in 3.2 | As CouchDB | Medium: native build | Version churn |
| 7 | **Syncthing** conflict handling | Conflict copies named by modification time and device ID | Any order among devices | Medium | CCR | Low to medium: several instances, network control | Timing, file system |
| 8 | **Riak KV** sibling resolution and vector clock pruning | Pruning, `allow_mult` | Any order | Medium | `alo_exact` | Low: maintenance and build | Project status |
| 9 | **Cassandra / Scylla** tombstones and `gc_grace_seconds` | Compaction purges tombstones | Anti-entropy repair, hinted handoff | Medium | State descent with GC as `N` | Medium | Zombie resurrection is already documented |
| 10 | **Kafka** log compaction with tombstones | Cleaner keeps the last value per key, drops tombstones after `delete.retention.ms` | Total order per partition | High | State descent | High | The failure mode is documented |
| 11 | **Automerge, Yjs, Loro** (movable tree) | Loro's move undoes and redoes by timestamp, skipping cycles | Any order | High | `merge_action_exact` | High | Convergence is proved in the literature (Kleppmann et al. 2021); low novelty |
| 12 | **Replicache, Zero, PowerSync, ElectricSQL** | Server applies mutations in one order; clients rebase | One server order | n/a | n/a | n/a | Convergence holds by construction; not a reordering question. ElectricSQL's older compensations for foreign keys are archived |
| 13 | **Temporal, Camunda, Axon** sagas | Compensations in reverse order inside one workflow | One deterministic history per workflow | n/a | n/a | n/a | No concurrent updates to shared state |

The top two are one family on purpose: they are the only candidates where the repair is a
deterministic function in the code, the delivery that reorders it is the normal operation of the
product, and a harness can put any revision in any order through a public API. Spock is the best
candidate of a different kind and the natural next target.

## (b1) CouchDB: replicated revisions under revs_limit

### The model

Transcribed from `apache/couchdb` (`main` at `6c0704e`, 2026-10-09; the modeled functions are
identical in tag 3.5.3) into [route2/couch_model.py](route2/couch_model.py):

- **State:** the revision tree of one document, a list of `(start position, node)` trees, with
  each leaf marked deleted or not. Internal bodies are kept in the model; every comparison below is
  up to *shape* (keys, structure and leaf deletion flags), which is what survives compaction. The
  steps respect shape (checked on all 36 trees of the closure in `gen_gsm.py`).
- **Event:** one replicated revision: `_rev = pos-id`, `_revisions` with a list of ancestor ids,
  `_deleted` or not; the request `_bulk_docs` with `new_edits=false` and one document. This is what
  the replicator writes on the target.
- **Governed step:** (1) the filter of `prep_and_validate_replicated_updates`: merge the path into
  the tree without stemming; if the incoming revision is not a leaf of the result, or was a leaf
  already, ignore the request; (2) `couch_key_tree:merge`; (3) `couch_key_tree:stem` to
  `revs_limit` (when `stem_interactive_updates` is true, the default). `stem` falls back to
  `repair_tree` when a key appears twice, which merges the truncated leaf paths again and does not
  stem the result.
- **Raw run:** the same with `stem_interactive_updates = false`; the repair is then applied once,
  by compaction (`couch_bt_engine_compactor.erl` calls the same `stem`).
- **Observations:** the leaf set with deletion flags (`GET /db/doc?open_revs=all`), the winner,
  and whether the document is live (`GET /db/doc` returns 200 or 404 deleted). Ancestor lists are
  not observed: reads truncate `_revisions` to `revs_limit` (`couch_db:make_doc`).
- **Abstracted away:** bodies and attachments; validation functions (none installed); the cluster
  layer (one node, `q=1`, `n=1`, so no internal replication or read repair); batching (one
  document per request).

### What the framework computes

Scenarios ([route2/compute.py](route2/compute.py), output [route2/compute.out](route2/compute.out)):

- **S1:** a linear history `1-a, 2-b, 3-c, 4-d` with `4-d` a deletion. Each revision is delivered
  with its full history from the root (a source that never stemmed). `revs_limit = 3`. Four
  events, 24 orders.
- **S2:** the same history, each revision delivered with every history length up to 2 (sources
  that stem at the same limit). `revs_limit = 2`. Seven events, 5040 orders.
- **S3:** S1 plus a real conflict branch `3-e` under `2-b`. `revs_limit = 2`.

Results (all over exactly-once orders; duplicates follow by `alo_exact`):

1. **Idempotence holds everywhere.** In every scenario each revision is idempotent at every reachable
   state where it is delivered for the first time. So `alo_exact` reduces convergence with
   duplicates to convergence without them: an immediate redelivery never changes the state, and
   every effect of a duplicate comes from non-commutation (a late redelivery).
2. **Commutation fails (CCR fails), and the failure is visible at the coarsest level.** The
   smallest witness in S1 is at the empty state: `1-a` then `4-d` ends deleted; `4-d` then `1-a`
   ends live. With `4-d` first, the tree is stemmed to `{2: b -> c -> d}`; `1-a` no longer overlaps
   it, so it is added as a separate tree and becomes a live leaf. A deleted document comes back.
3. **The exact rule in S1.** The document ends live on exactly 6 of the 24 orders: those where `1-a`
   is delivered last. On the other 18 it ends deleted with the single leaf `4-d`. The non-obvious
   part is the healing: if `2-b` or `3-c` arrives after the stray `1-a`, its path `a -> b` merges into
   the stray tree, the key `b` now appears twice, `stem` throws `dupe_keys`, and `repair_tree`
   re-merges the truncated paths into one tree `a -> b -> c -> d`. The stray leaf disappears. The
   repaired tree then holds 4 revisions with `revs_limit` 3, until the next update or compaction
   stems it.
4. **State descent fails, and the raw run converges.** With `stem_interactive_updates = false`
   and a compaction at the end, all 24 orders of S1 end deleted with the single leaf `4-d`. Raw
   merges of full root paths commute and are idempotent (the compensation-free fragment, where
   `merge_action_exact` gives convergence), and stemming once at the end gives one tree. Stemming
   after every update does not descend along merges: at the reachable raw state after `4-d`,
   `stem (merge (stem T) 1-a)` has the leaf `1-a` and `stem (merge T 1-a)` does not (the filter drops
   `1-a` as internal). This is `crdt_boundary`'s picture in a real system: the revision tree is a
   CRDT on root paths until a per-update repair is added, and that repair breaks state descent.
5. **With partial histories even the raw run diverges.** In S2, CCR fails for both configurations.
   The distributions over the 5040 orders:

   | Outcome over 5040 orders | CouchDB, interactive stemming | CouchDB, raw then compaction |
   |---|---|---|
   | live | 4520 | 4935 |
   | deleted | 520 | 105 |
   | winner `3-c` / `2-b` / `1-a` / `4-d` deleted | 2520 / 1302 / 698 / 520 | 3864 / 840 / 231 / 105 |
   | distinct leaf sets | 8 | 8 |

   The full leaf-set table is in `compute.out`. 1932 of the 5040 interactive orders pass through
   `repair_tree`.
6. **A real conflict masks the deletion but not the divergence.** In S3 the live branch `3-e` wins
   on every order, but the leaf set still differs on 24 of 120 orders (the stray `1-a`).

**gsm on the model.** `gen_gsm.py` writes a registry with one enum variable (the tree, up to shape,
9 states closed under the raw update and `stem`), the four S1 revisions as events (raw update), and
the invariant "stemmed" with repair `stem`. gsm's governed step is then CouchDB's step, except that
gsm repairs until the invariant holds where CouchDB stems once ([route2/gsm_couch.out](route2/gsm_couch.out)):

```
WFC: PASS (max repair depth: 2)
CC (Compensation Commutativity): FAIL
  Events: (replicate_1-a, replicate_2-b)
  State:  {tree=s5_4dx}
  replicate_1-a→replicate_2-b: {tree=s5_4dx}
  replicate_2-b→replicate_1-a: {tree=s6_1a_4dx}
```

The CC counterexample is the healing of result 3: after `4-d`, delivering `1-a` then `2-b` ends
deleted, and `2-b` then `1-a` ends live. "Max repair depth 2" says that CouchDB's `stem` is not
idempotent on these trees (the output of `repair_tree` is not stemmed), so it is not a canonical
repair in the sense of `rho_star_qualifier`. The observable predictions do not depend on this: on
the states S1 reaches, one more `stem` does not change the leaf set.

### Why this is not already documented

- CouchDB documents one case. `test/elixir/test/rev_stemming_test.exs`, "revs limit produces
  replication conflict": if more edits than `revs_limit` are made between replications, the later
  path does not overlap the old one and a spurious conflict appears. That is a gap in the
  delivered histories, not an order effect.
- PouchDB issue #9085 (open) reports the same gap mechanism: a deletion does not propagate from
  CouchDB to PouchDB with a low `revs_limit`.
- `stem_interactive_updates` is documented only as a performance switch (2.2 release notes,
  `default.ini`).
- Searched and not found (CouchDB and PouchDB issue trackers, docs, tests): the order dependence
  with full histories; the rule "live iff `1-a` is last"; the healing by a later ancestor through
  `repair_tree`; that `stem_interactive_updates = false` changes outcomes; any count over orders.
  A wider web search was not run.

The mechanism (stemmed trees no longer overlap old paths) is known to CouchDB developers. What is
computed here is the exact consequence per order, and the parts nobody states.

### Test plan against the real software

- **Software:** the official `couchdb:3.5.3` image, single node, admin user, `[cluster] q=1, n=1`.
- **Harness:** [route2/couch_harness.py](route2/couch_harness.py) (not run). For each order: a fresh
  document id; one `POST /db/_bulk_docs` per revision with `new_edits: false`, `_rev`, `_revisions`
  and `_deleted`; each request waits for its response. Then `GET /db/id?open_revs=all` (leaf set,
  deletion flags) and `GET /db/id` (live or 404). Compare with the model's prediction for that
  order (`export_predictions.py` writes them; `predictions_S1.json` is included).
- **Configurations:** (i) defaults; (ii) `PUT /_node/_local/_config/couchdb/stem_interactive_updates`
  `"false"`, every order delivered, then `POST /db/_compact` and wait until `compact_running` is
  false, then read.
- **Orders:** S1 all 24 orders in both configurations; S2 all 5040 orders in both configurations;
  S3 all 120. About 95,000 requests per repetition (S2 dominates: 9 requests per order), well
  under an hour on a laptop.
- **Duplicates:** with `--dup` the harness delivers every revision twice in a row; the model
  predicts the same observations as without (item 5 of the draft P3).
- **Repetitions and nondeterminism:** three repetitions, each in a fresh database. The modeled path
  is sequential and deterministic, so the three must agree; any disagreement between repetitions
  is reported as nondeterminism and investigated before scoring. A mismatch with the model counts
  only if it reproduces in all three.
- **Revision ids:** 32 hex characters (`aaaa...`, `bbbb...`), so CouchDB stores them as 16-byte
  binaries whose order is the order used in the model.

### Risks

- **Model wrong:** a transcription error in `merge_at`, `stem_tree` or `repair_tree`; Erlang term
  order in `lists:sort` on ties (none expected with distinct keys); the leaf filter's use of
  `multi_merge`. The S1 claims touch the filter, `merge_at` with a gap, and one `repair_tree`
  call per healing order; S2 exercises `repair_tree` on 1932 orders and is more fragile.
- **Harness wrong:** `_bulk_docs` semantics differ from the replicator's in some detail not modeled
  (for example attachment stubs; none are used).
- **Software bug or nondeterminism:** none expected on this sequential path; three repetitions guard.

## (b2) PouchDB: the same model, implemented separately

### The model

Transcribed from `apache/pouchdb` (`master` at `27de91f`, 2026-08-25; `merge.js` last changed
2023-11-21, before release 9.0.0) into [route2/pouch_model.py](route2/pouch_model.py):

- **Governed step** (`updateDoc.js` with `new_edits: false`): skip if the revision already exists
  anywhere in the tree (`revExists`); otherwise `doMerge` (find the branch the path joins, or add it
  as a separate tree), then `stem`. PouchDB's `stem` differs from CouchDB's: it cuts every
  root-to-leaf path to `revs_limit` on its own and re-merges the cut paths only when they start at
  the same position with the same root.
- **Observations:** `db.get(id, {open_revs: 'all'})` and `db.get(id)`, on the memory or LevelDB
  adapter in Node (both use `pouchdb-adapter-utils`; the browser `indexeddb` adapter does not and is
  out of scope).

### What the framework computes

- Idempotence at first delivery holds; CCR fails at the same 2-event witness as CouchDB.
- **S1:** live on exactly 12 of 24 orders: those where `1-a` comes after `4-d`. No healing: a later
  `2-b` or `3-c` already exists in the tree, so `revExists` skips it.
- **CouchDB and PouchDB disagree** on 6 of the 24 S1 orders (each has `4-d` before `1-a` and some
  of `2-b`, `3-c` after `1-a`; for example `4-d, 1-a, 2-b, 3-c`: CouchDB deleted, PouchDB live).
- **S2:** live on 5023 of 5040 orders, deleted on 17; winner `3-c` 2520, `2-b` 2352, `1-a` 151,
  `4-d` deleted 17. Disagreement with CouchDB: 503 orders on live or deleted, 1091 on the winner,
  1932 on the leaf set.
- **S3:** the leaf set differs from CouchDB's on 16 of 120 orders.

Why not documented: the same sources as above; nothing compares the two implementations' stemming,
and PouchDB's source comment says it follows `couch_key_tree.erl`.

### Test plan

[route2/pouch_harness.js](route2/pouch_harness.js) (not run): `npm install pouchdb@9.0.0
pouchdb-adapter-memory@9.0.0`; one fresh database per order with `revs_limit: k`; one `bulkDocs`
per revision with `new_edits: false`; read and compare with `predictions_<S>.json`. S1 (24), S2
(5040), S3 (120), three repetitions, with and without `--dup`. Risk: as for CouchDB, plus JavaScript details (stable sort,
in-place mutation shared between trees) that the transcription reproduces but could miss.

## (c) Draft P3

Not committed. The owner may copy it to `P3.md` unchanged, or narrow it (see the probability).

### Claim: CouchDB and PouchDB resurrect deleted documents on computed orders, and only on those

**Model.** As in (b1) and (b2): a document's revision tree; events are replicated revisions written
with `new_edits=false`, one per request; the governed step is the implementation's filter, merge
and stem; observations are the leaf set with deletion flags and whether `GET` returns the document.

**Claim (the computed answer).** On a single-node CouchDB 3.5.3 (`q=1`, `n=1`) and on PouchDB 9.0.0
in Node (memory adapter), for one document with the linear history `1-a, 2-b, 3-c, 4-d` where
`4-d` is a deletion, each revision delivered once with its full history and `revs_limit = 3`
(scenario S1), and for scenario S2 (`revs_limit = 2`, every revision with every history length up
to 2), the final leaf set and live flag of every delivery order are the ones in
`route2/predictions_S1.json` and `route2/predictions_S2.json` (generated by
`export_predictions.py` at the commit that adds P3). In particular:

1. CouchDB with default settings ends live (winner `1-a`, leaves `{1-a, 4-d deleted}`) on exactly
   the 6 S1 orders where `1-a` is delivered last, and deleted with the single leaf `4-d` on the other
   18.
2. CouchDB with `stem_interactive_updates = false`, compacted after the last delivery, ends deleted
   with the single leaf `4-d` on all 24 S1 orders.
3. PouchDB ends live on exactly the 12 S1 orders where `1-a` comes after `4-d`.
4. On S2, CouchDB with default settings ends live on 4520 of the 5040 orders and deleted on 520,
   with the per-order leaf sets of the prediction file.
5. Redelivering a revision immediately after its first delivery never changes the observations, in
   either implementation.

**Plain sentence.** The framework computes, from the code, exactly which arrival orders of the same
replicated revisions bring a deleted CouchDB or PouchDB document back to life, and the running
databases agree order by order.

**Derivation.**
- `alo_exact`: convergence under duplicates is commutation at reachable states plus idempotence at
  first delivery; the model satisfies the second and fails the first, so divergence comes only from
  order, and items 5 and 1 to 4 are the two halves.
- `causal_exact` (CCR) locates the failing pairs; the smallest is `1-a` against `4-d` at the empty
  state.
- `normalization_descent` and `state_descent_iff_cc2`: interactive stemming is the governed run,
  compaction after the raw run is `N` of the raw run; descent fails at the state after `4-d`, so the
  two configurations must differ (item 2 against item 1), while raw merges of full paths are in the
  compensation-free fragment (`merge_action_exact`) and converge.
- gsm, on the generated registry, reports the CC failure `(1-a, 2-b)` after `4-d` and a repair that
  is not idempotent.
- The per-order answers are the exhaustive evaluation of the governed step of each implementation.

**Pass.** Every order of S1 in all three configurations (72 runs) and every order of S2 in CouchDB
with default settings (5040 runs) gives the predicted leaf set and live flag, in each of three
repetitions, and item 5 holds on every immediate redelivery tried (each revision redelivered once
after its first delivery, on every S1 order).

**Fail.** Any order whose observation differs from the prediction in all three repetitions, in any
configuration. An order that differs in some repetitions and not others is recorded as
nondeterminism, investigated, and scored as a failure if it cannot be traced to the harness.

**What a refutation looks like.** For example, CouchDB keeps the stray `1-a` after a later `2-b`
(no healing, so the S1 count is 12, not 6), or the stem-off configuration diverges, or the S2
counts differ. Any of these means the transcription of the code is wrong somewhere, or the HTTP
path does more than the modeled functions.

**How it could fail.** Through the model, not the mathematics: a transcription error in
`couch_key_tree` (the `repair_tree` path most of all), a difference between `_bulk_docs` and the
modeled update path, or an unmodeled read-path effect.

**Probability that the real systems match the model.** About 0.6 for the whole claim: about 0.85 for
items 1 and 2 (they use the filter, `merge_at` across a gap and one `repair_tree` call), 0.85 for
item 3, 0.95 for item 5, and about 0.7 for item 4 (1932 of its orders go through `repair_tree`
and sibling ordering). Dropping item 4 gives a claim at about 0.75.

**Literature and documentation check.** `rev_stemming_test.exs` (the gap case), PouchDB issue #9085
(the gap case, deletion not propagated), the 2.2 release notes and `default.ini` (performance
only). No statement found of the order dependence with full histories, the healing, the effect of
`stem_interactive_updates`, or the CouchDB and PouchDB difference.

**Size of the test.** About 140,000 HTTP requests for CouchDB (S1 in two configurations and with
duplicates, S2 once, three repetitions; S2 is 9 requests per order) and a few hundred `bulkDocs`
calls for PouchDB; about an hour including setup.

## Files

Under [route2/](route2/):

| File | What it is |
|---|---|
| `couch_model.py` | CouchDB transcription: `merge`, `stem`, `repair_tree`, the replicated-update filter, observations |
| `pouch_model.py` | PouchDB transcription: `doMerge`, `mergeTree`, `stem`, `revExists`, `winningRev` |
| `compute.py`, `compute.out` | The exact conditions (CCR, idempotence), the per-order distributions, the cross-implementation comparison |
| `gen_gsm.py`, `gsm_couch/`, `gsm_couch.out` | The S1 registry for gsm and its build report |
| `export_predictions.py`, `predictions_S1.json` | Per-order predictions (S2's file is generated, about 5040 rows) |
| `couch_harness.py`, `pouch_harness.js` | The harnesses for the test, not run |

Reproduce: `cd research/predictions/route2 && python3 compute.py && python3 gen_gsm.py && (cd
gsm_couch && go run .)`.
