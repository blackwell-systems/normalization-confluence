# Can the CouchDB replicator reach the P3 behaviors?

An exploration, not a scored prediction. P3 ([PR #165](https://github.com/blackwell-systems/normalization-confluence/pull/165),
`research/predictions/P3.md` on branch `research/p3-test`) drove CouchDB 3.5.3 by direct injection
(`POST /db/_bulk_docs` with `new_edits: false`) and found two behaviors:

1. **Resurrection (P3 claim 1).** With `revs_limit` 3, a stray old revision `1-a` arriving after the
   history of a deleted document has been stemmed brings the document back, winner `1-a`.
2. **validate_doc_update dependence (P3, unscored S2 section).** In 3.5.3 `couch_db:before_docs_update`
   runs `prep_and_validate_replicated_updates` only when the database has a `validate_doc_update`
   function (or the request holds a design document or a document with attachments). That function
   drops a replicated revision that is already a leaf or is not a leaf after the merge. So when a
   revision is delivered first with a short history and later with a longer one, the same deliveries
   end live on one database and deleted on another, depending only on whether it has a
   `validate_doc_update` function, even one that accepts everything.

The question here: can the real replicator (`POST /_replicate`) produce these, with no injection?

**Answer: yes, both.** Every write below is an ordinary interactive edit on a source database, and
every revision reaches a target through one-shot `POST /_replicate` runs, one after another. The
second behavior needs a heuristic in the 3.5.x replicator that skips `_revs_diff`; it triggers with
default replication settings once the replication has seen enough documents the target lacks.

## Setup

- CouchDB 3.5.3, Homebrew build (`/opt/homebrew/opt/couchdb`), the same node P3 used: single node,
  `[cluster] q = 1, n = 1`, admin user, `127.0.0.1:5984`, replicator settings at their defaults,
  `stem_interactive_updates` unset (default `true`). Started with `/opt/homebrew/opt/couchdb/bin/couchdb`.
- Every replica is a database on that node, with its own `_revs_limit`. "T1" never has a design
  document; "T2" has `_design/accept` with
  `validate_doc_update: function(newDoc, oldDoc, userCtx, secObj) {}` (accepts everything).
- Replications: `POST /_replicate {"source": ..., "target": ...}`, one-shot, sequential, checkpoints on
  (the default). Options used are listed per step: `doc_ids` for replicas that sync only document
  `X`, and in `vdu_min` `worker_processes: 1, worker_batch_size: 1` to make the trigger small.
- Script: [replicate.py](replicate.py) (Python 3 standard library only).
  `COUCH=http://admin:p3password@127.0.0.1:5984 python3 replicate.py [scenario ...]`.
  Output: [results/run.log](results/run.log) and one JSON file per scenario in [results/](results/)
  with every step, the per-session replication counters (`missing_found`, `docs_written`, ...), and the
  final state of each target (`GET /db/X?conflicts=true&deleted_conflicts=true` and
  `GET /db/X?open_revs=all&revs=true`, leaves shown as root-to-leaf paths). The whole set was run
  twice; the outcomes agree.
- Revision labels: `1-a`, `2-b`, ... are the revisions CouchDB generated for the edits (ids in the
  JSON files). A leaf written `1-a/2-b/3-d` is one path; `1-a; 2-b` is two separate roots.

## How the replicator sends revisions (3.5.3 source)

`src/couch_replicator/src/`:

1. **Changes.** `couch_replicator_changes_reader` reads the source `_changes` with `style=all_docs`
   (or `main_only` with `winning_revs_only`): for each changed document, its current leaf revisions.
2. **Missing check.** `couch_replicator_worker:find_missing` posts those leaves to the target's
   `_revs_diff`. A revision is missing when it is not in the target's revision tree, so a revision the
   target has stemmed away counts as missing.
3. **Fetch.** Missing revisions are fetched from the source with `_bulk_get` (or
   `GET /db/id?open_revs=[...]`) with options `[latest, revs]`. `_revisions` is the path stored on the
   source. The replicator does not shorten it, but the source has already stemmed it to its own
   `revs_limit`: `couch_db_updater:maybe_stem_full_doc_info` stems on every update, interactive or
   replicated, while `stem_interactive_updates` is true (the default). So a replica with
   `revs_limit` 1 sends `_revisions` of length 1.
4. **Write.** `POST /target/_bulk_docs` with `new_edits: false`; the target merges and stems to its own
   `revs_limit`.

**The `_revs_diff` skip.** `find_missing` keeps, per worker, an exponential moving average of the
fraction of checked revisions that were missing on the target (`REVS_DIFF_RATIO_DECAY` 0.4, start 0).
When that average exceeds `REVS_DIFF_RATIO_THRESHOLD` 0.95, later batches skip `_revs_diff` and treat
every leaf in the batch as missing, until `REVS_DIFF_RETRY_SEC` (37 s) has passed since the last
check. After k consecutive batches in which everything was missing the average is 1 - 0.6^k:
0.922 after 5, 0.953 after 6. So from the 7th batch on, a revision the target already holds is
fetched and written again, with the source's history. This is the "same revision, longer history
later" delivery that P3's S2 used, now produced by the replicator. Without the skip, sequential
replication never delivers a revision the target already has, and the `validate_doc_update` filter
has nothing to drop: a delivered revision is absent from the target and, being a source leaf, is a
leaf after the merge.

## Scenario `resurrect` (P3 claim 1)

Replicas: A (`revs_limit` 1000), C (1000), T1 and T2 (3; T2 with the accept-all
`validate_doc_update`), U1 and U2 (as T1 and T2, opposite order), E (1000).

1. A: create `X` (`1-a`). Replicate A to C. C is a replica that synced once and went quiet.
2. A: edit to `2-b`, edit to `3-c`, delete (`4-d`).
3. T1, T2: replicate A, then C. U1, U2: replicate C, then A.
4. Replicate T1 to A, A to T1, T1 to E, A to E.

| Database | Final state | Leaves |
|---|---|---|
| T1 (no VDU), A then C | **live, winner `1-a`** | `1-a`; `2-b/3-c/4-d` deleted |
| T2 (VDU), A then C | **live, winner `1-a`** | `1-a`; `2-b/3-c/4-d` deleted |
| U1 (no VDU), C then A | deleted | `2-b/3-c/4-d` deleted |
| U2 (VDU), C then A | deleted | `2-b/3-c/4-d` deleted |
| A | deleted | `1-a/2-b/3-c/4-d` deleted |
| C | live, `1-a` | `1-a` |
| E | **live, winner `1-a`** | `1-a`; `2-b/3-c/4-d` deleted |

T1 stores the deletion as `2-b/3-c/4-d` after stemming, so `_revs_diff` reports C's `1-a` as missing
and the replicator delivers it as a separate live root. The opposite order ends deleted (the deletion
path joins `1-a` and stemming then drops it). The `validate_doc_update` function makes no difference
here: `1-a` is absent from the target and is a leaf after the merge, so the filter keeps it. After
step 4, A stays deleted and T1 stays live: A to T1 finds nothing missing (`4-d` is on T1), and T1 to A
finds nothing missing (`1-a` is an interior revision on A). Replication between them never repairs
it, and a replica that pulls from T1 (E) receives `1-a` and ends live as well. This matches the known
stemming tradeoff (COUCHDB-1649); the point here is only that the replicator alone reaches it.

## Scenario `vdu_min` (the validate_doc_update dependence)

Replicas: A (`revs_limit` 1000), C (1000), B (`revs_limit` 1), D (`revs_limit` 2), T1 (1000, no
VDU), T2 (1000, accept-all VDU). C, B and D replicate from A with `doc_ids: ["X"]`, so they hold only
`X`.

| Step | Action | Effect |
|---|---|---|
| 1 | A: create `X` (`1-a`); replicate A to C | C: `1-a` |
| 2 | A: write 6 unrelated documents | they precede `X`'s next change in A's `_changes` |
| 3 | A: edit `X` to `2-b`; replicate A to B | B stems to history `[2-b]` |
| 4 | Replicate C to T, then B to T (T = T1, T2) | both: roots `1-a`; `2-b`, live, winner `2-b`, conflict `1-a` |
| 5 | Replicate A to T with `worker_processes: 1, worker_batch_size: 1` | the 6 unrelated documents push the average to 0.953; `X`'s batch skips `_revs_diff`, and `2-b` is re-sent with history `[1-a, 2-b]` (`missing_found` 7 of 7) |
|   | T1 after step 5 | joined: `1-a/2-b`, no conflict |
|   | T2 after step 5 | `2-b` was already a leaf, so `prep_and_validate_replicated_updates` drops it: still `1-a`; `2-b` |
| 6 | A: delete `X` (`3-d`); replicate A to D | D stems to history `[2-b, 3-d]` |
| 7 | Replicate D to T1, D to T2 | |

| Target | Final state | Leaves |
|---|---|---|
| T1 (no VDU) | **deleted** | `1-a/2-b/3-d` deleted |
| T2 (accept-all VDU) | **live, winner `1-a`** | `1-a`; `2-b/3-d` deleted |

Same replicas, same replications, in the same order; the only difference between T1 and T2 is a
design document whose `validate_doc_update` accepts everything.

**Controls.**

| Scenario | Change from `vdu_min` | T1 | T2 |
|---|---|---|---|
| `vdu_control` | the 6 unrelated documents written after the `2-b` edit (so they follow `X` in `_changes`) | live, `1-a` | live, `1-a` |
| `vdu_five` | 5 unrelated documents instead of 6 (average 0.922) | live, `1-a` | live, `1-a` |
| `vdu_default` | 20000 unrelated documents before the `2-b` edit, step 5 with **default** replication settings (4 workers, batch size 500) | **deleted** | **live, `1-a`** |
| `vdu_default_control` | 20000 unrelated documents after the `2-b` edit, default settings | live, `1-a` | live, `1-a` |

In both controls step 5 sends only the unrelated documents (`missing_found` 6 of 7, or 20000 of
20001): `_revs_diff` runs for `X` and reports `2-b` present. So T1's outcome also depends on
something outside document `X`: how many documents the target lacked that came before `X` in the
source's changes feed during one replication. With default settings, an initial replication of a
large database into a target that already holds a few of its documents from other replicas meets
that condition.

## Reported upstream

The `validate_doc_update` dependence was reported to Apache CouchDB on 2026-10-11 as
[apache/couchdb#6162](https://github.com/apache/couchdb/issues/6162), with a curl reproduction of `vdu_min`. The resurrection is the
known stemming tradeoff (COUCHDB-1649) and was not reported.

## Conclusion

Reachable through the real replicator, both behaviors, with no injection.

- **Resurrection:** minimal topology is three databases: a full-history source A, a replica C that
  synced at `1-a`, and a target with `revs_limit` 3. Edit A to `4-d` (deleted), replicate A to T,
  then C to T: T ends live with winner `1-a`, and replication between A and T never repairs it. This
  path uses only ordinary `_revs_diff`; the `validate_doc_update` function plays no part.
- **validate_doc_update dependence:** needs a revision to reach a target it already holds, and in
  sequential replication that happens only through the `_revs_diff` skip in
  `couch_replicator_worker` (`find_missing` after the missing-ratio average passes 0.95). The minimal
  run is `vdu_min` above: a `revs_limit` 1 replica delivers `2-b` with history `[2-b]`, then the full
  source re-delivers `2-b` with history `[1-a, 2-b]` after 6 or more batches of documents the target
  lacked, then a `revs_limit` 2 replica delivers the deletion with history `[2-b, 3-d]`. The target
  without a `validate_doc_update` function ends deleted; the target with an accept-all one ends live
  with winner `1-a`. Default replication settings reach it too (`vdu_default`).
- **Without the skip** (fewer preceding missing documents, or the 37 s retry window forcing a
  `_revs_diff`), sequential replication does not reach the second behavior: each delivered revision is
  a source leaf absent from the target, so the filter keeps it and both targets end the same. The
  other ways to deliver a revision the target already has are races (two replications into one
  target at once, or source writes between `_changes` and the fetch with `latest`); those were not
  run.
