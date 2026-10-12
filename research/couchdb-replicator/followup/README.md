# CouchDB 6162: default-settings and mixed-limit tests

Local test evidence for the upstream CouchDB issue
([apache/couchdb#6162](https://github.com/apache/couchdb/issues/6162)) about replication results
depending on whether the target has a `validate_doc_update` function (VDU). Run on 2026-10-12 against a
fresh Homebrew CouchDB 3.5.3 (single node, q=1, n=1, admin `admin` / `p3password` on 127.0.0.1:5984,
a throwaway local install, uninstalled afterwards). Archived here unchanged from the working directory,
except that one absolute local path in a traceback in `results/deep_early.log` was shortened; that log
ends in an assertion of the test harness itself (a `new_edits: false` injection sent without a
history) in the unfinished scenario `early_inj_Afirst_ddoc`, which has no result file; it is not a
CouchDB result. Summary in
[../README.md](../README.md#follow-up-mismatched-revision-limits).

## Result

- **Same `_revs_limit` on every database (1000, and also 2, 3, 10, 100): no divergence** in 23 runs,
  including documents edited 1,205 times, an early-synced target, a mid-history replica, and two
  sources in both orders, via the replicator (with and without the `_revs_diff` skip) and via
  `_bulk_docs` with `new_edits:false`.
- **Mixed limits: divergence every time.** Replicas B and D at a lower limit L, A, C and the targets
  at 1000, document history deeper than L: the target without a VDU ends deleted; the target with an
  accept-all VDU ends live on a stale revision. Reproduced at L = 3, 10, 100 and 999 (999 needs a
  1,000-edit document), via both the replicator and `_bulk_docs`, and with default replication
  settings when about 20,000 unrelated documents precede X in A's changes feed.
- **Control:** the issue's original script (limits 1 and 2) gives the reported split.

## Minimal recipe

A, C and targets at 1000; B and D at any lower limit L.

1. Create X on A; replicate A to C (C holds rev 1).
2. Edit X on A to generation L+1; replicate A to B (B keeps L revisions, without rev 1).
3. Targets replicate C, then B (they now hold two roots).
4. Targets replicate A; at least 6 batches of missing docs before X make `find_missing` skip
   `_revs_diff` and re-send X with its full history.
5. Delete X on A; replicate A to D; targets replicate D.

## Cause (CouchDB code)

- The divergence is in the server: `_bulk_docs` reproduces it without the replicator. The replicator
  only supplies the re-delivery, through the `_revs_diff` skip in `couch_replicator_worker:find_missing`
  (missing ratio above 0.95).
- Without a VDU, the re-sent revision is merged (`couch_key_tree:merge`), and
  `maybe_stem_full_doc_info` then calls `couch_key_tree:stem`, which finds duplicate keys and runs
  `repair_tree`, joining the two roots.
- With a VDU, `prep_and_validate_replicated_updates` runs first; the re-sent revision is already a
  leaf (`IsOldLeaf`) and is dropped in the "ignore but consider it a success" branch, so the roots stay
  separate. The dropped revision never reaches `validate_doc_update`, so `oldDoc` is not the mechanism.
- At a uniform limit, every database stores the same last min(generation, L) ancestors for a leaf, so
  a longer copy of a leaf never exists, which is why uniform limits cannot trigger it.

## The dropped revision never reaches the VDU (tested)

`reject_vdu.py` (log in `results/reject_vdu_3.log`), run 2026-10-12 on a fresh 3.5.3: target T2 holds X
as two roots (`1` and `2..4`). A VDU that rejects every write to X is installed, then:

- Re-delivery of leaf 4 with full history `1..4`: `HTTP 201 []`, no error, tree unchanged (`[1]; [2..4]`).
  The VDU was never called for it.
- Control, a revision T2 does not have (deleted leaf 5): `forbidden`, "vdu saw 5-...". The VDU is
  active and rejects new revisions.
- Same re-delivery on a target with no VDU: the roots join (`[1..4]`), conflict gone.

So with a VDU the re-sent leaf is dropped before `validate_doc_update` runs, consistent with the
`IsOldLeaf` branch of `prep_and_validate_replicated_updates`.

## Side findings

- A design document in the same `_bulk_docs` request makes a target without a VDU take the filtered
  path too (`ValidatePred` in `before_docs_update` fires on any design doc or attachment in the
  batch), so the outcome also depends on batch composition.
- At default settings, a document with more than 1,000 edits plus an early-synced target comes back
  live on the stale early revision after a delete, on both targets: the known stemming resurrection
  (COUCHDB-1649), not this bug.

## Files

- `control_issue.sh`: the issue's repro.
- `couchlib.py`: harness (needs a running CouchDB at 127.0.0.1:5984 with the admin above).
- `deep.py`: default-limit deep-history tests (1a, 1b, 2).
- `limits.py`: uniform and mixed-limit sweeps, plus controls.
- `results/`: logs and one JSON per scenario (steps, replication stats, final state of both targets:
  winner, conflicts, every leaf's full path).
