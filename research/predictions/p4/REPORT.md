# Sync Gateway built-in conflict handling: NC screening

Screening only. Everything below comes from reading source and docs and from an offline model. No Couchbase Server or Sync Gateway was installed or run. No custom resolvers are in scope. Nothing was posted anywhere.

**Classification: COUNTEREXAMPLE CANDIDATE** (race-dependent; caveats in section 6).

The setup is the recommended one: one active Sync Gateway running a `push_and_pull` replication with the default resolver, and a passive peer. Suppose two tombstone versions of a document from the same source are in flight to the active side at once, and they commit out of order. Then:
- The active side's version vector moves back to the older tombstone and forgets the newer one.
- From then on, every write to the document on the active side is rejected by the passive side with 409.
- The push checkpoint advances anyway, and the pull has nothing to re-deliver.
- The two clusters stay different (one live, one deleted) with no replication work pending.

With the same writes and a different delivery order, the clusters converge.

## 1. Versions and what was read

- **sync_gateway**: `main` at `f1c59eb25924479b2eecdf244ada5db6a0a935b6` (2026-10-13). The latest 4.x release tag is `4.1.2` (`deb6c06bae2f33320d71d7db9f3b6c5a615d3be1`, 2026-09-04).
  - Diffing `4.1.2..main` over `db/hybrid_logical_vector.go`, `db/blip_handler.go`, `db/crud.go`, `db/document.go` and `db/sg_replicate_conflict_resolver.go` shows no change to any function modelled here.
  - The changes that do exist: renames (`extractHLVFromBlipString` to `ExtractHLVFromBlipString`), throttle-channel `select`s, the import `UseXattrs` condition, and attachment cloning.
  - `4.0.8` has the same `DefaultLWWConflictResolutionType`.
  - The tombstone rule was added by CBG-4894 (commit `6f77f70f`, 2025-10-08, PR #7798; 4.0 backport PR #7804).
- **go-blip** at `002c1b20b67a` (pinned in `go.mod`): `receiver.go` `getPendingRequest` and `context.go` `dispatchRequest`. Each incoming request is read and dispatched in its own goroutine.
- **docs-sync-gateway**: `release/4.0` at `6ff247c5`, `release/4.1` at `2ebc24b8`.
- **Not read**: `sg-bucket`'s `HybridLogicalClock`. Its behaviour is taken from the call sites: `hlc.Now(floor)` with floor = `maxValueForSource(own source)`, per the comments in `crud.go` (`documentUpdateFunc`, `updateHLV`).
- Enterprise-only code was not needed; ISGR and the default resolver are in the BSL source.

Functions read, by file:
- `db/hybrid_logical_vector.go`: `AddVersion`, `InvalidateMV`, `GetValue`, `DominatesSource`, `maxValueForSource`, `AddVersionToPV`, `UpdateHistory`, `UpdateWithIncomingHLV`, `MergeWithIncomingHLV`, `IsInConflict`, `DefaultLWWConflictResolutionType`, `compactWithValue`, `LegacyRevToRevTreeEncodedVersion`
- `db/crud.go`: `PutExistingCurrentVersion`, `PutExistingRevWithConflictResolution`, `resolveHLVConflict`, `resolveConflict`, `resolveLocalWinsHLV`, `resolveRemoteWinsHLV`, `resolveDocMergeHLV`, `localWinsConflictResolutionRevTreeHandling`, `tombstoneActiveRevision`, `updateHLV`, `documentUpdateFunc`, `storeOldBodyInRevTreeAndUpdateCurrent`, `updateWinningRevAndSetDocFlags`, `alignRevTreeHistoryForHLVWrite`, `CheckChangeVersion`, `localVersionDominates`, `CheckProposedVersion`, `CheckProposedRev`, `IsIllegalConflict`, `Put`, `OnDemandImportForWrite`
- `db/document.go`: `Document.IsInConflict`
- `db/blip_handler.go`: `processRev` (lines 1041-1420), `handleChanges`, `handleProposeChanges`
- `db/blip_sync_context.go`: `sendRevision`, and the `sendRevisionWithProperties` response goroutine (409 handling, `sgr2PushProcessedSeqCallback`)
- `db/active_replicator_push.go`, `db/active_replicator_pull.go`: resolver wiring; `ignoreNoConflicts: true` on push
- `db/sg_replicate_conflict_resolver.go`: `ResolveForHLV`, `NewConflictResolverFuncForHLV`, `DefaultConflictResolver`
- `db/change_cache.go`: handling of the `UnchangedCV` flag
- `db/revtree.go`, `db/database.go`: `pruneRevisions` (default `revs_limit` 50 without conflicts), `GetVersionPruningWindow` (default 30 days)
- `topologytest/hlv_test.go`, `topologytest/multi_actor_conflict_clock_tie_test.go`: upstream statements about tombstone convergence and clock ties

## 2. State, events, repair and when repair runs

**Document state per gateway** (4.x, HLV mode):
- `_vv`: current version `cv = (source, value)`, previous versions `pv` (map from source to value), and merge versions `mv`.
- The body and a deleted flag.
- A revision tree, kept for legacy peers.

There is one current version per document. In HLV mode, no unresolved conflict branch is ever stored.

**Events**

- **Local write** (REST `PUT`, `DELETE`, or `PUT {"_deleted":true}` on a tombstone). `updateHLV` with `NewVersion` calls `AddVersion((ownSource, hlc.Now(floor)))`: the old cv moves to pv, and mv is invalidated into pv. `Put` allows a write without `_rev` on a deleted document, and a tombstone write on a tombstone leaf (`IsIllegalConflict` case a).
- **Replicated revision** (`processRev` to `PutExistingCurrentVersion`). `ISGRWrite` is true on both ends, because both use client type `sgr2`. It has two phases:
  1. `handleChanges` calls `CheckChangeVersion`. If the local HLV dominates the change's cv, the rev is not requested.
  2. Later, the `rev` message is handled in its own goroutine (go-blip `asyncRead` to `dispatchRequest`; up to `max_concurrent_revs`, default 5). The write runs inside `updateAndReturnDoc`'s CAS-retry loop, and the callback re-runs on a CAS mismatch.
- **Import** of an SDK write is a background DCP process. Every Sync Gateway write calls `OnDemandImportForWrite` first, inside the same CAS-retry callback. So an unimported SDK mutation is never the base of an SG write.

**Repair** happens inside `PutExistingCurrentVersion`, in the same callback and the same CAS write as the event.

- **Both sides tombstones.** `forceAllowConflictingTombstone = incoming.Deleted && (active-with-resolver || passive sgr2)` (`blip_handler.go:1373`), so it is true at both ISGR ends. When the local document is also deleted, `allowConflictingTombstone` is true and the code calls `doc.HLV.UpdateWithIncomingHLV(incoming)` **with no `IsInConflict` call** (`crud.go:1590-1637`).
- **Otherwise, `IsInConflict` decides:**
  - Equal cv: no-op.
  - Incoming dominates the local cv: `UpdateWithIncomingHLV`.
  - Local dominates the incoming cv: no-op.
  - Equal non-empty mv: no conflict.
  - Anything else: conflict.
- **Conflict at the passive end** (no resolver): the write is rejected with **409**. The active end's response handler counts it (`SendRevErrorConflictCount`) and still calls `sgr2PushProcessedSeqCallback`. The sequence is checkpointed and never retried.
- **Conflict at the active pull end**: `DefaultLWWConflictResolutionType` decides.
  - A tombstone beats a live revision regardless of timestamp. Otherwise the higher cv value wins, and a tie goes to local.
  - Local wins (`resolveLocalWinsHLV`): `newHLV = remote.Copy(); newHLV.UpdateWithIncomingHLV(local)`. The cv is unchanged, the remote cv is added to pv, and the `UnchangedCV` flag is set.
  - Remote wins (`resolveRemoteWinsHLV`): the remote cv is kept, together with the local history.
  - The default resolver never mints a new version.
- **History merge.** `UpdateHistory` / `AddVersionToPV` add a source's value to pv only if it is newer. **If the source equals the receiving HLV's cv source, the value is dropped without comparison** (`sourceIsCV`, `hybrid_logical_vector.go:917-922`).
- **PV compaction** (`compactWithValue`) runs inside `updateHLV` only when pv has more than 5 sources. That is not reachable with two gateways and REST writes.

**When repair runs relative to events.** Resolution and the HLV merge run atomically with the write that delivers the conflicting revision, so there is no stored unresolved state. The one separation is between the dominance gate (`CheckChangeVersion`, phase 1) and the merge (phase 2):
- On every non-tombstone path, `IsInConflict` re-applies the gate inside the write.
- On the tombstone-over-tombstone path, it does not.

## 3. Model

`model/sg_model.py` transcribes section 2. It covers:
- HLV operations, `put_existing_current_version`, the resolver, and `CheckChangeVersion`
- local writes with a per-gateway HLC and floor
- two-phase replication with up to 2 revs in flight per direction, applied in any order
- checkpoints that advance on a push 409

It uses the standard library only.

`model/search.py` explores every interleaving across four topologies:
- T1: A runs `push_and_pull`, B is passive
- T2: A pulls and B pulls
- T3: both run `push_and_pull`
- T4: A runs push only

It crosses these with 4 clock settings (no skew, A behind, B behind, equal values possible) and 8 write programs on 2 gateways and 1 document. The programs are:
- P1: `a1 | b1`
- P2: `a1 | del`
- P3: `del | del`
- P4: `a1,a2 | b1,del`
- P5: `a1,del | b1`
- P6: `a2 | del,del`, where the second delete is `PUT {"_deleted":true}` on the tombstone
- P7: `del,del | b2`
- P8: `a4 | del,b2,del`

The checks are:
- convergence after full synchronisation (every schedule, run until no replication step is enabled)
- one outcome per set of identical writes, with identical HLVs for every write
- (a) state descent: canon N(e(N(s))) = canon N(e(s))
- (b) CC1
- (c) termination
- whether the resolver followed the documented "latest timestamp wins" rule

`model/trace_p8.py` replays the candidate. Outputs are in `model/results/`: `T1_T2_T4_all.txt`, `T3_*.txt`, `attribution.txt` and `trace_p8.txt`.

### Results

Counts are of terminal states. "Canon" means live or deleted, plus the body.

| Finding | Where | Status |
|---|---|---|
| (c) termination | all runs | holds: 0 non-terminating states |
| Canonical divergence, push only | T4, every program with concurrent writes | documented ("Conflicts are not resolved in push replications") |
| Canonical divergence, equal HLV values, both sides resolving | T2/T3, equal values possible, P1 | see note 1 |
| cv differs, both deleted | concurrent tombstones crossing (P3), all topologies | metadata only; matches the upstream comment in `topologytest/hlv_test.go:189-200` |
| Tombstone beats a later live write | all topologies (`lww_lower_ts_won_tombstone` count) | intentional (CBG-4894); the docs do not state it |
| (a) and (b) failures | all topologies | see note 2 |
| **Canonical divergence with pull and push configured** | **T1, P6 and P8, every clock setting** | **candidate** |

1. In the equal-values case, a tie goes to local on each side, so each side keeps its own copy. This needs two sources to produce the identical 64-bit value, and upstream already tests clock ties (`topologytest` `forceClockTie`). It is not a viable prediction.
2. The (a) and (b) failures are mostly expected LWW causality: a write made after a sync dominates, and a concurrent write competes. None of them is a divergence.

### Attribution for the candidate (`results/attribution.txt`)

- It disappears with at most one rev in flight per direction (`--inflight=1`).
- It disappears when a dominance re-check is added to the tombstone path (`--counterfactual`). That re-check is only a model switch, not SG code.
- It does not occur in T2 or T3, because B's own pull resolves it, toward deleted. In P6 and P8, A's re-create is then lost.

## 4. The trace

Topology T1: A runs `push_and_pull` with the default resolver; B is passive. Both start with `x0` (cv `srcA:5`).

Writes:
- On B, all with source `srcB`: `DELETE` (tb1), then `PUT` to re-create (b2), then `DELETE` (tb3).
- On A: `PUT` without `_rev` on the deleted document (a4).

### Order X: the candidate

| Step | A | B |
|---|---|---|
| B deletes (tb1). Pull: A lacks tb1 and requests the rev. | x0 `srcA:5` | DEL `srcB:10` |
| B re-creates (b2), then deletes (tb3). Pull: A requests tb3. | | DEL `srcB:30` |
| The tb3 rev commits first (`no_conflict`). | DEL `srcB:30` | |
| The tb1 rev commits. Both are tombstones, so the code calls `UpdateWithIncomingHLV` with no conflict check, and `srcB:30` is dropped as `sourceIsCV`. | **DEL `srcB:10`** | |
| A re-creates (a4). | live a4 `srcA:40`, pv `srcB:10` | |
| Push a4: B lacks `srcA:40`, and a4's HLV has no `srcB:30`, so `IsInConflict` reports a conflict. B returns **409**, and A's checkpoint advances. | | DEL `srcB:30` |
| Full synchronisation: the pull has no new change on B, and the push is done. | **live a4** | **deleted** |

### Comparison orders

- **Order Y.** The same writes, each with an identical HLV (a4 = `srcA:40`, pv `srcB:10`). Only the order differs: tb1 commits first, then a4 is written, then tb3 lands. At A, tb3 conflicts with the live a4 and the tombstone wins. On the next push, B already knows tb3. **Result: both deleted.**
- **Order Z.** tb1, then tb3, then a4, whose HLV now carries `srcB:30`. **Result: both live a4.**

X and Y have the same local writes with byte-identical version vectors and differ only in delivery and commit order. Y converges. X ends with the two clusters holding different documents and nothing left to send.

After X, any further write on A to this document is also rejected by B with 409, until B itself writes; then A's pull resolves by LWW. A manual pull reset would re-send tb3 and converge to deleted, losing a4. That reset is an operator action, not an automatic retry.

The same divergence occurs with a tombstone update instead of the re-create (P6: `DELETE`, then `PUT {"_deleted":true}` with the tombstone's rev).

### How X is reached in the real code

- The tb1 and tb3 `rev` messages are handled in separate goroutines.
- Suppose tb1's handler reads the document before tb3 commits. Its CAS write then fails, and the callback re-runs on the committed tb3 state. It takes the tombstone path and writes the regressed HLV.
- Nothing on that path, or in `documentUpdateFunc`, cancels a write whose rev already exists as an interior rev-tree node. On the rev-tree side the code sets `NewestRev` and `Hidden`, then continues.
- tb1 must still be retrievable by cv on B when A requests it. ISGR does not set `sendReplacementRevs`, so if tb1 is not retrievable, B sends `norev` and nothing happens.

### Guarantees X would violate

All are from the docs repo, branch `release/4.1` at `2ebc24b8`; the same text is on `release/4.0`.

- `modules/ROOT/partials/incpg-icr-conflict.adoc`: "Conflicts are only resolved during a *pull* replication. If conflicts occur, you should configure a `pushAndPull` replication." Here `pushAndPull` is configured, and the conflicting write is never resolved.
- `modules/ROOT/pages/conflict-resolution.adoc`: "Conflicts are automatically resolved ... using deterministic algorithms that verify consistency across all participating nodes". It also says LWW provides "Deterministic conflict resolution across all clusters".
- `modules/sync/pages/sync-inter-syncgateway-overview.adoc`: ISGR "was designed to keep clusters in different data centers in sync."

Separately, `modules/ROOT/partials/concepts/rep-auto-conflict-resolution-policy.adoc` says only "The revision with the most recent timestamp wins." It does not mention the tombstone-wins rule the code applies. That is a docs gap, not an NC finding.

### NC reading

The repair is the dominance gate plus the HLV merge.
- The gate runs in phase 1, against a state that the phase-2 commit no longer sees.
- On the tombstone path the gate is not re-applied.
- The merge itself is not order-independent, because `AddVersionToPV` drops a newer value from the same source.

So the two deliveries do not commute at a reachable state where both are in flight (a CC1 failure). That failure is reachable only because the gate and the merge are separated, which is the state-descent condition. Sequential delivery, with one rev in flight, never reaches it: the phase-1 gate filters out the stale tombstone.

## 5. Issue-tracker check (read-only)

### GitHub couchbase/sync_gateway
- Searched with `gh search issues` and `gh search prs` for: tombstone conflict, HLV, out of order, regress, resurrect, divergence, push 409.
- No issue matches.
- PRs #7798 and #7804 (CBG-4894 and CBG-4903, tombstones in the default resolver) are where the tombstone-wins rule came from.

### Couchbase JIRA
Queried `jira.issues.couchbase.com` via REST v3, anonymously.
- CBG-1044, "Don't trigger conflict resolution for two tombstones" (2020, closed), is the origin of the tombstone-over-tombstone path.
- CBG-1127, "Treat resurrected tombstones as non-conflict when no shared history" (2020), is the rev-tree resurrection rule.
- No ticket found about the cv moving backwards, out-of-order revs of one document, or a 409 blocking a `pushAndPull` replication.

### Limits of the JIRA search
- Most 4.x CBG tickets are not visible anonymously. CBG-4894 and CBG-5842 are named in commits, but a key lookup does not return them; only backport tickets show.
- So an internal ticket cannot be ruled out.

### Related behaviour upstream already tests
- Different cvs for concurrent tombstones on Couchbase Lite peers (`topologytest/hlv_test.go`).
- HLC clock ties (`forceClockTie`).
- Neither covers this scenario.

## 6. Classification

**COUNTEREXAMPLE CANDIDATE.**
- The execution is derived from source.
- It leaves distinct canonical outcomes after full bidirectional synchronisation, in the configuration the docs recommend.
- The same writes in another order converge.

### Caveats that keep it a candidate
1. **Race-dependent.** It needs two revisions of one document, from the same source, in flight to the active side at once and committing newest first. Sequential delivery is prevented by the phase-1 gate.
2. **Rev-tree side not modelled.** The tombstone write lands on a rev that is already an interior node. I found no cancelling guard in `PutExistingCurrentVersion` or `documentUpdateFunc`, but this was read, not run.
3. **Retrievability of tb1.** B must serve tb1 by cv from its revision cache when A requests it; otherwise B sends `norev`.
4. **JIRA visibility.** Coverage is partial (section 5).

### Out of scope but noted (UNDETERMINED, not modelled)
- **PV compaction.** Needs more than 5 sources and a peer offline for longer than the version pruning window (default 30 days, read from the bucket). Compaction could then drop the peer's cv, giving the same pattern: a false conflict, a 409 from the passive side, and no re-delivery. It needs Couchbase Lite sources and elapsed time.
- **Pre-upgrade documents and legacy (v3) ISGR.** These use rev-tree-encoded cvs and `IsIllegalConflict` case (c). That case allows a disconnected live branch on a tombstone whose history was pruned (`revs_limit` 50). It has the same shape as the CouchDB stemming resurrection, but it is documented as design (CBG-1127).

## 7. Draft prediction (not committed)

**P-SG1: A stale tombstone blocks a push_and_pull replication.** The model and the expected outcome are fixed before any live test.

### Setting
- Two Couchbase Server clusters, each with one Sync Gateway 4.1.2. Record the exact SG version and the Couchbase Server build.
- One database each, with separate buckets and different source IDs.
- Default `max_concurrent_revs`. Delta sync off.
- **On A:** one replication to B: `{"direction": "pushAndPull", "continuous": true, "conflict_resolution_type": "default"}`.
- **On B:** no replication configured; default sync function.
- **Sync function on A:**
  `function(doc){ if (doc.slow) { var t = Date.now(); while (Date.now() - t < 3000) {} } channel("all"); }`
  This holds tb1's first write attempt open, so tb3 commits first.
- **Start:** document `X` created on B, replicated to A, then wait for idle.

### Steps
1. On B: `PUT X {"_deleted": true, "slow": true}` (tb1).
2. Within 1 s on B: `PUT X {"v": 2}` (b2), then `DELETE X` (tb3).
3. Wait for the replication to report idle. On A: `PUT X {"v": 4}` with no `_rev`.
4. Wait for idle: 60 s with no change in `docs_checked_push`.

### Claims
1. **Order X, forced.** A returns `X` live with `v: 4`. B returns `X` deleted. A's `_vv` has no entry for `srcB` at or above tb3's version. The replication status shows `doc_write_conflict` >= 1.
2. **Control, order Y.** The same steps, but step 3 runs before tb3 commits on A: no `slow` on tb1, and a4 is written right after A shows tb1. Expected: both deleted.
3. **Control, no race.** No `slow`, and 5 s between each of tb1, b2 and tb3, then step 3. Expected: both live with `v: 4`.

### Repetitions and scoring
- Each configuration is run 5 times, on fresh documents.
- Claim 1 **passes** if at least 4 of 5 runs end with A live and B deleted.
- Claim 1 **fails** if no run diverges.
- 1 to 3 divergent runs are reported as "reached, not forced".
- The controls are scored the same way against their expected outcomes.

### Probability
About 0.45 that claim 1 passes as written. The main risks:
- the sync function runs outside the CAS window;
- tb1 is not retrievable by cv on B (giving `norev`);
- a rev-tree guard exists that I did not find by reading;
- the slow write does not overlap tb3's processing.

### Commitment rule
The model (`model/sg_model.py`, `model/trace_p8.py`) and these expected outcomes are fixed before any live run, and the run is scored only against them.

## Addendum: push-only divergence and the tombstone-wins rule

### Push-only (T4)
Permanent divergence is reachable with every program that has concurrent writes:
- the passive side rejects the write with 409;
- the active side counts it (`SendRevErrorConflictCount`) and still checkpoints (`sgr2PushProcessedSeqCallback`), so it never retries;
- nothing pulls.

This is documented in `incpg-icr-conflict.adoc`: "Conflicts are *not* resolved in *push* replications ... The passive end of the push simply detects and rejects any conflicting revisions (409 Conflict response)". The note there adds "Conflicts are only resolved during a *pull* replication. If conflicts occur, you should configure a pushAndPull replication." The docs do not explicitly say that the checkpoint skips the rejected rev; that part is from the source. Because it is documented, it is not a prediction.

### Tombstone beats live
- **Code.** `db/hybrid_logical_vector.go:973-992` (`DefaultLWWConflictResolutionType`). Lines 977-984 apply "deleted beats live" before the `Version` comparison. It is wired through `db/sg_replicate_conflict_resolver.go:232-245` (`NewConflictResolverFuncForHLV`, case `"default"`).
- **4.x docs.** Not described. `rep-auto-conflict-resolution-policy.adoc` and `pages/conflict-resolution.adoc` say only that the most recent or latest timestamp wins.
- **Legacy docs.** "Deletes always win" appears only in the 3.x rev-tree docs (`modules/configuration/attachments/configuration-properties-legacy.yaml:1017`).
- **Tracker.** The rule is deliberate: CBG-4894 (commit `6f77f70f`, PR #7798) and CBG-4903 (PR #7804, the 4.0 backport), with tests in `rest/replicatortest/replicator_conflict_test.go`. The JIRA tickets themselves are not publicly visible. No ticket was found about the docs omitting the rule.
- **Assessment.** Intentional behaviour plus a docs gap. All replicas converge, so it is not an NC divergence.

## Files
- `model/sg_model.py`: the transcription.
- `model/search.py`: exhaustive search. Options: `--topo=`, `--skew=`, `--prog=`, `--traces`, `--inflight=`, `--counterfactual`.
- `model/trace_p8.py`: orders X, Y and Z.
- `model/results/`: `T1_T2_T4_all.txt`, `T3_*.txt`, `attribution.txt`, `trace_p8.txt`.
