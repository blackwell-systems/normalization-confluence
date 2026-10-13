# Adversarial review of the Sync Gateway candidate (2026-10-13)

Reviewer: a fresh agent instructed to break the candidate. Read-only; nothing run. Source: sync_gateway main f1c59eb2, cross-checked at tag 4.1.2 (same logic: crud.go:1618/1642, blip_handler.go:1361; go-blip pin 002c1b20b67a).

**Overall: CANDIDATE SURVIVES**, with one narrowing: tb1 must be sent by B while tb1 is still current on B.

## A. Two revs of one doc in flight to A: HOLDS
- go-blip receiver.go:270-276 and message.go:367-389: each incoming request runs in its own goroutine; no per-profile or per-doc ordering.
- SG's only limit is processRev's inFlightRevsThrottle (blip_handler.go:1060-1075; DefaultMaxConcurrentRevs=5 at :60), a counting semaphore, not per-doc.
- No per-doc lock on the pull path (blip_collection_context.go has only changesCtxLock and pendingInsertionsLock); the checkpointer's expectedSeqs is keyed by IDAndRev (blip_handler.go:801).
- Changes batches are pipelined: sendBatchOfChanges (blip_handler.go:604-660) runs handleChangesResponse in a goroutine under inFlightChangesThrottle.
- tb1 is requested only if A does not yet have tb3 when CheckChangeVersion runs (crud.go:4115 localVersionDominates); trace X satisfies this.

## B. Can B serve tb1 after tb3 exists: PARTLY BREAKS the general claim; trace X still holds
- sendRevision calls GetRev(docID, CV) at handleChangesResponse time (blip_sync_context.go:766).
- getRev passes loadBackup = IsRevTreeID(rev), false for a CV (crud.go:532); on a revcache miss getCurrentVersion returns ErrMissing for a non-current CV (revision_cache_interface.go:450-454); insert-on-write is off by default (revision_cache_interface.go:120-125).
- ISGR never sets sendReplacementRevs (only blip_handler.go:335, from a subChanges property the active replicator does not send), so a stale CV gets norev (blip_sync_context.go:777-779).
- So tb1 reaches A only if B sent it while tb1 was current (or revcache-resident). The race window is on A's side: tb1's processRev must be delayed past B's recreate and delete, B's changes, and tb3's full round trip.

## C. Anything on A cancelling the regression: HOLDS (nothing cancels it)
- forceAllowConflictingTombstone = newDoc.Deleted && (!conflictResolver.IsEmpty() || clientType==SGR2) (blip_handler.go:1373); true on the active pull side.
- PutExistingCurrentVersion: allowConflictingTombstone = force && doc.IsDeleted() (crud.go:1590); branch :1614-1619 calls UpdateWithIncomingHLV with no IsInConflict.
- UpdateWithIncomingHLV (hybrid_logical_vector.go:950-953) runs incoming.UpdateHistory(local); AddVersionToPV(srcB,30) returns sourceIsCV at :920-922, so srcB:30 is dropped and cv becomes srcB:10.
- Rev tree does not cancel: alignRevTreeHistoryForHLVWrite(skip=true) (crud.go:4350-4371) adds nothing; updateWinningRevAndSetDocFlags (crud.go:2422) keeps 4-c as winner; documentUpdateFunc logs "leaves still current" (crud.go:2891-2912) and persists; updateHLV(ExistingVersion) only sets cvCAS (crud.go:1198-1200). No ErrUpdateCancel on this path (the RTE-CV check at :1621 needs an encoded rev-tree source).
- A ends with rev-tree winner 4-c and _vv cv srcB:10: internally inconsistent, unguarded.
- CAS retry re-runs the callback on fresh state (crud.go:1536; updateAndReturnDoc:2977-2978): if tb1's first attempt ran on live x0 and lost to tb3, the retry takes the tombstone-on-tombstone branch.

## D. Is the push 409 final: HOLDS
- B passive, no resolver; push uses "changes" with ignoreNoConflicts (active_replicator_push.go:241-250).
- B's IsInConflict(local {srcB:30}, incoming {srcA:40; pv srcB:10}) is HLVConflict (hybrid_logical_vector.go:845-881; document.go:1645-1667); ISGRWrite with nil resolver gives 409 (crud.go:1686-1690).
- On 409, sendRevisionWithProperties bumps a stat and calls sgr2PushProcessedSeqCallback(seq) (blip_sync_context.go:501-536); no retry.
- A's pull checkpoint already passed B's tb3 seq (blip_handler.go:1409-1417); B's doc never changes again, so nothing re-delivers.
- Only escape: a pull restart from an older unpersisted checkpoint would re-send tb3; LWW then picks deleted (hybrid_logical_vector.go:977-984, CBG-4894), losing a4.

## E. EE vs CE: HOLDS (not EE-only)
- All code is public; EE build tags only in base/*_ee.go and *_ce.go constants. ISGR runs in CE with the default resolver; ValidateReplication (sg_replicate_cfg.go:179-189) gates only non-default resolvers, delta sync, batch_size. The EE/CE branch in sendRevision (blip_sync_context.go:813-843) only affects body marshalling.

## F. Documented or ticketed: NOT FOUND, no carve-out
- The tombstone skip comes from CBG-1044 (commit 1d447a57, rev-tree era, where the rev-tree winner made it harmless) and was carried into the HLV path.
- Related but different: CBG-1127, CBG-4894. CheckChangeVersion carries a TODO "CBG-4792: enhance here for conflict check" (crud.go:4114).
- gh search: nothing matching. Open PR #8884 (CBG-5853, tombstone bodies with _deleted failing validateBlipBody) is a different bug and a test hazard.
- Docs (release/4.0): conflict-resolution.adoc:56 "Deterministic conflict resolution across all clusters"; incpg-icr-conflict.adoc:16-30 (pull resolves; use pushAndPull). No tombstone carve-out. Best framing of the violated guarantee: pushAndPull with default LWW converges (implied by both docs, not stated as a sentence).

## G. Model mismatches (none affect trace X)
1. The model snapshots the version at changes time and always delivers it; Go fetches at changes-response time and sends norev for a non-current CV. Over-approximation: other search results may include unreachable stale sends.
2. Model checkpoint is max(q) on apply; Go's Checkpointer uses a safe-seq over the expected list (active_replicator_checkpointer.go:262/309).
3. No rev tree in the model (cannot show the 4-c / srcB:10 inconsistency; outcome unchanged).
4. Matches Go: forced tombstone flag at both ends, IsInConflict, AddVersionToPV, AddVersion, LWW, 409-processed.

## Remaining assumptions
(a) B's sendRevision for tb1 executes while tb1 is current. (b) A's commit of tb1 is delayed until after tb3 commits. (c) Tombstone rev bodies pass validateBlipBody (current-tombstone bodies should; CBG-5853 hazard otherwise). (d) No restart that rewinds A's pull checkpoint.

## Probability (reviewer)
About 75% that the CV regression reproduces (A's cv goes from srcB:30 back to srcB:10) and about 65-70% for the full final state (A live, B deleted, quiescent) with the forced-delay test. Natural reproduction without forcing is low (the window is one full changes+rev round trip).

## Minimal live test (reviewer's design)
Two SG 4.1.x nodes, each on its own bucket; A runs continuous pushAndPull ISGR to B, default resolver. Sync function on A:
`function(doc,oldDoc){ if (doc._deleted && doc._rev.indexOf("2-")==0) { var t=Date.now(); while(Date.now()-t<8000){} } channel("*"); }`
(prepareSyncFn sets _rev to the incoming RevTreeHistory[0], crud.go:1750, 2526; javascript_timeout defaults to 0, base/constants.go:151.)
1. Create x on A; wait until both have 1-x. 2. DELETE on B (tb1, 2-a). 3. Wait ~1 s (A is in the slow sync function, so B already sent tb1). 4. On B: PUT recreate (3-b), then DELETE (tb3, 4-c). 5. Wait ~10 s; GET /{ks}/_raw/x on A: expect deleted, rev 4-c, _vv cv = B's source at tb1's value (regression oracle). 6. PUT a4 on A; expect SendRevErrorConflictCount to increment and B's _raw still at tb3. 7. Wait for idle: A live, B deleted, nothing pending.
Control: same steps without the delay (or delay on "4-"): converges to a4 on both.
Cheaper deterministic check of links 1-2: a rosmar unit test calling PutExistingCurrentVersion(tb3) then PutExistingCurrentVersion(tb1, ForceAllowConflictingTombstone=true, ISGRWrite=true) and asserting the CV.
