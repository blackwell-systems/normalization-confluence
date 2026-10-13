"""Model of Sync Gateway 4.x Inter-Sync Gateway Replication (ISGR) for one
document, built-in conflict handling only (conflict_resolution_type "default").

A transcription, by reading, of couchbase/sync_gateway main @ f1c59eb2
(conflict logic identical in tag 4.1.2):

  db/hybrid_logical_vector.go
      HybridLogicalVector.AddVersion, InvalidateMV, GetValue, DominatesSource,
      AddVersionToPV, UpdateHistory, UpdateWithIncomingHLV, IsInConflict,
      DefaultLWWConflictResolutionType
  db/crud.go
      PutExistingCurrentVersion (the ISGR v4 write path, both ends),
      resolveHLVConflict, resolveLocalWinsHLV, resolveRemoteWinsHLV,
      CheckChangeVersion, localVersionDominates, updateHLV (NewVersion,
      ExistingVersion)
  db/blip_handler.go
      processRev (forceAllowConflictingTombstone, ConflictResolver only on
      the active side, ISGRWrite on the passive side)
  db/blip_sync_context.go
      sendRevision response handling: a 409 on push is counted and the
      sequence is still marked processed (sgr2PushProcessedSeqCallback)
  db/sg_replicate_conflict_resolver.go
      ResolveForHLV, NewConflictResolverFuncForHLV ("default" -> LWW)

No Sync Gateway or Couchbase Server code is run. Standard library only.

Not modelled (each stated in REPORT.md): custom resolvers, merge versions
(only produced by merges), PV compaction (needs more than 5 sources in PV,
unreachable with two gateways and REST writes), pre-upgrade documents
without an HLV, the revtree (v3 subprotocol) path, attachments, channels,
sync function rejections, import of SDK writes (OnDemandImportForWrite runs
the import inside the same CAS-retry callback before any SG write).
"""

from collections import deque
from itertools import count

# ---------------------------------------------------------------- HLV
# HLV = (src, ver, pv, mv); pv and mv are frozensets of (src, ver) pairs,
# at most one pair per source (they model Go maps).


def _m(fs):
    return dict(fs)


def _f(d):
    return frozenset(d.items())


EMPTY = ("", 0, frozenset(), frozenset())

# Attribution switch for search.py --counterfactual: re-check dominance on the
# tombstone-over-tombstone path. False reproduces Sync Gateway.
RECHECK_TOMBSTONE_PATH = False


def get_value(h, s):
    src, ver, pv, mv = h
    if s == "":
        return None
    if s == src:
        return ver
    mvd = _m(mv)
    if s in mvd:
        return mvd[s]
    pvd = _m(pv)
    if s in pvd:
        return pvd[s]
    return None


def dominates_source(h, version):
    s, v = version
    x = get_value(h, s)
    return x is not None and x >= v


def cv(h):
    return (h[0], h[1])


def add_version(h, version):
    """HybridLogicalVector.AddVersion (local write, updateHLV NewVersion)."""
    src, ver, pv, mv = h
    s, v = version
    if src == "":
        return (s, v, pv, mv)
    x = get_value(h, s)
    if x is not None and x > v:
        raise AssertionError("AddVersion: older value for same source")
    pvd = _m(pv)
    for ms, mval in _m(mv).items():  # InvalidateMV
        if ms != src:
            pvd[ms] = mval
    if s == src:
        return (src, v, _f(pvd), frozenset())
    pvd[src] = ver
    pvd.pop(s, None)
    return (s, v, _f(pvd), frozenset())


def add_version_to_pv(h, s, v):
    src, ver, pv, mv = h
    if src == s:
        return h, "sourceIsCV"
    mvd = _m(mv)
    if s in mvd:
        return h, ("versionInMVNewer" if mvd[s] >= v else "versionInMVOlder")
    pvd = _m(pv)
    if s not in pvd or pvd[s] < v:
        pvd[s] = v
        return (src, ver, _f(pvd), mv), "versionAddedToPV"
    return h, "versionInPVNewer"


def update_history(h, incoming):
    """h.UpdateHistory(incoming): add incoming's CV, MV, PV to h's PV."""
    isrc, iver, ipv, imv = incoming
    if isrc != "":
        h, _ = add_version_to_pv(h, isrc, iver)
    invalidate = False
    for s, v in sorted(imv):
        h2, st = add_version_to_pv(h, s, v)
        if st == "versionInMVOlder":
            invalidate = True
            break
        h = h2
    if invalidate:  # not reachable without merge versions; kept for fidelity
        src, ver, pv, mv = h
        pvd = _m(pv)
        for ms, mval in _m(mv).items():
            if ms != src:
                pvd[ms] = mval
        h = (src, ver, _f(pvd), frozenset())
        for s, v in sorted(imv):
            h, _ = add_version_to_pv(h, s, v)
    for s, v in sorted(ipv):
        h, _ = add_version_to_pv(h, s, v)
    return h


def update_with_incoming(h, incoming):
    """h.UpdateWithIncomingHLV(incoming): result is incoming with h's history."""
    return update_history(incoming, h)


NO_CONFLICT, CONFLICT, ALREADY = "HLVNoConflict", "HLVConflict", "HLVNoConflictRevAlreadyPresent"


def is_in_conflict(local, incoming):
    if cv(local) == cv(incoming):
        return ALREADY
    if dominates_source(incoming, cv(local)):
        return NO_CONFLICT
    if dominates_source(local, cv(incoming)):
        return ALREADY
    lmv, imv = local[3], incoming[3]
    if imv and lmv and imv == lmv:
        return NO_CONFLICT
    return CONFLICT


# ---------------------------------------------------------------- documents
# doc = (hlv, body, deleted); body is a label, None for a tombstone.


def lww_winner(local, remote):
    """DefaultLWWConflictResolutionType. Returns 'local' or 'remote'."""
    (lh, _, ldel), (rh, _, rdel) = local, remote
    if ldel and not rdel:
        return "local"
    if rdel and not ldel:
        return "remote"
    if rh[1] > lh[1]:
        return "remote"
    return "local"


def put_existing_current_version(local, incoming, has_resolver, log=None):
    """PutExistingCurrentVersion for an ISGR v4 write (ISGRWrite or active
    with resolver). Returns (new_doc or None if cancelled/rejected, status)."""
    ih, ibody, idel = incoming
    # processRev: forceAllowConflictingTombstone = newDoc.Deleted &&
    #   (active with resolver || passive SGR2). Both ends of ISGR qualify.
    force = idel
    if local is None:
        # doc.HLV == nil: new HLV, UpdateWithIncomingHLV
        return (update_with_incoming(EMPTY, ih), ibody, idel), "new"
    lh, lbody, ldel = local
    if force and ldel:
        # allowConflictingTombstone: no conflict check at all
        if RECHECK_TOMBSTONE_PATH and dominates_source(lh, cv(ih)):
            # counterfactual used only for attribution (not Sync Gateway code)
            return None, "counterfactual_cancel"
        return (update_with_incoming(lh, ih), ibody, idel), "tombstone_over_tombstone"
    st = is_in_conflict(lh, ih)
    if st == ALREADY:
        return None, "cancel_already_present"
    if st == NO_CONFLICT:
        if cv(lh) == cv(ih):
            return None, "cancel_equal_cv"
        return (update_with_incoming(lh, ih), ibody, idel), "no_conflict"
    # CONFLICT. ISGRWrite is true for the passive end, and the active end has
    # a resolver; RevTreeHistory checks for CBL do not apply.
    if not has_resolver:
        return None, "409"
    w = lww_winner(local, incoming)
    if log is not None:
        log.append((w, local, incoming))
    if w == "local":
        # resolveLocalWinsHLV: newHLV = remote.Copy(); newHLV.UpdateWithIncomingHLV(local)
        nh = update_with_incoming(ih, lh)
        return (nh, lbody, ldel), "resolved_local"
    # resolveRemoteWinsHLV: newHLV = local.Copy(); newHLV.UpdateWithIncomingHLV(remote)
    nh = update_with_incoming(lh, ih)
    return (nh, ibody, idel), "resolved_remote"


def change_not_missing(local, change_cv):
    """CheckChangeVersion: the change is skipped when localVersionDominates."""
    if local is None:
        return False
    return dominates_source(local[0], change_cv)


# ---------------------------------------------------------------- system
# Global state (a tuple):
#   docs:     (docA, docB)
#   seqs:     (seqA, seqB)            changes-feed position of the doc
#   ckpt:     {direction: seq}        replicator checkpoint per direction
#   inflight: {direction: tuple of (snapshot, seq)} revs requested, not applied
#   pcs:      program counters into each gateway's local event list
#   clock:    global real-time tick (advanced by local writes)
#   writes:   tuple of HLVs produced by local writes, in program order per gateway
#
# Directions are (src, dst, dst_has_resolver).

GW = ("A", "B")
SRC = {"A": "srcA", "B": "srcB"}


class Config:
    def __init__(self, name, directions, skew, max_inflight=2):
        self.name = name
        self.directions = directions  # tuple of (src_idx, dst_idx, resolver)
        self.skew = skew              # per-gateway clock offset
        self.max_inflight = max_inflight


def local_write(state, g, ev, cfg):
    docs, seqs, ckpt, inflight, pcs, clock, writes = state
    doc = docs[g]
    h = doc[0] if doc else EMPTY
    floor = get_value(h, SRC[GW[g]]) or 0
    # MV max for the CV source (maxValueForSource); MV is empty here
    now = (clock + 1) * 10 + cfg.skew[g]
    v = max(now, floor + 1)
    nh = add_version(h, (SRC[GW[g]], v))
    if ev == "del":
        nd = (nh, None, True)
    else:
        nd = (nh, ev, False)
    docs = tuple(nd if i == g else docs[i] for i in range(2))
    seqs = tuple(seqs[i] + 1 if i == g else seqs[i] for i in range(2))
    pcs = tuple(pcs[i] + 1 if i == g else pcs[i] for i in range(2))
    w = tuple(writes[i] + ((ev, nh),) if i == g else writes[i] for i in range(2))
    return (docs, seqs, ckpt, inflight, pcs, clock + 1, w)


def repl_actions(state, cfg, log_sink=None):
    """All enabled replication steps. Yields (label, next_state)."""
    docs, seqs, ckpt, inflight, pcs, clock, writes = state
    ck = dict(ckpt)
    inf = dict(inflight)
    for d in cfg.directions:
        s, t, res = d
        # phase 1: changes entry sent, receiver runs CheckChangeVersion
        pending = inf.get(d, ())
        sent_upto = max([ck[d]] + [q for _, q in pending])
        if seqs[s] > sent_upto and len(pending) < cfg.max_inflight:
            snap = docs[s]
            if change_not_missing(docs[t], cv(snap[0])):
                # no rev requested; the sequence is processed at once
                ck2 = dict(ck)
                ck2[d] = max(ck[d], seqs[s])
                yield (("skip", d), (docs, seqs, _f(ck2), inflight, pcs, clock, writes))
            else:
                inf2 = dict(inf)
                inf2[d] = pending + ((snap, seqs[s]),)
                yield (("send", d), (docs, seqs, ckpt, _f(inf2), pcs, clock, writes))
        # phase 2: any in-flight rev may be applied (revs are handled concurrently)
        for i, (snap, q) in enumerate(pending):
            rest = pending[:i] + pending[i + 1:]
            inf2 = dict(inf)
            if rest:
                inf2[d] = rest
            else:
                inf2.pop(d, None)
            ck2 = dict(ck)
            # A push 409 still marks the sequence processed (blip_sync_context.go);
            # on the active pull side every modelled outcome is a success or a cancel.
            ck2[d] = max(ck[d], q)
            log = [] if log_sink is not None else None
            nd, status = put_existing_current_version(docs[t], snap, res, log)
            if nd is None:
                ndocs, nseqs = docs, seqs
            else:
                ndocs = tuple(nd if j == t else docs[j] for j in range(2))
                nseqs = tuple(seqs[j] + 1 if j == t else seqs[j] for j in range(2))
            if log_sink is not None and log:
                log_sink.extend(log)
            yield (("apply", d, q, status), (ndocs, nseqs, _f(ck2), _f(inf2), pcs, clock, writes))


def local_actions(state, program, cfg):
    pcs = state[4]
    for g in range(2):
        if pcs[g] < len(program[g]):
            ev = program[g][pcs[g]]
            yield (("local", GW[g], ev), local_write(state, g, ev, cfg))


def initial_state(cfg):
    h0 = ("srcA", 5, frozenset(), frozenset())
    d0 = (h0, "x0", False)
    ck = {d: 1 for d in cfg.directions}
    return ((d0, d0), (1, 1), _f(ck), frozenset(), (0, 0), 0, ((), ()))


def canon(doc):
    if doc is None:
        return ("absent",)
    return ("deleted",) if doc[2] else ("live", doc[1])


def outcome(state):
    a, b = state[0]
    return (canon(a), canon(b))


def quiescent_closure(state, cfg, limit=200000):
    """N: every quiescent state reachable by replication steps alone.
    Returns (set of quiescent states, terminated_flag)."""
    seen = {state}
    dq = deque([state])
    out = set()
    while dq:
        s = dq.popleft()
        succ = list(repl_actions(s, cfg))
        if not succ:
            out.add(s)
        for _, n in succ:
            if n not in seen:
                seen.add(n)
                if len(seen) > limit:
                    return out, False
                dq.append(n)
    return out, True
