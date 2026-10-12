#!/usr/bin/env python3
"""apache/couchdb#6162 at uniform revs_limit (default 1000): deep-history scenarios.

Every database in a scenario has the same _revs_limit L (1000 unless a scenario says otherwise).
T1 has no design doc; T2 has an accept-all validate_doc_update. Both get the same deliveries in
the same order; the final state of X is compared.

Topology "early" (test 1a):
  A  full source, edited k times, then up to N (N > k + L - 1 so A's stored history of N no longer
     reaches k), then deleted (N+1).
  T  synced early from A at generation k.
  R  a replica that synced X from A at generation m (k < m <= k + L - 1, m >= N + 2 - L) and then
     went quiet; it holds F unrelated docs of its own written before it received X.
  Deliveries to T are POST /_replicate one-shot (mode "rep") or POST _bulk_docs new_edits:false with
  the same leaf and history the replicator would send (mode "inj").

Topology "two" (test 1b): A full source edited to N0, S_late created from A at N0 (stemmed copy),
  A edited further to N1; T optionally synced early at k; deliveries from S_late and A in both
  orders, with and without the _revs_diff skip; then a delete on A replicated to T.

Usage: COUCH=... python3 deep.py <scenario> [...]   (see SCENARIOS at the bottom)
"""
import sys

from couchlib import Run, SMALL, ONLY_X


def early(name, L=1000, k=5, m=600, N=1205, F=6, fillers_before=True, ropts=None, order="A_first",
          mode="rep", ddoc_in_batch=False):
    ropts = SMALL if ropts is None else ropts
    print(f"scenario {name}: L={L} k={k} m={m} N={N} F={F} fillers_before={fillers_before} "
          f"R->T opts={ropts} order={order} mode={mode}", flush=True)
    r = Run(name)
    A = r.db("A", L)
    R = r.db("R", L)
    T1 = r.db("T1", L)
    T2 = r.db("T2", L, vdu=True)
    Ts = ((T1, "T1"), (T2, "T2"))
    r.edit(A, "A", k)
    if mode == "rep":
        for T, n in Ts:
            r.replicate(A, T, "A", n, **ONLY_X)          # T synced early, at k
    else:
        for T, n in Ts:
            r.inject(T, n, max(1, k - L + 1), k)
    if F and fillers_before:
        r.fillers(R, "R", F, "r")
    r.edit(A, "A", m - k)
    r.replicate(A, R, "A", "R", **ONLY_X)               # R holds X at m (history max(1,m-L+1)..m)
    if F and not fillers_before:
        r.fillers(R, "R", F, "r")
    r.edit(A, "A", N - m)                               # A holds N with history N-L+1..N
    mid = []

    def deliver_A(last):
        if mode == "rep":
            for T, n in Ts:
                r.replicate(A, T, "A", n)
        else:
            for T, n in Ts:
                r.inject(T, n, max(1, last - L + 1), last, deleted=(last == N + 1))

    def deliver_R():
        if mode == "rep":
            for T, n in Ts:
                r.replicate(R, T, "R", n, **ropts)
        else:
            extra = [{"_id": "_design/plain", "_rev": "1-0123456789abcdef0123456789abcdef", "views": {}}] if ddoc_in_batch else None
            for T, n in Ts:
                r.inject(T, n, max(1, m - L + 1), m, extra_docs=extra)

    def snap(label):
        mid.extend([r.observe(T1, f"T1 {label}"), r.observe(T2, f"T2 {label}")])

    if order == "A_first":          # A's N, A's delete, then R's m
        deliver_A(N); snap("after A(N)")
        r.edit(A, "A", 1, deleted=True); deliver_A(N + 1); snap("after A(delete)")
        deliver_R()
    elif order == "R_between":      # A's N, R's m, then A's delete
        deliver_A(N); snap("after A(N)")
        deliver_R(); snap("after R")
        r.edit(A, "A", 1, deleted=True); deliver_A(N + 1)
    elif order == "R_first":        # R's m, A's N, A's delete
        deliver_R(); snap("after R")
        deliver_A(N); snap("after A(N)")
        r.edit(A, "A", 1, deleted=True); deliver_A(N + 1)
    else:
        raise ValueError(order)
    finals = [r.observe(T1, "T1 final"), r.observe(T2, "T2 final")]
    differ = not r.same(*finals)
    print(f"  => {name}: T1 vs T2 {'DIFFER' if differ else 'same'}", flush=True)
    r.save({"params": dict(L=L, k=k, m=m, N=N, F=F, fillers_before=fillers_before, ropts=ropts, order=order,
                           mode=mode, ddoc_in_batch=ddoc_in_batch),
            "intermediate": mid, "final": finals, "differ": differ})
    return differ


def two(name, L=1000, k=None, N0=1205, N1=1300, F=0, ropts=None, order="late_first"):
    """Test 1b: a full replica (A) and a late replica created from a stemmed copy (S)."""
    ropts = {} if ropts is None else ropts
    print(f"scenario {name}: L={L} k={k} N0={N0} N1={N1} F={F} opts={ropts} order={order}", flush=True)
    r = Run(name)
    A = r.db("A", L)
    S = r.db("S", L)
    T1 = r.db("T1", L)
    T2 = r.db("T2", L, vdu=True)
    Ts = ((T1, "T1"), (T2, "T2"))
    if F:
        r.fillers(A, "A", F, "a")
        r.fillers(S, "S", F, "s")
    if k:
        r.edit(A, "A", k)
        for T, n in Ts:
            r.replicate(A, T, "A", n, **ONLY_X)
    r.edit(A, "A", N0 - (k or 0))
    r.replicate(A, S, "A", "S", **ONLY_X)               # S: X at N0, history N0-L+1..N0 (stemmed copy)
    r.edit(A, "A", N1 - N0)                             # A: X at N1
    seq = [(S, "S"), (A, "A")] if order == "late_first" else [(A, "A"), (S, "S")]
    mid = []
    for src, sn in seq:
        for T, n in Ts:
            r.replicate(src, T, sn, n, **ropts)
        mid.extend([r.observe(T1, f"T1 after {sn}"), r.observe(T2, f"T2 after {sn}")])
    r.edit(A, "A", 1, deleted=True)
    for src, sn in seq:                                  # both again, after the delete
        for T, n in Ts:
            r.replicate(src, T, sn, n, **ropts)
    finals = [r.observe(T1, "T1 final"), r.observe(T2, "T2 final")]
    differ = not r.same(*finals)
    print(f"  => {name}: T1 vs T2 {'DIFFER' if differ else 'same'}", flush=True)
    r.save({"params": dict(L=L, k=k, N0=N0, N1=N1, F=F, ropts=ropts, order=order),
            "intermediate": mid, "final": finals, "differ": differ})
    return differ


DEF = {}  # default replication settings (4 workers, batch size 500)
SCENARIOS = {
    # --- test 1a, through the replicator, L = 1000 ---
    "early_rep_noskip_default": lambda: early("early_rep_noskip_default", F=0, ropts=DEF),
    "early_rep_skip_small": lambda: early("early_rep_skip_small", F=6, ropts=SMALL),
    "early_rep_five_small": lambda: early("early_rep_five_small", F=5, ropts=SMALL),
    "early_rep_after_small": lambda: early("early_rep_after_small", F=6, fillers_before=False, ropts=SMALL),
    "early_rep_skip_default": lambda: early("early_rep_skip_default", F=20000, ropts=DEF),
    "early_rep_skip_small_Rbetween": lambda: early("early_rep_skip_small_Rbetween", order="R_between"),
    "early_rep_skip_small_Rfirst": lambda: early("early_rep_skip_small_Rfirst", order="R_first"),
    # --- test 2, same deliveries by _bulk_docs new_edits:false ---
    "early_inj_Afirst": lambda: early("early_inj_Afirst", F=0, mode="inj"),
    "early_inj_Rbetween": lambda: early("early_inj_Rbetween", F=0, mode="inj", order="R_between"),
    "early_inj_Rfirst": lambda: early("early_inj_Rfirst", F=0, mode="inj", order="R_first"),
    # --- test 1b, two sources at L = 1000 ---
    "two_late_first": lambda: two("two_late_first", order="late_first"),
    "two_full_first": lambda: two("two_full_first", order="full_first"),
    "two_late_first_early5": lambda: two("two_late_first_early5", k=5, order="late_first"),
    "two_full_first_early5": lambda: two("two_full_first_early5", k=5, order="full_first"),
    "two_full_first_early5_skip": lambda: two("two_full_first_early5_skip", k=5, F=6, ropts=SMALL, order="full_first"),
    "two_late_first_early5_skip": lambda: two("two_late_first_early5_skip", k=5, F=6, ropts=SMALL, order="late_first"),
}

if __name__ == "__main__":
    for s in sys.argv[1:] or list(SCENARIOS):
        SCENARIOS[s]()
