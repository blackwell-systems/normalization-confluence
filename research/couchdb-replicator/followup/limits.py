#!/usr/bin/env python3
"""apache/couchdb#6162: the issue's topology with revs_limit as a parameter.

Databases: A (full source, limit LA), C (limit LA, synced X at generation c), B (limit LB, holds X
at generation m), D (limit LD, holds the deletion m+1), T1 (limit LT, no design doc), T2 (limit LT,
accept-all validate_doc_update). Steps, as in the issue:
  1. A: c edits of X; replicate A -> C (doc_ids X).
  2. A: F unrelated docs (they precede X's next change in A's _changes).
  3. A: edit X up to m; replicate A -> B (doc_ids X). B stores X at m with history max(1, m-LB+1)..m.
  4. T1, T2: replicate C, then B.
  5. T1, T2: replicate A (opts; worker_processes 1, batch size 1 by default). With F >= 6 the worker
     skips _revs_diff for X's batch and re-sends m with A's history max(1, m-LA+1)..m.
  6. A: delete X (m+1); replicate A -> D (doc_ids X). D stores max(1, m-LD+2)..m+1.
  7. T1, T2: replicate D.
mode "inj" performs steps 4, 5, 7 as _bulk_docs new_edits:false with the same leaves and histories.

Usage: COUCH=... python3 limits.py <scenario> [...]
"""
import sys

from couchlib import Run, SMALL, ONLY_X


def topo(name, LA=1000, LB=1, LD=2, LT=1000, c=1, m=2, F=6, opts=None, mode="rep", ddoc_in_batch=False):
    opts = SMALL if opts is None else opts
    print(f"scenario {name}: LA={LA} LB={LB} LD={LD} LT={LT} c={c} m={m} F={F} A->T opts={opts} mode={mode}", flush=True)
    r = Run(name)
    A = r.db("A", LA)
    C = r.db("C", LA)
    B = r.db("B", LB)
    D = r.db("D", LD)
    T1 = r.db("T1", LT)
    T2 = r.db("T2", LT, vdu=True)
    Ts = ((T1, "T1"), (T2, "T2"))
    r.edit(A, "A", c)
    r.replicate(A, C, "A", "C", **ONLY_X)
    if F:
        r.fillers(A, "A", F, "f")
    r.edit(A, "A", m - c)
    r.replicate(A, B, "A", "B", **ONLY_X)
    mid = []
    for T, n in Ts:
        if mode == "rep":
            r.replicate(C, T, "C", n)
            r.replicate(B, T, "B", n)
        else:
            r.inject(T, n, max(1, c - LA + 1), c)
            r.inject(T, n, max(1, m - LB + 1), m)
    mid += [r.observe(T1, "T1 after C,B"), r.observe(T2, "T2 after C,B")]
    for T, n in Ts:
        if mode == "rep":
            r.replicate(A, T, "A", n, **opts)
        else:
            extra = [{"_id": "_design/plain", "_rev": "1-0123456789abcdef0123456789abcdef", "views": {}}] if ddoc_in_batch else None
            r.inject(T, n, max(1, m - LA + 1), m, extra_docs=extra)
    mid += [r.observe(T1, "T1 after A"), r.observe(T2, "T2 after A")]
    r.edit(A, "A", 1, deleted=True)
    r.replicate(A, D, "A", "D", **ONLY_X)
    for T, n in Ts:
        if mode == "rep":
            r.replicate(D, T, "D", n)
        else:
            r.inject(T, n, max(1, m + 1 - LD + 1), m + 1, deleted=True)
    finals = [r.observe(T1, "T1 final"), r.observe(T2, "T2 final")]
    differ = not r.same(*finals)
    print(f"  => {name}: T1 vs T2 {'DIFFER' if differ else 'same'}", flush=True)
    r.save({"params": dict(LA=LA, LB=LB, LD=LD, LT=LT, c=c, m=m, F=F, opts=opts, mode=mode, ddoc_in_batch=ddoc_in_batch),
            "intermediate": mid, "final": finals, "differ": differ})
    return differ


S = {}
# control: the issue's limits (1 and 2) through this harness, replicator and injection
S["issue_rep"] = lambda: topo("issue_rep")
S["issue_inj"] = lambda: topo("issue_inj", F=0, mode="inj")
# side check: T1 (no VDU) with a design doc in the same _bulk_docs request as the re-delivery
S["issue_inj_ddoc"] = lambda: topo("issue_inj_ddoc", F=0, mode="inj", ddoc_in_batch=True)
# uniform revs_limit L on every database (no lowered replica); B's history excludes c, so m = c + L
for L in (2, 3, 10, 100, 1000):
    S[f"uniform_{L}"] = (lambda L=L: lambda: topo(f"uniform_{L}", LA=L, LB=L, LD=L, LT=L, c=1, m=L + 1))()
    S[f"uniform_{L}_inj"] = (lambda L=L: lambda: topo(f"uniform_{L}_inj", LA=L, LB=L, LD=L, LT=L, c=1, m=L + 1, F=0, mode="inj"))()
# heterogeneous: B and D at a lower limit L, A/C/T at the default 1000; smallest history: m = c + L
for L in (3, 10, 100, 999):
    S[f"het_{L}"] = (lambda L=L: lambda: topo(f"het_{L}", LB=L, LD=L, c=1, m=L + 1))()
    S[f"het_{L}_inj"] = (lambda L=L: lambda: topo(f"het_{L}_inj", LB=L, LD=L, c=1, m=L + 1, F=0, mode="inj"))()
# heterogeneous with a deep history: C synced at 300, X edited to 1200, B and D at 100
S["het_100_deep"] = lambda: topo("het_100_deep", LB=100, LD=100, c=300, m=1200)
# the same with default replication settings for A -> T (needs many docs before X in A's changes)
S["het_100_default_rep"] = lambda: topo("het_100_default_rep", LB=100, LD=100, c=1, m=101, F=20000, opts={})
S["het_100_default_rep_nofill"] = lambda: topo("het_100_default_rep_nofill", LB=100, LD=100, c=1, m=101, F=0, opts={})

if __name__ == "__main__":
    for s in sys.argv[1:] or list(S):
        S[s]()
