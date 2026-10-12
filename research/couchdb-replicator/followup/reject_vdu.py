#!/usr/bin/env python3
"""Does the re-sent revision reach validate_doc_update?

The issue's topology with mismatched limits (B and D at L, A, C and T at 1000), using _bulk_docs
new_edits:false. T2 has no design doc until the re-delivery step. Just before it, T2 gets a VDU that
rejects every write to X. Then:
  - the re-delivery of leaf m with A's full history (the revision the theory says is dropped as an
    old leaf): a forbidden error means it reached the VDU; no error means it was dropped before it;
  - control: the deletion m+1 from D (a revision T2 does not have): should be rejected by the VDU.
A second VDU variant logs instead of rejecting, as a cross-check through CouchDB's log.

Usage: COUCH=... python3 reject_vdu.py [L]
"""
import sys

from couchlib import Run, req, DOC

REJECT = {"_id": "_design/reject",
          "validate_doc_update": "function(newDoc, oldDoc, userCtx, secObj) {"
                                 " if (newDoc._id == 'X') { throw({forbidden: 'vdu saw ' + newDoc._rev}); } }"}


def bulk(db, docs):
    s, b = req("POST", f"/{db}/_bulk_docs", {"docs": docs, "new_edits": False})
    return s, b


def doc_for(r, lo, hi, deleted=False):
    labels = [str(g) for g in range(lo, hi + 1)]
    d = {"_id": DOC, "_rev": r.revs[labels[-1]], "_revisions": r.path_revs(labels), "v": f"inj-{hi}"}
    if deleted:
        d["_deleted"] = True
    return d


def main(L=3):
    LA, c, m = 1000, 1, L + 1
    r = Run(f"reject_{L}")
    A = r.db("A", LA)
    T2 = r.db("T2", LA)
    r.edit(A, "A", m)                       # generations 1..m on A
    r.edit(A, "A", 1, deleted=True)         # m+1, deleted
    # step 4: C's copy (leaf c, history 1..c), then B's copy (leaf m, history m-L+1..m): two roots
    for lo, hi in ((max(1, c - LA + 1), c), (max(1, m - L + 1), m)):
        s, b = bulk(T2, [doc_for(r, lo, hi)])
        print(f"pre  inject leaf {hi} history {lo}..{hi}: HTTP {s} {b}")
    print("T2 before:", r.observe(T2, "T2 before re-delivery")["summary"])
    s, b = req("PUT", f"/{T2}/_design/reject", REJECT)
    print("install rejecting VDU:", s, b)
    # step 5: re-delivery of leaf m with A's full history 1..m
    s, b = bulk(T2, [doc_for(r, max(1, m - LA + 1), m)])
    print(f"RE-DELIVERY leaf {m} history 1..{m}: HTTP {s} {b}")
    print("T2 after re-delivery:", r.observe(T2, "T2 after")["summary"])
    # control: a revision T2 does not have (the deletion m+1 with D's history)
    s, b = bulk(T2, [doc_for(r, max(1, m + 1 - L + 1), m + 1, deleted=True)])
    print(f"CONTROL new leaf {m + 1} (deleted): HTTP {s} {b}")
    print("T2 final:", r.observe(T2, "T2 final")["summary"])


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
