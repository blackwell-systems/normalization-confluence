"""Test harness against a real CouchDB. NOT RUN before P3 is committed.

Replays every exactly-once delivery order of a scenario's replicated
revisions into a fresh document, one revision per request
(POST /db/_bulk_docs with new_edits=false, which is what the replicator does on
the target), then reads the leaf set, the winner and live-or-deleted, and
compares each order with the model's prediction (compute.py).

Usage:
  COUCH=http://admin:pw@127.0.0.1:5984 python3 couch_harness.py S1 [--raw] [--reps 3]
  --raw: set [couchdb] stem_interactive_updates = false for the run, deliver
         every order, then compact the database once and read.
  --dup: deliver every revision twice in a row (the model predicts no change).
Writes results_<scenario>[_raw]_rep<n>.csv and prints mismatch counts.
"""

import base64
import itertools
import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

import compute as C
import couch_model as cm

URL = os.environ.get("COUCH", "http://admin:password@127.0.0.1:5984")
_u = urllib.parse.urlsplit(URL)
BASE = "%s://%s:%d" % (_u.scheme, _u.hostname, _u.port or 5984)
AUTH = base64.b64encode(("%s:%s" % (_u.username, _u.password)).encode()).decode()


def req(method, path, body=None):
    data = None if body is None else json.dumps(body).encode()
    r = urllib.request.Request(BASE + path, data=data, method=method)
    r.add_header("Authorization", "Basic " + AUTH)
    r.add_header("Content-Type", "application/json")
    r.add_header("Accept", "application/json")
    try:
        with urllib.request.urlopen(r) as resp:
            return resp.status, json.loads(resp.read() or b"null")
    except urllib.error.HTTPError as e:
        return e.code, json.loads(e.read() or b"null")


def deliver(db, doc_id, ev):
    pos, ids, deleted = ev
    doc = {"_id": doc_id, "_rev": "%d-%s" % (pos, ids[0]),
           "_revisions": {"start": pos, "ids": ids}, "v": "%d-%s" % (pos, ids[0][0])}
    if deleted:
        doc["_deleted"] = True
    st, body = req("POST", "/%s/_bulk_docs" % db, {"docs": [doc], "new_edits": False})
    assert st == 201, (st, body)


def observe(db, doc_id):
    q = urllib.parse.quote(doc_id, safe="")
    st, body = req("GET", "/%s/%s?open_revs=all" % (db, q))
    assert st == 200, (st, body)
    leaves = []
    for item in body:
        d = item["ok"]
        p, r = d["_rev"].split("-", 1)
        leaves.append((int(p), r, bool(d.get("_deleted"))))
    st, w = req("GET", "/%s/%s" % (db, q))
    live = st == 200
    winner = None
    if live:
        p, r = w["_rev"].split("-", 1)
        winner = (int(p), r, False)
    return tuple(sorted(leaves)), live, winner


def fmt_winner(w):
    return "-" if w is None else "%d-%s" % (w[0], w[1][0])


def predicted_winner(leaves):
    """Non-deleted before deleted, then the higher position, then the higher id."""
    live = [l for l in leaves if not l[2]]
    return max(live, key=lambda l: (l[0], l[1])) if live else None


def fmt_leaves(ls):
    return "{" + " ".join("%d-%s%s" % (p, r[0], "(del)" if d else "") for p, r, d in ls) + "}"


def main():
    scen = sys.argv[1]
    raw = "--raw" in sys.argv
    dup = "--dup" in sys.argv
    reps = int(sys.argv[sys.argv.index("--reps") + 1]) if "--reps" in sys.argv else 3
    title, hist, dl, sel, k = C.SCENARIOS[scen]
    events = C.events_for(hist, dl, sel)
    orders = list(itertools.permutations(range(len(events))))
    cfg = "/_node/_local/_config/couchdb/stem_interactive_updates"
    if raw:
        prev_st, prev = req("GET", cfg)
        req("PUT", cfg, "false")
    try:
        for rep in range(reps):
            db = "p3_%s%s%s_rep%d_%d" % (scen.lower(), "_raw" if raw else "",
                                         "_dup" if dup else "", rep, int(time.time()))
            st, b = req("PUT", "/%s?q=1&n=1" % db)
            assert st in (201, 202), (st, b)
            st, b = req("PUT", "/%s/_revs_limit" % db, k)
            assert st == 200, (st, b)
            for n, order in enumerate(orders):
                for i in order:
                    for _ in range(2 if dup else 1):
                        deliver(db, "o%06d" % n, events[i][1])
            if raw:
                st, b = req("POST", "/%s/_compact" % db, {})
                assert st == 202, (st, b)
                time.sleep(1)
                while req("GET", "/%s" % db)[1].get("compact_running"):
                    time.sleep(1)
            bad = 0
            bad_leaves = 0
            with open("results_%s%s%s_rep%d.csv" % (scen, "_raw" if raw else "",
                                                   "_dup" if dup else "", rep), "w") as f:
                f.write("order,predicted_live,observed_live,predicted_winner,observed_winner,"
                        "predicted_leaves,observed_leaves,scored_match,leaves_match\n")
                for n, order in enumerate(orders):
                    T = ()
                    for i in order:
                        T = cm.replicated_update(T, events[i][1], k, not raw)
                    if raw:
                        T = cm.compact(T, k)
                    pl, pls = cm.obs_live(T), cm.obs_leaves(T)
                    ol, olive, ow = observe(db, "o%06d" % n)
                    pw = predicted_winner(pls)
                    # P3 scores live or deleted and the winner; the leaf set is reported.
                    ok = (pl == olive) and (pw == ow)
                    lok = pls == ol
                    bad += not ok
                    bad_leaves += not lok
                    f.write("%s,%s,%s,%s,%s,%s,%s,%s,%s\n" % (
                        " ".join(events[i][0] for i in order), pl, olive,
                        fmt_winner(pw), fmt_winner(ow),
                        fmt_leaves(pls), fmt_leaves(ol), ok, lok))
            print("%s%s rep %d: %d of %d orders differ from the model on live/deleted or "
                  "winner; %d on the leaf set"
                  % (scen, " (raw)" if raw else "", rep, bad, len(orders), bad_leaves))
    finally:
        if raw:
            if prev_st == 200:
                req("PUT", cfg, prev)
            else:
                req("DELETE", cfg)


if __name__ == "__main__":
    main()
