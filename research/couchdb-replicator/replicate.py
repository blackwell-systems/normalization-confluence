#!/usr/bin/env python3
"""Can the real CouchDB replicator reach the P3 behaviors? (CouchDB 3.5.3)

Every write to a source database is an ordinary interactive edit (PUT, DELETE,
or _bulk_docs without new_edits). Every revision that reaches a target arrives
through POST /_replicate (one-shot, sequential). Nothing is injected with
new_edits=false.

Usage: COUCH=http://admin:p3password@127.0.0.1:5984 python3 replicate.py [scenario ...]
Scenarios: resurrect, vdu_min, vdu_five, vdu_control, vdu_default, vdu_default_control
Writes results/<scenario>.json and prints a summary.
"""
import base64
import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

COUCH = os.environ.get("COUCH", "http://admin:p3password@127.0.0.1:5984")
_u = urllib.parse.urlsplit(COUCH)
BASE = f"{_u.scheme}://{_u.hostname}:{_u.port}"
AUTH = "Basic " + base64.b64encode(f"{_u.username}:{_u.password}".encode()).decode()
HERE = os.path.dirname(os.path.abspath(__file__))
RUN = str(int(time.time()))
DOC = "X"
VDU = {
    "_id": "_design/accept",
    "validate_doc_update": "function(newDoc, oldDoc, userCtx, secObj) {}",
}


def req(method, path, body=None, headers=None):
    data = None if body is None else json.dumps(body).encode()
    h = {"Authorization": AUTH, "Content-Type": "application/json",
         "Accept": "application/json"}
    h.update(headers or {})
    r = urllib.request.Request(BASE + path, data=data, method=method, headers=h)
    try:
        with urllib.request.urlopen(r, timeout=600) as resp:
            return resp.status, json.loads(resp.read() or b"null")
    except urllib.error.HTTPError as e:
        return e.code, json.loads(e.read() or b"null")


class Run:
    def __init__(self, name):
        self.name = name
        self.steps = []
        self.labels = {}  # rev string -> short label
        self.dbs = []
        self.prev = {}

    def db(self, short, revs_limit=1000, vdu=False):
        name = f"rc_{self.name}_{short.lower()}_{RUN}"
        req("DELETE", f"/{name}")
        s, b = req("PUT", f"/{name}")
        assert s in (201, 202), (s, b)
        s, b = req("PUT", f"/{name}/_revs_limit", revs_limit)
        assert s == 200, (s, b)
        if vdu:
            s, b = req("PUT", f"/{name}/_design/accept", VDU)
            assert s in (201, 202), (s, b)
        self.dbs.append(name)
        self.log(f"create {short} revs_limit={revs_limit}" + (" with accept-all validate_doc_update" if vdu else ""))
        return name

    def log(self, text, **extra):
        rec = {"step": len(self.steps) + 1, "action": text}
        rec.update(extra)
        self.steps.append(rec)
        print(f"  {rec['step']:2d}. {text}" + (f"  {extra}" if extra else ""))

    def label(self, rev, lab):
        self.labels[rev] = lab

    def lab(self, rev):
        return self.labels.get(rev, rev)

    # interactive edits on a source
    def put(self, db, short, lab, body, deleted=False):
        s, cur = req("GET", f"/{db}/{DOC}")
        doc = dict(body)
        doc["_id"] = DOC
        if s == 200:
            doc["_rev"] = cur["_rev"]
        if deleted:
            doc["_deleted"] = True
        s, b = req("PUT", f"/{db}/{DOC}", doc)
        assert s in (200, 201, 202), (s, b)
        self.label(b["rev"], lab)
        self.log(f"{short}: {'delete' if deleted else 'edit'} {DOC} -> {lab}", rev=b["rev"])

    def fillers(self, db, short, n, tag):
        docs = [{"_id": f"filler_{tag}_{i:06d}", "n": i} for i in range(n)]
        for i in range(0, n, 5000):
            s, b = req("POST", f"/{db}/_bulk_docs", {"docs": docs[i:i + 5000]})
            assert s == 201, (s, b)
        self.log(f"{short}: write {n} unrelated filler docs")

    def replicate(self, src, dst, ssh, dsh, **opts):
        body = {"source": COUCH + "/" + src, "target": COUCH + "/" + dst}
        body.update(opts)
        s, b = req("POST", "/_replicate", body)
        assert s == 200 and b.get("ok"), (s, b)
        h = (b.get("history") or [{}])[0]
        # history stats are cumulative over sessions of the same replication id: report this session's delta
        cum = {k: h.get(k) or 0 for k in ("missing_checked", "missing_found", "docs_read", "docs_written", "doc_write_failures")}
        prev = self.prev.get((src, dst), {})
        stats = {k: v - prev.get(k, 0) for k, v in cum.items()}
        self.prev[(src, dst)] = cum
        o = " ".join(f"{k}={v}" for k, v in opts.items())
        self.log(f"replicate {ssh} -> {dsh}" + (f" ({o})" if o else ""), stats=stats)
        return stats

    def observe(self, db, short):
        s, doc = req("GET", f"/{db}/{DOC}?conflicts=true&deleted_conflicts=true")
        _, leaves = req("GET", f"/{db}/{DOC}?open_revs=all&revs=true")
        leafs = []
        for item in leaves:
            d = item.get("ok")
            if not d:
                continue
            r = d["_revisions"]
            path = [f"{r['start'] - i}-{x}" for i, x in enumerate(r["ids"])]
            leafs.append({
                "leaf": self.lab(d["_rev"]),
                "deleted": bool(d.get("_deleted")),
                "path_root_to_leaf": [self.lab(p) for p in reversed(path)],
            })
        out = {
            "db": short,
            "GET_status": s,
            "live": s == 200,
            "winner": self.lab(doc["_rev"]) if s == 200 else None,
            "_conflicts": [self.lab(x) for x in doc.get("_conflicts", [])] if s == 200 else None,
            "_deleted_conflicts": [self.lab(x) for x in doc.get("_deleted_conflicts", [])] if s == 200 else None,
            "leaves": sorted(leafs, key=lambda x: x["leaf"]),
        }
        print(f"     {short}: " + (f"LIVE winner={out['winner']} conflicts={out['_conflicts']}" if out["live"] else f"DELETED (GET {s})")
              + "  leaves=" + "; ".join(f"{'/'.join(l['path_root_to_leaf'])}{' (deleted)' if l['deleted'] else ''}" for l in out["leaves"]))
        return out

    def save(self, finals, note=""):
        os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
        with open(os.path.join(HERE, "results", f"{self.name}.json"), "w") as f:
            json.dump({"scenario": self.name, "note": note, "couchdb": req("GET", "/")[1].get("version"),
                       "steps": self.steps, "final": finals}, f, indent=1)
        for d in self.dbs:
            req("DELETE", f"/{d}")


# ---------------------------------------------------------------------------
# P3 claim 1 through the replicator: a stray 1-a resurrects a deleted document
# ---------------------------------------------------------------------------
def resurrect():
    print("scenario resurrect")
    r = Run("resurrect")
    A = r.db("A", 1000)
    C = r.db("C", 1000)
    T1 = r.db("T1", 3)
    T2 = r.db("T2", 3, vdu=True)
    U1 = r.db("U1", 3)              # same as T1, opposite replication order
    U2 = r.db("U2", 3, vdu=True)
    E = r.db("E", 1000)             # a third replica that later pulls from T1
    r.put(A, "A", "1-a", {"v": "a"})
    r.replicate(A, C, "A", "C")     # C syncs at 1-a and goes offline
    r.put(A, "A", "2-b", {"v": "b"})
    r.put(A, "A", "3-c", {"v": "c"})
    r.put(A, "A", "4-d", {}, deleted=True)
    # order 1: deletion first, stray 1-a after
    for T, n in ((T1, "T1"), (T2, "T2")):
        r.replicate(A, T, "A", n)
        r.replicate(C, T, "C", n)
    # order 2: stray 1-a first, deletion after
    for U, n in ((U1, "U1"), (U2, "U2")):
        r.replicate(C, U, "C", n)
        r.replicate(A, U, "A", n)
    # does the resurrection spread, and does it ever heal?
    r.replicate(T1, A, "T1", "A")
    r.replicate(A, T1, "A", "T1")
    r.replicate(T1, E, "T1", "E")
    r.replicate(A, E, "A", "E")
    finals = [r.observe(d, n) for d, n in ((T1, "T1"), (T2, "T2"), (U1, "U1"), (U2, "U2"), (A, "A"), (C, "C"), (E, "E"))]
    r.save(finals)
    return finals


# ---------------------------------------------------------------------------
# The validate_doc_update dependence (P3 S2) through the replicator
# ---------------------------------------------------------------------------
def vdu(name, n_fill, fillers_before, rep_opts):
    """A: full history. C: synced at 1-a. B: revs_limit 1 (holds 2-b with history [b]).
    D: revs_limit 2 (holds the deletion with history [b, d]).
    C, B and D replicate from A with doc_ids=[X], so they never hold the fillers.
    T1: no validate_doc_update. T2: accept-all validate_doc_update.
    n_fill unrelated docs are written on A, before the 2-b edit (so they precede X
    in A's changes feed) when fillers_before, else after it."""
    print(f"scenario {name}")
    r = Run(name)
    A = r.db("A", 1000)
    C = r.db("C", 1000)
    B = r.db("B", 1)
    D = r.db("D", 2)
    T1 = r.db("T1", 1000)
    T2 = r.db("T2", 1000, vdu=True)
    r.put(A, "A", "1-a", {"v": "a"})
    only_x = {"doc_ids": [DOC]}    # C, B and D are replicas that sync only document X
    r.replicate(A, C, "A", "C", **only_x)
    if fillers_before:
        r.fillers(A, "A", n_fill, "f")
    r.put(A, "A", "2-b", {"v": "b"})
    if not fillers_before:
        r.fillers(A, "A", n_fill, "f")
    r.replicate(A, B, "A", "B", **only_x)  # B stems 2-b to history [b]
    for T, n in ((T1, "T1"), (T2, "T2")):
        r.replicate(C, T, "C", n)   # 1-a with history [a]
        r.replicate(B, T, "B", n)   # 2-b with history [b]: a second root
    mid = [r.observe(T1, "T1 after C,B"), r.observe(T2, "T2 after C,B")]
    for T, n in ((T1, "T1"), (T2, "T2")):
        r.replicate(A, T, "A", n, **rep_opts)  # A holds 2-b with history [a, b]
    mid += [r.observe(T1, "T1 after A"), r.observe(T2, "T2 after A")]
    r.put(A, "A", "3-d", {}, deleted=True)
    r.replicate(A, D, "A", "D", **only_x)  # D stems the deletion to history [b, d]
    for T, n in ((T1, "T1"), (T2, "T2")):
        r.replicate(D, T, "D", n)
    finals = [r.observe(T1, "T1"), r.observe(T2, "T2")]
    r.save({"intermediate": mid, "final": finals},
           note=f"{n_fill} fillers {'before' if fillers_before else 'after'} the 2-b edit; A->T options {rep_opts}")
    return finals


SMALL = {"worker_processes": 1, "worker_batch_size": 1}
SCENARIOS = {
    "resurrect": resurrect,
    "vdu_min": lambda: vdu("vdu_min", 6, True, SMALL),
    "vdu_five": lambda: vdu("vdu_five", 5, True, SMALL),
    "vdu_control": lambda: vdu("vdu_control", 6, False, SMALL),
    "vdu_default": lambda: vdu("vdu_default", 20000, True, {}),
    "vdu_default_control": lambda: vdu("vdu_default_control", 20000, False, {}),
}

if __name__ == "__main__":
    for s in (sys.argv[1:] or list(SCENARIOS)):
        SCENARIOS[s]()
