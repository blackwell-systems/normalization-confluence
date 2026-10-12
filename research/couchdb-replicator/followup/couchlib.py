"""Shared helpers for the apache/couchdb#6162 default-settings tests (CouchDB 3.5.3, local only).

Python 3 standard library only. COUCH=http://admin:p3password@127.0.0.1:5984
Revisions of document X on the main line are labelled by generation number ("600");
paths are shown compressed, e.g. "207..1206(del)".
"""
import base64
import json
import os
import time
import urllib.error
import urllib.parse
import urllib.request

COUCH = os.environ.get("COUCH", "http://admin:p3password@127.0.0.1:5984")
_u = urllib.parse.urlsplit(COUCH)
BASE = f"{_u.scheme}://{_u.hostname}:{_u.port}"
AUTH = "Basic " + base64.b64encode(f"{_u.username}:{_u.password}".encode()).decode()
HERE = os.path.dirname(os.path.abspath(__file__))
DOC = "X"
VDU = {"_id": "_design/accept",
       "validate_doc_update": "function(newDoc, oldDoc, userCtx, secObj) {}"}
SMALL = {"worker_processes": 1, "worker_batch_size": 1}
ONLY_X = {"doc_ids": [DOC]}


def req(method, path, body=None):
    data = None if body is None else json.dumps(body).encode()
    h = {"Authorization": AUTH, "Content-Type": "application/json", "Accept": "application/json"}
    r = urllib.request.Request(BASE + path, data=data, method=method, headers=h)
    try:
        with urllib.request.urlopen(r, timeout=600) as resp:
            return resp.status, json.loads(resp.read() or b"null")
    except urllib.error.HTTPError as e:
        return e.code, json.loads(e.read() or b"null")


class Run:
    def __init__(self, name, quiet=False):
        self.name = name
        self.tag = f"{name}_{int(time.time() * 1000) % 10**9}"
        self.steps = []
        self.labels = {}
        self.revs = {}      # label -> rev
        self.dbs = []
        self.prev = {}
        self.quiet = quiet

    def log(self, text, **extra):
        rec = {"step": len(self.steps) + 1, "action": text}
        rec.update(extra)
        self.steps.append(rec)
        if not self.quiet:
            print(f"  {rec['step']:2d}. {text}" + (f"  {extra}" if extra else ""), flush=True)

    def db(self, short, revs_limit=1000, vdu=False):
        name = f"t6162_{self.tag.lower()}_{short.lower()}"
        req("DELETE", f"/{name}")
        s, b = req("PUT", f"/{name}")
        assert s in (201, 202), (s, b)
        s, b = req("PUT", f"/{name}/_revs_limit", revs_limit)
        assert s == 200, (s, b)
        if vdu:
            s, b = req("PUT", f"/{name}/_design/accept", VDU)
            assert s in (201, 202), (s, b)
        self.dbs.append(name)
        self.log(f"create {short} revs_limit={revs_limit}" + (" +accept-all VDU" if vdu else ""))
        return name

    def lab(self, rev):
        return self.labels.get(rev, rev)

    # ---- interactive edits on a source ----
    def edit(self, db, short, n=1, deleted=False, branch=""):
        """n interactive edits of X on db (creating it if absent); labels by generation."""
        s, cur = req("GET", f"/{db}/{DOC}")
        rev = cur["_rev"] if s == 200 else None
        first = None
        for i in range(n):
            doc = {"_id": DOC, "v": f"{short}{branch}-{i}-{time.time()}"}
            if rev:
                doc["_rev"] = rev
            if deleted and i == n - 1:
                doc["_deleted"] = True
            s, b = req("PUT", f"/{db}/{DOC}", doc)
            assert s in (200, 201, 202), (s, b)
            rev = b["rev"]
            gen = rev.split("-")[0]
            lab = gen + branch
            self.labels[rev] = lab
            self.revs[lab] = rev
            first = first or lab
        self.log(f"{short}: {n} edit(s) of {DOC}{' (last is a delete)' if deleted else ''} -> {first}..{lab}")
        return rev

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
        cum = {k: h.get(k) or 0 for k in ("missing_checked", "missing_found", "docs_read", "docs_written", "doc_write_failures")}
        rid = (src, dst, json.dumps(opts.get("doc_ids")))  # replication id varies with doc_ids, not worker settings
        prev = self.prev.get(rid, {})
        stats = {k: v - prev.get(k, 0) for k, v in cum.items()}
        self.prev[rid] = cum
        o = " ".join(f"{k}={v}" for k, v in opts.items() if k != "doc_ids") + (" doc_ids=[X]" if "doc_ids" in opts else "")
        self.log(f"replicate {ssh} -> {dsh}" + (f" ({o.strip()})" if o.strip() else ""), stats=stats)
        return stats

    # ---- direct injection (what the replicator sends) ----
    def path_revs(self, labels):
        """labels root-to-leaf (contiguous generations) -> _revisions object"""
        revs = [self.revs[l] for l in labels]
        start = int(revs[-1].split("-")[0])
        return {"start": start, "ids": [r.split("-", 1)[1] for r in reversed(revs)]}

    def inject(self, db, short, lo, hi, deleted=False, extra_docs=None, branch=""):
        """POST _bulk_docs new_edits:false with leaf `hi` and history lo..hi (generations)."""
        labels = [f"{g}{branch}" for g in range(lo, hi + 1)]
        doc = {"_id": DOC, "_rev": self.revs[labels[-1]], "_revisions": self.path_revs(labels), "v": f"inj-{hi}"}
        if deleted:
            doc["_deleted"] = True
        s, b = req("POST", f"/{db}/_bulk_docs", {"docs": [doc] + (extra_docs or []), "new_edits": False})
        assert s == 201, (s, b)
        self.log(f"inject into {short}: leaf {hi}{branch}{' (deleted)' if deleted else ''} with history {lo}..{hi}"
                 + (f" (+{len(extra_docs)} other docs in the same request)" if extra_docs else ""), resp=b)

    # ---- observation ----
    def compress(self, labels):
        out, i = [], 0
        while i < len(labels):
            j = i
            while j + 1 < len(labels) and labels[j + 1].isdigit() and labels[j].isdigit() and int(labels[j + 1]) == int(labels[j]) + 1:
                j += 1
            out.append(labels[i] if i == j else f"{labels[i]}..{labels[j]}")
            i = j + 1
        return ",".join(out)

    def observe(self, db, short):
        s, doc = req("GET", f"/{db}/{DOC}?conflicts=true&deleted_conflicts=true")
        _, leaves = req("GET", f"/{db}/{DOC}?open_revs=all&revs=true")
        leafs = []
        for item in leaves if isinstance(leaves, list) else []:
            d = item.get("ok")
            if not d:
                continue
            r = d["_revisions"]
            path = [f"{r['start'] - i}-{x}" for i, x in enumerate(r["ids"])]
            labs = [self.lab(p) for p in reversed(path)]
            leafs.append({"leaf": self.lab(d["_rev"]), "deleted": bool(d.get("_deleted")),
                          "path_len": len(labs), "path": self.compress(labs)})
        out = {
            "db": short, "GET_status": s, "live": s == 200,
            "winner": self.lab(doc["_rev"]) if s == 200 else None,
            "_conflicts": [self.lab(x) for x in doc.get("_conflicts", [])] if s == 200 else None,
            "_deleted_conflicts": [self.lab(x) for x in doc.get("_deleted_conflicts", [])] if s == 200 else None,
            "leaves": sorted(leafs, key=lambda x: x["path"]),
        }
        out["summary"] = (f"LIVE winner={out['winner']} conflicts={out['_conflicts']}" if out["live"] else f"DELETED (GET {s})") \
            + "  leaves=" + "; ".join(f"[{l['path']}]{'(del)' if l['deleted'] else ''}" for l in out["leaves"])
        if not self.quiet:
            print(f"     {short}: {out['summary']}", flush=True)
        return out

    def same(self, a, b):
        key = lambda o: (o["live"], o["winner"], tuple(sorted(o["_conflicts"] or [])),
                         tuple((l["leaf"], l["deleted"], l["path"]) for l in o["leaves"]))
        return key(a) == key(b)

    def save(self, result, note="", keep=False):
        os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
        with open(os.path.join(HERE, "results", f"{self.name}.json"), "w") as f:
            json.dump({"scenario": self.name, "note": note, "couchdb": req("GET", "/")[1].get("version"),
                       "steps": self.steps, "result": result}, f, indent=1)
        if not keep:
            for d in self.dbs:
                req("DELETE", f"/{d}")
