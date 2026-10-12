#!/usr/bin/env python3
"""Manage the papers' versions on Zenodo from this repository.

  python3 scripts/zenodo.py status [paper ...]   compare Zenodo's latest version with the repo (no token)
  python3 scripts/zenodo.py draft  [paper ...]   create an unpublished new-version draft with the repo's
                                                 files and the version fields of zenodo/papers.json
  python3 scripts/zenodo.py publish <deposition-id>   publish a reviewed draft (permanent)
  python3 scripts/zenodo.py check                 confirm the token works (read-only: lists your depositions)

Papers are the keys of zenodo/papers.json (default: all). draft and publish need ZENODO_TOKEN in the
environment (scopes deposit:write and deposit:actions); ZENODO_URL selects the server
(default https://zenodo.org; https://sandbox.zenodo.org for tests). Standard library only.
"""
import datetime
import hashlib
import json
import os
import sys
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONFIG = json.loads((ROOT / "zenodo" / "papers.json").read_text())
BASE = os.environ.get("ZENODO_URL", "https://zenodo.org").rstrip("/")
TOKEN = os.environ.get("ZENODO_TOKEN")


def call(method, url, body=None, raw=None, auth=True):
    if not url.startswith("http"):
        url = BASE + url
    data, headers = None, {"Accept": "application/json"}
    if body is not None:
        data, headers["Content-Type"] = json.dumps(body).encode(), "application/json"
    if raw is not None:
        data, headers["Content-Type"] = raw, "application/octet-stream"
    if auth:
        if not TOKEN:
            sys.exit("ZENODO_TOKEN is not set")
        headers["Authorization"] = "Bearer " + TOKEN
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    try:
        with urllib.request.urlopen(req) as r:
            text = r.read()
            return json.loads(text) if text else {}
    except urllib.error.HTTPError as e:
        sys.exit(f"{method} {url}: HTTP {e.code}: {e.read().decode(errors='replace')[:500]}")


def md5(path):
    return hashlib.md5((ROOT / path).read_bytes()).hexdigest()


def papers(names):
    allp = CONFIG["papers"]
    for n in names:
        if n not in allp:
            sys.exit(f"unknown paper {n}; known: {', '.join(allp)}")
    return {n: allp[n] for n in (names or allp)}


def latest(concept):
    return call("GET", f"/api/records/{concept}", auth=False)


def status(names):
    stale = False
    for name, p in papers(names).items():
        rec = latest(p["concept"])
        remote = {f["key"]: f.get("checksum", "").removeprefix("md5:") for f in rec.get("files", [])}
        print(f"{name}: latest version {rec['id']} ({rec['metadata'].get('publication_date')}, "
              f"version {rec['metadata'].get('version') or 'unlabeled'})")
        for key, path in p["files"].items():
            local = md5(path)
            state = "same" if remote.get(key) == local else ("missing on Zenodo" if key not in remote else "differs")
            stale |= state != "same"
            print(f"  {key}: {state}")
    return 1 if stale else 0


def draft(names):
    for name, p in papers(names).items():
        rec = latest(p["concept"])
        res = call("POST", f"/api/deposit/depositions/{rec['id']}/actions/newversion")
        dep = call("GET", res["links"]["latest_draft"])
        for f in dep.get("files", []):
            call("DELETE", f"/api/deposit/depositions/{dep['id']}/files/{f['id']}")
        bucket = dep["links"]["bucket"]
        for key, path in p["files"].items():
            call("PUT", f"{bucket}/{key}", raw=(ROOT / path).read_bytes())
        meta = dict(dep["metadata"])
        meta.update(p.get("version", {}))
        meta["publication_date"] = datetime.date.today().isoformat()
        rel = [r for r in meta.get("related_identifiers", []) if r.get("relation") != "isNewVersionOf"]
        known = {r["identifier"] for r in rel}
        rel += [r for r in CONFIG.get("related_identifiers", []) if r["identifier"] not in known]
        meta["related_identifiers"] = rel
        meta.pop("doi", None)
        meta.pop("prereserve_doi", None)
        call("PUT", f"/api/deposit/depositions/{dep['id']}", body={"metadata": meta})
        print(f"{name}: draft {dep['id']} created, not published. Review it at "
              f"{BASE}/deposit/{dep['id']}, then: python3 scripts/zenodo.py publish {dep['id']}")


def check():
    deps = call("GET", "/api/deposit/depositions?size=50")
    print(f"token works: {len(deps)} depositions visible")
    for d in deps:
        print(f"  {d['id']}  {d.get('state')}  submitted={d.get('submitted')}  {d.get('title')}")


def publish(dep_id):
    res = call("POST", f"/api/deposit/depositions/{dep_id}/actions/publish")
    print(f"published {dep_id}: DOI {res.get('doi')}, {res.get('links', {}).get('record_html') or res.get('links', {}).get('html')}")


if __name__ == "__main__":
    if len(sys.argv) < 2 or sys.argv[1] not in ("status", "draft", "publish", "check"):
        sys.exit(__doc__)
    cmd, args = sys.argv[1], sys.argv[2:]
    if cmd == "status":
        sys.exit(status(args))
    if cmd == "check":
        check()
    elif cmd == "draft":
        draft(args)
    else:
        if len(args) != 1:
            sys.exit("publish takes one deposition id")
        publish(args[0])
