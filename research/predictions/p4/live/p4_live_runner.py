#!/usr/bin/env python3
"""Live runner for prediction P4 (research/predictions/P4.md), one run per invocation.

Follows P4's Steps 1-8 against two running Sync Gateways:
  A: admin http://127.0.0.1:4985, database "dba" (bucketA), runs the ISGR replication "p4" to B
  B: admin http://127.0.0.1:4995, database "dbb" (bucketB), passive

Usage: p4_live_runner.py <mode> <run-number>   (mode: delayed | control)
The mode only labels the run; the sync function on A is configured outside this script.
Writes runs/<mode>_<n>.json and logs/<mode>_<n>_{A,B}.log (the gateways' console output during the run).
"""
import base64
import datetime
import json
import os
import sys
import time
import urllib.error
import urllib.request

A = "http://127.0.0.1:4985/dba"
B = "http://127.0.0.1:4995/dbb"
A_ROOT = "http://127.0.0.1:4985"
REPL = "p4"
AUTH = "Basic " + base64.b64encode(os.environ.get("SG_ADMIN_AUTH", "Administrator:password").encode()).decode()  # local throwaway credentials
A_CONSOLE = "/tmp/nc-agents/p4work/sgA/console.log"
B_CONSOLE = "/tmp/nc-agents/p4work/sgB/console.log"
HERE = os.path.dirname(os.path.abspath(__file__))
IDLE_SECS = 60
IDLE_CAP_SECS = 600


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="milliseconds")


def req(method, url, body=None):
    data = None if body is None else json.dumps(body).encode()
    r = urllib.request.Request(url, data=data, method=method)
    r.add_header("Authorization", AUTH)
    if data is not None:
        r.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(r, timeout=60) as resp:
            raw = resp.read()
            code = resp.status
    except urllib.error.HTTPError as e:
        raw = e.read()
        code = e.code
    try:
        parsed = json.loads(raw) if raw else None
    except ValueError:
        parsed = raw.decode(errors="replace")
    return code, parsed


def le_hex(h):
    """_vv ver/cvCas: 0x-prefixed little-endian hex of a uint64."""
    return int.from_bytes(bytes.fromhex(h[2:] if h.startswith("0x") else h), "little")


def delta_hex(h):
    """pv/mv delta: little-endian hex with trailing zeros stripped (base.HexCasToUint64ForDelta)."""
    if len(h) % 2:
        h += "0"
    b = bytes.fromhex(h)
    return int.from_bytes(b + bytes(8 - len(b)), "little")


def deltas_to_map(lst):
    out, acc = {}, 0
    for item in lst or []:
        ts, src = item.split("@", 1)
        acc += delta_hex(ts)
        out[src] = acc
    return out


def cv_of_response(cv):
    """cv as returned by the REST write responses: '<big-endian hex>@<src>'."""
    ts, src = cv.split("@", 1)
    return src, int(ts, 16)


def decode_raw(raw):
    """Summarize a GET /_raw/{doc} response: deleted flag, rev-tree winner, _vv decoded."""
    if not isinstance(raw, dict):
        return {"error": raw}
    x = raw.get("_xattrs", {})
    sync = x.get("_sync") or {}
    vv = x.get("_vv") or {}
    meta = x.get("$document") or {}
    return {
        "deleted_document_meta": meta.get("deleted"),
        "sync_flags": sync.get("flags"),
        "revtree_winner": (sync.get("rev") or {}).get("rev"),
        "revtree_revs": sync.get("history", {}).get("revs", []),
        "revtree_deleted_idx": sync.get("history", {}).get("deleted"),
        "cv_src": vv.get("src"),
        "cv_ver": le_hex(vv["ver"]) if vv.get("ver") else None,
        "pv": deltas_to_map(vv.get("pv")),
        "mv": deltas_to_map(vv.get("mv")),
        "body": {k: v for k, v in raw.items() if k != "_xattrs"},
    }


def repl_snapshot():
    _, status = req("GET", f"{A}/_replicationStatus/{REPL}")
    _, ev = req("GET", f"{A_ROOT}/_expvar")
    stats = ev["syncgateway"]["per_db"]["dba"]["replications"].get(REPL, {}) if isinstance(ev, dict) else {}
    return {"status": status, "stats": stats}


def counters(snap):
    s = dict(snap["stats"])
    st = snap["status"] if isinstance(snap["status"], dict) else {}
    keys = ["docs_read", "docs_checked_pull", "docs_written", "docs_checked_push", "doc_write_conflict",
            "doc_write_failures", "rejected_by_remote", "rejected_by_local", "last_seq_pull", "last_seq_push"]
    return json.dumps([s, {k: st.get(k) for k in keys}], sort_keys=True)


def read_doc(base, docid):
    code, body = req("GET", f"{base}/{docid}")
    rcode, raw = req("GET", f"{base}/_raw/{docid}")
    return {"GET_status": code, "GET_body": body, "raw_status": rcode, "raw": raw, "raw_decoded": decode_raw(raw)}


def pending(base, since):
    _, ch = req("GET", f"{base}/_changes?since={since}")
    return ch


def main():
    mode, n = sys.argv[1], int(sys.argv[2])
    docid = f"x-{mode}-{n}-{int(time.time())}"
    out = {"mode": mode, "run": n, "doc_id": docid, "steps": {}}
    st = out["steps"]
    a_off = os.path.getsize(A_CONSOLE)
    b_off = os.path.getsize(B_CONSOLE)
    out["repl_before"] = repl_snapshot()

    # 1. Create x on A; wait until both gateways hold 1- of x.
    t = now()
    code, resp = req("PUT", f"{A}/{docid}", {"v": 1})
    rev1 = resp.get("rev") if isinstance(resp, dict) else None
    st["1_create_on_A"] = {"t": t, "status": code, "resp": resp}
    deadline = time.time() + 120
    while True:
        cb, bb = req("GET", f"{B}/{docid}")
        if cb == 200 and isinstance(bb, dict) and bb.get("_rev", "").startswith("1-"):
            break
        if time.time() > deadline:
            st["1_wait_both"] = {"t": now(), "timeout": True, "B": [cb, bb]}
            break
        time.sleep(0.1)
    st.setdefault("1_wait_both", {"t": now(), "B_rev": bb.get("_rev") if isinstance(bb, dict) else None})

    # 2. On B: DELETE x (tb1, revision 2-).
    t = now()
    code, resp = req("DELETE", f"{B}/{docid}?rev={rev1}")
    st["2_delete_on_B_tb1"] = {"t": t, "status": code, "resp": resp}
    tb1 = cv_of_response(resp["cv"]) if isinstance(resp, dict) and resp.get("cv") else None

    # 3. Wait 1 s.
    time.sleep(1.0)
    st["3_waited_1s"] = {"t": now()}

    # 4. On B: PUT x {"v": 2} (3-), then DELETE x (tb2, 4-).
    t = now()
    code, resp = req("PUT", f"{B}/{docid}", {"v": 2})
    rev3 = resp.get("rev") if isinstance(resp, dict) else None
    st["4a_recreate_on_B"] = {"t": t, "status": code, "resp": resp}
    t = now()
    code, resp = req("DELETE", f"{B}/{docid}?rev={rev3}")
    st["4b_delete_on_B_tb2"] = {"t": t, "status": code, "resp": resp}
    tb2 = cv_of_response(resp["cv"]) if isinstance(resp, dict) and resp.get("cv") else None

    # 5. Wait 10 s. Read A's _raw/x.
    time.sleep(10.0)
    t = now()
    a5 = read_doc(A, docid)
    b5 = read_doc(B, docid)
    st["5_after_10s"] = {"t": t, "A": a5, "B": b5}

    # 6. On A: PUT x {"v": 4} without _rev (a4).
    t = now()
    code, resp = req("PUT", f"{A}/{docid}", {"v": 4})
    st["6_put_on_A_a4"] = {"t": t, "status": code, "resp": resp}

    # 7. Wait until the replication is idle: 60 s with no change in its push and pull counters.
    t7 = time.time()
    last = counters(repl_snapshot())
    last_change = time.time()
    while time.time() - last_change < IDLE_SECS and time.time() - t7 < IDLE_CAP_SECS:
        time.sleep(2.0)
        c = counters(repl_snapshot())
        if c != last:
            last, last_change = c, time.time()
    st["7_idle"] = {"t": now(), "waited_s": round(time.time() - t7, 1),
                    "idle_reached": time.time() - last_change >= IDLE_SECS}

    # 8. Read x on both gateways, and A's replication status and stats.
    t = now()
    snap = repl_snapshot()
    a8 = read_doc(A, docid)
    b8 = read_doc(B, docid)
    st_status = snap["status"] if isinstance(snap["status"], dict) else {}
    pend = {
        "A_changes_since_last_seq_push": pending(A, st_status.get("last_seq_push", 0)),
        "B_changes_since_last_seq_pull": pending(B, st_status.get("last_seq_pull", 0)),
        "A_db": req("GET", f"{A}/")[1],
        "B_db": req("GET", f"{B}/")[1],
    }
    st["8_final"] = {"t": t, "A": a8, "B": b8, "repl": snap, "pending": pend}

    # Logs during the run.
    os.makedirs(os.path.join(HERE, "logs"), exist_ok=True)
    os.makedirs(os.path.join(HERE, "runs"), exist_ok=True)
    asserts = []
    for label, path, off in (("A", A_CONSOLE, a_off), ("B", B_CONSOLE, b_off)):
        with open(path, "rb") as f:
            f.seek(off)
            chunk = f.read().decode(errors="replace")
        with open(os.path.join(HERE, "logs", f"{mode}_{n}_{label}.log"), "w") as g:
            g.write(chunk)
        if label == "A":
            asserts = [l for l in chunk.splitlines() if "Assertion failed" in l]
            out["A_error_lines"] = [l for l in chunk.splitlines() if "[ERR]" in l]
    out["A_assertion_failed_lines"] = asserts

    # Scoring helpers (raw facts; the claims are scored in score.py).
    srcB = tb1[0] if tb1 else None
    d5 = a5["raw_decoded"]
    out["facts"] = {
        "tb1": {"src": tb1[0], "ver": tb1[1]} if tb1 else None,
        "tb2": {"src": tb2[0], "ver": tb2[1]} if tb2 else None,
        "after5_A_deleted": d5.get("deleted_document_meta"),
        "after5_A_winner": d5.get("revtree_winner"),
        "after5_A_cv": [d5.get("cv_src"), d5.get("cv_ver")],
        "after5_A_pv": d5.get("pv"),
        "after5_A_mv": d5.get("mv"),
        "after5_A_has_srcB_ge_tb2": bool(tb2) and any(
            src == srcB and ver >= tb2[1]
            for src, ver in [(d5.get("cv_src"), d5.get("cv_ver") or 0)] + list(d5.get("pv", {}).items()) + list(d5.get("mv", {}).items())),
        "final_A_status": a8["GET_status"], "final_A_body": a8["GET_body"],
        "final_B_status": b8["GET_status"], "final_B_body": b8["GET_body"],
        "final_A_cv": [a8["raw_decoded"].get("cv_src"), a8["raw_decoded"].get("cv_ver")],
        "final_B_cv": [b8["raw_decoded"].get("cv_src"), b8["raw_decoded"].get("cv_ver")],
        "repl_status": st_status.get("status"),
        "doc_write_conflict": st_status.get("doc_write_conflict", 0),
        "sgr_push_conflict_count": snap["stats"].get("sgr_push_conflict_count"),
        "sgr_push_conflict_count_before": out["repl_before"]["stats"].get("sgr_push_conflict_count"),
        "idle_reached": st["7_idle"]["idle_reached"],
        "pending_A_results": len((pend["A_changes_since_last_seq_push"] or {}).get("results", [])),
        "pending_B_results": len((pend["B_changes_since_last_seq_pull"] or {}).get("results", [])),
        "assertion_failed_lines": len(asserts),
    }
    with open(os.path.join(HERE, "runs", f"{mode}_{n}.json"), "w") as f:
        json.dump(out, f, indent=1, sort_keys=True)
    print(json.dumps(out["facts"], sort_keys=True))


if __name__ == "__main__":
    main()
