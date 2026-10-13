#!/usr/bin/env python3
"""Score P4's claims from runs/<mode>_<n>.json, exactly as P4.md's Pass and fail section states.

Claim 1 (delayed runs): after step 5, A holds x deleted, its rev-tree winner is the 4- tombstone, its _vv cv is
  B's source at tb1's value, and no _vv entry (cv, pv or mv) for B's source is at or above tb2's value.
Claim 2 (delayed runs): after step 7, x is live with {"v": 4} on A and deleted on B, and the replication is idle with
  nothing pending (status running, 60 s without counter change, no changes on either side past the replication's
  last_seq_push / last_seq_pull).
Claim 3 (control runs): x ends live with {"v": 4} on both gateways.
Per claim: pass if >= 4 of 5 runs show it, fail if none does, "reached, not forced" for 1 to 3.
Usage: score.py [prefix]   (default prefix "": scored runs delayed_* and control_*)
"""
import csv
import glob
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
prefix = sys.argv[1] if len(sys.argv) > 1 else ""


def live_v4(status, body):
    return status == 200 and isinstance(body, dict) and body.get("v") == 4 and not body.get("_deleted")


def deleted(status, body):
    return status == 404 and isinstance(body, dict) and body.get("reason") == "deleted"


def claim1(f):
    tb1, tb2 = f["tb1"], f["tb2"]
    return bool(
        f["after5_A_deleted"] is True
        and str(f["after5_A_winner"]).startswith("4-")
        and f["after5_A_cv"] == [tb1["src"], tb1["ver"]]
        and not f["after5_A_has_srcB_ge_tb2"]
    )


def idle(f):
    return f["idle_reached"] and f["repl_status"] == "running" and f["pending_A_results"] == 0 and f["pending_B_results"] == 0


def claim2(f):
    return bool(live_v4(f["final_A_status"], f["final_A_body"]) and deleted(f["final_B_status"], f["final_B_body"]) and idle(f))


def claim3(f):
    return bool(live_v4(f["final_A_status"], f["final_A_body"]) and live_v4(f["final_B_status"], f["final_B_body"]))


def grade(k, n):
    if k >= 4:
        return "PASS"
    if k == 0:
        return "FAIL"
    return "REACHED, NOT FORCED"


rows = []
for mode in ("delayed", "control"):
    for path in sorted(glob.glob(os.path.join(HERE, "runs", f"{prefix}{mode}_*.json"))):
        d = json.load(open(path))
        f = d["facts"]
        rows.append({
            "file": os.path.basename(path), "mode": d["mode"], "run": d["run"], "doc_id": d["doc_id"],
            "t_create": d["steps"]["1_create_on_A"]["t"],
            "after5_A_deleted": f["after5_A_deleted"], "after5_A_winner": f["after5_A_winner"],
            "after5_A_cv_is_tb1": f["after5_A_cv"] == [f["tb1"]["src"], f["tb1"]["ver"]],
            "after5_A_cv_is_tb2": f["after5_A_cv"] == [f["tb2"]["src"], f["tb2"]["ver"]],
            "after5_A_srcB_ge_tb2": f["after5_A_has_srcB_ge_tb2"],
            "final_A": "live " + json.dumps({"v": f["final_A_body"].get("v")}) if f["final_A_status"] == 200 else f"{f['final_A_status']} {f['final_A_body'].get('reason')}",
            "final_B": "live " + json.dumps({"v": f["final_B_body"].get("v")}) if f["final_B_status"] == 200 else f"{f['final_B_status']} {f['final_B_body'].get('reason')}",
            "idle_nothing_pending": idle(f),
            "doc_write_conflict_total": f["doc_write_conflict"],
            "push_conflicts_in_run": (f["sgr_push_conflict_count"] or 0) - (f["sgr_push_conflict_count_before"] or 0),
            "assertion_failed_lines": f["assertion_failed_lines"],
            "claim1": claim1(f) if d["mode"] == "delayed" else "",
            "claim2": claim2(f) if d["mode"] == "delayed" else "",
            "claim3": claim3(f) if d["mode"] == "control" else "",
        })

out = os.path.join(HERE, f"{prefix}results.csv")
with open(out, "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
    w.writeheader()
    w.writerows(rows)

for claim, mode in (("claim1", "delayed"), ("claim2", "delayed"), ("claim3", "control")):
    rs = [r for r in rows if r["mode"] == mode]
    k = sum(1 for r in rs if r[claim] is True)
    print(f"{claim}: {k} of {len(rs)} {mode} runs -> {grade(k, len(rs)) if len(rs) == 5 else '(not 5 runs)'}")
print("wrote", out)
