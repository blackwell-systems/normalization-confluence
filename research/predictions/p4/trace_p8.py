"""Replay the candidate trace and two comparison orders step by step.

python3 trace_p8.py

Topology T1: A runs one push_and_pull replication to B with the default
resolver; B is passive. Writes: on B delete, re-create (b2), delete; on A one
re-create (a4). Same model as search.py (sg_model.py), explicit schedules.
"""

import sg_model as M
from search import PULL_AB, PUSH_AB, fmt_doc

CFG = M.Config("T1", (PULL_AB, PUSH_AB), (0, 0), max_inflight=2)
PROGRAM = (("a4",), ("del", "b2", "del"))


def step(state, want):
    """Take the enabled action whose label matches `want`."""
    if want[0] == "local":
        g = M.GW.index(want[1])
        return M.local_write(state, g, PROGRAM[g][state[4][g]], CFG), f"{want[1]}:{PROGRAM[g][state[4][g]]}"
    for lab, nxt in M.repl_actions(state, CFG):
        if lab[0] == want[0] and lab[1] == want[1] and (len(want) < 3 or lab[2] == want[2]):
            return nxt, lab
    raise RuntimeError(f"not enabled: {want}")


def settle(state):
    """Run replication to quiescence; assert the schedule does not matter."""
    outs = {M.outcome(q) for q in M.quiescent_closure(state, CFG)[0]}
    return outs


def run(name, schedule):
    s = M.initial_state(CFG)
    print(f"--- {name}")
    for want in schedule:
        s, lab = step(s, want)
        print(f"  {str(lab):60s} A={fmt_doc(s[0][0])}   B={fmt_doc(s[0][1])}")
    outs = settle(s)
    print(f"  after full synchronisation (all schedules): {sorted(outs)}")
    print(f"  writes: {[(ev, h[0], h[1], sorted(h[2])) for g in s[6] for ev, h in g]}")
    return outs


L = "local"
X = run("X: newer tombstone applied first (candidate)", [
    (L, "B"), ("send", PULL_AB), (L, "B"), (L, "B"), ("send", PULL_AB),
    ("apply", PULL_AB, 4), ("apply", PULL_AB, 2), (L, "A"),
])
Y = run("Y: same writes, older tombstone applied first, a4 before the newer tombstone lands", [
    (L, "B"), ("send", PULL_AB), (L, "B"), (L, "B"), ("send", PULL_AB),
    ("apply", PULL_AB, 2), (L, "A"), ("apply", PULL_AB, 4),
])
Z = run("Z: in-order delivery, a4 written after both tombstones (different a4 HLV)", [
    (L, "B"), ("send", PULL_AB), (L, "B"), (L, "B"), ("send", PULL_AB),
    ("apply", PULL_AB, 2), ("apply", PULL_AB, 4), (L, "A"),
])
