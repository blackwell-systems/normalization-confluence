"""Exhaustive search over interleavings for the Sync Gateway ISGR model.

python3 search.py            all scenarios, summary
python3 search.py --traces   also print example traces for every finding

Checks, at every reachable state (two gateways, one document):
  conv   after full bidirectional synchronisation (no replication step
         enabled, all local events done) the two gateways hold the same
         canonical state (live body or deleted), and the same CV
  group  terminal states produced by the SAME local writes (identical HLV for
         every write, so identical causal history) have one canonical outcome:
         delivery order alone does not change the result
  (a)    state descent: canon N(e(N(s))) == canon N(e(s)), N = run
         replication to quiescence over all schedules
  (b)    CC1: canon N(e1(N(e2(N(s))))) == canon N(e2(N(e1(N(s)))))
  (c)    termination: replication alone reaches quiescence from every state
  lww    every conflict resolution picks the version with the higher
         timestamp (the documented rule); exceptions are counted by cause
"""

import sys
from collections import deque, defaultdict

import sg_model as M

PULL_AB = (1, 0, True)    # A pulls from B, A resolves
PUSH_AB = (0, 1, False)   # A pushes to B, B rejects conflicts (409)
PULL_BA = (0, 1, True)    # B pulls from A, B resolves
PUSH_BA = (1, 0, False)   # B pushes to A, A rejects conflicts

TOPOLOGIES = {
    "T1 A push_and_pull (default resolver), B passive": (PULL_AB, PUSH_AB),
    "T2 A pull + B pull (both resolve)": (PULL_AB, PULL_BA),
    "T3 A push_and_pull + B push_and_pull": (PULL_AB, PUSH_AB, PULL_BA, PUSH_BA),
    "T4 A push only (no resolution anywhere)": (PUSH_AB,),
}

SKEWS = {
    "no skew": (0, 0),
    "A clock 25 behind": (-25, 0),
    "B clock 25 behind": (0, -25),
    "equal values possible": (0, -10),
}

PROGRAMS = {
    "P1 a1 | b1": (("a1",), ("b1",)),
    "P2 a1 | del": (("a1",), ("del",)),
    "P3 del | del": (("del",), ("del",)),
    "P4 a1,a2 | b1,del": (("a1", "a2"), ("b1", "del")),
    "P5 a1,del | b1": (("a1", "del"), ("b1",)),
    # "del" on a tombstone = PUT {"_deleted": true} with the tombstone's rev
    # (allowed by Put: matchRev is the current leaf, IsIllegalConflict case a)
    "P6 a2 | del,del": (("a2",), ("del", "del")),
    "P7 del,del | b2": (("del", "del"), ("b2",)),
    # delete, re-create, delete again on B (no tombstone update needed)
    "P8 a4 | del,b2,del": (("a4",), ("del", "b2", "del")),
}


def explore(cfg, program):
    s0 = M.initial_state(cfg)
    seen = {s0}
    dq = deque([s0])
    edges = {}
    while dq:
        s = dq.popleft()
        succ = list(M.local_actions(s, program, cfg)) + list(M.repl_actions(s, cfg))
        edges[s] = succ
        for _, n in succ:
            if n not in seen:
                seen.add(n)
                dq.append(n)
    return s0, edges


def done(s, program):
    return s[4] == (len(program[0]), len(program[1]))


class NCache:
    def __init__(self, cfg):
        self.cfg = cfg
        self.cache = {}
        self.nonterm = 0

    def N(self, s):
        """Quiescent states reachable by replication alone. Memoised DFS; a
        state met again while still on the DFS stack is a replication cycle
        (counted as nontermination)."""
        if s in self.cache:
            return self.cache[s]
        onstack = set()
        stack = [(s, None)]
        while stack:
            cur, it = stack[-1]
            if it is None:
                if cur in self.cache:
                    stack.pop()
                    continue
                onstack.add(cur)
                succ = [n for _, n in M.repl_actions(cur, self.cfg)]
                stack[-1] = (cur, iter(succ))
                if not succ:
                    self.cache[cur] = frozenset([cur])
                    onstack.discard(cur)
                    stack.pop()
                continue
            nxt = next(it, None)
            if nxt is None:
                acc = set()
                for _, n in M.repl_actions(cur, self.cfg):
                    acc |= self.cache.get(n, frozenset())
                self.cache[cur] = frozenset(acc)
                onstack.discard(cur)
                stack.pop()
            elif nxt in onstack:
                self.nonterm += 1
            elif nxt not in self.cache:
                stack.append((nxt, None))
        return self.cache[s]


def canon_set(states):
    return frozenset(M.outcome(s) for s in states)


def apply_local(s, g, program, cfg):
    pc = s[4][g]
    if pc >= len(program[g]):
        return None
    ev = program[g][pc]
    return M.local_write(s, g, ev, cfg)


def path_to(s0, edges, target):
    prev = {s0: None}
    dq = deque([s0])
    while dq:
        s = dq.popleft()
        if s == target:
            break
        for lab, n in edges.get(s, ()):
            if n not in prev:
                prev[n] = (s, lab)
                dq.append(n)
    out = []
    cur = target
    while prev.get(cur):
        p, lab = prev[cur]
        out.append(lab)
        cur = p
    return list(reversed(out))


def fmt_label(lab):
    if lab[0] == "local":
        return f"{lab[1]}:{lab[2]}"
    names = {PULL_AB: "pull B->A", PUSH_AB: "push A->B", PULL_BA: "pull A->B", PUSH_BA: "push B->A"}
    d = names.get(lab[1], str(lab[1]))
    if lab[0] == "skip":
        return f"{d}:skip(known)"
    if lab[0] == "send":
        return f"{d}:send"
    return f"{d}:apply#{lab[2]}={lab[3]}"


def fmt_doc(d):
    if d is None:
        return "absent"
    h, body, dele = d
    pv = ",".join(f"{s}:{v}" for s, v in sorted(h[2]))
    return f"{'DEL' if dele else body} cv={h[0]}:{h[1]} pv=[{pv}]"


def run(cfg, program, traces=False):
    s0, edges = explore(cfg, program)
    nc = NCache(cfg)
    res = defaultdict(int)
    examples = {}
    terminals = [s for s, succ in edges.items() if not succ]
    res["states"] = len(edges)
    res["terminals"] = len(terminals)
    by_writes = defaultdict(set)
    for t in terminals:
        a, b = t[0]
        if M.canon(a) != M.canon(b):
            res["conv_fail_canon"] += 1
            examples.setdefault("conv_fail_canon", t)
        elif M.cv(a[0]) != M.cv(b[0]):
            res["conv_fail_cv_only"] += 1
            examples.setdefault("conv_fail_cv_only", t)
        by_writes[t[6]].add(M.outcome(t))
    res["outcomes"] = len({M.outcome(t) for t in terminals})
    for w, outs in by_writes.items():
        if len(outs) > 1:
            res["group_fail"] += 1
            examples.setdefault("group_fail", (w, outs))
    # (c) termination of replication from every reachable state
    for s in edges:
        nc.N(s)
    res["nonterminating"] = nc.nonterm
    # (a) and (b)
    for s in edges:
        Ns = nc.N(s)
        for g in range(2):
            es = apply_local(s, g, program, cfg)
            if es is None:
                continue
            lhs = set()
            for q in Ns:
                lhs |= set(nc.N(apply_local(q, g, program, cfg)))
            rhs = nc.N(es)
            if canon_set(lhs) != canon_set(rhs):
                res["a_fail"] += 1
                examples.setdefault("a_fail", (s, g, canon_set(lhs), canon_set(rhs)))
        e0 = apply_local(s, 0, program, cfg)
        e1 = apply_local(s, 1, program, cfg)
        if e0 is not None and e1 is not None:
            def seq(first, second):
                out = set()
                for q in Ns:
                    for r in nc.N(apply_local(q, first, program, cfg)):
                        out |= set(nc.N(apply_local(r, second, program, cfg)))
                return canon_set(out)
            l, r = seq(0, 1), seq(1, 0)
            if l != r:
                res["b_fail"] += 1
                examples.setdefault("b_fail", (s, l, r))
    # lww: resolutions taken anywhere in the reachable graph
    for s in edges:
        sink = []
        list(M.repl_actions(s, cfg, log_sink=sink))
        for w, loc, rem in sink:
            win, lose = (loc, rem) if w == "local" else (rem, loc)
            if win[0][1] < lose[0][1]:
                res["lww_lower_ts_won_tombstone" if win[2] and not lose[2] else "lww_lower_ts_won_other"] += 1
            elif win[0][1] == lose[0][1]:
                res["lww_tie_local"] += 1
    return res, examples, (s0, edges)


def main():
    traces = "--traces" in sys.argv
    if "--counterfactual" in sys.argv:
        M.RECHECK_TOMBSTONE_PATH = True
    forced_inflight = None
    for a in sys.argv:
        if a.startswith("--inflight="):
            forced_inflight = int(a.split("=")[1])
    def opt(name):
        for a in sys.argv:
            if a.startswith(f"--{name}="):
                return a.split("=", 1)[1].split(",")
        return None
    # --topo=T1,T2  --skew=none,A,B,tie  --prog=P6,P8   (prefix match, ANDed)
    topo_f, skew_f, prog_f = opt("topo"), opt("skew"), opt("prog")
    skew_key = {"none": "no skew", "A": "A clock", "B": "B clock", "tie": "equal values"}
    for tname, dirs in TOPOLOGIES.items():
        for kname, skew in SKEWS.items():
            for pname, prog in PROGRAMS.items():
                if topo_f and not any(tname.startswith(t + " ") for t in topo_f):
                    continue
                if skew_f and not any(kname.startswith(skew_key[k]) for k in skew_f):
                    continue
                if prog_f and not any(pname.startswith(p + " ") for p in prog_f):
                    continue
                inflight = forced_inflight or (2 if len(dirs) <= 2 else 1)
                cfg = M.Config(tname, dirs, skew, max_inflight=inflight)
                res, ex, (s0, edges) = run(cfg, prog, traces)
                keys = ["states", "terminals", "outcomes", "conv_fail_canon", "conv_fail_cv_only",
                        "group_fail", "a_fail", "b_fail", "nonterminating",
                        "lww_lower_ts_won_tombstone", "lww_lower_ts_won_other", "lww_tie_local"]
                print(f"[{tname} | {kname} | {pname} | inflight<={inflight}]")
                print("   " + " ".join(f"{k}={res.get(k, 0)}" for k in keys))
                if traces:
                    for k in ("conv_fail_canon", "conv_fail_cv_only"):
                        if k in ex:
                            t = ex[k]
                            print(f"   {k} trace: " + " ; ".join(fmt_label(l) for l in path_to(s0, edges, t)))
                            print(f"      A = {fmt_doc(t[0][0])}")
                            print(f"      B = {fmt_doc(t[0][1])}")
                    if "group_fail" in ex:
                        w, outs = ex["group_fail"]
                        print(f"   group_fail writes={w} outcomes={sorted(outs)}")
                    if "a_fail" in ex:
                        s, g, l, r = ex["a_fail"]
                        print(f"   a_fail at {fmt_doc(s[0][0])} / {fmt_doc(s[0][1])} event@{M.GW[g]}: "
                              f"N(e(N(s)))={sorted(l)} N(e(s))={sorted(r)}")
                    if "b_fail" in ex:
                        s, l, r = ex["b_fail"]
                        print(f"   b_fail at {fmt_doc(s[0][0])} / {fmt_doc(s[0][1])}: A-then-B={sorted(l)} B-then-A={sorted(r)}")


if __name__ == "__main__":
    main()
