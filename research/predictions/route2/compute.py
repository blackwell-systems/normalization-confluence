"""The computed predictions for CouchDB and PouchDB (models only).

For a universe of replicated revisions and a revs_limit k, this prints, for
each implementation model:
  * the exact conditions of the at-least-once theorem (alo_exact): governed
    steps commute after every reachable exactly-once prefix, and each event is
    idempotent where it is first delivered; with the first failing witness;
  * for CouchDB, state descent along N = stem_k at reachable raw states
    (CC2; normalization_descent), with stem_interactive_updates=false as the
    raw run and compaction as N;
  * the distribution of final observations over ALL exactly-once delivery
    orders of the full universe (the quantitative prediction), at three
    levels: live or deleted, winner, leaf set;
  * the orders on which the two implementations disagree.

Usage: python3 compute.py [scenario ...]   (default: all scenarios)
"""

import math
import sys

import couch_model as cm
import pouch_model as pm

R = {c: c * 32 for c in "abcdef"}


def chain(hist, r):
    out = []
    while r is not None:
        out.append(r)
        r = hist[r]
    return out


def events_for(hist, deleted, select):
    evs = []
    for r in sorted(hist):
        ch = chain(hist, r)
        for L in range(1, len(ch) + 1):
            if select(r, len(ch), L):
                evs.append(("%d-%s/%d" % (len(ch), r, L),
                            (len(ch), [R[x] for x in ch[:L]], r in deleted)))
    return evs


class Impl:
    def __init__(self, name, step, init, shape, obs):
        self.name, self.step, self.init, self.shape, self.obs = (
            name, step, init, shape, obs)


def couch_impl(k, interactive=True):
    return Impl("CouchDB" + ("" if interactive else " (stem_interactive_updates=false, then compaction)"),
                lambda T, d: cm.replicated_update(T, d, k, interactive),
                (), cm.shape if hasattr(cm, "shape") else None,
                {"live": cm.obs_live, "winner": cm.winner, "leaves": cm.obs_leaves})


def _couch_shape(T):
    def sn(node):
        k, v, ch = node
        return (k, (v.deleted if not ch else None), tuple(sn(c) for c in ch))
    return tuple((d, sn(nd)) for d, nd in T)


cm.shape = _couch_shape


def pouch_impl(k):
    return Impl("PouchDB", lambda S, d: pm.replicated_update(S, d, k), "",
                pm.shape,
                {"live": pm.obs_live, "winner": pm.winner, "leaves": pm.obs_leaves})


def reach(impl, events):
    """mask -> {state: (count of orders, one witness word)}"""
    n = len(events)
    layers = {0: {impl.init: (1, ())}}
    allm = dict(layers)
    for _ in range(n):
        nxt = {}
        for mask, sts in layers.items():
            for T, (c, w) in sts.items():
                for i in range(n):
                    if mask >> i & 1:
                        continue
                    T2 = impl.step(T, events[i][1])
                    d = nxt.setdefault(mask | 1 << i, {})
                    c0, w0 = d.get(T2, (0, w + (i,)))
                    d[T2] = (c0 + c, w0)
        layers = nxt
        allm.update(nxt)
    return allm


def name(events, w):
    return " ".join(events[i][0] for i in w)


def conditions(impl, events, allm, out):
    n = len(events)
    sh, g = impl.shape, impl.step
    fails = []
    for mask, sts in allm.items():
        for T, (_, w) in sts.items():
            for i in range(n):
                for j in range(i + 1, n):
                    if mask >> i & 1 or mask >> j & 1:
                        continue
                    a = g(g(T, events[i][1]), events[j][1])
                    b = g(g(T, events[j][1]), events[i][1])
                    if sh(a) != sh(b):
                        lv = "live" if impl.obs["live"](a) != impl.obs["live"](b) else (
                            "leaves" if impl.obs["leaves"](a) != impl.obs["leaves"](b) else "shape")
                        fails.append((len(w), lv != "live", w, i, j, lv))
    nonidem = [w for mask, sts in allm.items() for T, (_, w) in sts.items()
               if w and sh(g(T, events[w[-1]][1])) != sh(T)]
    out.append("  commutation after every reachable prefix (CCR): %s"
               % ("holds" if not fails else "FAILS, %d witnesses" % len(fails)))
    if fails:
        fails.sort(key=lambda f: (f[1], f[0], f[2]))
        _, _, w, i, j, lv = fails[0]
        out.append("    smallest observable one: after [%s], %s then %s differs from %s then %s (%s)"
                   % (name(events, w), events[i][0], events[j][0],
                      events[j][0], events[i][0], lv))
    out.append("  idempotence where first delivered: %s"
               % ("holds (no event needs deduplication on its own)" if not nonidem
                  else "FAILS at [%s]" % name(events, min(nonidem, key=len))))


def distribution(impl, events, allm, out):
    full = (1 << len(events)) - 1
    total = math.factorial(len(events))
    for lvl in ("live", "winner", "leaves"):
        f = impl.obs[lvl]
        d = {}
        for T, (c, w) in allm[full].items():
            o = f(T)
            c0, w0 = d.get(o, (0, w))
            d[o] = (c0 + c, w0)
        out.append("  %s: %d outcome(s) over %d orders" % (lvl, len(d), total))
        for o, (c, w) in sorted(d.items(), key=lambda kv: -kv[1][0]):
            out.append("    %6d  %-40s e.g. %s" % (c, fmt(o, lvl), name(events, w)))


def fmt(o, lvl):
    if lvl == "live":
        return {True: "live", False: "deleted", None: "missing"}[o]
    if lvl == "winner":
        return "none" if o is None else "%d-%s%s" % (o[0], o[1][0], " (deleted)" if o[2] else "")
    return "{" + ", ".join("%d-%s%s" % (p, r[0], "(del)" if d else "") for p, r, d in o) + "}"


def cross(events, k, out):
    """Orders on which CouchDB and PouchDB disagree, by level."""
    n = len(events)
    ci, pi = couch_impl(k), pouch_impl(k)
    layer = {0: {(ci.init, pi.init): (1, ())}}
    for _ in range(n):
        nxt = {}
        for mask, sts in layer.items():
            for (T, S), (c, w) in sts.items():
                for i in range(n):
                    if mask >> i & 1:
                        continue
                    key = (ci.step(T, events[i][1]), pi.step(S, events[i][1]))
                    d = nxt.setdefault(mask | 1 << i, {})
                    c0, w0 = d.get(key, (0, w + (i,)))
                    d[key] = (c0 + c, w0)
        layer = nxt
    full = (1 << n) - 1
    for lvl in ("live", "winner", "leaves"):
        bad = [(c, w, T, S) for (T, S), (c, w) in layer[full].items()
               if ci.obs[lvl](T) != pi.obs[lvl](S)]
        tot = sum(b[0] for b in bad)
        out.append("  CouchDB vs PouchDB, %s: disagree on %d of %d orders"
                   % (lvl, tot, math.factorial(n)))
        if bad:
            c, w, T, S = bad[0]
            out.append("    e.g. %s: CouchDB %s, PouchDB %s"
                       % (name(events, w), fmt(ci.obs[lvl](T), lvl), fmt(pi.obs[lvl](S), lvl)))


def run(title, hist, deleted, select, k, out, with_cross=True):
    events = events_for(hist, deleted, select)
    out.append("")
    out.append("## %s; revs_limit %d; %d events: %s"
               % (title, k, len(events), ", ".join(e for e, _ in events)))
    for impl in (couch_impl(k), couch_impl(k, False), pouch_impl(k)):
        allm = reach(impl, events)
        out.append("### " + impl.name)
        conditions(impl, events, allm, out)
        distribution(impl, events, allm, out)
    if with_cross:
        cross(events, k, out)


H1 = {"a": None, "b": "a", "c": "b", "d": "c"}
H2 = {"a": None, "b": "a", "c": "b", "d": "c", "e": "b"}

SCENARIOS = {
    # S1: every revision of a linear history a-b-c-d, d a deletion, each sent
    # with its full history (what a source that never stemmed sends)
    "S1": ("S1: linear a-b-c-d, 4-d deleted, full histories", H1, {"d"},
           lambda r, depth, L: L == depth, 3),
    # S2: the same history; every revision sent with every history length up
    # to the target's revs_limit (sources that stem at the same limit)
    "S2": ("S2: linear a-b-c-d, 4-d deleted, histories of length <= 2", H1, {"d"},
           lambda r, depth, L: L <= 2, 2),
    # S3: a real conflict: b-x beside b-c-d, d deleted, full histories
    "S3": ("S3: a-b-c-d with branch b-e, 4-d deleted, full histories", H2, {"d"},
           lambda r, depth, L: L == depth, 2),
}

if __name__ == "__main__":
    which = sys.argv[1:] or sorted(SCENARIOS)
    out = []
    for s in which:
        title, hist, dl, sel, k = SCENARIOS[s]
        run(title, hist, dl, sel, k, out)
    print("\n".join(out))
