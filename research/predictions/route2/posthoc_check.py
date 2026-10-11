"""Post-hoc check of the S2 diagnosis, run after P3 was scored. NOT SCORED.

For each scenario, two CouchDB runs (default settings, one revision per request,
the same delivery as couch_harness.py):
  * novdu: a plain database, compared with couch_model_posthoc (no leaf filter);
  * vdu:   the database has a design document with a validate_doc_update function
           that accepts everything, compared with couch_model.py (leaf filter on).
Also reports on how many orders the two models disagree.

Usage: COUCH=http://admin:pw@127.0.0.1:5984 python3 posthoc_check.py S1 S2 S3
Writes results_posthoc_<S>_<novdu|vdu>.csv.
"""

import itertools
import sys
import time

import compute as C
import couch_harness as H
import couch_model as cm
import couch_model_posthoc as cp


def run(scen, vdu):
    title, hist, dl, sel, k = C.SCENARIOS[scen]
    events = C.events_for(hist, dl, sel)
    orders = list(itertools.permutations(range(len(events))))
    db = "p3_posthoc_%s_%s_%d" % (scen.lower(), "vdu" if vdu else "novdu", int(time.time()))
    st, b = H.req("PUT", "/%s?q=1&n=1" % db)
    assert st in (201, 202), (st, b)
    st, b = H.req("PUT", "/%s/_revs_limit" % db, k)
    assert st == 200, (st, b)
    if vdu:
        st, b = H.req("PUT", "/%s/_design/accept" % db,
                      {"validate_doc_update": "function(newDoc, oldDoc, userCtx) {}"})
        assert st == 201, (st, b)
    for n, order in enumerate(orders):
        for i in order:
            H.deliver(db, "o%06d" % n, events[i][1])
    bad = bad_leaves = models_differ = 0
    with open("results_posthoc_%s_%s.csv" % (scen, "vdu" if vdu else "novdu"), "w") as f:
        f.write("order,predicted_live,observed_live,predicted_winner,observed_winner,"
                "predicted_leaves,observed_leaves,scored_match,leaves_match\n")
        for n, order in enumerate(orders):
            T = Tp = ()
            for i in order:
                T = cm.replicated_update(T, events[i][1], k)
                Tp = cp.replicated_update(Tp, events[i][1], k)
            models_differ += cm.obs_leaves(T) != cm.obs_leaves(Tp)
            M = T if vdu else Tp
            pl, pls = cm.obs_live(M), cm.obs_leaves(M)
            ol, olive, ow = H.observe(db, "o%06d" % n)
            pw = H.predicted_winner(pls)
            ok = (pl == olive) and (pw == ow)
            lok = pls == ol
            bad += not ok
            bad_leaves += not lok
            f.write("%s,%s,%s,%s,%s,%s,%s,%s,%s\n" % (
                " ".join(events[i][0] for i in order), pl, olive,
                H.fmt_winner(pw), H.fmt_winner(ow),
                H.fmt_leaves(pls), H.fmt_leaves(ol), ok, lok))
    print("%s %s (model: %s): %d of %d orders differ on live/deleted or winner; %d on the "
          "leaf set; the two models differ on %d orders"
          % (scen, "vdu" if vdu else "novdu",
             "couch_model" if vdu else "couch_model_posthoc",
             bad, len(orders), bad_leaves, models_differ))


if __name__ == "__main__":
    for s in sys.argv[1:]:
        run(s, False)
        run(s, True)
