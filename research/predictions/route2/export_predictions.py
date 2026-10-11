"""Write predictions_<S>.json: the scenario's events and, for every exactly-once
order, the CouchDB and PouchDB models' predicted live flag and leaf set.
This file is what P3 would freeze; the harnesses read it.

Usage: python3 export_predictions.py S1 [S2 ...]
"""

import itertools
import json
import sys

import compute as C
import couch_model as cm
import pouch_model as pm


def run(scen):
    title, hist, dl, sel, k = C.SCENARIOS[scen]
    events = C.events_for(hist, dl, sel)
    orders = []
    for order in itertools.permutations(range(len(events))):
        T, Tr, S = (), (), ""
        for i in order:
            T = cm.replicated_update(T, events[i][1], k)
            Tr = cm.replicated_update(Tr, events[i][1], k, False)
            S = pm.replicated_update(S, events[i][1], k)
        Tr = cm.compact(Tr, k)
        orders.append({
            "order": list(order),
            "names": " ".join(events[i][0] for i in order),
            "couch": {"live": cm.obs_live(T), "leaves": [list(x) for x in cm.obs_leaves(T)]},
            "couch_raw_compacted": {"live": cm.obs_live(Tr),
                                    "leaves": [list(x) for x in cm.obs_leaves(Tr)]},
            "pouch": {"live": pm.obs_live(S), "leaves": [list(x) for x in pm.obs_leaves(S)]},
        })
    out = {"scenario": title, "k": k,
           "events": [{"name": n, "doc": [d[0], d[1], d[2]]} for n, d in events],
           "orders": orders}
    with open("predictions_%s.json" % scen, "w") as f:
        json.dump(out, f, indent=0)
    print(scen, len(orders), "orders written")


if __name__ == "__main__":
    for s in sys.argv[1:] or ["S1", "S2", "S3"]:
        run(s)
