"""Model of PouchDB's replicated document update (bulkDocs new_edits=false):
revExists check, then doMerge, then stem to revs_limit.

A transcription, by reading, of pouchdb/pouchdb master as fetched on
2026-10-11:
  packages/node_modules/pouchdb-merge/src/merge.js      (doMerge, mergeTree,
                                                        stem, pathToTree)
  packages/node_modules/pouchdb-merge/src/rootToLeaf.js
  packages/node_modules/pouchdb-merge/src/winningRev.js
  packages/node_modules/pouchdb-merge/src/revExists.js
  packages/node_modules/pouchdb-adapter-utils/src/updateDoc.js
  packages/node_modules/pouchdb-adapter-utils/src/parseDoc.js
No PouchDB code is run here.

The JS mutates nested arrays; the step below deep-copies the stored tree,
runs the transcription on mutable lists (object identity as in JS), and
returns an immutable snapshot, as storing the tree as JSON would.
Node: [id, opts, children]; opts: {"status": ..., "deleted": bool}.
Tree: list of {"pos": int, "ids": node}.
"""

import copy
import json


def _freeze(tree):
    return json.dumps(tree, sort_keys=True)


def _thaw(state):
    return json.loads(state) if state else []


def _compare_tree(a, b):
    return -1 if a[0] < b[0] else 1


def _insert_sorted(arr, item):
    lo, hi = 0, len(arr)
    while lo < hi:
        mid = (lo + hi) >> 1
        if _compare_tree(arr[mid], item) < 0:
            lo = mid + 1
        else:
            hi = mid
    arr.insert(lo, item)


def _path_to_tree(path, num_stemmed):
    root = leaf = None
    for node in path[num_stemmed:]:
        cur = [node["id"], node["opts"], []]
        if leaf is not None:
            leaf[2].append(cur)
            leaf = cur
        else:
            root = leaf = cur
    return root


def _merge_tree(in1, in2):
    queue = [(in1, in2)]
    conflicts = False
    while queue:
        t1, t2 = queue.pop()
        if t1[1].get("status") or t2[1].get("status"):
            t1[1]["status"] = ("available" if t1[1].get("status") == "available"
                               or t2[1].get("status") == "available" else "missing")
        for i in range(len(t2[2])):
            if not t1[2]:
                conflicts = "new_leaf"
                t1[2].append(t2[2][i])  # tree1[2][0] = tree2[2][i]
                continue
            merged = False
            for j in range(len(t1[2])):
                if t1[2][j][0] == t2[2][i][0]:
                    queue.append((t1[2][j], t2[2][i]))
                    merged = True
            if not merged:
                conflicts = "new_branch"
                _insert_sorted(t1[2], t2[2][i])
    return conflicts, in1


def _do_merge(tree, path, dont_expand=False):
    restree = []
    conflicts = False
    merged = False
    if not tree:
        return [path], "new_leaf"
    for branch in tree:
        if branch["pos"] == path["pos"] and branch["ids"][0] == path["ids"][0]:
            c, t = _merge_tree(branch["ids"], path["ids"])
            restree.append({"pos": branch["pos"], "ids": t})
            conflicts = conflicts or c
            merged = True
        elif dont_expand is not True:
            t1 = branch if branch["pos"] < path["pos"] else path
            t2 = path if branch["pos"] < path["pos"] else branch
            diff = t2["pos"] - t1["pos"]
            cands = []
            stack = [{"ids": t1["ids"], "diff": diff, "parent": None, "idx": None}]
            while stack:
                item = stack.pop()
                if item["diff"] == 0:
                    if item["ids"][0] == t2["ids"][0]:
                        cands.append(item)
                    continue
                for j, el in enumerate(item["ids"][2]):
                    stack.append({"ids": el, "diff": item["diff"] - 1,
                                  "parent": item["ids"], "idx": j})
            if not cands:
                restree.append(branch)
            else:
                el = cands[0]
                c, t = _merge_tree(el["ids"], t2["ids"])
                el["parent"][2][el["idx"]] = t
                restree.append({"pos": t1["pos"], "ids": t1["ids"]})
                conflicts = conflicts or c
                merged = True
        else:
            restree.append(branch)
    if not merged:
        restree.append(path)
    restree.sort(key=lambda b: b["pos"])  # stable, as Array.prototype.sort
    return restree, conflicts or "internal_node"


def _root_to_leaf(revs):
    paths = []
    to_visit = list(revs)
    while to_visit:
        node = to_visit.pop()
        pos, tree = node["pos"], node["ids"]
        history = list(node.get("history", []))
        history.append({"id": tree[0], "opts": tree[1]})
        if not tree[2]:
            paths.append({"pos": pos + 1 - len(history), "ids": history})
        for br in tree[2]:
            to_visit.append({"pos": pos + 1, "ids": br, "history": history})
    paths.reverse()
    return paths


def _stem(tree, depth):
    result = None
    for path in _root_to_leaf(tree):
        st = path["ids"]
        if len(st) > depth:
            ns = len(st) - depth
            node = {"pos": path["pos"] + ns, "ids": _path_to_tree(st, ns)}
        else:
            node = {"pos": path["pos"], "ids": _path_to_tree(st, 0)}
        if result is not None:
            result, _ = _do_merge(result, node, True)
        else:
            result = [node]
    return result if result is not None else []


def _rev_exists(revs, pos, rid):
    to_visit = list(revs)
    while to_visit:
        node = to_visit.pop()
        if node["pos"] == pos and node["ids"][0] == rid:
            return True
        for br in node["ids"][2]:
            to_visit.append({"pos": node["pos"] + 1, "ids": br})
    return False


def to_path(pos, ids, deleted):
    opts = {"status": "available"}
    if deleted:
        opts["deleted"] = True
    node = [ids[0], opts, []]
    for rid in ids[1:]:
        node = [rid, {"status": "missing"}, [node]]
    return {"pos": pos - len(ids) + 1, "ids": node}


def replicated_update(state, doc, limit):
    """state: frozen tree (or "" for no document). doc = (pos, ids, deleted)."""
    pos, ids, deleted = doc
    tree = copy.deepcopy(_thaw(state))
    if _rev_exists(tree, pos, ids[0]):
        return state
    merged, _ = _do_merge(tree, to_path(pos, ids, deleted))
    return _freeze(_stem(merged, limit))


def leaves(state):
    out = []
    to_visit = list(_thaw(state))
    while to_visit:
        node = to_visit.pop()
        t = node["ids"]
        if not t[2]:
            out.append((node["pos"], t[0], bool(t[1].get("deleted"))))
        for br in t[2]:
            to_visit.append({"pos": node["pos"] + 1, "ids": br})
    return out


def obs_leaves(state):
    return tuple(sorted(leaves(state)))


def winner(state):
    tree = _thaw(state)
    wid = wpos = wdel = None
    to_visit = list(tree)
    while to_visit:
        node = to_visit.pop()
        t, pos = node["ids"], node["pos"]
        if t[2]:
            for br in t[2]:
                to_visit.append({"pos": pos + 1, "ids": br})
            continue
        d = bool(t[1].get("deleted"))
        if (wid is None or ((wdel if wdel != d else
                             (wpos < pos if wpos != pos else wid < t[0])))):
            wid, wpos, wdel = t[0], pos, d
    return None if wid is None else (wpos, wid, wdel)


def obs_live(state):
    w = winner(state)
    return None if w is None else (not w[2])


def shape(state):
    """Keys, structure and leaf deletion flags, trees in stored order."""
    def sn(t):
        return (t[0], bool(t[1].get("deleted")) if not t[2] else None,
                tuple(sn(c) for c in t[2]))
    return tuple((b["pos"], sn(b["ids"])) for b in _thaw(state))
