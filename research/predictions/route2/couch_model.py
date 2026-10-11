"""Model of CouchDB's replicated document update: merge a revision path into
the revision tree, then stem the tree to revs_limit.

A transcription, by reading, of
  src/couch/src/couch_key_tree.erl   (merge, merge_tree, merge_at, merge_extend,
                                      stem, stem_tree, check_key, repair_tree,
                                      get_all_leafs_full, value_pref)
  src/couch/src/couch_db.erl          (prep_and_validate_replicated_updates: the
                                      leaf filter for new_edits=false)
  src/couch/src/couch_db_updater.erl  (merge_rev_tree with replicated changes,
                                      maybe_stem_full_doc_info)
  src/couch/src/couch_doc.erl         (to_path, to_doc_info_path: the winner)
of apache/couchdb main as fetched on 2026-10-11. No CouchDB code is run here.

Representation (mirrors the Erlang terms):
  node    = (key, value, children)      children: tuple of nodes
  tree    = (depth, node)
  revtree = tuple of trees, kept sorted as lists:sort would
  value   = MISSING (the atom-free [] of ?REV_MISSING) or Leaf(deleted)
"""

from functools import cmp_to_key

MISSING = None


class Leaf(tuple):
    """A document body at a revision: (deleted,). Stands for #doc / #leaf."""

    def __new__(cls, deleted):
        return tuple.__new__(cls, (bool(deleted),))

    @property
    def deleted(self):
        return self[0]

    def __repr__(self):
        return "Del" if self[0] else "Doc"


class Fail(Exception):
    pass


class Dupe(Exception):
    pass


# ---------------------------------------------------------------- term order
# Erlang term order, restricted to the terms that occur: integers, binaries
# (rev ids), tuples (#leaf / #doc records, nodes, trees), nil ([] = MISSING)
# and lists (children). number < tuple < nil < list < binary.

def _rank(t):
    if isinstance(t, int):
        return 0
    if t is MISSING:
        return 2
    if isinstance(t, Leaf):
        return 1
    if isinstance(t, str):
        return 4
    raise TypeError(t)


def cmp_value(a, b):
    ra, rb = _rank(a), _rank(b)
    if ra != rb:
        return -1 if ra < rb else 1
    if ra == 1:
        return (a > b) - (a < b)
    return 0


def cmp_node(a, b):
    ka, kb = a[0].encode(), b[0].encode()
    if ka != kb:
        return -1 if ka < kb else 1
    c = cmp_value(a[1], b[1])
    if c:
        return c
    return cmp_list(a[2], b[2])


def cmp_list(xs, ys):
    for x, y in zip(xs, ys):
        c = cmp_node(x, y)
        if c:
            return c
    return (len(xs) > len(ys)) - (len(xs) < len(ys))


def cmp_tree(a, b):
    if a[0] != b[0]:
        return -1 if a[0] < b[0] else 1
    return cmp_node(a[1], b[1])


def sort_trees(ts):
    return tuple(sorted(ts, key=cmp_to_key(cmp_tree)))


# ---------------------------------------------------------------- merge

def value_pref(v1, v2):
    if v1 is MISSING:
        return v2
    if v2 is MISSING:
        return v1
    return v1


def merge(revtree, path):
    merged, result = merge_tree(list(revtree), path, [])
    return sort_trees(merged), result


def merge_tree(rt, tree, acc):
    if not rt:
        if not acc:
            return [tree], "new_leaf"
        return [tree] + acc, "new_branch"
    (depth, nodes), rest = rt[0], rt[1:]
    idepth, inodes = tree
    try:
        merged_list, result = merge_at([nodes], depth - idepth, [inodes])
    except Fail:
        return merge_tree(rest, tree, [(depth, nodes)] + acc)
    [merged] = merged_list
    return rest + [(min(depth, idepth), merged)] + acc, result


def merge_at(nodes, pos, inodes):
    if not inodes:
        raise Fail
    if not nodes:
        raise Fail
    if pos > 0:
        assert len(inodes) == 1
        ik, iv, ich = inodes[0]
        if len(ich) == 1:
            merged, result = merge_at(nodes, pos - 1, [ich[0]])
            return [(ik, iv, tuple(merged))], result
        if len(ich) == 0:
            raise Fail
        raise AssertionError("no clause: insert path is not a path")
    if pos < 0:
        k, v, sub = nodes[0]
        sibs = nodes[1:]
        try:
            merged, result = merge_at(list(sub), pos + 1, inodes)
            return [(k, v, tuple(merged))] + sibs, result
        except Fail:
            merged, result = merge_at(sibs, pos, inodes)
            return [(k, v, sub)] + merged, result
    # pos == 0
    assert len(inodes) == 1
    k1, v1, sub = nodes[0]
    k2, v2, isub = inodes[0]
    if k1 == k2:
        merged, result = merge_extend(list(sub), list(isub))
        return [(k1, value_pref(v1, v2), tuple(merged))] + nodes[1:], result
    if k1.encode() > k2.encode():
        raise Fail
    merged, result = merge_at(nodes[1:], 0, inodes)
    return [nodes[0]] + merged, result


def merge_extend(a, b):
    if not a and b:
        return b, "new_leaf"
    if not b:
        return a, "internal_node"
    assert len(b) == 1
    k1, v1, suba = a[0]
    k2, v2, subb = b[0]
    if k1 == k2:
        merged, result = merge_extend(list(suba), list(subb))
        return [(k1, value_pref(v1, v2), tuple(merged))] + a[1:], result
    if k1.encode() > k2.encode():
        return [b[0], a[0]] + a[1:], "new_branch"
    merged, result0 = merge_extend(a[1:], b)
    result = result0 if len(merged) == len(a[1:]) else "new_branch"
    return [a[0]] + merged, result


def multi_merge(revtree, paths):
    for p in sorted(paths, key=cmp_to_key(cmp_tree)):
        revtree, _ = merge(revtree, p)
    return revtree


# ---------------------------------------------------------------- stem

def stem(trees, limit):
    try:
        seen = set()
        branches = []
        for t in trees:
            seen, newb = _stem_top(t, limit, seen)
            branches = newb + branches
        return sort_trees(branches)
    except Dupe:
        return repair_tree(trees, limit)


def _stem_top(tree, limit, seen):
    depth, child = tree
    r = _stem_tree(depth, child, limit, seen)
    if len(r) == 4:
        newseen, _, newchild, newbranches = r
        return newseen, [(depth, newchild)] + newbranches
    newseen, _, newbranches = r
    return newseen, newbranches


def _check_key(key, seen):
    if key in seen:
        raise Dupe
    return seen | {key}


def _stem_tree(depth, node, limit, seen0):
    key, val, children = node
    if not children:
        return _check_key(key, seen0), limit - 1, node, []
    seen = _check_key(key, seen0)
    lpacc, chacc, bracc = -1, [], []
    for child in children:
        r = _stem_tree(depth + 1, child, limit, seen)
        if len(r) == 4:
            seen, lp, newchild, newbr = r
            lpacc = max(lp, lpacc)
            chacc = [newchild] + chacc
            bracc = newbr + bracc
        else:
            seen, lp, newbr = r
            lpacc = max(lp, lpacc)
            bracc = newbr + bracc
    if lpacc > 0 and chacc:
        return seen, lpacc - 1, (key, val, tuple(reversed(chacc))), bracc
    if lpacc == 0 and chacc:
        nb = [(depth + 1, c) for c in reversed(chacc)]
        return seen, -1, nb + bracc
    if lpacc < 0 and not chacc:
        return seen, lpacc - 1, bracc
    raise AssertionError("case_clause in stem_tree")


def get_all_leafs_full(trees):
    acc = []
    for pos, tree in trees:
        acc = _glf(pos, [tree], []) + acc
    return acc


def _glf(pos, nodes, kpa):
    out = []
    for k, v, sub in nodes:
        if not sub:
            out.append((pos, [(k, v)] + kpa))
        else:
            out.extend(_glf(pos + 1, list(sub), [(k, v)] + kpa))
    return out


def _cmp_path_entry(a, b):
    if a[0] != b[0]:
        return -1 if a[0] < b[0] else 1
    for (k1, v1), (k2, v2) in zip(a[1], b[1]):
        if k1 != k2:
            return -1 if k1.encode() < k2.encode() else 1
        c = cmp_value(v1, v2)
        if c:
            return c
    return (len(a[1]) > len(b[1])) - (len(a[1]) < len(b[1]))


def repair_tree(trees, limit):
    paths = []
    for pos, path in get_all_leafs_full(trees):
        sp = path[:limit]
        paths.append((pos + 1 - len(sp), sp))
    paths.sort(key=cmp_to_key(_cmp_path_entry))
    acc = ()
    for start, path in paths:
        node = None
        for k, v in path:
            node = (k, v, () if node is None else (node,))
        acc, _ = merge(acc, (start, node))
    return acc


# ---------------------------------------------------------------- documents

def to_path(pos, ids, deleted):
    """A replicated doc with _rev = pos-ids[0] and _revisions.ids = ids
    (leaf first), as couch_doc:to_path builds it."""
    def build(rs):
        rid = rs[0]
        if len(rs) == 1:
            return (rid, Leaf(deleted), ())
        return (rid, MISSING, (build(rs[1:]),))
    return (pos - len(ids) + 1, build(list(reversed(ids))))


def leaves(trees):
    return [(pos, path[0][0], path[0][1]) for pos, path in get_all_leafs_full(trees)]


def replicated_update(trees, doc, limit, stem_interactive=True):
    """One _bulk_docs?new_edits=false request carrying one doc for the id.

    doc = (pos, ids, deleted). Returns the updated revision tree."""
    pos, ids, deleted = doc
    path = to_path(pos, ids, deleted)
    if trees:
        old_leafs = {(p, k) for p, k, _ in leaves(trees)}
        new_rt = multi_merge(trees, [path])
        new_leafs = {(p, k) for p, k, _ in leaves(new_rt)}
        if (pos, ids[0]) not in new_leafs or (pos, ids[0]) in old_leafs:
            return trees  # "this doc isn't a leaf or already exists": ignored
    merged, _ = merge(trees, path)
    if stem_interactive:
        merged = stem(merged, limit)
    return merged


def compact(trees, limit):
    return stem(trees, limit)


# ---------------------------------------------------------------- observables

def obs_tree(trees):
    """What GET ?open_revs=all&revs=true shows: every leaf with its deletion
    flag and its _revisions (start, ids leaf first)."""
    out = []
    for pos, path in get_all_leafs_full(trees):
        out.append((pos, tuple(k for k, _ in path), path[0][1].deleted))
    return tuple(sorted(out))


def obs_leaves(trees):
    return tuple(sorted((p, k, v.deleted) for p, k, v in leaves(trees)))


def winner(trees):
    ls = leaves(trees)
    if not ls:
        return None
    best = max(ls, key=lambda t: (not t[2].deleted, t[0], t[1].encode()))
    return (best[0], best[1], best[2].deleted)


def obs_live(trees):
    w = winner(trees)
    return None if w is None else (not w[2])


def shape(trees):
    """The tree with internal bodies erased (what compaction keeps): keys,
    structure, and the deletion flag of each leaf."""
    def sn(node):
        k, v, ch = node
        return (k, (v.deleted if not ch else None), tuple(sn(c) for c in ch))
    return tuple((d, sn(nd)) for d, nd in trees)
