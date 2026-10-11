"""Post-hoc correction of couch_model.py, written after the P3 runs. NOT SCORED.

The S2 run against CouchDB 3.5.3 disagreed with couch_model.py on 3009 of 5040
orders (S1 and S3 agreed on every order). The cause: couch_model.replicated_update
always applies the leaf filter of prep_and_validate_replicated_updates ("this doc
isn't a leaf or already exists in the tree": ignored). In couch_db.erl (3.5.3),
before_docs_update calls that function only when the database has
validate_doc_update functions, or a document in the request is a design document
or carries attachments:

    case (VDFuns /= []) orelse lists:any(ValidatePred, Docs2) of
        true -> ... PVFun(Db, DocBuckets, ExistingDocs) ...
        false -> {ok, DocBuckets, LocalDocs, []}

Otherwise the revision path is merged unfiltered. With full histories (S1, S3)
and each revision delivered once, the filter never fires, so the two agree there.
With partial histories (S2), a revision sent first with a short history and later
with a longer one is dropped by the model and merged by CouchDB.

couch_model.py is not changed: it is the model P3 committed to.
"""

import couch_model as cm


def replicated_update(trees, doc, limit, stem_interactive=True, validating=False):
    """One _bulk_docs?new_edits=false request carrying one doc for the id.

    validating: the database has a validate_doc_update function (or the doc is a
    design doc or has attachments), so the leaf filter applies."""
    if validating:
        return cm.replicated_update(trees, doc, limit, stem_interactive)
    pos, ids, deleted = doc
    merged, _ = cm.merge(trees, cm.to_path(pos, ids, deleted))
    if stem_interactive:
        merged = cm.stem(merged, limit)
    return merged
