#!/bin/sh
# Control: the reproduction from apache/couchdb#6162, verbatim except COUCH and a DB reset.
COUCH=${COUCH:-http://admin:p3password@127.0.0.1:5984}
J='Content-Type: application/json'

for db in a c b d t1 t2; do curl -sS -X DELETE "$COUCH/$db" > /dev/null; done
for db in a c b d t1 t2; do curl -sS -X PUT "$COUCH/$db" > /dev/null; done
curl -sS -X PUT "$COUCH/b/_revs_limit" -d 1 > /dev/null
curl -sS -X PUT "$COUCH/d/_revs_limit" -d 2 > /dev/null
curl -sS -X PUT "$COUCH/t2/_design/accept" -H "$J" \
  -d '{"validate_doc_update":"function(newDoc, oldDoc, userCtx, secObj) {}"}' > /dev/null

rep() { curl -sS -X POST "$COUCH/_replicate" -H "$J" \
  -d "{\"source\":\"$COUCH/$1\",\"target\":\"$COUCH/$2\"${3:+,$3}}" > /dev/null; }
ONLY_X='"doc_ids":["X"]'

REV=$(curl -sS -X PUT "$COUCH/a/X" -H "$J" -d '{"v":"a"}' | jq -r .rev)
rep a c "$ONLY_X"
curl -sS -X POST "$COUCH/a/_bulk_docs" -H "$J" -d '{"docs":[
  {"_id":"f1"},{"_id":"f2"},{"_id":"f3"},{"_id":"f4"},{"_id":"f5"},{"_id":"f6"}]}' > /dev/null
REV=$(curl -sS -X PUT "$COUCH/a/X" -H "$J" -d "{\"_rev\":\"$REV\",\"v\":\"b\"}" | jq -r .rev)
rep a b "$ONLY_X"
for t in t1 t2; do rep c $t; rep b $t; done
for t in t1 t2; do rep a $t '"worker_processes":1,"worker_batch_size":1'; done
curl -sS -X DELETE "$COUCH/a/X?rev=$REV" > /dev/null
rep a d "$ONLY_X"
for t in t1 t2; do rep d $t; done

echo "t1:"; curl -sS "$COUCH/t1/X"
echo "t2:"; curl -sS "$COUCH/t2/X"
echo "t1 leaves:"; curl -sS "$COUCH/t1/X?open_revs=all&revs=true" -H 'Accept: application/json' | jq -c '[.[].ok | {_rev, _deleted, revs: ._revisions.ids | length}]'
echo "t2 leaves:"; curl -sS "$COUCH/t2/X?open_revs=all&revs=true" -H 'Accept: application/json' | jq -c '[.[].ok | {_rev, _deleted, revs: ._revisions.ids | length}]'
for db in a c b d t1 t2; do curl -sS -X DELETE "$COUCH/$db" > /dev/null; done
