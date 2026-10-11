// Test harness against real PouchDB. NOT RUN before P3 is committed.
//
// npm install pouchdb@9.0.0 pouchdb-adapter-memory@9.0.0
// The scenario and the model's per-order predictions are read from
// predictions_<S>.json, written by `python3 export_predictions.py S1`.
// Usage: node pouch_harness.js S1 [reps] [--dup]   (--dup: every revision twice in a row)
//
// Every order: a fresh database with revs_limit k, one bulkDocs call per
// revision with new_edits: false, then get(id, {open_revs: 'all'}) and get(id).

const PouchDB = require('pouchdb');
PouchDB.plugin(require('pouchdb-adapter-memory'));
// ADAPTER=leveldb runs on PouchDB's default Node adapter instead of the memory adapter.
const ADAPTER = process.env.ADAPTER || 'memory';

// The winning revision the leaves predict: non-deleted before deleted, then the
// higher position, then the higher revision id (CouchDB and PouchDB both use this rule).
function predictedWinner(leaves, live) {
  if (!live) return '';
  const w = leaves.filter((l) => !l[2]).sort((a, b) =>
    (b[0] - a[0]) || (a[1] < b[1] ? 1 : a[1] > b[1] ? -1 : 0))[0];
  return `${w[0]}-${w[1]}`;
}
const fs = require('fs');

async function observe(db, id) {
  const revs = await db.get(id, {open_revs: 'all'});
  const leaves = revs.filter((r) => r.ok).map((r) => {
    const [p, h] = r.ok._rev.split(/-(.*)/s);
    return [parseInt(p, 10), h, !!r.ok._deleted];
  }).sort((a, b) => (a[0] - b[0]) || (a[1] < b[1] ? -1 : a[1] > b[1] ? 1 : 0));
  let live = true;
  let winner = '';
  try { winner = (await db.get(id))._rev; } catch (e) { live = false; }
  return {leaves, live, winner};
}

async function main() {
  const scen = process.argv[2];
  const reps = parseInt(process.argv[3] || '3', 10);
  const dup = process.argv.includes('--dup');
  const P = JSON.parse(fs.readFileSync(`predictions_${scen}.json`, 'utf8'));
  for (let rep = 0; rep < reps; rep++) {
    let bad = 0;
    let badLeaves = 0;
    const rows = ['order,predicted_live,observed_live,predicted_winner,observed_winner,' +
      'predicted_leaves,observed_leaves,scored_match,leaves_match'];
    for (let n = 0; n < P.orders.length; n++) {
      const o = P.orders[n];
      const db = new PouchDB(`p3_${scen}_${rep}_${n}`, {adapter: ADAPTER, revs_limit: P.k});
      for (const i of o.order) {
        const [pos, ids, deleted] = P.events[i].doc;
        const doc = {_id: 'doc', _rev: `${pos}-${ids[0]}`,
          _revisions: {start: pos, ids}, v: P.events[i].name};
        if (deleted) doc._deleted = true;
        for (let t = 0; t < (dup ? 2 : 1); t++) {
          await db.bulkDocs([doc], {new_edits: false});
        }
      }
      const got = await observe(db, 'doc');
      const pw = predictedWinner(o.pouch.leaves, o.pouch.live);
      // P3 scores live or deleted and the winner; the leaf set is reported.
      const scored = got.live === o.pouch.live && got.winner === pw;
      const lok = JSON.stringify(got.leaves) === JSON.stringify(o.pouch.leaves);
      if (!scored) bad++;
      if (!lok) badLeaves++;
      const short = (ls) => '{' + ls.map((l) => `${l[0]}-${l[1][0]}${l[2] ? '(del)' : ''}`).join(' ') + '}';
      const sw = (w) => (w ? w.slice(0, 3) : '-');
      rows.push([o.names, o.pouch.live, got.live, sw(pw), sw(got.winner), short(o.pouch.leaves),
        short(got.leaves), scored, lok].join(','));
      await db.destroy();
    }
    const tag = ADAPTER === 'memory' ? '' : `_${ADAPTER}`;
    fs.writeFileSync(`results_pouch_${scen}${tag}${dup ? '_dup' : ''}_rep${rep}.csv`, rows.join('\n') + '\n');
    console.log(`${scen}${tag} rep ${rep}: ${bad} of ${P.orders.length} orders differ from the model ` +
      `on live/deleted or winner; ${badLeaves} on the leaf set`);
  }
}

main().catch((e) => { console.error(e); process.exit(1); });
