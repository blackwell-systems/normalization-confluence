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
const fs = require('fs');

async function observe(db, id) {
  const revs = await db.get(id, {open_revs: 'all'});
  const leaves = revs.filter((r) => r.ok).map((r) => {
    const [p, h] = r.ok._rev.split(/-(.*)/s);
    return [parseInt(p, 10), h, !!r.ok._deleted];
  }).sort((a, b) => (a[0] - b[0]) || (a[1] < b[1] ? -1 : a[1] > b[1] ? 1 : 0));
  let live = true;
  try { await db.get(id); } catch (e) { live = false; }
  return {leaves, live};
}

async function main() {
  const scen = process.argv[2];
  const reps = parseInt(process.argv[3] || '3', 10);
  const dup = process.argv.includes('--dup');
  const P = JSON.parse(fs.readFileSync(`predictions_${scen}.json`, 'utf8'));
  for (let rep = 0; rep < reps; rep++) {
    let bad = 0;
    const rows = ['order,predicted_live,observed_live,predicted_leaves,observed_leaves,match'];
    for (let n = 0; n < P.orders.length; n++) {
      const o = P.orders[n];
      const db = new PouchDB(`p3_${scen}_${rep}_${n}`, {adapter: 'memory', revs_limit: P.k});
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
      const ok = got.live === o.pouch.live &&
        JSON.stringify(got.leaves) === JSON.stringify(o.pouch.leaves);
      if (!ok) bad++;
      rows.push([o.names, o.pouch.live, got.live, JSON.stringify(o.pouch.leaves),
        JSON.stringify(got.leaves), ok].join(','));
      await db.destroy();
    }
    fs.writeFileSync(`results_pouch_${scen}${dup ? '_dup' : ''}_rep${rep}.csv`, rows.join('\n') + '\n');
    console.log(`${scen} rep ${rep}: ${bad} of ${P.orders.length} orders differ from the model`);
  }
}

main().catch((e) => { console.error(e); process.exit(1); });
