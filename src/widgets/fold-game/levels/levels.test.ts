// Run: node src/widgets/fold-game/levels/levels.test.ts
// Checks every level file: known lattice, a valid string, best ≤ upper bound, and that the
// stored solution is a complete fold scoring exactly `best` (every level has one).
import assert from 'node:assert/strict';
import { readdirSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { Fold, LATTICES, parseSequence, upperBound } from '../engine/index.ts';

const dir = dirname(fileURLToPath(import.meta.url));
const files = readdirSync(dir).filter((f) => f.endsWith('.json'));
const ids = new Set<string>();
const orders = new Set<number>();

for (const file of files) {
  const l = JSON.parse(readFileSync(join(dir, file), 'utf8'));
  const where = `${file}:`;
  for (const k of ['id', 'order', 'group', 'title', 'lattice', 'sequence', 'best', 'optimal', 'bestKind', 'bestSource', 'intro'])
    assert.ok(l[k] !== undefined, `${where} missing ${k}`);
  assert.equal(`${l.id}.json`, file, `${where} id must match the file name`);
  assert.ok(!ids.has(l.id), `${where} duplicate id`);
  assert.ok(!orders.has(l.order), `${where} duplicate order`);
  ids.add(l.id);
  orders.add(l.order);
  assert.ok(LATTICES[l.lattice], `${where} unknown lattice ${l.lattice}`);
  assert.match(l.sequence, /^[HP]+$/, `${where} sequence must be H/P only`);
  assert.ok(['proved', 'computed', 'cited'].includes(l.bestKind), `${where} bad bestKind`);
  const lat = LATTICES[l.lattice];
  const seq = parseSequence(l.sequence);
  assert.ok(l.best <= upperBound(lat, seq), `${where} best exceeds the upper bound`);
  assert.ok(l.solution !== undefined, `${where} missing solution (the game's "Show solution")`);
  {
    const f = Fold.fromMoves(lat, seq, l.solution);
    assert.ok(f.complete, `${where} solution places only ${f.placed} of ${seq.length} residues`);
    assert.equal(f.score(), l.best, `${where} solution scores ${f.score()}, not ${l.best}`);
  }
}
assert.ok(files.length > 0);
console.log(`levels tests passed (${files.length} levels)`);
