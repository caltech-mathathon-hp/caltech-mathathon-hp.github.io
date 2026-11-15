// Run: node src/widgets/bin-pack/levels/levels.test.ts
// Checks every level file: the fields, an instance of modified bin packing (even sizes adding
// up to K·B), the answer against the solver, a stored solution that packs every item, and a
// reason for every "no".
import assert from 'node:assert/strict';
import { readdirSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { PackState, instanceError, solve } from '../engine/index.ts';

const dir = dirname(fileURLToPath(import.meta.url));
const files = readdirSync(dir).filter((f) => f.endsWith('.json'));
const ids = new Set<string>();
const orders = new Set<number>();
let no = 0;

for (const file of files) {
  const l = JSON.parse(readFileSync(join(dir, file), 'utf8'));
  const where = `${file}:`;
  for (const k of ['id', 'order', 'title', 'bins', 'capacity', 'items', 'answer', 'intro'])
    assert.ok(l[k] !== undefined, `${where} missing ${k}`);
  assert.equal(`${l.id}.json`, file, `${where} id must match the file name`);
  assert.ok(!ids.has(l.id), `${where} duplicate id`);
  assert.ok(!orders.has(l.order), `${where} duplicate order`);
  ids.add(l.id);
  orders.add(l.order);
  const inst = { bins: l.bins, capacity: l.capacity, sizes: l.items };
  assert.equal(instanceError(inst, true), null, `${where} ${instanceError(inst, true)}`);
  const r = solve(inst);
  assert.ok(r.exhaustive, `${where} the solver did not finish`);
  assert.equal(r.complete ? 'yes' : 'no', l.answer, `${where} the answer is wrong`);
  if (l.answer === 'no') {
    no++;
    assert.ok(l.why, `${where} a "no" level needs "why"`);
    assert.equal(l.solution, undefined, `${where} a "no" level has no solution`);
  }
  if (l.solution) {
    assert.equal(l.solution.length, l.items.length, `${where} solution: one bin per item`);
    assert.ok(PackState.fromAssignment(inst, l.solution).complete, `${where} the solution does not pack every item`);
  }
}
assert.ok(files.length > 0);
assert.ok(no > 0, 'at least one "no" level');
console.log(`bin-pack levels tests passed (${files.length} levels)`);
