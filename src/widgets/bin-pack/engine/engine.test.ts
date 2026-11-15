// Run: node src/widgets/bin-pack/engine/engine.test.ts   (Node ≥ 23 runs TypeScript directly)
import assert from 'node:assert/strict';
import { PackState, instanceError, sumText, type Instance } from './pack.ts';
import { solve, extendable } from './solve.ts';
import { PackController } from './controller.ts';

const running: Instance = { bins: 2, capacity: 10, sizes: [6, 2, 8, 4] };
const sixes: Instance = { bins: 2, capacity: 10, sizes: [6, 6, 6, 2] };

// instances: the sizes must add up to K·B; even sizes on request
assert.equal(instanceError(running, true), null);
assert.equal(instanceError(sixes, true), null);
assert.match(instanceError({ bins: 2, capacity: 10, sizes: [6, 2, 8] }) ?? '', /add up to 16/);
assert.match(instanceError({ bins: 2, capacity: 10, sizes: [12, 8] }) ?? '', /larger than a bin/);
assert.equal(instanceError({ bins: 2, capacity: 9, sizes: [5, 4, 9] }), null);
assert.match(instanceError({ bins: 2, capacity: 9, sizes: [5, 4, 9] }, true) ?? '', /even/);

// placing, overflow, moving between bins, taking out
let s = new PackState(running);
assert.ok(s.place(0, 0)); // 6 in bin 0
assert.ok(!s.place(2, 0), '8 does not fit next to 6');
assert.ok(s.place(3, 0)); // 4 in bin 0: full
assert.equal(s.free(0), 0);
assert.equal(s.fullBins(), 1);
assert.equal(s.offset(0, 3), 6, 'the 4 starts after the 6');
assert.equal(s.offset(1, 2), 0, 'an item would start bin 1 at 0');
assert.ok(!s.place(3, 0), 'already there');
assert.ok(s.place(3, 1), 'move the 4 to bin 1');
assert.deepEqual(s.contents, [[0], [3]]);
assert.ok(s.fits(0, 0), 'an item fits where it already is');
assert.ok(s.remove(3));
assert.ok(!s.remove(3), 'not in a bin');
assert.deepEqual(s.loose(), [1, 2, 3]);
assert.equal(s.packed(), 6);
assert.ok(!s.complete && !s.stuck);

// complete and stuck
s = PackState.fromAssignment(running, [0, 1, 1, 0]);
assert.ok(s.complete && !s.stuck);
assert.equal(s.packed(), 20);
assert.equal(sumText(running, s.contents[1]), '2 + 8');
s = PackState.fromAssignment(sixes, [0, 1, null, null]);
assert.ok(!s.stuck, 'the 2 still fits');
s.place(3, 0);
assert.ok(s.stuck, 'the third 6 fits nowhere');
assert.throws(() => PackState.fromAssignment(running, [0, 0, 0, 0]));

// the solver: yes, no, and the best partial packing of a no instance
let r = solve(running);
assert.ok(r.complete && r.exhaustive);
assert.ok(PackState.fromAssignment(running, r.assignment).complete);
r = solve(sixes);
assert.ok(!r.complete && r.exhaustive, 'three sixes: no packing');
assert.equal(r.packed, 14, 'the best one can do is 6 + 2 and 6');
assert.equal(r.assignment.filter((b) => b === null).length, 1);
r = solve({ bins: 2, capacity: 10, sizes: [4, 4, 4, 4, 4] });
assert.ok(!r.complete && r.exhaustive && r.packed === 16, 'no subset of 4’s adds up to 10');

// starting from a partial packing: 6 + 4 in one bin of 12 is a dead end
const dead: Instance = { bins: 2, capacity: 12, sizes: [6, 4, 8, 6] };
assert.equal(extendable(dead, [0, 0, null, null]), false);
assert.equal(extendable(dead, [1, 0, 0, null]), true);
assert.equal(extendable(dead, [null, null, null, null]), true);

// against brute force on random small instances
let seed = 7;
const rand = (k: number) => {
  seed = (seed * 1103515245 + 12345) % 2147483648;
  return seed % k;
};
for (let t = 0; t < 300; t++) {
  const K = 1 + rand(3);
  const B = 2 * (2 + rand(5));
  const sizes: number[] = [];
  let left = K * B;
  while (left > 0) {
    const x = Math.min(left, 2 * (1 + rand(B / 2)));
    sizes.push(x);
    left -= x;
  }
  if (sizes.length > 8) continue;
  const inst = { bins: K, capacity: B, sizes };
  // brute force: every assignment of items to bins or "out"
  let bestPacked = 0;
  const a = new Array(sizes.length).fill(0);
  const total = Math.pow(K + 1, sizes.length);
  for (let code = 0; code < total; code++) {
    let c = code;
    const load = new Array(K).fill(0);
    let packed = 0;
    let ok = true;
    for (let u = 0; u < sizes.length; u++) {
      a[u] = c % (K + 1);
      c = Math.floor(c / (K + 1));
      if (a[u] < K) {
        load[a[u]] += sizes[u];
        packed += sizes[u];
        if (load[a[u]] > B) ok = false;
      }
    }
    if (ok && packed > bestPacked) bestPacked = packed;
  }
  const res = solve(inst);
  assert.ok(res.exhaustive);
  assert.equal(res.packed, bestPacked, `K=${K} B=${B} sizes=${sizes}`);
  const st = new PackState(inst);
  res.assignment.forEach((b, u) => b !== null && assert.ok(st.place(u, b)));
  assert.equal(st.packed(), res.packed);
}

// a node budget stops the search
r = solve({ bins: 6, capacity: 30, sizes: [14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 12] }, { maxNodes: 50 });
assert.equal(r.exhaustive, false);

// the controller: undo, reset, selection, notifications
const c = new PackController(running);
let calls = 0;
c.subscribe(() => calls++);
c.select(2);
assert.equal(c.selected, 2);
assert.ok(c.place(2, 1));
assert.equal(c.selected, null, 'placing drops the selection');
assert.ok(!c.place(0, 1), '6 does not fit next to 8');
assert.ok(c.place(1, 1));
assert.ok(c.place(0, 0));
assert.ok(c.place(1, 0), 'move the 2 next to the 6');
assert.deepEqual(c.state.contents, [[0, 1], [2]]);
assert.ok(c.undo());
assert.deepEqual(c.state.contents, [[0], [2, 1]]);
assert.ok(c.remove(1));
assert.ok(!c.remove(1));
assert.ok(c.reset());
assert.equal(c.state.packed(), 0);
assert.ok(!c.reset(), 'nothing to reset');
assert.ok(c.undo(), 'reset is one undo step');
assert.deepEqual(c.state.contents, [[0], [2]]);
const saved = c.snapshot();
c.load([[0, 3], [1, 2]]);
assert.ok(c.state.complete);
c.load(saved);
assert.deepEqual(c.state.contents, [[0], [2]]);
c.setInstance(sixes);
assert.ok(!c.canUndo && c.state.packed() === 0);
assert.ok(calls >= 12);

console.log('bin-pack engine tests passed');
