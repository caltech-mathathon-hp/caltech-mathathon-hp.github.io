// Run: node src/widgets/fold-game/engine/engine.test.ts   (Node ≥ 23 runs TypeScript directly)
import assert from 'node:assert/strict';
import { Fold, upperBound, shapeBound, maxPairs, parseSequence, encodeMoves, decodeMoves, chainBonds, type Residue } from './fold.ts';
import { square, cubic, triangular, fcc, hexagonal, diamond, LATTICES, type Lattice, stepsAt, stepNamesAt, neighbours, key, girthOf } from './lattice.ts';
import { GameController } from './controller.ts';
import { Solver, solve } from './solve.ts';
import { absoluteStep, stepGlyph } from '../keys.ts';

const dist = (l: Lattice, u: readonly number[], v: readonly number[]) => {
  const a = l.embed(u);
  const b = l.embed(v);
  return Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]);
};

/** the lattice points within `r` steps of the origin (BFS) */
function ball(l: Lattice, r: number): number[][] {
  const o = l.steps[0].map(() => 0);
  const seen = new Map([[key(o), o]]);
  let front = [o];
  for (let d = 0; d < r; d++) {
    const next: number[][] = [];
    for (const v of front)
      for (const w of neighbours(l, v))
        if (!seen.has(key(w))) {
          seen.set(key(w), w);
          next.push(w);
        }
    front = next;
  }
  return [...seen.values()];
}

// every lattice: the same number of steps at every point, each step unit length in the drawing,
// and adjacency symmetric (the step back is a step of the point reached)
for (const l of Object.values(LATTICES)) {
  const pts = ball(l, 4);
  for (const v of pts) {
    const steps = stepsAt(l, v);
    assert.equal(steps.length, l.steps.length, `${l.id}: degree at ${v}`);
    assert.equal(stepNamesAt(l, v).length, steps.length);
    for (const s of steps) {
      const w = v.map((x, i) => x + s[i]);
      assert.ok(Math.abs(dist(l, v, w) - 1) < 1e-9, `${l.id}: step ${s} at ${v} not unit`);
      assert.ok(stepsAt(l, w).some((t) => t.every((c, i) => c === -s[i])), `${l.id}: no way back from ${w} to ${v}`);
    }
  }
  // the drawing: points at distance 1 are neighbours, and no two points coincide
  const nb = new Set(pts.flatMap((v) => neighbours(l, v).map((w) => `${key(v)}|${key(w)}`)));
  for (const u of pts)
    for (const v of pts) {
      if (u === v) continue;
      const d = dist(l, u, v);
      assert.ok(d > 0.99, `${l.id}: ${u} and ${v} drawn ${d} apart`);
      if (d < 1.01) assert.ok(nb.has(`${key(u)}|${key(v)}`), `${l.id}: ${u} and ${v} drawn as neighbours`);
    }
  assert.equal(l.steps.length, l.stepNames.length);
}
assert.equal(fcc.steps.length, 12);
assert.equal(hexagonal.steps.length, 3);
assert.equal(diamond.steps.length, 4);
// two kinds of points: every step changes the kind (so residue i sits on kind i mod 2)
for (const l of [hexagonal, diamond]) {
  const o = l.steps[0].map(() => 0);
  for (const v of ball(l, 4))
    for (const w of neighbours(l, v)) assert.notEqual(stepsAt(l, v), stepsAt(l, w), `${l.id}: ${v} and ${w} of one kind`);
  assert.equal(stepsAt(l, o), l.steps);
  assert.ok(l.bipartite);
  assert.equal(girthOf(l), 6);
}

// a 2x2 square of HHHH: one contact (0,3)
let f = Fold.fromMoves(square, 'HHHH', 'RUL');
assert.equal(f.score(), 1);
assert.deepEqual(f.contacts(), [{ i: 0, j: 3 }]);
assert.equal(f.moves(), 'RUL');
assert.equal(chainBonds(parseSequence('HHHH')), 3);

// self-avoidance and adjacency
f = new Fold(square, 'HPPH');
assert.ok(f.extendStep(0));
assert.ok(!f.extendTo([0, 0]), 'occupied');
assert.ok(!f.extendTo([3, 0]), 'not adjacent');
assert.equal(f.options().length, 3);

// stuck: spiral into a dead end
f = Fold.fromMoves(square, 'H'.repeat(10), 'RULLDDRRR'.slice(0, 7));
assert.equal(f.placed, 8);

// cube 2x2x2 of 8 H's: max contacts = 12 edges of cube - 7 chain = 5
const cubeMoves = 'RULFRDL'; // a Hamiltonian path of the 2x2x2 cube
f = Fold.fromMoves(cubic, 'HHHHHHHH', cubeMoves);
assert.equal(f.placed, 8);
assert.equal(f.score(), 5);
assert.ok(upperBound(cubic, parseSequence('HHHHHHHH')) >= 5);

// cube bound: the most neighbouring pairs among k nodes, minus the pairs joined by the chain
assert.deepEqual([1, 2, 3, 4, 8, 27].map((k) => maxPairs(cubic, k)), [0, 1, 2, 4, 12, 54]);
assert.deepEqual([1, 2, 3, 4, 6, 9].map((k) => maxPairs(square, k)), [0, 1, 2, 4, 7, 12]);
assert.equal(maxPairs(triangular, 4), null);
assert.equal(shapeBound(cubic, parseSequence('HHHHHHHH')), 5); // 12 − 7, met by the 2×2×2 cube
assert.equal(shapeBound(cubic, parseSequence('PHHPPHHPPHHPPHHP')), 8); // 12 − 4
assert.equal(upperBound(cubic, parseSequence('PHHPPHHPPHHPPHHP')), 16); // the parity bound
assert.equal(shapeBound(cubic, parseSequence('H'.repeat(27))), 28); // 54 − 26
assert.equal(shapeBound(square, parseSequence('HHHH')), 1); // 4 − 3

// parity bound on the square lattice: HPHPH… vs HH…
assert.equal(upperBound(square, parseSequence('HPH')), 0); // both H even class
assert.equal(upperBound(square, parseSequence('HH')), 3); // ends: z-1 each, min(3,3)

// triangular lattice: E, NW, W makes a trapezoid of three triangles: contacts (0,2) and (0,3)
f = Fold.fromMoves(triangular, 'HHHH', '0' + '4' + '1'); // E, NW, W
assert.equal(f.score(), 2);
assert.equal(encodeMoves(triangular, f.path), '041');

// hexagonal: a hexagon closes after six residues; R L U at one kind of node, R L D at the other
f = Fold.fromMoves(hexagonal, 'HPPPPH', 'RDLLU');
assert.equal(f.placed, 6);
assert.equal(f.score(), 1);
assert.equal(f.moves(), 'RDLLU');
assert.deepEqual(decodeMoves(hexagonal, 'RDLLU'), [0, 2, 1, 1, 2]);
assert.deepEqual(decodeMoves(hexagonal, 'RU'), [0, -1], 'no U at a node of the second kind');
assert.equal(Fold.fromMoves(hexagonal, 'HPPPPH', 'RUL').placed, 2);
assert.equal(upperBound(hexagonal, parseSequence('HPPPPH')), 2); // ends: z − 1 = 2 each
assert.equal(upperBound(hexagonal, parseSequence('HPPPPHPPPPH')), 1); // the middle H has one free side
// keys on the hexagonal lattice depend on the node
assert.equal(absoluteStep(hexagonal, 'ArrowUp', [0, 0]), 2);
assert.equal(absoluteStep(hexagonal, 'ArrowUp', [1, 0]), null);
assert.equal(absoluteStep(hexagonal, 'ArrowDown', [1, 0]), 2);
assert.equal(absoluteStep(hexagonal, 'ArrowLeft', [1, 0]), 1);
assert.equal(stepGlyph(hexagonal, 2, [0, 0]), '↑');
assert.equal(stepGlyph(hexagonal, 2, [1, 0]), '↓');
assert.equal(absoluteStep(square, 'ArrowUp'), 2, 'square keys unchanged');

// diamond: the shortest cycle has six nodes (a chair ring)
f = Fold.fromMoves(diamond, 'HPPPPH', '03103');
assert.equal(f.placed, 6);
assert.equal(f.score(), 1);
assert.equal(f.moves(), '03103');
assert.equal(upperBound(diamond, parseSequence('HHHH')), 5); // free sides: 3 at the ends, 2 in the middle; min(3+2, 2+3)

// controller: undo/redo/truncate and notifications
const c = new GameController({ lattice: 'square', sequence: 'HPPHHPH' });
let calls = 0;
c.subscribe(() => calls++);
c.extendStep(0);
c.extendStep(2);
c.extendStep(1);
assert.equal(c.fold.placed, 4);
assert.equal(c.score, 1); // H0 at (0,0), H3 at (0,1)
c.undo();
assert.equal(c.fold.placed, 3);
c.redo();
assert.equal(c.fold.placed, 4);
c.truncate(2);
assert.equal(c.fold.placed, 2);
c.redo();
c.redo();
assert.equal(c.fold.placed, 4);
assert.equal(c.fold.moves(), 'RUL');
c.applyMoves('RULL');
assert.equal(c.fold.placed, 5);
assert.ok(calls >= 8);

// truncation preview: only before the last residue, cleared by any change of the fold
c.setCut(1);
assert.equal(c.cut, 1);
c.setCut(c.fold.placed - 1);
assert.equal(c.cut, null, 'no preview on the last residue');
c.setCut(2);
c.truncate(3);
assert.equal(c.cut, null);

// the solver: known optima, a valid fold scoring them, and slicing gives the same answer
for (const [lat, s, best] of [
  [square, 'HPHPPHHPHPPHPHHPPHPH', 9],
  [square, 'HPHPHPHPH', 0],
  [cubic, 'HHHHHHHH', 5],
  [triangular, 'HPHPHPHPH', 7],
  [fcc, 'HHHHHHHH', 11],
  [hexagonal, 'HPPPPH', 1],
  [hexagonal, 'HPPH', 0], // too short to close a hexagon
  [diamond, 'HPPPPH', 1],
  [diamond, 'HPPH', 0],
] as const) {
  const r = solve(lat, s);
  assert.ok(r.exhaustive);
  assert.equal(r.score, best, `${lat.id} ${s}`);
  const g = Fold.fromMoves(lat, s, r.moves);
  assert.ok(g.complete && g.score() === best, `${lat.id} ${s}: solver fold`);
}
const sliced = new Solver(square, 'HPPHPPHHPPHPPH');
let slices = 0;
while (!sliced.run(500)) slices++;
assert.ok(slices > 1);
assert.equal(sliced.best, 6);
assert.equal(solve(square, 'HPHPPHHPHPPHPHHPPHPH', 1000).exhaustive, false, 'a node budget stops the search');

// the solver against plain enumeration of all folds (no pruning, no symmetry), on the
// lattices with two kinds of points
function bruteForce(l: Lattice, seq: Residue[]): number {
  const o = l.steps[0].map(() => 0);
  const occ = new Map<string, number>([[key(o), 0]]);
  const path = [o];
  let best = -1;
  const rec = (score: number) => {
    const k = path.length;
    if (k === seq.length) {
      best = Math.max(best, score);
      return;
    }
    for (const w of neighbours(l, path[k - 1])) {
      if (occ.has(key(w))) continue;
      let g = 0;
      if (seq[k] === 'H')
        for (const u of neighbours(l, w)) {
          const j = occ.get(key(u));
          if (j !== undefined && j < k - 1 && seq[j] === 'H') g++;
        }
      occ.set(key(w), k);
      path.push(w);
      rec(score + g);
      path.pop();
      occ.delete(key(w));
    }
  };
  rec(0);
  return best;
}
let seed = 7;
const rand = () => ((seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648);
for (const [l, n, count] of [
  [hexagonal, 14, 12],
  [diamond, 10, 12],
] as const)
  for (let t = 0; t < count; t++) {
    const seq = Array.from({ length: n }, () => (rand() < 0.6 ? 'H' : 'P')) as Residue[];
    const r = solve(l, seq);
    assert.ok(r.exhaustive);
    assert.equal(r.score, bruteForce(l, seq), `${l.id} ${seq.join('')}`);
    const g = Fold.fromMoves(l, seq, r.moves);
    assert.ok(g.complete && g.score() === r.score, `${l.id} ${seq.join('')}: solver fold`);
  }

console.log('engine tests passed');
