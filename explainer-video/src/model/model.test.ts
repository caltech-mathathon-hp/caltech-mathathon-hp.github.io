/** Checks the toy example's numbers: `node src/model/model.test.ts`. */
import assert from 'node:assert/strict';
import * as M from './toy.ts';

const { n, q, T, B, K, SIZES, PACKING } = M;
assert.equal(q, 2);
assert.equal(n, 12);
assert.equal(T, 30);
assert.equal(M.TOY.pad, 20);
assert.equal(M.TOY.linker, 626);
assert.deepEqual([M.REAL.q, M.REAL.n, M.REAL.T, M.REAL.h], [6, 80, 858, 512000]);
assert.ok(T > 2 * B, 'a padding fills more than half a strip');
assert.ok(q >= K && q % 2 === 0);

// pieces of the frame
assert.equal(M.cornerRod.length, 9 * n - 10);
assert.equal(M.tenthRod.length, n - 2);
assert.equal(M.core.length, (n - 2) ** 3);
assert.equal(M.FACES.length, 5);
for (const f of M.FACES) assert.equal(f.nodes.length, (n - 2) ** 2);

// a perfect fold: every node of the cube exactly once
const fold = M.perfectFold();
assert.equal(fold.length, n ** 3);
const seen = new Set(fold.map((h) => M.key(h.pos)));
assert.equal(seen.size, n ** 3);
for (const h of fold) {
  const [x, y, z] = h.pos;
  assert.ok(x >= 0 && x < n && y >= 0 && y < n && z <= 0 && z > -n, `inside: ${h.pos}`);
}

// local rules: rod H's on edges or corners (≥ 2 outside neighbours), ribbon H's on the surface
for (const h of fold) {
  const out = M.outsideNormals(h.pos).length;
  if (['corner', 'tenth', 'wall-rod', 'spaced'].includes(h.piece)) assert.ok(out >= 2, `rod H off an edge: ${h.pos}`);
  else if (h.piece !== 'core') assert.ok(out >= 1, `ribbon H inside: ${h.pos}`);
  else assert.equal(out, 0);
}
// consecutive H's of a ribbon are neighbours
for (const piece of ['face', 'wall', 'padding', 'item'] as const) {
  const byIndex = new Map<number, typeof fold>();
  for (const h of fold.filter((h) => h.piece === piece)) byIndex.set(h.index, [...(byIndex.get(h.index) ?? []), h]);
  for (const hs of byIndex.values()) {
    hs.sort((a, b) => a.order - b.order);
    // walls are two ribbons per period; check within each half
    const parts: M.HNode[][] = piece === 'wall' ? [hs.slice(0, n - 2), hs.slice(n - 2)] : [hs];
    for (const part of parts)
      for (let i = 1; i < part.length; i++) {
        const d = part[i].pos.map((v: number, a: number) => Math.abs(v - part[i - 1].pos[a])).reduce((s: number, v: number) => s + v, 0);
        // a face ribbon's snake steps by one; between blocks PHHP the H's are joined through two P's outside, still neighbours here
        assert.equal(d, 1, `${piece} ${hs[0].index} breaks at ${part[i].pos}`);
      }
  }
}

// strips: q strips of T nodes, padding T − B, holes of B; items fill the holes
assert.equal(M.strips.length, q);
for (const s of M.strips) {
  assert.equal(s.snake.length, T);
  assert.equal(s.padding.length, T - B);
  assert.equal(s.hole.length, B);
  assert.ok(M.isEven(s.padding[0]) && !M.isEven(s.padding[s.padding.length - 1]));
}
const items = M.placeItems(SIZES, PACKING);
items.forEach((cells, u) => {
  assert.ok(cells && cells.length === SIZES[u]);
  assert.ok(M.isEven(cells![0]) && !M.isEven(cells![cells!.length - 1]), `item ${u} starts even`);
});
// first linker starts on an odd node
assert.ok(!M.isEven(M.spacedRod[M.spacedRod.length - 1]));

// the string has n³ H's
const str = M.toyString();
const hs = str.reduce((a, s) => a + s.h, 0);
assert.equal(hs, n ** 3);
const letters = str.reduce((a, s) => a + s.len, 0);
const linkers = str.filter((s) => s.origin === 'linker');
assert.equal(linkers.length, q + (q - K) + SIZES.length);
console.log(`toy model ok: n = ${n}, ${hs} H's, ${letters} letters, ${linkers.length} linkers of ${52 * n} + 2 P's`);
