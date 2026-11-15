// Independent coordinate checks for the replacement of Lemma F(D).
// Run: node research/tetrahedral/check_padding.mjs
// This checks the local padding construction, not the Bulk/N certificates
// or the entire reduction. Only Node's standard library is required.
import assert from 'node:assert/strict';

const directions = [[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]];
const mod = (n, k) => ((n % k) + k) % k;
const key = v => v.join(',');
const same = (a, b) => key(a) === key(b);
function inLattice([x, y, z]) {
  return mod(x - y, 2) === 0 && mod(x - z, 2) === 0
    && mod(x + y + z, 4) === (mod(x, 2) === 0 ? 0 : 3);
}
function neighbours(v) {
  const sign = mod(v[0], 2) === 0 ? 1 : -1;
  return directions.map(t => v.map((a, i) => a + sign * t[i]));
}
function adjacent(a, b) {
  return neighbours(a).some(v => same(v, b));
}
function coordinates(m, v) {
  const Y = v[1] - (2 * m - 2), Z = v[2] - 1;
  return {rho: Math.abs(Y) + Math.abs(Z), alpha: Math.abs(Y) - Math.abs(Z),
    quadrant: Y * Z === 0 ? null : `${Math.sign(Y)},${Math.sign(Z)}`};
}
function avenue(m, u, alpha) {
  const cache = new Map();
  return x => {
    if (cache.has(x)) return cache.get(x);
    const candidates = [];
    for (const rho of [u, u + 2]) for (const a of [alpha, alpha + 2]) {
      const Y = (rho + a) / 2, Z = (rho - a) / 2;
      const v = [x, 2 * m - 2 + Y, Z + 1];
      if (Number.isInteger(Y) && Number.isInteger(Z) && Y > 0 && Z > 0 && inLattice(v)) {
        candidates.push(v);
      }
    }
    assert.equal(candidates.length, 1, 'one avenue site per X');
    cache.set(x, candidates[0]);
    return candidates[0];
  };
}
function appendInterval(path, get, start, end) {
  const direction = start <= end ? 1 : -1;
  for (let x = start; ; x += direction) {
    path.push(get(x));
    if (x === end) return;
  }
}
function makePadding(m, u, alpha, a, b, extra) {
  assert(extra >= 6 && extra % 2 === 0);
  const A = avenue(m, u, alpha), B = avenue(m, u, alpha + 4);
  let p = a - 1;
  while (!(coordinates(m, A(p)).alpha === alpha + 2 && mod(p, 2) === 0)) p--;
  const r = a - p;
  assert(r === 2 || r === 3);
  const t = (extra - 2 * r) / 2;
  assert(Number.isInteger(t) && t >= 0);
  const j = t % 4, delta = j % 2 === 0 ? 1 : 0, eta = Math.floor(j / 2);
  const d = Math.floor(t / 4), epsilon = 1 - 2 * delta;
  const v0 = p + delta - 4 * d, v1 = p + delta + 4, q = p + 8;
  const path = [];
  appendInterval(path, A, a, v0);
  appendInterval(path, B, v0 - epsilon, v1 - epsilon);
  if (eta) {
    appendInterval(path, A, v1, q);
    appendInterval(path, B, q - 1, q + 2);
    appendInterval(path, A, q + 1, b);
  } else {
    appendInterval(path, A, v1, b);
  }
  return {path, r, delta, eta, d};
}

// Generate actual level-curve approaches by raw lattice adjacency, without
// using the avenue constructor or its phase formulas. Keep one approach
// starting in each quadrant, with |alpha_c| <= alpha - 6 as in Lemma F.
function approaches(m, u, alpha, s) {
  const backward = [s], found = new Map();
  const first = neighbours(s).filter(v => {
    const c = coordinates(m, v);
    return c.rho === u && c.quadrant === '1,1' && c.alpha === alpha - 2;
  });
  assert.equal(first.length, 1);
  backward.push(first[0]);
  for (let steps = 1; steps <= 4 * u + 4; steps++) {
    const v = backward.at(-1), c = coordinates(m, v);
    if (c.quadrant && Math.abs(c.alpha) <= alpha - 6 && !found.has(c.quadrant)) {
      found.set(c.quadrant, [...backward].reverse());
      if (found.size === 4) return [...found.values()];
    }
    const next = neighbours(v).filter(w => coordinates(m, w).rho === u
      && !same(w, backward.at(-2)));
    assert.equal(next.length, 1, 'level curve has a unique forward continuation');
    assert(!same(next[0], s), 'all four approaches found before closing the curve');
    backward.push(next[0]);
  }
  throw Error('level-curve approach bound exceeded');
}

let geometries = 0, paths = 0, checkedSites = 0, approachPaths = 0;
const phaseTypes = new Set(), residues = new Set(), crossingOptions = new Set();
const cases = [];
for (const m of [2, 3, 80]) for (const u of [21, 23, 31, 33, 47, 49, 63, 65]) {
  for (let alpha = 7; alpha <= u - 10; alpha += 2) cases.push({m, u, alpha});
}
// Also exercise avenues outside the entire m=80 octahedron.
for (const u of [201, 203, 401, 403]) for (const alpha of [7, 9, 31, 33, 101]) {
  cases.push({m: 80, u, alpha});
}
for (const {m, u, alpha} of cases) {
  const A = avenue(m, u, alpha);
  for (let a = -12; a < -4; a++) {
    const ca = coordinates(m, A(a));
    if (ca.rho !== u || ca.alpha !== alpha) continue;
    for (const gap of [48, 60]) {
      const b = a + gap, endpoints = new Set([key(A(a)), key(A(b))]);
      const incoming = [...approaches(m, u, alpha, A(a)), ...approaches(m, u, alpha, A(b))];
      const protectedSites = new Set(incoming.flat().map(key));
      approachPaths += incoming.length;
      geometries++;
      for (let extra = 6; extra <= 134; extra += 2) {
        const {path, r, delta, eta} = makePadding(m, u, alpha, a, b, extra);
        assert.equal(path.length, gap + 1 + extra, 'exact added site count');
        assert(same(path[0], A(a)) && same(path.at(-1), A(b)), 'endpoints preserved');
        const visited = new Set();
        for (let i = 0; i < path.length; i++) {
          const v = path[i], k = key(v), c = coordinates(m, v);
          assert(inLattice(v));
          assert(!visited.has(k), 'self-avoidance');
          visited.add(k);
          if (i) assert(adjacent(path[i - 1], v), 'raw lattice adjacency');
          assert(c.quadrant === '1,1' && [u, u + 2].includes(c.rho));
          assert([alpha, alpha + 2, alpha + 4, alpha + 6].includes(c.alpha));
          assert(!protectedSites.has(k) || endpoints.has(k), 'approaches avoided');
        }
        // Every site stays beyond every possible wire strip: the largest
        // wire alpha is alpha-6, and its avenue uses at most alpha-4.
        assert(path.every(v => coordinates(m, v).alpha >= alpha));
        phaseTypes.add(r); residues.add(extra % 8); crossingOptions.add(`${delta},${eta}`);
        checkedSites += path.length; paths++;
      }
    }
  }
}
assert.equal(phaseTypes.size, 2);
assert.equal(residues.size, 4);
assert.equal(crossingOptions.size, 4);
console.log(JSON.stringify({status: 'passed', geometries, paths, checkedSites, approachPaths,
  extraSites: 'every even value from 6 through 134',
  phaseTypes: [...phaseTypes].sort(), residuesMod8: [...residues].sort(),
  crossingOptions: [...crossingOptions].sort(),
  scope: 'local padding, actual lattice adjacency, simplicity, length, private levels/strips, and level-curve approaches; not a full-fold audit'
}, null, 2));
