/**
 * The construction of Berger and Leighton (RECOMB '98), executed: the string S_B of Fig. 3 for a
 * bin packing instance, and an explicit perfect fold of it built from a packing, following §3.2.3
 * with the paper's coordinates (i, j, k), cube [0, n-1]^3, front face k = 0.
 *
 * Plain JavaScript without DOM or three.js, so it also runs in Node:
 *   const res = build(2, 8, [4, 2, 6, 2, 2]);   // res.fold, res.val.checks, res.str.types, …
 *
 * Two routes the paper only asserts are filled in by construction (see the page text):
 * the short P-hops between faces (exact-length search at distance >= 2 from the cube), and the
 * linkers, which use one plane each in front of the cube instead of the switchboard of
 * Lemmas 3.3-3.8, with their slack in a hairpin loop. validate() checks every fold.
 */
// ---------------------------------------------------------------- bin packing
export function solveBinPacking(sizes, K, B) {
  const N = sizes.length;
  const order = sizes.map((_, i) => i).sort((a, b) => sizes[b] - sizes[a]);
  const load = new Array(K).fill(0);
  const assign = new Array(N).fill(-1);
  let nodes = 0;
  function rec(t) {
    nodes++;
    if (t === N) return true;
    const i = order[t];
    const seen = new Set();
    for (let b = 0; b < K; b++) {
      if (load[b] + sizes[i] > B || seen.has(load[b])) continue; // symmetry pruning
      seen.add(load[b]);
      load[b] += sizes[i]; assign[i] = b;
      if (rec(t + 1)) return true;
      load[b] -= sizes[i]; assign[i] = -1;
    }
    return false;
  }
  const ok = rec(0);
  return { assign: ok ? assign : null, nodes };
}

// ---------------------------------------------------------------- parameters
function icbrt(B) { let t = 0; while (t * t * t < B) t++; return t; }

export function params(K, B) {
  const q = 2 * Math.max(K, icbrt(B));
  const n = q * (2 * q + 1) + 2;
  const T = (2 * q - 1) * (n - 2);
  const c = 52;
  return { K, B, q, n, T, c, m: n - 2 };
}

export function checkInstance(K, B, sizes) {
  const errs = [];
  if (!(Number.isInteger(K) && K >= 1)) errs.push('K must be a positive integer');
  if (!(Number.isInteger(B) && B >= 2)) errs.push('B must be an integer ≥ 2');
  if (B % 2) errs.push('B must be even (the B-strings are (PHHP)^{B/2})');
  if (!sizes.length) errs.push('need at least one item');
  sizes.forEach((s, i) => {
    if (!(Number.isInteger(s) && s > 0 && s % 2 === 0)) errs.push(`item ${i + 1}: size must be a positive even integer`);
  });
  const sum = sizes.reduce((a, b) => a + b, 0);
  if (sum !== B * K) errs.push(`sizes must sum to B·K = ${B * K} (they sum to ${sum})`);
  if (errs.length) return { errs };
  const P = params(K, B);
  if (2 * (P.T - P.B) <= P.T) errs.push('need 2(T−B) > T');
  return { errs, P };
}

// ---------------------------------------------------------------- the string S_B (Fig. 3)
// Returns { types: Uint8Array (1 = H, 0 = P), factors: [{key, start, end}] }
export function buildString(P, sizes) {
  const { q, n, T, c, K, B, m } = P;
  const out = [];
  const factors = [];
  const rep = (s, k) => { for (let r = 0; r < k; r++) for (const ch of s) out.push(ch === 'H' ? 1 : 0); };
  const fac = (key, fn) => { const s = out.length; fn(); factors.push({ key, start: s, end: out.length }); };
  fac('edges', () => rep('PHP', 9 * n - 10));
  fac('back', () => rep('PHHP', m * m / 2));
  fac('bl', () => rep('PHP', m));
  fac('p4', () => rep('P', 4));
  fac('faces', () => { for (let r = 0; r < 3; r++) { rep('PHHP', m * m / 2); rep('P', 7); } });
  fac('top', () => rep('PHHP', m * m / 2 - 1));
  fac('int', () => { rep('P', 1); rep('H', m * m * m + 2); });
  fac('down', () => rep('P', 8 + q));
  fac('walls', () => {
    for (let r = 0; r < q; r++) {
      rep('PHP', q); rep('PHHP', m / 2); rep('PHP', 2 * q + 1); rep('P', 4);
      rep('PHHP', m / 2); rep('PHP', q); rep('P', 2 * q);
    }
  });
  fac('special', () => { rep('PH', 1); for (let r = 0; r < q - 1; r++) { rep('P', 2 * q + 6); rep('H', 1); } rep('P', 1); });
  fac('fill', () => { for (let r = 0; r < q; r++) { rep('P', c * n); rep('PHHP', (T - B) / 2); } });
  fac('dummy', () => { for (let r = 0; r < q - K; r++) { rep('P', c * n); rep('PHHP', B / 2); } });
  fac('items', () => { for (const s of sizes) { rep('P', c * n); rep('PHHP', s / 2); } });
  return { types: Uint8Array.from(out), factors };
}

// ---------------------------------------------------------------- the fold (Section 3.2.3)
const OFF = 4096, SP = 8192;
const key = (x, y, z) => ((x + OFF) * SP + (y + OFF)) * SP + (z + OFF);
const DIRS = [[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]];

export function buildFold(P, sizes, assign) {
  const { q, n, T, c, K, B, m } = P;
  const L = c * n;            // the P^{cn} runs
  const inCube = (x, y, z) => x >= 0 && y >= 0 && z >= 0 && x < n && y < n && z < n;
  const dCube = (x, y, z) => {
    let d = 0;
    for (const v of [x, y, z]) { if (v < 0) d -= v; else if (v > n - 1) d += v - (n - 1); }
    return d;
  };
  const normals = (x, y, z) => {
    const r = [];
    if (x === 0) r.push([-1, 0, 0]); if (x === n - 1) r.push([1, 0, 0]);
    if (y === 0) r.push([0, -1, 0]); if (y === n - 1) r.push([0, 1, 0]);
    if (z === 0) r.push([0, 0, -1]); if (z === n - 1) r.push([0, 0, 1]);
    return r;
  };
  const add3 = (a, d) => [a[0] + d[0], a[1] + d[1], a[2] + d[2]];
  const man = (a, b) => Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]) + Math.abs(a[2] - b[2]);
  const sameDir = (a, b) => a[0] === b[0] && a[1] === b[1] && a[2] === b[2];

  // bead storage
  let cap = 1 << 16;
  let X = new Int32Array(cap), Y = new Int32Array(cap), Z = new Int32Array(cap);
  let TY = new Uint8Array(cap), SG = new Uint16Array(cap), CAT = new Uint8Array(cap);
  let N = 0;
  const occ = new Map();
  let curSeg = 0, curCat = 0;
  const segs = [];

  function grow() {
    cap *= 2;
    const g = (A, C) => { const b = new C(cap); b.set(A); return b; };
    X = g(X, Int32Array); Y = g(Y, Int32Array); Z = g(Z, Int32Array);
    TY = g(TY, Uint8Array); SG = g(SG, Uint16Array); CAT = g(CAT, Uint8Array);
  }
  function fail(msg) { throw new Error(`[fold] ${msg} (bead ${N}, segment ${segs.length ? segs[segs.length - 1].key : '-'})`); }
  function isFree(p) { return !occ.has(key(p[0], p[1], p[2])); }
  function last() { return [X[N - 1], Y[N - 1], Z[N - 1]]; }

  function add(t, p) {
    const [x, y, z] = p;
    if (N > 0) {
      const d = Math.abs(x - X[N - 1]) + Math.abs(y - Y[N - 1]) + Math.abs(z - Z[N - 1]);
      if (d !== 1) fail(`non-adjacent step to (${x},${y},${z}) from (${X[N - 1]},${Y[N - 1]},${Z[N - 1]})`);
    }
    const k = key(x, y, z);
    if (occ.has(k)) fail(`collision at (${x},${y},${z}) with bead ${occ.get(k)}`);
    if (t === 1 && !inCube(x, y, z)) fail(`H outside cube at (${x},${y},${z})`);
    if (t === 0 && inCube(x, y, z)) fail(`P inside cube at (${x},${y},${z})`);
    if (N === cap) grow();
    X[N] = x; Y[N] = y; Z[N] = z; TY[N] = t; SG[N] = curSeg; CAT[N] = curCat;
    occ.set(k, N);
    N++;
  }
  const addP = (p) => add(0, p);
  const addH = (p) => add(1, p);
  const addPath = (cells) => { for (const p of cells) addP(p); };

  function seg(keyName, label, cat, fn, extra) {
    curSeg = segs.length; curCat = cat;
    const s = { key: keyName, label, cat, start: N, end: N, ...(extra || {}) };
    segs.push(s);
    fn();
    s.end = N;
    return s;
  }

  // (PHP)^r along edges: Hs on cube edges/corners; each consecutive pair joined by a
  // 2-P staple h_i+d, h_{i+1}+d with d a shared outward normal; d_in != d_out at every H.
  function edgeRun(hs, opt = {}) {
    const r = hs.length;
    const NR = hs.map((h) => normals(...h));
    // allowed d for slot index t: t=0 in-slot of h0, t=1..r-1 staple between h_{t-1},h_t, t=r out-slot of h_{r-1}
    const allowed = [];
    for (let t = 0; t <= r; t++) {
      let cand;
      if (t === 0) cand = NR[0];
      else if (t === r) cand = NR[r - 1];
      else cand = NR[t - 1].filter((d) => NR[t].some((e) => sameDir(d, e)));
      cand = cand.filter((d) => {
        if (t === 0) {
          const p = add3(hs[0], d);
          if (!isFree(p)) return false;
          if (opt.firstDir) return sameDir(d, opt.firstDir);
          return N === 0 || man(p, last()) === 1;
        }
        if (t === r) {
          const p = add3(hs[r - 1], d);
          if (!isFree(p)) return false;
          if (opt.lastDir && !sameDir(d, opt.lastDir)) return false;
          if (opt.next && man(p, opt.next) !== 1) return false;
          return true;
        }
        return isFree(add3(hs[t - 1], d)) && isFree(add3(hs[t], d));
      });
      allowed.push(cand);
    }
    // backward feasibility
    const feas = allowed.map((a) => a.map(() => false));
    feas[r] = allowed[r].map(() => true);
    for (let t = r - 1; t >= 0; t--) {
      feas[t] = allowed[t].map((d) => allowed[t + 1].some((e, j) => feas[t + 1][j] && !sameDir(d, e)));
    }
    const pick = [];
    let prev = null;
    for (let t = 0; t <= r; t++) {
      let j = allowed[t].findIndex((d, jj) => feas[t][jj] && (!prev || !sameDir(prev, d)));
      if (j < 0) fail('edgeRun: no consistent staple directions');
      pick.push(allowed[t][j]); prev = allowed[t][j];
    }
    for (let i = 0; i < r; i++) {
      addP(add3(hs[i], pick[i]));
      addH(hs[i]);
      if (i === r - 1) addP(add3(hs[i], pick[r]));
      else addP(add3(hs[i], pick[i + 1]));
    }
  }

  // (PHHP)^{r/2} on a face/bin: hs consecutive adjacent face nodes, P's in the unique outward slot.
  function faceRun(hs) {
    if (hs.length % 2) fail('faceRun: odd length');
    for (let i = 0; i < hs.length; i += 2) {
      const a = hs[i], b = hs[i + 1];
      const na = normals(...a), nb = normals(...b);
      if (na.length !== 1 || nb.length !== 1) fail('faceRun: node not in a face interior');
      addP(add3(a, na[0])); addH(a); addH(b); addP(add3(b, nb[0]));
    }
  }

  // k P's from the last bead to a cell adjacent to `to`, staying at distance >= 2 from the cube
  function transfer(k, to) {
    const from = last();
    const path = [];
    const vis = new Set();
    const lo = [Math.min(from[0], to[0]) - 3, Math.min(from[1], to[1]) - 3, Math.min(from[2], to[2]) - 3];
    const hi = [Math.max(from[0], to[0]) + 3, Math.max(from[1], to[1]) + 3, Math.max(from[2], to[2]) + 3];
    const okc = (p) => p[0] >= lo[0] && p[1] >= lo[1] && p[2] >= lo[2] && p[0] <= hi[0] && p[1] <= hi[1] && p[2] <= hi[2]
      && !inCube(...p) && dCube(...p) >= 2 && isFree(p) && !vis.has(key(...p));
    function dfs(cur, rem) {
      if (rem === 0) return man(cur, to) === 1;
      const cand = DIRS.map((d) => add3(cur, d)).filter(okc)
        .sort((a, b) => (man(a, to) - man(b, to)) || (dCube(...a) - dCube(...b)));
      for (const nx of cand) {
        const dist = man(nx, to);
        if (dist === 0 || dist > rem || (rem - dist) % 2) continue;
        vis.add(key(...nx)); path.push(nx);
        if (dfs(nx, rem - 1)) return true;
        vis.delete(key(...nx)); path.pop();
      }
      return false;
    }
    if (!dfs(from, k)) fail(`transfer of ${k} P's to (${to}) impossible`);
    addPath(path);
  }

  // ------------------------------------------------------------------ CAT codes
  // 0 P, 1 edges, 2 back, 3 back-left edge, 4 left, 5 bottom, 6 right, 7 top, 8 interior,
  // 9 wall, 10 special, 11 filler, 12 dummy, 13 item
  // ================================================================== §3.2.3 part 1: all but the front face
  // 1. (PHP)^{9n-10}: nine edges (Fig. 4)
  seg('edges', 'Nine edges', 1, () => {
    const E = [];
    for (let x = n - 2; x >= 0; x--) E.push([x, n - 1, n - 1]);
    for (let z = n - 2; z >= 0; z--) E.push([0, n - 1, z]);
    for (let x = 1; x <= n - 1; x++) E.push([x, n - 1, 0]);
    for (let z = 1; z <= n - 1; z++) E.push([n - 1, n - 1, z]);
    for (let y = n - 2; y >= 0; y--) E.push([n - 1, y, n - 1]);
    for (let z = n - 2; z >= 0; z--) E.push([n - 1, 0, z]);
    for (let x = n - 2; x >= 0; x--) E.push([x, 0, 0]);
    for (let z = 1; z <= n - 1; z++) E.push([0, 0, z]);
    for (let x = 1; x <= n - 2; x++) E.push([x, 0, n - 1]);
    edgeRun(E, { firstDir: [0, 0, 1], next: [n - 2, 1, n] });
  });
  // 2. (PHHP)^{(n-2)^2/2}: back face, vertical snake (Fig. 6)
  seg('back', 'Back face', 2, () => {
    const hs = [];
    for (let i = 0; i < m; i++) {
      const x = n - 2 - i;
      if (i % 2 === 0) for (let y = 1; y <= n - 2; y++) hs.push([x, y, n - 1]);
      else for (let y = n - 2; y >= 1; y--) hs.push([x, y, n - 1]);
    }
    faceRun(hs);
  });
  // 3. (PHP)^{n-2}: back-left edge
  seg('bl', 'Back-left edge', 3, () => {
    const hs = [];
    for (let y = 1; y <= n - 2; y++) hs.push([0, y, n - 1]);
    edgeRun(hs, { lastDir: [0, 0, 1] });
  });
  // 4.-5. P^4, then left/bottom/right faces each followed by P^7, then the top face
  const leftH = [], botH = [], rightH = [], topH = [];
  for (let r = 0; r < m; r++) {
    const y = n - 2 - r;
    if (r % 2 === 0) for (let z = n - 2; z >= 1; z--) leftH.push([0, y, z]);
    else for (let z = 1; z <= n - 2; z++) leftH.push([0, y, z]);
  }
  for (let r = 0; r < m; r++) {
    const x = 1 + r;
    if (r % 2 === 0) for (let z = n - 2; z >= 1; z--) botH.push([x, 0, z]);
    else for (let z = 1; z <= n - 2; z++) botH.push([x, 0, z]);
  }
  for (let r = 0; r < m; r++) {
    const y = 1 + r;
    if (r % 2 === 0) for (let z = n - 2; z >= 1; z--) rightH.push([n - 1, y, z]);
    else for (let z = 1; z <= n - 2; z++) rightH.push([n - 1, y, z]);
  }
  for (let r = 0; r < m; r++) {
    const z = n - 2 - r;
    if (r % 2 === 0) for (let x = n - 2; x >= 1; x--) topH.push([x, n - 1, z]);
    else for (let x = 1; x <= (r === m - 1 ? n - 4 : n - 2); x++) topH.push([x, n - 1, z]);
  }
  const slot = (h) => add3(h, normals(...h)[0]);
  seg('p4', 'P⁴ to the left face', 0, () => transfer(4, slot(leftH[0])));
  seg('left', 'Left face', 4, () => faceRun(leftH));
  seg('p7a', 'P⁷ around the bottom-left edge', 0, () => transfer(7, slot(botH[0])));
  seg('bottom', 'Bottom face', 5, () => faceRun(botH));
  seg('p7b', 'P⁷ around the bottom-right edge', 0, () => transfer(7, slot(rightH[0])));
  seg('right', 'Right face', 6, () => faceRun(rightH));
  seg('p7c', 'P⁷ around the top-right edge', 0, () => transfer(7, slot(topH[0])));
  seg('top', 'Top face (one pair short)', 7, () => faceRun(topH));

  // 6. P H^{(n-2)^3+2}: enter at (n-3,n-1,1), truncated snake through the interior,
  //    leave the column (n-2,*,1) open, climb it, exit at (n-2,n-1,1).
  seg('int', 'Interior', 8, () => {
    addP([n - 3, n, 1]);
    addH([n - 3, n - 1, 1]);
    const PA = [];
    for (let u = m - 2; u >= 0; u--) PA.push([u, 0]);
    for (let w = 1; w < m; w++) {
      if (w % 2 === 1) for (let u = 0; u < m; u++) PA.push([u, w]);
      else for (let u = m - 1; u >= 0; u--) PA.push([u, w]);
    }
    for (let li = 0; li < m; li++) {
      const v = m - 1 - li;
      if (li % 2 === 0) for (let t = 0; t < PA.length; t++) addH([PA[t][0] + 1, v + 1, PA[t][1] + 1]);
      else for (let t = PA.length - 1; t >= 0; t--) addH([PA[t][0] + 1, v + 1, PA[t][1] + 1]);
    }
    for (let v = 0; v < m; v++) addH([n - 2, v + 1, 1]);
    addH([n - 2, n - 1, 1]);
  });
  // 7. P^{8+q} to (n-1, n-1-q, -2)
  seg('down', 'P^{8+q} to the front face', 0, () => {
    const cells = [[n - 2, n, 1], [n - 2, n + 1, 1], [n - 2, n + 1, 0], [n - 2, n + 1, -1], [n - 2, n + 1, -2], [n - 1, n + 1, -2]];
    for (let y = n; y >= n - 1 - q; y--) cells.push([n - 1, y, -2]);
    addPath(cells);
  });

  // ================================================================== §3.2.3 part 2: the bins
  const walls = [];
  for (let w = 0; w < q; w++) {
    const rt = n - 2 - w * (2 * q + 1), rb = rt - 2 * q;
    walls.push({ w, rt, rb, gap: rt - q });
  }
  seg('walls', 'Bin walls', 9, () => {
    for (const { w, rt, rb } of walls) {
      const hsA = []; for (let j = rt - q + 1; j <= rt; j++) hsA.push([n - 1, j, 0]);
      edgeRun(hsA, { next: [n - 2, rt, -1] });
      const row1 = []; for (let x = n - 2; x >= 1; x--) row1.push([x, rt, 0]);
      faceRun(row1);
      const hsL = []; for (let j = rt; j >= rb; j--) hsL.push([0, j, 0]);
      edgeRun(hsL, { next: [-1, rb, -1] });
      addPath([[-1, rb, -1], [-1, rb, -2], [0, rb, -2], [1, rb, -2]]); // the P^4
      const row2 = []; for (let x = 1; x <= n - 2; x++) row2.push([x, rb, 0]);
      faceRun(row2);
      const hsB = []; for (let j = rb; j <= rb + q - 1; j++) hsB.push([n - 1, j, 0]);
      const j1 = rb + q - 1;
      if (w < q - 1) {
        edgeRun(hsB, { next: [n, j1, -1], lastDir: [0, 0, -1] });
        const cells = []; for (let j = j1; j >= rb - q; j--) cells.push([n, j, -1]); // P^{2q} at distance 2
        addPath(cells);
      } else {
        edgeRun(hsB, { lastDir: [0, 0, -1] });
        const cells = []; // P^{2q}: a hairpin "distance q away from the cube and back"
        for (let t = 1; t <= q; t++) cells.push([n - 1 + t, q, -1]);
        for (let t = q; t >= 1; t--) cells.push([n - 1 + t, q + 1, -1]);
        addPath(cells);
      }
    }
  });
  // PH (P^{2q+6} H)^{q-1} P: one H in the gap of each wall, bottom to top
  seg('special', 'Special q-string', 10, () => {
    const g = []; for (let w = q - 1; w >= 0; w--) g.push(walls[w].gap);
    addP([n - 1, g[0], -1]);
    for (let k = 0; k < q; k++) {
      addH([n - 1, g[k], 0]);
      if (k === q - 1) break;
      const a = g[k], b = g[k + 1], cells = [];
      if (k % 2 === 0) { // out through the right side, run at distance 3 (x = n+2)
        cells.push([n, a, 0], [n + 1, a, 0], [n + 2, a, 0]);
        for (let j = a + 1; j <= b; j++) cells.push([n + 2, j, 0]);
        cells.push([n + 1, b, 0], [n, b, 0]);
      } else { // out through the front, run at distance 3 (k = -3)
        cells.push([n - 1, a, -1], [n - 1, a, -2], [n - 1, a, -3]);
        for (let j = a + 1; j <= b; j++) cells.push([n - 1, j, -3]);
        cells.push([n - 1, b, -2], [n - 1, b, -1]);
      }
      addPath(cells);
    }
    addP([n - 1, g[q - 1], -1]);
  });

  // ================================================================== §3.2.3 part 3: the items
  // bins: snake through rows rt-1 .. rb+1, starting at an even node
  const bins = walls.map(({ w, rt, rb }) => {
    const cells = [];
    const x0 = ((1 + rt - 1) % 2 === 0) ? 1 : n - 2;
    let r = 0;
    for (let y = rt - 1; y >= rb + 1; y--, r++) {
      const fwd = (r % 2 === 0) === (x0 === 1);
      if (fwd) for (let x = 1; x <= n - 2; x++) cells.push([x, y, 0]);
      else for (let x = n - 2; x >= 1; x--) cells.push([x, y, 0]);
    }
    return { w, rt, rb, cells, ptr: 0, contents: [] };
  });
  const strings = [];
  for (let w = 0; w < q; w++) strings.push({ kind: 'filler', bin: w, len: T - B });
  for (let w = K; w < q; w++) strings.push({ kind: 'dummy', bin: w, len: B });
  sizes.forEach((s, u) => strings.push({ kind: 'item', item: u, bin: assign[u], len: s }));
  for (const s of strings) {
    const bn = bins[s.bin];
    s.cells = bn.cells.slice(bn.ptr, bn.ptr + s.len);
    if (s.cells.length !== s.len) throw new Error('bin overflow');
    const par = (s.cells[0][0] + s.cells[0][1]) % 2;
    if (par !== 0) throw new Error('item string does not start on an even node');
    bn.ptr += s.len;
    bn.contents.push(s);
  }
  bins.forEach((bn) => { if (bn.ptr !== bn.cells.length) throw new Error(`bin ${bn.w} not exactly filled`); });

  // ---- connectors of exactly cn + 2 P's (cn intermediate cells + the two flanking slot P's)
  const M = strings.length;
  const conn = [];
  let prevEnd = [n - 1, walls[0].gap];
  for (let s = 0; s < M; s++) {
    conn.push({ a: prevEnd, b: [strings[s].cells[0][0], strings[s].cells[0][1]], idx: s });
    const lc = strings[s].cells[strings[s].len - 1];
    prevEnd = [lc[0], lc[1]];
  }
  // Every linker gets a plane k = -D of its own in front of the cube (D = 4, 6, 8, ...). Its two ends
// drop straight to that plane (stubs), run in it to just below the cube (legs), and its slack is
// folded into a small box of P's under the front of the cube: a snake through the box layer by
// layer that climbs back up a free column, plus a short drop above the box for the remainder.
// Boxes of linkers whose planes are less than `side` apart sit in different columns, so no two
// boxes meet and the drops above the boxes never cross another box. If a box cannot be placed,
// that linker falls back to a hairpin loop to the side of all boxes.
const side = Math.max(4, 2 * Math.round(Math.cbrt(L * 0.95) / 2)); // even box side
const NC = side / 2; // columns of boxes; planes 2*NC = side apart share a column
const CW = side + 3; // column width (box width up to side + 1, plus a gap)
const col0 = Math.round(n / 2 - (NC * CW) / 2);
const colX = (c) => col0 + c * CW;
const XMIN = Math.min(-3, col0 - 2), XMAX = Math.max(n + 2, colX(NC) + 2 * M + 8), YMIN = -2, YMAX = n + 2;
const YT = YMIN; // legs end on this row, the boxes hang below it
const W2 = XMAX - XMIN + 1;
const pk = (x, y) => (y - YMIN) * W2 + (x - XMIN);
// a leg in the plane k = z from `start` to `target` (on the row YT, which legs only enter at their
// target), avoiding `blocked` and anything already placed. Moving sideways in front of the face
// costs 8 and every other step 1, so legs drop straight out of the face and travel sideways on
// the two free rows just below the cube, where they do not hide the strips.
const GH = YMAX - YMIN + 1, GN = W2 * GH;
function bfsTo(start, target, blocked, z) {
  const dist = new Int32Array(GN).fill(0x3fffffff), prev = new Int32Array(GN).fill(-1);
  const s0 = pk(start[0], start[1]), t0 = pk(target[0], target[1]);
  const heap = [[0, s0]];
  dist[s0] = 0;
  const push = (d, v) => {
    heap.push([d, v]);
    for (let i = heap.length - 1; i > 0;) { const j = (i - 1) >> 1; if (heap[j][0] <= heap[i][0]) break; [heap[i], heap[j]] = [heap[j], heap[i]]; i = j; }
  };
  const pop = () => {
    const top = heap[0], last = heap.pop();
    if (heap.length) {
      heap[0] = last;
      for (let i = 0; ;) {
        const l = 2 * i + 1, r = l + 1; let m = i;
        if (l < heap.length && heap[l][0] < heap[m][0]) m = l;
        if (r < heap.length && heap[r][0] < heap[m][0]) m = r;
        if (m === i) break;
        [heap[i], heap[m]] = [heap[m], heap[i]]; i = m;
      }
    }
    return top;
  };
  while (heap.length) {
    const [d, cur] = pop();
    if (d !== dist[cur]) continue;
    if (cur === t0) {
      const path = [];
      for (let p = cur; p !== -1; p = prev[p]) path.push([(p % W2) + XMIN, Math.floor(p / W2) + YMIN]);
      return path.reverse();
    }
    const cx = (cur % W2) + XMIN, cy = Math.floor(cur / W2) + YMIN;
    for (const [dx, dy] of [[0, -1], [1, 0], [-1, 0], [0, 1]]) {
      const nx = cx + dx, ny = cy + dy;
      if (nx < XMIN || nx > XMAX || ny < YMIN || ny > YMAX) continue;
      const nk = pk(nx, ny);
      if (blocked.has(nk) || (ny === YT && nk !== t0) || occ.has(key(nx, ny, z))) continue;
      const w = dy === 0 && cy >= 1 && cx >= 0 && cx <= n - 1 ? 8 : 1;
      if (d + w < dist[nk]) { dist[nk] = d + w; prev[nk] = cur; push(d + w, nk); }
    }
  }
  return null;
}
// box W x Dd x Lh (Dd, Lh even) with as little left over as possible and close to a cube
function boxDims(ell) {
  let best = null;
  for (let W = Math.max(2, side - 4); W <= side + 1; W++)
    for (let Dd = Math.max(2, side - 4); Dd <= side; Dd += 2)
      for (let Lh = 2; Lh <= 8 * side; Lh += 2) {
        const V = W * Dd * Lh;
        if (V > ell) break;
        const score = (ell - V) + 3 * (Math.abs(W - Dd) + Math.abs(Lh - Dd));
        if (!best || score < best.score) best = { W, Dd, Lh, V, score };
      }
  return best;
}
// a path through the whole box from (W-2, 0) to (W-1, 0) on the top layer, as [u, w, layer]:
// each layer is snaked row by row without the column (W-1, 0), every other layer backwards,
// and the column takes the path back up
function boxPath(W, Dd, Lh) {
  const PA = [];
  for (let u = W - 2; u >= 0; u--) PA.push([u, 0]);
  for (let w = 1; w < Dd; w++) {
    if (w % 2) for (let u = 0; u < W; u++) PA.push([u, w]);
    else for (let u = W - 1; u >= 0; u--) PA.push([u, w]);
  }
  const out = [];
  for (let li = 0; li < Lh; li++) {
    if (li % 2 === 0) for (const [u, w] of PA) out.push([u, w, li]);
    else for (let t = PA.length - 1; t >= 0; t--) out.push([PA[t][0], PA[t][1], li]);
  }
  for (let li = Lh - 1; li >= 0; li--) out.push([W - 1, 0, li]);
  return out;
}
const freeCells = (cells) => {
  const seen = new Set();
  for (const c of cells) {
    const k = key(c[0], c[1], c[2]);
    if (occ.has(k) || seen.has(k)) return false;
    seen.add(k);
  }
  return true;
};
// legs from both ends to the targets ta, tb on the row YT (either end may take either target)
function legsTo(a, b, ta, tb, blocked, z) {
  for (const [p, q] of [[ta, tb], [tb, ta]]) {
    for (const aFirst of [true, false]) {
      const first = aFirst ? a : b, second = aFirst ? b : a;
      const t1 = aFirst ? p : q, t2 = aFirst ? q : p;
      const bl1 = new Set(blocked); bl1.add(pk(second[0], second[1]));
      const l1 = bfsTo(first, [t1, YT], bl1, z);
      if (!l1) continue;
      const bl2 = new Set(blocked); for (const c of l1) bl2.add(pk(c[0], c[1]));
      const l2 = bfsTo(second, [t2, YT], bl2, z);
      if (!l2) continue;
      return aFirst ? { legA: l1, legB: l2 } : { legA: l2, legB: l1 };
    }
  }
  return null;
}
function stubsAndLegs(a, b, legA, legB, z) {
  const head = [], tail = [];
  for (let zz = -2; zz >= z; zz--) head.push([a[0], a[1], zz]);
  for (let t = 1; t < legA.length; t++) head.push([legA[t][0], legA[t][1], z]);
  for (let t = legB.length - 1; t >= 1; t--) tail.push([legB[t][0], legB[t][1], z]);
  for (let zz = z; zz <= -2; zz++) tail.push([b[0], b[1], zz]);
  return { head, tail };
}
function routeBox(ci, D, c, blocked) {
  const { a, b } = conn[ci], z = -D;
  const xa = colX(c) + CW - 4, xb = xa + 1;
  const legs = legsTo(a, b, xa, xb, blocked, z);
  if (!legs) return null;
  const { legA, legB } = legs;
  const ell = L - 2 * (D - 1) - (legA.length - 1) - (legB.length - 1);
  if (ell % 2) throw new Error('linker parity mismatch');
  const dims = boxDims(ell);
  if (!dims) return null;
  const { W, Dd, Lh, V } = dims, dd = (ell - V) / 2, y0 = YT - 1 - dd;
  const ea = legA[legA.length - 1][0], eb = legB[legB.length - 1][0];
  let path = boxPath(W, Dd, Lh).map(([u, w, li]) => [xa - (W - 2) + u, y0 - li, z - w]);
  if (ea !== xa) path = path.reverse();
  const { head, tail } = stubsAndLegs(a, b, legA, legB, z);
  const cells = [...head];
  for (let y = YT - 1; y > y0; y--) cells.push([ea, y, z]);
  cells.push(...path);
  for (let y = y0 + 1; y <= YT - 1; y++) cells.push([eb, y, z]);
  cells.push(...tail);
  if (cells.length !== L || !freeCells(cells)) return null;
  return { cells, depth: D, box: { W, Dd, Lh, drop: dd } };
}
function routeLoop(ci, D, blocked) {
  const { a, b } = conn[ci], z = -D;
  const tx = colX(NC) + 2 + 2 * (D / 2); // right of all boxes, one column per plane
  const legs = legsTo(a, b, tx, tx + 1, blocked, z);
  if (!legs) return null;
  const { legA, legB } = legs;
  const ell = L - 2 * (D - 1) - (legA.length - 1) - (legB.length - 1);
  if (ell % 2 || ell < 2) return null;
  const h = ell / 2;
  const ea = legA[legA.length - 1][0], eb = legB[legB.length - 1][0];
  const { head, tail } = stubsAndLegs(a, b, legA, legB, z);
  const cells = [...head];
  for (let y = YT - 1; y >= YT - h; y--) cells.push([ea, y, z]);
  for (let y = YT - h; y <= YT - 1; y++) cells.push([eb, y, z]);
  cells.push(...tail);
  if (cells.length !== L || !freeCells(cells)) return null;
  return { cells, depth: D, loop: h };
}
// greedy layering: shallowest plane first; the stubs of the deeper linkers are obstacles there
const remaining = conn.map((_, i) => i);
const routes = new Array(M);
for (let d = 0; d < M; d++) {
  const D = 4 + 2 * d;
  let route = null, chosen = -1;
  for (const pass of ['box', 'loop']) {
    for (const ci of remaining) {
      const blocked = new Set();
      for (const cj of remaining) if (cj !== ci) { blocked.add(pk(...conn[cj].a)); blocked.add(pk(...conn[cj].b)); }
      route = pass === 'box' ? routeBox(ci, D, d % NC, blocked) : routeLoop(ci, D, blocked);
      if (route) { chosen = ci; break; }
    }
    if (route) break;
  }
  if (!route) throw new Error('could not route the linkers');
  routes[chosen] = route;
  remaining.splice(remaining.indexOf(chosen), 1);
}

const itemSegs = [];
  strings.forEach((s, si) => {
    const cat = s.kind === 'filler' ? 11 : s.kind === 'dummy' ? 12 : 13;
    const label = s.kind === 'filler' ? `Filler string → bin ${s.bin + 1}`
      : s.kind === 'dummy' ? `B-string → bin ${s.bin + 1}` : `Item u${s.item + 1} (size ${sizes[s.item]}) → bin ${s.bin + 1}`;
    const sg = seg(s.kind, label, cat, () => {
      const cStart = N;
      curCat = 0; addPath(routes[si].cells);
      curCat = cat; faceRun(s.cells);
      s.connStart = cStart; s.connEnd = cStart + L;
    }, { string: si, bin: s.bin, item: s.item, depth: routes[si].depth });
    itemSegs.push(sg);
  });

  // CAT for P beads -> 0 everywhere except we keep their segment
  for (let i = 0; i < N; i++) if (TY[i] === 0) CAT[i] = 0;

  return {
    N, X: X.slice(0, N), Y: Y.slice(0, N), Z: Z.slice(0, N), TY: TY.slice(0, N),
    SG: SG.slice(0, N), CAT: CAT.slice(0, N), segs, walls, bins, strings, routes, occ,
  };
}

// ---------------------------------------------------------------- validation
export function validate(P, fold, types) {
  const { n } = P;
  const { N, X, Y, Z, TY } = fold;
  const checks = [];
  // 1. sequence equals S_B
  let seqOk = N === types.length;
  if (seqOk) for (let i = 0; i < N; i++) if (TY[i] !== types[i]) { seqOk = false; break; }
  checks.push({ name: 'H/P sequence of the fold equals S_B (Fig. 3)', ok: seqOk, detail: `${N.toLocaleString()} residues` });
  // 2. self-avoiding walk
  let adj = true;
  for (let i = 1; i < N; i++) {
    if (Math.abs(X[i] - X[i - 1]) + Math.abs(Y[i] - Y[i - 1]) + Math.abs(Z[i] - Z[i - 1]) !== 1) { adj = false; break; }
  }
  const seen = new Set();
  let inj = true;
  for (let i = 0; i < N; i++) { const k = key(X[i], Y[i], Z[i]); if (seen.has(k)) { inj = false; break; } seen.add(k); }
  checks.push({ name: 'consecutive residues on adjacent lattice sites', ok: adj });
  checks.push({ name: 'no lattice site used twice (self-avoiding)', ok: inj });
  // 3. H's = cube
  let hCount = 0, hIn = true;
  for (let i = 0; i < N; i++) if (TY[i]) {
    hCount++;
    if (X[i] < 0 || Y[i] < 0 || Z[i] < 0 || X[i] >= n || Y[i] >= n || Z[i] >= n) hIn = false;
  }
  checks.push({ name: `the ${(n ** 3).toLocaleString()} H's fill the ${n}×${n}×${n} cube`, ok: hIn && hCount === n ** 3 });
  // 4. contacts
  const hIdx = new Map();
  for (let i = 0; i < N; i++) if (TY[i]) hIdx.set(key(X[i], Y[i], Z[i]), i);
  const contactPrefix = new Int32Array(N + 1);
  let cnt = 0;
  for (let i = 0; i < N; i++) {
    if (TY[i]) {
      for (const [dx, dy, dz] of DIRS) {
        const j = hIdx.get(key(X[i] + dx, Y[i] + dy, Z[i] + dz));
        if (j !== undefined && j < i) cnt++;
      }
    }
    contactPrefix[i + 1] = cnt;
  }
  const target = 3 * n * n * (n - 1);
  checks.push({ name: `H–H pairs = 3n²(n−1) = ${target.toLocaleString()}, the maximum (Thm 3.2)`, ok: cnt === target, detail: cnt.toLocaleString() });
  return { checks, ok: checks.every((c) => c.ok), contactPrefix, contacts: cnt, target };
}

// `given` (optional): a packing chosen by the user, assign[u] = bin of item u; it must fill every bin exactly
export function build(K, B, sizes, given) {
  const chk = checkInstance(K, B, sizes);
  if (chk.errs.length) return { error: chk.errs.join('; ') };
  const P = chk.P;
  const t0 = Date.now();
  let sol;
  if (given) {
    const load = new Array(K).fill(0);
    given.forEach((b, u) => { load[b] += sizes[u]; });
    if (given.length !== sizes.length || load.some((l) => l !== B)) return { error: 'the given packing does not fill every bin exactly' };
    sol = { assign: given.slice(), nodes: 0, given: true };
  } else sol = solveBinPacking(sizes, K, B);
  const t1 = Date.now();
  const str = buildString(P, sizes);
  if (!sol.assign) return { P, solvable: false, solverNodes: sol.nodes, str, tSolve: t1 - t0 };
  const fold = buildFold(P, sizes, sol.assign);
  const t2 = Date.now();
  const val = validate(P, fold, str.types);
  const t3 = Date.now();
  return { P, solvable: true, assign: sol.assign, given: !!sol.given, solverNodes: sol.nodes, str, fold, val, tSolve: t1 - t0, tFold: t2 - t1, tVal: t3 - t2 };
}
