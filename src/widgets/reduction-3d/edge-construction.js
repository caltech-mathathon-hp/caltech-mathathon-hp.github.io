/**
 * The construction of "Protein folding in the HP model on the cubic lattice is NP-complete: a short
 * proof", executed: the string S for an instance of EXACT PACKING (Section 3) and the perfect fold
 * of S built from a packing (Section 5, Table 1). The instance is encoded on a single edge of the
 * cube, the shelf E* = {(x, 0, 0)}: separators sigma_j cut it into bins of B nodes, and the items are
 * intervals of the shelf.
 *
 * Coordinates are the paper's: Q = {0..N}^3 is the cube, N = n - 1; -e_y is "down", (x, -1, 0) is
 * below and (x, 0, -1) in front of the shelf node (x, 0, 0).
 *
 * Plain JavaScript without DOM or three.js, so it also runs in Node:
 *   const res = build(3, 2, [2, 1, 2, 1]);   // m bins of size B, items; res.fold, res.val.checks, ...
 *
 * The fold object has the same shape as the one of construction.js (Berger and Leighton), so the
 * same viewer shows both: N, X, Y, Z, TY (1 = H), SG (segment of each letter), CAT (colour class),
 * segs [{ key, label, cat, start, end, ... }].
 */
import { solveBinPacking, validate as validateFold } from './construction.js';

export { solveBinPacking };

// colour classes of the H's, as indices into the viewer's palettes (shared with construction.js):
// the core is coloured like an interior, the runs on edges like edges, the separators like walls,
// and the items (the added one too) by item
export const CAT = { P: 0, core: 8, A: 1, F1: 3, F2: 10, sep: 9, item: 13 };

// ---------------------------------------------------------------- instance and normalisation
// Section 3: multiply B and all sizes by 6; if m is even, add one item of size B and make m odd.
export function normalise(m, B, sizes) {
  const a = sizes.map((s) => 6 * s);
  const itemOf = sizes.map((_, u) => u); // normalised item -> original item (-1: the added one)
  let mm = m, BB = 6 * B, added = false;
  if (m % 2 === 0) { a.push(BB); itemOf.push(-1); mm = m + 1; added = true; }
  return { m: mm, B: BB, a, itemOf, added, orig: { m, B, sizes: sizes.slice() } };
}

export function params(m, B, sizes) {
  const nz = normalise(m, B, sizes);
  const n = nz.m * (nz.B + 1) + 3, N = n - 1, k = nz.a.length;
  return { n, N, N0: n ** 3 - 12 * n + 16, lambda: 4 * n + 2 * k, k, m: nz.m, B: nz.B, nz, K: m, origB: B };
}

export function checkInstance(m, B, sizes) {
  const errs = [];
  if (!(Number.isInteger(m) && m >= 1)) errs.push('the number of bins must be a positive integer');
  if (!(Number.isInteger(B) && B >= 1)) errs.push('the bin size must be a positive integer');
  if (!sizes.length) errs.push('need at least one item');
  sizes.forEach((s, i) => { if (!(Number.isInteger(s) && s > 0)) errs.push(`item ${i + 1}: size must be a positive integer`); });
  const sum = sizes.reduce((x, y) => x + y, 0);
  if (!errs.length && sum !== m * B) errs.push(`sizes must add up to m·B = ${m * B} (they add up to ${sum})`);
  if (errs.length) return { errs };
  return { errs, P: params(m, B, sizes) };
}

// ---------------------------------------------------------------- the string S (Section 3)
const dense = (out, r) => { out.push(1); for (let t = 1; t < r; t++) out.push(0, 0, 1); };
const ps = (out, k) => { for (let t = 0; t < k; t++) out.push(0); };

export function buildString(P) {
  const { n, N0, lambda, m, B, nz } = P;
  const out = [], factors = [];
  const fac = (key, fn) => { const s = out.length; fn(); factors.push({ key, start: s, end: out.length }); };
  fac('core', () => { for (let t = 0; t < N0; t++) out.push(1); });
  fac('pp', () => ps(out, 2));
  fac('A', () => dense(out, 9 * n - 10));
  fac('link0', () => ps(out, lambda));
  fac('F1', () => dense(out, n - 2));
  fac('teth1', () => ps(out, n));
  fac('seps', () => { out.push(1); for (let j = 0; j < m; j++) { ps(out, B + 6); out.push(1); } });
  fac('teth2', () => ps(out, n));
  fac('F2', () => dense(out, n - 2));
  fac('items', () => { for (const a of nz.a) { ps(out, lambda); dense(out, a); } ps(out, 1); });
  return { types: Uint8Array.from(out), factors };
}

// ---------------------------------------------------------------- the fold (Section 5, Table 1)
const OFF = 4096, SP = 8192;
const key = (x, y, z) => ((x + OFF) * SP + (y + OFF)) * SP + (z + OFF);
const NORMALS = [[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]];
const same = (a, b) => a[0] === b[0] && a[1] === b[1] && a[2] === b[2];
const add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];

// Lemma 14: a Hamiltonian path of Q minus the skeleton from (1,0,N-1) to (1,N,N-1), layer by layer
function corePath(N) {
  // Delta: Hamiltonian cycle of [1,N-1]^2 in (x, z)
  const delta = [];
  for (let x = 1; x <= N - 1; x++) delta.push([x, 1]);
  for (let c = 0; c < N - 1; c++) {
    const x = N - 1 - c;
    if (c % 2 === 0) for (let z = 2; z <= N - 1; z++) delta.push([x, z]);
    else for (let z = N - 1; z >= 2; z--) delta.push([x, z]);
  }
  // Gamma: Hamiltonian cycle of [0,N]^2 without its corners
  const g0 = [];
  for (let z = 0; z <= N; z++) g0.push([1, z]);
  for (let c = 0; c < N - 3; c++) {
    const x = 2 + c;
    if (c % 2 === 0) for (let z = N; z >= 1; z--) g0.push([x, z]);
    else for (let z = 1; z <= N; z++) g0.push([x, z]);
  }
  for (let z = N; z >= 0; z--) g0.push([N - 1, z]);
  for (let x = N - 2; x >= 2; x--) g0.push([x, 0]);
  const gamma = [];
  for (let i = 0; i < g0.length; i++) {
    const [x, z] = g0[i];
    gamma.push([x, z]);
    const nx = g0[(i + 1) % g0.length];
    // detours through (0, z), (0, z+1) on column 1 (upwards) and (N, z+1), (N, z) on column N-1 (downwards)
    if (x === 1 && nx[0] === 1 && nx[1] === z + 1 && z % 2 === 1 && z <= N - 2) gamma.push([0, z], [0, z + 1]);
    if (x === N - 1 && nx[0] === N - 1 && nx[1] === z - 1 && (z - 1) % 2 === 1 && z - 1 <= N - 2) gamma.push([N, z], [N, z - 1]);
  }
  // walk a cycle from `from` to its neighbour `to` the long way round (without the edge from-to)
  const walk = (cyc, from, to) => {
    const i = cyc.findIndex((c) => c[0] === from[0] && c[1] === from[1]);
    const L = cyc.length, nxt = cyc[(i + 1) % L];
    const dir = nxt[0] === to[0] && nxt[1] === to[1] ? -1 : 1;
    const out = [];
    for (let t = 0; t < L; t++) out.push(cyc[(i + dir * t + L * 2) % L]);
    if (!(out[L - 1][0] === to[0] && out[L - 1][1] === to[1])) throw new Error('core: cycle does not contain the edge');
    return out;
  };
  const p = [2, N - 1], r = [1, N - 1], pp = [2, N];
  const cells = [];
  for (const [x, z] of walk(delta, r, p)) cells.push([x, 0, z]);
  for (let y = 1; y < N; y++) {
    const seq = y % 2 ? walk(gamma, p, pp) : walk(gamma, pp, p);
    for (const [x, z] of seq) cells.push([x, y, z]);
  }
  for (const [x, z] of walk(delta, p, r)) cells.push([x, N, z]);
  return cells;
}

export function buildFold(P, classes) {
  const { n, N, lambda, m, B, nz } = P;
  const inQ = (c) => c[0] >= 0 && c[1] >= 0 && c[2] >= 0 && c[0] <= N && c[1] <= N && c[2] <= N;
  const normals = (u) => NORMALS.filter((d) => !inQ(add(u, d)));

  let cap = 1 << 16, Nn = 0;
  let X = new Int32Array(cap), Y = new Int32Array(cap), Z = new Int32Array(cap), TY = new Uint8Array(cap), SG = new Uint16Array(cap), CA = new Uint8Array(cap);
  const occ = new Map();
  const segs = [];
  let curSeg = 0, curCat = 0;
  const grow = () => {
    cap *= 2;
    const g = (A, C) => { const b = new C(cap); b.set(A); return b; };
    X = g(X, Int32Array); Y = g(Y, Int32Array); Z = g(Z, Int32Array); TY = g(TY, Uint8Array); SG = g(SG, Uint16Array); CA = g(CA, Uint8Array);
  };
  const fail = (msg) => { throw new Error(`[edge fold] ${msg} (letter ${Nn}, piece ${segs.length ? segs[segs.length - 1].key : '-'})`); };
  const put = (t, c) => {
    if (Nn > 0 && Math.abs(c[0] - X[Nn - 1]) + Math.abs(c[1] - Y[Nn - 1]) + Math.abs(c[2] - Z[Nn - 1]) !== 1) fail(`not adjacent: (${c}) after (${X[Nn - 1]},${Y[Nn - 1]},${Z[Nn - 1]})`);
    const k = key(...c);
    if (occ.has(k)) fail(`site (${c}) used twice`);
    if (t === 1 && !inQ(c)) fail(`H outside the cube at (${c})`);
    if (t === 0 && inQ(c)) fail(`P inside the cube at (${c})`);
    if (Nn === cap) grow();
    X[Nn] = c[0]; Y[Nn] = c[1]; Z[Nn] = c[2]; TY[Nn] = t; SG[Nn] = curSeg; CA[Nn] = t ? curCat : 0;
    occ.set(k, Nn); Nn++;
  };
  const H = (c) => put(1, c), Pp = (c) => put(0, c);
  const seg = (k, label, cat, fn, extra) => {
    curSeg = segs.length; curCat = cat;
    const s = { key: k, label, cat, start: Nn, end: Nn, ...(extra || {}) };
    segs.push(s); fn(); s.end = Nn;
    return s;
  };

  // Lemma 13: lay a dense run on the path us; the P before it sits at us[0] + nu0 (placed by the
  // previous piece), the one after it must sit at us[r-1] + nuLast (placed by the next piece)
  const denseRun = (us, nu0, nuLast) => {
    const r = us.length;
    // allowed normals of the links t = 1..r-1 (between us[t-1] and us[t]) and of the last P
    const allow = [];
    for (let t = 1; t < r; t++) {
      const A = normals(us[t - 1]), Bn = normals(us[t]);
      allow.push(A.filter((d) => Bn.some((e) => same(d, e)) && !occ.has(key(...add(us[t - 1], d))) && !occ.has(key(...add(us[t], d)))));
    }
    allow.push([nuLast]);
    // backward feasibility, then a forward choice
    const L = allow.length, ok = allow.map((a) => a.map(() => false));
    ok[L - 1] = allow[L - 1].map(() => true);
    for (let t = L - 2; t >= 0; t--) ok[t] = allow[t].map((d) => allow[t + 1].some((e, j) => ok[t + 1][j] && !same(d, e)));
    const nus = [];
    let prev = nu0;
    for (let t = 0; t < L; t++) {
      const j = allow[t].findIndex((d, jj) => ok[t][jj] && !same(d, prev));
      if (j < 0) fail('no admissible normals for a dense run');
      nus.push(allow[t][j]); prev = allow[t][j];
    }
    for (let t = 0; t < r; t++) {
      H(us[t]);
      if (t < r - 1) { Pp(add(us[t], nus[t])); Pp(add(us[t + 1], nus[t])); }
    }
  };
  const line = (from, to) => { // inclusive straight segment
    const d = [Math.sign(to[0] - from[0]), Math.sign(to[1] - from[1]), Math.sign(to[2] - from[2])];
    const len = Math.abs(to[0] - from[0]) + Math.abs(to[1] - from[1]) + Math.abs(to[2] - from[2]);
    const out = [];
    for (let t = 0; t <= len; t++) out.push([from[0] + d[0] * t, from[1] + d[1] * t, from[2] + d[2] * t]);
    return out;
  };
  const path = (...pts) => { const out = [pts[0]]; for (let i = 1; i < pts.length; i++) out.push(...line(pts[i - 1], pts[i]).slice(1)); return out; };

  // separators and bins on the shelf
  const xs = []; for (let j = 1; j <= m + 1; j++) xs.push(1 + (j - 1) * (B + 1));
  const beta = (x) => [x, -1, 0], gamma = (x) => [x, 0, -1];
  // place the items of every class: class j odd runs -x from x_{j+1}-1, class j even +x from x_j+1
  const place = new Array(nz.a.length);
  const bins = [];
  for (let j = 1; j <= m; j++) {
    const cls = classes[j - 1];
    const odd = j % 2 === 1;
    let cur = odd ? xs[j] - 1 : xs[j - 1] + 1;
    const contents = [];
    for (const i of cls) {
      const a = nz.a[i];
      const f = cur, l = odd ? cur - a + 1 : cur + a - 1;
      place[i] = { f, l, cols: line([f, 0, 0], [l, 0, 0]) };
      cur = odd ? l - 1 : l + 1;
      contents.push(i);
    }
    bins.push({ j, x0: xs[j - 1] + 1, x1: xs[j] - 1, contents });
  }
  if (place.some((p) => !p)) fail('the classes do not cover all items');

  // The linkers (Routing Lemma 15): each goes straight down to a horizontal level of its own, runs
  // there and comes back up. The paper uses up the surplus length with a rectangle in front of the
  // cube; here it is folded into a flat meander under the cube, which keeps the picture compact.
  // The vertical legs of all linkers are reserved first, so that no level path crosses them.
  const reserved = new Set();
  const legCells = (p, Y) => { const out = []; for (let y = p[1] - 1; y >= Y; y--) out.push([p[0], y, p[2]]); return out; };
  const underCube = (x, z) => x >= 0 && x <= N && z >= 1 && z <= N;
  const levelRoute = (p, q, steps, Y, init, anchor, inR, name) => {
    const legP = legCells(p, Y), legQ = legCells(q, Y);
    const Lh = steps - legP.length - legQ.length;
    const pc = init.slice(); // [x, z] cells on level Y from below p to below q
    if (pc.length - 1 > Lh || (Lh - pc.length + 1) % 2) fail(`${name}: ${steps} steps cannot be routed`);
    const onPath = new Set(pc.map(([x, z]) => key(x, Y, z)));
    const free = (x, z) => inR(x, z) && !onPath.has(key(x, Y, z)) && !occ.has(key(x, Y, z)) && !reserved.has(key(x, Y, z));
    let len = pc.length - 1;
    while (len < Lh) {
      // widen the path by a bump of two cells next to one of its edges, as close to the anchor as possible
      let best = -1, bc = null, bs = Infinity;
      for (let t = 0; t + 1 < pc.length; t++) {
        const [ux, uz] = pc[t], [vx, vz] = pc[t + 1];
        const perp = ux === vx ? [[1, 0], [-1, 0]] : [[0, 1], [0, -1]];
        for (const [dx, dz] of perp) {
          const ax = ux + dx, az = uz + dz, bx = vx + dx, bz = vz + dz;
          if (!free(ax, az) || !free(bx, bz)) continue;
          const sc = (ax - anchor[0]) ** 2 + (az - anchor[1]) ** 2 + (bx - anchor[0]) ** 2 + (bz - anchor[1]) ** 2;
          if (sc < bs) { bs = sc; best = t; bc = [[ax, az], [bx, bz]]; }
        }
      }
      if (best < 0) fail(`${name}: no room to use up the surplus`);
      pc.splice(best + 1, 0, bc[0], bc[1]);
      onPath.add(key(bc[0][0], Y, bc[0][1])); onPath.add(key(bc[1][0], Y, bc[1][1]));
      len += 2;
    }
    const out = [p, ...legP];
    for (let t = 1; t + 1 < pc.length; t++) out.push([pc[t][0], Y, pc[t][1]]);
    for (let t = legQ.length - 1; t >= 0; t--) out.push(legQ[t]);
    out.push(q);
    return out;
  };
  const row = (x0, x1, z) => line([x0, 0, z], [x1, 0, z]).map((c) => [c[0], c[2]]);
  const col = (x, z0, z1) => line([x, 0, z0], [x, 0, z1]).map((c) => [c[0], c[2]]);
  const join = (...parts) => { const out = parts[0].slice(); for (let i = 1; i < parts.length; i++) out.push(...parts[i].slice(1)); return out; };
  // the item linkers: from p_i to q_i = beta(f_i) on level -2 - i (link0 has level -2)
  const ends = [];
  { let pp = [1, -1, N]; nz.a.forEach((_, i) => { const q = beta(place[i].f); ends.push({ p: pp, q, Y: -3 - i }); pp = beta(place[i].l); }); }
  for (const e of ends) for (const c of [...legCells(e.p, e.Y), ...legCells(e.q, e.Y)]) reserved.add(key(...c));
  const strings = [];

  // core H^N0
  seg('core', 'the core', CAT.core, () => { for (const c of corePath(N)) H(c); });
  seg('pp', 'PP', CAT.P, () => { Pp([1, N + 1, N - 1]); Pp([0, N + 1, N - 1]); });
  // A: through the eight corners, nine edges
  seg('A', 'the run A', CAT.A, () => denseRun(path([0, N, N - 1], [0, N, 0], [0, 0, 0], [0, 0, N], [0, N, N], [N, N, N], [N, 0, N], [N, 0, 0], [N, N, 0], [N, N, N - 1]), [0, 1, 0], [1, 0, 0]));
  // linker P^lambda from A to F1: the P after A, pi_0 (Routing Lemma, level -2), then two P's in front of F1
  seg('link0', 'the first linker', CAT.P, () => {
    Pp([N + 1, N, N - 1]);
    const L = lambda - 4, Y = -2;
    const init = join(row(N + 2, N - 1, N - 1), col(N - 1, N - 1, -3));
    const r = Math.sqrt(L - 2 * (N + 2)) / 2;
    const st = Nn;
    for (const c of levelRoute([N + 2, N, N - 1], [N - 1, N, -3], L, Y, init, [N - 1 - r, N - 1 - r], underCube, 'the first linker')) Pp(c);
    Pp([N - 1, N, -2]); Pp([N - 1, N, -1]);
    strings.push({ kind: 'link0', cat: CAT.F1, connStart: st - 1, connEnd: Nn, level: Y });
  }, { link: true, string: 0 });
  seg('F1', 'the run F1', CAT.F1, () => denseRun(path([N - 1, N, 0], [1, N, 0]), [0, 0, -1], [0, 0, -1]));
  seg('teth1', 'the tether down the front face', CAT.P, () => { for (let y = N; y >= 0; y--) Pp([1, y, -1]); });
  seg('seps', 'separators and inner tethers', CAT.sep, () => {
    for (let j = 1; j <= m + 1; j++) {
      H([xs[j - 1], 0, 0]);
      if (j === m + 1) break;
      const xa = xs[j - 1], xb = xs[j];
      Pp(beta(xa));
      for (let x = xa; x <= xb - 1; x++) Pp([x, -1, -1]);
      Pp([xb - 1, -1, -2]); Pp([xb, -1, -2]); Pp([xb, 0, -2]); Pp(gamma(xb));
    }
  });
  seg('teth2', 'the tether under the bottom face', CAT.P, () => { for (let z = 0; z <= N; z++) Pp([N - 1, -1, z]); });
  seg('F2', 'the run F2', CAT.F2, () => denseRun(path([N - 1, 0, N], [1, 0, N]), [0, -1, 0], [0, -1, 0]));
  // the items, each after its linker
  nz.a.forEach((a, i) => {
    const pl = place[i], e = ends[i], orig = nz.itemOf[i];
    // the added item gets the next item number, so that it has an item colour of its own
    const u = orig < 0 ? nz.orig.sizes.length : orig;
    const sg = seg('item', orig < 0 ? 'the added item' : `item u${orig + 1}`, CAT.item, () => {
      const st = Nn;
      const L = lambda - 1, Lh = L - 2 * (e.p[1] - e.Y);
      const init = e.p[2] === N ? join(col(e.p[0], N, 1), row(e.p[0], e.q[0], 1), col(e.q[0], 1, 0))
        : join(col(e.p[0], 0, 1), row(e.p[0], e.q[0], 1), col(e.q[0], 1, 0));
      const anchor = [(e.p[0] + e.q[0]) / 2, Math.min(N - 2, 2 + Math.sqrt(Lh) / 2)];
      for (const c of levelRoute(e.p, e.q, L, e.Y, init, anchor, underCube, `the linker before item ${i + 1}`)) Pp(c);
      strings.push({ kind: 'item', item: u, connStart: st, connEnd: Nn, level: e.Y });
      denseRun(pl.cols, [0, -1, 0], [0, -1, 0]);
      if (i === nz.a.length - 1) Pp(beta(pl.l));
    }, { item: u, added: orig < 0, nitem: i, fkey: 'item-' + i, size: a, bin: classOf(classes, i), f: pl.f, l: pl.l, level: e.Y, string: i + 1 });
    sg.connEnd = strings[i + 1].connEnd;
  });

  return {
    N: Nn, X: X.slice(0, Nn), Y: Y.slice(0, Nn), Z: Z.slice(0, Nn), TY: TY.slice(0, Nn), SG: SG.slice(0, Nn), CAT: CA.slice(0, Nn),
    segs, xs, bins, strings,
  };
}
const classOf = (classes, i) => classes.findIndex((c) => c.includes(i));

// ---------------------------------------------------------------- everything at once
// `given` (optional): assign[u] = bin of the original item u, filling every bin exactly
export function build(m, B, sizes, given) {
  const chk = checkInstance(m, B, sizes);
  if (chk.errs.length) return { error: chk.errs.join('; ') };
  const P = chk.P;
  const t0 = Date.now();
  let sol;
  if (given) {
    const load = new Array(m).fill(0);
    given.forEach((b, u) => { load[b] += sizes[u]; });
    if (given.length !== sizes.length || load.some((l) => l !== B)) return { error: 'the given packing does not fill every bin exactly' };
    sol = { assign: given.slice(), nodes: 0, given: true };
  } else sol = solveBinPacking(sizes, m, B);
  const t1 = Date.now();
  const str = buildString(P);
  if (!sol.assign) return { P, solvable: false, solverNodes: sol.nodes, str, tSolve: t1 - t0 };
  // classes of the normalised instance: the original bins, plus the added item alone
  const classes = Array.from({ length: P.m }, () => []);
  P.nz.itemOf.forEach((u, i) => { classes[u < 0 ? P.m - 1 : sol.assign[u]].push(i); });
  const fold = buildFold(P, classes);
  const t2 = Date.now();
  const val = validateFold({ n: P.n }, fold, str.types, { str: 'S (§3)', max: 'a perfect fold' });
  const t3 = Date.now();
  return { P, solvable: true, assign: sol.assign, given: !!sol.given, solverNodes: sol.nodes, str, fold, val, classes, tSolve: t1 - t0, tFold: t2 - t1, tVal: t3 - t2 };
}
