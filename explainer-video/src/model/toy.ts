/**
 * The worked example of the video: Berger and Leighton's construction for the bin packing puzzle
 * "items 6, 2, 8, 4 into two bins of 10" (the running example of the site's bin-packing game),
 * with one number turned down so that every node can be drawn.
 *
 * The recipe sets q = 2·max(K, ⌈B^(1/3)⌉) = 6 here, which gives n = 80. We take q = 2 instead:
 * the smallest q that still has q ≥ K, q even and T > 2B (so a padding fills more than half a
 * strip). Every other number follows the recipe: n = q(2q+1)+2 = 12, T = (2q−1)(n−2) = 30,
 * paddings of T − B = 20, linkers of 52n + 2 = 626 P's.
 *
 * World coordinates (three.js): x to the right, y up, z towards the viewer. The cube is
 * 0 ≤ x, y ≤ n−1 and −(n−1) ≤ z ≤ 0, so the front face is z = 0 and "in front of the cube" is
 * z > 0. Berger and Leighton's (i, j, k) is (x, y, −z), so the parity of a node is that of x+y+z.
 * On the front face, row r counts from the top: y = n − 1 − r.
 *
 * No DOM and no three.js here, so `node src/model/model.test.ts` checks it.
 */

export type V3 = [number, number, number];

// ---------- the puzzle ----------
export const SIZES = [6, 2, 8, 4];
export const K = 2;
export const B = 10;
/** a packing: bin 1 = {6, 4}, bin 2 = {2, 8} (item indices) */
export const PACKING = [
  [0, 3],
  [1, 2],
];
/** the instance with no packing, from the game's "three sixes" level */
export const NO_SIZES = [6, 6, 6, 2];

// ---------- the recipe ----------
export const recipe = (K: number, B: number, q = 2 * Math.max(K, Math.ceil(Math.cbrt(B) - 1e-9))) => {
  const n = q * (2 * q + 1) + 2;
  const T = (2 * q - 1) * (n - 2);
  return { q, n, T, pad: T - B, linker: 52 * n + 2, h: n ** 3, perfect: 3 * n * n * (n - 1) };
};
/** what the recipe gives for this puzzle: q = 6, n = 80 */
export const REAL = recipe(K, B);
/** the toy: q = 2, n = 12 */
export const TOY = recipe(K, B, 2);
export const n = TOY.n;
export const q = TOY.q;
export const T = TOY.T;
const N1 = n - 1;

export const key = ([x, y, z]: V3) => `${x},${y},${z}`;
export const isEven = ([x, y, z]: V3) => (((x + y + z) % 2) + 2) % 2 === 0;
const range = (a: number, b: number) => Array.from({ length: Math.max(0, b - a) }, (_, i) => a + i);
/** a front-face node from column c and row r (r = 0 is the top row) */
export const F = (c: number, r: number): V3 => [c, N1 - r, 0];

// ---------- the frame: everything but the front face ----------
/** corners: A B C D on top (A front-left), A' B' C' D' below them */
const A: V3 = [0, N1, 0];
const Bc: V3 = [N1, N1, 0];
const Cc: V3 = [N1, N1, -N1];
const D: V3 = [0, N1, -N1];
const A_: V3 = [0, 0, 0];
const B_: V3 = [N1, 0, 0];
const C_: V3 = [N1, 0, -N1];
const D_: V3 = [0, 0, -N1];

/** the n − 2 nodes strictly between two corners, from p towards r */
const between = (p: V3, r: V3): V3[] => {
  const d = [Math.sign(r[0] - p[0]), Math.sign(r[1] - p[1]), Math.sign(r[2] - p[2])];
  return range(1, n - 1).map((t) => [p[0] + d[0] * t, p[1] + d[1] * t, p[2] + d[2] * t] as V3);
};

/**
 * The corner rod, 9n − 10 lone H's in string order: an end run on edge CD, round the top face
 * D A B C, down C C', round the bottom face C' B' A' D', and an end run on edge D'C'. It covers
 * 9 edges and all 8 corners; the edges AA', BB' (the free edges of the front face) and DD' are left.
 */
export const cornerRod: V3[] = [
  ...between(Cc, D),
  D,
  ...between(D, A),
  A,
  ...between(A, Bc),
  Bc,
  ...between(Bc, Cc),
  Cc,
  ...between(Cc, C_),
  C_,
  ...between(C_, B_),
  B_,
  ...between(B_, A_),
  A_,
  ...between(A_, D_),
  D_,
  ...between(D_, C_),
];
/** the tenth-edge rod fills DD' */
export const tenthRod: V3[] = between(D, D_);
/** the two free edges: the left and right edges of the front face */
export const freeEdges: V3[][] = [between(A, A_), between(Bc, B_)];

export type FaceName = 'back' | 'left' | 'right' | 'top' | 'bottom';
/** the five faces the face ribbons fill, with their outward normals, in the order they are drawn */
export const FACES: { name: FaceName; normal: V3; nodes: V3[] }[] = (() => {
  const inner = range(1, n - 1);
  const faces: { name: FaceName; normal: V3; nodes: V3[] }[] = [
    { name: 'top', normal: [0, 1, 0], nodes: [] },
    { name: 'left', normal: [-1, 0, 0], nodes: [] },
    { name: 'back', normal: [0, 0, -1], nodes: [] },
    { name: 'right', normal: [1, 0, 0], nodes: [] },
    { name: 'bottom', normal: [0, -1, 0], nodes: [] },
  ];
  for (const a of inner)
    for (const b of inner) {
      faces[0].nodes.push([a, N1, -b]);
      faces[1].nodes.push([0, a, -b]);
      faces[2].nodes.push([a, b, -N1]);
      faces[3].nodes.push([N1, a, -b]);
      faces[4].nodes.push([a, 0, -b]);
    }
  // snake order (column by column, back and forth), as the face ribbons are folded
  for (const f of faces) f.nodes = snakeSort(f.nodes, f.normal);
  return faces;
})();

function snakeSort(nodes: V3[], normal: V3): V3[] {
  // two in-face axes
  const axes = [0, 1, 2].filter((a) => normal[a] === 0);
  const [u, v] = axes;
  const cols = new Map<number, V3[]>();
  for (const p of nodes) {
    const c = cols.get(p[u]) ?? [];
    c.push(p);
    cols.set(p[u], c);
  }
  const keys = [...cols.keys()].sort((a, b) => a - b);
  return keys.flatMap((k, i) => {
    const c = cols.get(k)!.sort((a, b) => a[v] - b[v]);
    return i % 2 ? c.reverse() : c;
  });
}

/** the core: every node inside the cube, layer by layer from the back */
export const core: V3[] = (() => {
  const out: V3[] = [];
  for (let z = -(n - 2); z <= -1; z++) for (const y of range(1, n - 1)) for (const x of range(1, n - 1)) out.push([x, y, z]);
  return out;
})();

// ---------- the front face: walls ----------
export interface Period {
  p: number;
  /** rows of its two walls */
  top: number;
  bottom: number;
  qRod1: V3[];
  wall1: V3[];
  q2Rod: V3[];
  wall2: V3[];
  qRod2: V3[];
  /** the spaced rod's H in this period */
  spaced: V3;
}

/**
 * One period per strip, as the site's wall figures draw it: a q-rod up the right free edge, a
 * wall right to left, a (2q+1)-rod down the left free edge, a wall left to right, a q-rod up.
 */
export const periods: Period[] = range(0, q).map((p) => {
  const t = 1 + (2 * q + 1) * p;
  const b = t + 2 * q;
  const cols = range(1, n - 1);
  return {
    p,
    top: t,
    bottom: b,
    qRod1: range(0, q).map((i) => F(N1, t + q - 1 - i)),
    wall1: [...cols].reverse().map((c) => F(c, t)),
    q2Rod: range(t, b + 1).map((r) => F(0, r)),
    wall2: cols.map((c) => F(c, b)),
    qRod2: range(0, q).map((i) => F(N1, b - i)),
    spaced: F(N1, t + q),
  };
});
/** the spaced rod's H's, in string order (its last H is odd, where the first linker starts) */
export const spacedRod: V3[] = [...periods].reverse().map((p) => p.spaced);

// ---------- the front face: strips, paddings, holes ----------
export interface Strip {
  s: number;
  /** its 2q − 1 rows */
  rows: number[];
  /** all T nodes, in snake order from its even corner */
  snake: V3[];
  /** the padding: the first T − B nodes of the snake */
  padding: V3[];
  /** the B nodes left, in a row, left to right */
  hole: V3[];
}

export const strips: Strip[] = periods.map((per) => {
  const rows = range(per.top + 1, per.bottom);
  const cols = range(1, n - 1);
  const first = F(1, rows[0]);
  const ltr = isEven(first);
  const snake = rows.flatMap((r, i) => {
    const forward = (i % 2 === 0) === ltr;
    return (forward ? cols : [...cols].reverse()).map((c) => F(c, r));
  });
  const pad = T - B;
  const padding = snake.slice(0, pad);
  const rest = snake.slice(pad);
  const hole = [...rest].sort((a, b) => a[0] - b[0]);
  return { s: per.p, rows, snake, padding, hole };
});

/**
 * Item ribbons on the front face for a packing: the items of bin b fill the hole of strip b from
 * the left, in the order listed. Each ribbon is returned in string order, starting on its even end.
 */
export function placeItems(sizes: number[], packing: number[][]): (V3[] | null)[] {
  const out: (V3[] | null)[] = sizes.map(() => null);
  packing.forEach((items, b) => {
    let x = 0;
    for (const u of items) {
      const cells = strips[b].hole.slice(x, x + sizes[u]);
      if (cells.length < sizes[u]) throw new Error(`bin ${b} overflows`);
      out[u] = isEven(cells[0]) ? cells : [...cells].reverse();
      x += sizes[u];
    }
  });
  return out;
}

/** the ribbons of the item part in string order: paddings, then items (no plugs, as q = K) */
export function itemPart(sizes: number[], packing: number[][]) {
  const items = placeItems(sizes, packing);
  const pieces: { kind: 'padding' | 'item'; index: number; cells: V3[] }[] = [
    ...strips.map((s) => ({ kind: 'padding' as const, index: s.s, cells: s.padding })),
    ...items.map((cells, u) => ({ kind: 'item' as const, index: u, cells: cells ?? [] })),
  ];
  /** linkers: from the end of the piece before (the spaced rod's last H for the first) to the start of each piece */
  const links = pieces.map((pc, i) => ({
    to: i,
    from: i === 0 ? spacedRod[spacedRod.length - 1] : pieces[i - 1].cells[pieces[i - 1].cells.length - 1],
    end: pc.cells[0],
  }));
  return { pieces, links };
}

// ---------- the string ----------
export type Origin = 'corner' | 'tenth' | 'face' | 'core' | 'wall-rod' | 'wall' | 'spaced' | 'padding' | 'plug' | 'linker' | 'item' | 'join';
export interface Seg {
  origin: Origin;
  /** H's in this piece (0 for runs of P) */
  h: number;
  /** letters in this piece */
  len: number;
  /** item index for 'item', strip for 'padding' */
  index?: number;
}

/**
 * The toy string piece by piece, following Fig. 3 of the paper with q = 2. Short runs of P's
 * between pieces are merged into 'join' segments.
 */
export function toyString(sizes = SIZES): Seg[] {
  const s: Seg[] = [];
  const rod = (origin: Origin, k: number) => s.push({ origin, h: k, len: 3 * k });
  const ribbon = (origin: Origin, k: number, index?: number) => s.push({ origin, h: k, len: 2 * k, index });
  const ps = (len: number, origin: Origin = 'join') => s.push({ origin, h: 0, len });
  const m = n - 2;
  rod('corner', 9 * n - 10);
  ribbon('face', m * m);
  rod('tenth', m);
  ps(4);
  for (let i = 0; i < 3; i++) {
    ribbon('face', m * m);
    ps(7);
  }
  ribbon('face', m * m - 2);
  s.push({ origin: 'core', h: m ** 3 + 2, len: m ** 3 + 3 });
  ps(8 + q);
  for (let p = 0; p < q; p++) {
    rod('wall-rod', q);
    ribbon('wall', m);
    rod('wall-rod', 2 * q + 1);
    ps(4);
    ribbon('wall', m);
    rod('wall-rod', q);
    ps(2 * q);
  }
  s.push({ origin: 'spaced', h: q, len: 2 + q + (q - 1) * (2 * q + 6) });
  for (let i = 0; i < q; i++) {
    ps(52 * n, 'linker');
    ribbon('padding', T - B, i);
  }
  for (let i = 0; i < q - K; i++) {
    ps(52 * n, 'linker');
    ribbon('plug', B, i);
  }
  sizes.forEach((sz, u) => {
    ps(52 * n, 'linker');
    ribbon('item', sz, u);
  });
  return s;
}

// ---------- every H of a perfect fold, with the piece it belongs to ----------
export type Piece = 'corner' | 'tenth' | 'face' | 'core' | 'wall-rod' | 'wall' | 'spaced' | 'padding' | 'item';
export interface HNode {
  pos: V3;
  piece: Piece;
  /** face index for 'face', period for wall pieces, strip for 'padding', item for 'item' */
  index: number;
  /** position within its piece, in string order */
  order: number;
}

export function perfectFold(sizes = SIZES, packing = PACKING): HNode[] {
  const out: HNode[] = [];
  const add = (cells: V3[], piece: Piece, index = 0) => cells.forEach((pos, order) => out.push({ pos, piece, index, order }));
  add(cornerRod, 'corner');
  add(tenthRod, 'tenth');
  FACES.forEach((f, i) => add(f.nodes, 'face', i));
  add(core, 'core');
  periods.forEach((p) => {
    add([...p.qRod1, ...p.q2Rod, ...p.qRod2], 'wall-rod', p.p);
    add([...p.wall1, ...p.wall2], 'wall', p.p);
  });
  add(spacedRod, 'spaced');
  strips.forEach((s) => add(s.padding, 'padding', s.s));
  placeItems(sizes, packing).forEach((cells, u) => cells && add(cells, 'item', u));
  return out;
}

/** the outside neighbours of a cube node (where P's can go) */
export function outsideNormals([x, y, z]: V3): V3[] {
  const out: V3[] = [];
  if (x === 0) out.push([-1, 0, 0]);
  if (x === N1) out.push([1, 0, 0]);
  if (y === 0) out.push([0, -1, 0]);
  if (y === N1) out.push([0, 1, 0]);
  if (z === 0) out.push([0, 0, 1]);
  if (z === -N1) out.push([0, 0, -1]);
  return out;
}
