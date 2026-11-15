/**
 * The linkers, shared by "linkers" (steps 26–28) and the end of "forward" (step 36). The front
 * face is drawn as one row of beads at `ys` (labelled "front face", sub-line "its two holes end to
 * end"): its two holes laid end to end, with walls and rods beside them as in the face sketch of
 * steps 20–25. A few rows of the cube's H's below it ("inside the cube") fade out downwards. Above
 * the face is the space in front of the cube, where the linkers run.
 *
 * Linker k joins the end of item ribbon k to the start of item ribbon k + 1 (string order). It
 * leaves the face straight out (three P's), goes into the switchboard, comes out of its far side
 * at its own pair of gates, makes a loop, goes back through the switchboard and down into the
 * start of the next ribbon. The gates are the same for every packing: a packing changes only the
 * routes inside the switchboard and the size of the loops, never the linkers' length.
 *
 * Inside the switchboard a route is a line: up from its stub, along its own lane, up to its gate.
 * Where two routes cross, the one behind has a gap, as in a knot diagram: they pass at different
 * depths and never meet.
 *
 * Beads and sticks are drawn with Scene3D, face on at 44 px a step, as the face sketch draws them
 * (sticks behind the beads). The switchboard and its routes are SVG under the beads, the labels
 * SVG over them. The board is an SVG fragment: draw it inside a full-frame <svg> (the 3D layers sit
 * in foreignObjects).
 */
import React from 'react';
import * as M from '../../model/toy';
import type { V3 } from '../../model/toy';
import { C, FONT, itemColor } from '../../theme/theme';
import { clamp01, lerp } from '../../lib/anim';
import { Scene3D, R_RES, R_BOND, type Bead, type Stick, type Shot } from '../../three/Scene3D';
import { HOLE_COLOR } from '../../three/cube';

export type Pt = [number, number];

export const BOARD = {
  pitch: 44,
  /** the front face (its two holes end to end): the centres of its beads */
  ys: 620,
  /** x of the face row's first node; the row has `nRow` nodes */
  row0: 322,
  nRow: 30,
  /** the first node of hole 1 and of hole 2 in the row */
  holeAt: [3, 17],
  /** the wall pairs and the rods of the face row (node indices) */
  walls: [
    [1, 2],
    [13, 14],
    [15, 16],
    [27, 28],
  ],
  rods: [0, 29],
  /** how faded each row of the cube under the face is */
  below: [0.4, 0.62, 0.8],
  /** P's straight out of the face before the switchboard */
  out: 3,
  box: { x0: 404, x1: 1516, y0: 338, y1: 466 },
  /** left gate of each linker's pair, in string order; the right gate is one pitch further */
  gates: [586, 762, 938],
  /** centre of a loop's lowest P */
  loopY: 311,
  /** P's of a linker drawn straight out of the face (before the switchboard) */
  straight: 10,
};
const P = BOARD.pitch;
const YS = BOARD.ys;
export const HOLE_X = BOARD.holeAt.map((i) => BOARD.row0 + i * P);
/** the top of a stub: its third P */
const STUB_TOP = YS - BOARD.out * P;

// ---------------------------------------------------------------- the camera: face on, 44 px a step

const SHOT: Shot = { target: [0, 0, 0], dir: [0, 0, 1], dist: 1080 / (2 * Math.tan((15 * Math.PI) / 180) * P), offset: [0, 0] };
/** a screen point as a point of the 3D scene (the plane z = 0 is drawn at 44 px a step) */
const W3 = (p: Pt, z = 0): V3 => [(p[0] - 960) / P, (540 - p[1]) / P, z];

// ---------------------------------------------------------------- geometry

export interface Placed {
  u: number;
  hole: number;
  /** cell indices in the hole (0 = left), in string order */
  cells: number[];
}

/** where the items lie in the two holes for a packing (as in the model: from the left, even end first) */
export function placement(packing: number[][]): Placed[] {
  const ribbons = M.placeItems(M.SIZES, packing);
  return ribbons.map((cells, u) => {
    const hole = packing.findIndex((b) => b.includes(u));
    const idx = (cells ?? []).map((c) => M.strips[hole].hole.findIndex((h) => M.key(h) === M.key(c)));
    return { u, hole, cells: idx };
  });
}
/** the same items, each row moved whole into the other hole */
export const swapHoles = (pl: Placed[]): Placed[] => pl.map((p) => ({ ...p, hole: 1 - p.hole }));

export const cellPt = (hole: number, i: number): Pt => [HOLE_X[hole] + i * P, YS];
export const itemPts = (p: Placed): Pt[] => p.cells.map((i) => cellPt(p.hole, i));

export interface Route {
  k: number;
  /** the end of ribbon k and the start of ribbon k + 1 */
  a: Pt;
  b: Pt;
  /** the gates its two ends come out of, side by side */
  ga: number;
  gb: number;
  /** P's in each side of the loop: what the route through the switchboard leaves over */
  h: number;
  /** the lanes of its two halves in the switchboard (0 = the lowest) */
  lane: [number, number];
}

const permutations = (n: number): number[][] =>
  n === 0 ? [[]] : permutations(n - 1).flatMap((p) => Array.from({ length: n }, (_, i) => [...p.slice(0, i), n - 1, ...p.slice(i)]));
const PERMS6 = permutations(6);

/** the three linkers between the four item ribbons, for a placement */
export function routesOf(pl: Placed[]): Route[] {
  const rs = [0, 1, 2].map((k) => {
    const a = itemPts(pl[k]).at(-1)!;
    const b = itemPts(pl[k + 1])[0];
    let ga = BOARD.gates[k];
    let gb = ga + P;
    if (Math.abs(a[0] - gb) + Math.abs(b[0] - ga) < Math.abs(a[0] - ga) + Math.abs(b[0] - gb)) [ga, gb] = [gb, ga];
    const inside = Math.abs(a[0] - ga) + Math.abs(b[0] - gb);
    // the longer the way through the switchboard, the smaller the loop
    const h = Math.max(1, Math.min(5, Math.round(5 - (4 * (inside - 352)) / 616)));
    return { k, a, b, ga, gb, h, lane: [0, 0] as [number, number] };
  });
  // lanes: the order with the fewest crossings (each half: up at its low x, along its lane, up at its high x)
  const halves = rs.flatMap((r) => [
    { lo: r.a[0], hi: r.ga },
    { lo: r.b[0], hi: r.gb },
  ]);
  let best: number[] = PERMS6[0];
  let fewest = Infinity;
  for (const pm of PERMS6) {
    let n = 0;
    for (let i = 0; i < 6; i++)
      for (let j = 0; j < 6; j++) {
        if (i === j) continue;
        const x0 = Math.min(halves[j].lo, halves[j].hi);
        const x1 = Math.max(halves[j].lo, halves[j].hi);
        if (halves[i].lo > x0 && halves[i].lo < x1 && pm[j] < pm[i]) n++;
        if (halves[i].hi > x0 && halves[i].hi < x1 && pm[j] > pm[i]) n++;
      }
    if (n < fewest) {
      fewest = n;
      best = pm;
    }
  }
  rs.forEach((r, k) => (r.lane = [best[2 * k], best[2 * k + 1]]));
  return rs;
}
export const routes = (packing: number[][]): Route[] => routesOf(placement(packing));

const laneY = (lane: number) => {
  const { y0, y1 } = BOARD.box;
  return y1 - ((lane + 1) * (y1 - y0)) / 7;
};

/** one half of a route in the switchboard: from (x0, y0) up to its lane, along it, up to (x1, y1) */
interface Wire {
  from: Pt;
  to: Pt;
  y: number;
}
function wireD({ from: [x0, y0], to: [x1, y1], y }: Wire) {
  const dx = x1 - x0;
  const r = Math.min(12, Math.abs(dx) / 2);
  const s = Math.sign(dx) || 1;
  if (Math.abs(dx) < 1) return `M ${x0} ${y0} L ${x1} ${y1}`;
  // drawn from `from` to `to` whichever is lower, so that it grows in the direction it is laid
  return `M ${x0} ${y0} L ${x0} ${y + (y0 > y ? r : -r)} Q ${x0} ${y} ${x0 + s * r} ${y} L ${x1 - s * r} ${y} Q ${x1} ${y} ${x1} ${y + (y1 > y ? r : -r)} L ${x1} ${y1}`;
}
const wireLen = (w: Wire) => Math.abs(w.from[1] - w.y) + Math.abs(w.to[0] - w.from[0]) + Math.abs(w.to[1] - w.y);

/** the top of a route's loop (for labels) */
export const loopTop = (r: Route): Pt => [(r.ga + r.gb) / 2, BOARD.loopY - (r.h - 1) * P];

// ---------------------------------------------------------------- laying a chain of P's

/** a chain of nodes from an item's bead: P's joined by sticks, or by wires through the switchboard */
interface Chain {
  pts: Pt[];
  /** wire[i]: the step from node i − 1 to node i runs through the switchboard */
  wire: (Wire | null)[];
  /** bead[i]: node i is a P of the chain (node 0, and the item bead it may end on, are not) */
  bead: boolean[];
  /** 0: the stub out of ribbon k, 1: the wires and the loop, 2: the stub into ribbon k + 1 */
  part: number[];
}

function routeChain(r: Route, da: Pt, db: Pt): Chain {
  const { out, loopY } = BOARD;
  const pts: Pt[] = [];
  const wire: (Wire | null)[] = [];
  const bead: boolean[] = [];
  const part: number[] = [];
  const add = (p: Pt, b: boolean, pa: number, w: Wire | null = null) => {
    pts.push(p);
    bead.push(b);
    part.push(pa);
    wire.push(w);
  };
  const A = (p: Pt): Pt => [p[0] + da[0], p[1] + da[1]];
  const B = (p: Pt): Pt => [p[0] + db[0], p[1] + db[1]];
  add(A(r.a), false, 0);
  for (let k = 1; k <= out; k++) add(A([r.a[0], YS - k * P]), true, 0);
  const up: Wire = { from: A([r.a[0], STUB_TOP]), to: [r.ga, loopY], y: laneY(r.lane[0]) };
  add([r.ga, loopY], true, 1, up);
  for (let j = 1; j < r.h; j++) add([r.ga, loopY - j * P], true, 1);
  add([r.gb, loopY - (r.h - 1) * P], true, 1);
  for (let j = r.h - 2; j >= 0; j--) add([r.gb, loopY - j * P], true, 1);
  const down: Wire = { from: [r.gb, loopY], to: B([r.b[0], STUB_TOP]), y: laneY(r.lane[1]) };
  add(B([r.b[0], STUB_TOP]), true, 2, down);
  for (let k = out - 1; k >= 1; k--) add(B([r.b[0], YS - k * P]), true, 2);
  add(B(r.b), false, 2);
  return { pts, wire, bead, part };
}

function straightChain(a: Pt): Chain {
  const pts: Pt[] = [a];
  for (let k = 1; k <= BOARD.straight; k++) pts.push([a[0], YS - k * P]);
  return { pts, wire: pts.map(() => null), bead: pts.map((_, i) => i > 0), part: pts.map((_, i) => (i <= BOARD.out ? 0 : 1)) };
}

/**
 * Laying a chain, as every string in the video is laid: one tip, in string order. Each new P fades
 * in at its own node, at full size, over FADE frames; the next starts BEAD_DT frames later, so the
 * tip is a soft run of three or four P's. A stick is never stronger than the fainter of its two
 * beads. A wire through the switchboard is drawn from the P before it at about the beads' pace
 * (one pitch every BEAD_DT frames, so about 22 px a frame: WIRE_PACE is a little faster), never in
 * fewer than 10 frames, and the P at its far end fades in as it arrives.
 */
export const FADE = 7;
const BEAD_DT = 2;
const WIRE_PACE = 24;
const wireFrames = (w: Wire) => Math.min(36, Math.max(10, wireLen(w) / WIRE_PACE));

interface Plan {
  /** when the fade of node i starts (only for P's laid here) */
  start: number[];
  /** when the wire into node i is drawn, from … to */
  wire: ([number, number] | null)[];
  /** the last P's fade start, the last wire's end */
  lastBead: number;
  lastWire: number;
}
/** the natural timing (in frames) of laying nodes first + 1 … of a chain; nodes up to `first` and from `tail` on are there */
function plan(ch: Chain, first: number, tail: number): Plan {
  const n = ch.pts.length;
  const start: number[] = ch.pts.map(() => -Infinity);
  const wire: ([number, number] | null)[] = ch.pts.map(() => null);
  let t = 0;
  let lastBead = 0;
  let lastWire = 0;
  for (let i = first + 1; i < n && i <= tail; i++) {
    const w = ch.wire[i];
    if (w) {
      // a wire leaves a P once that P is half in
      if (i > first + 1) t += 2;
      const d = wireFrames(w);
      wire[i] = [t, t + d];
      lastWire = t + d;
      t += d - 3;
    }
    if (i === tail) break;
    if (ch.bead[i]) {
      start[i] = t;
      lastBead = t;
      t += BEAD_DT;
    }
  }
  return { start, wire, lastBead, lastWire };
}
/** frames a chain takes to lay at its natural pace */
const planFrames = (p: Plan) => Math.ceil(Math.max(p.lastBead + FADE, p.lastWire));

interface Laid {
  /** 0..1: how far node i has faded in (1 for what is there already, and for the item beads) */
  appear: number[];
  /** 0..1: how far the wire into node i is drawn */
  wire: number[];
}
const smooth = (t: number) => {
  const x = clamp01(t);
  return x * x * (3 - 2 * x);
};
/** lays a chain: `grow` 0..1 over `frames` frames (the natural pace stretched or squeezed to fit) */
function lay(ch: Chain, grow: number, frames: number, first: number, tail = ch.pts.length): Laid {
  const p = plan(ch, first, tail);
  const s = Math.min(p.lastBead > 0 ? (frames - FADE) / p.lastBead : Infinity, p.lastWire > 0 ? frames / p.lastWire : Infinity);
  const k = Number.isFinite(s) ? Math.max(0.05, s) : 1;
  const head = clamp01(grow) * frames;
  const appear = ch.pts.map((_, i) => {
    if (!ch.bead[i] || i <= first || i >= tail) return 1;
    return p.start[i] === -Infinity ? 0 : smooth((head - k * p.start[i]) / FADE);
  });
  const wire = ch.pts.map((_, i) => {
    const w = p.wire[i];
    if (!w) return 1;
    return clamp01((head - k * w[0]) / Math.max(1, k * (w[1] - w[0])));
  });
  return { appear, wire };
}

/** frames a route takes to lay at the natural pace (for scheduling routes one after the other) */
export function routeFrames(r: Route, opts: { fromStub?: boolean; toStub?: boolean } = {}): number {
  const ch = routeChain(r, [0, 0], [0, 0]);
  const n = ch.pts.length;
  return planFrames(plan(ch, opts.fromStub ? BOARD.out : 0, opts.toStub ? n - 1 - BOARD.out : n));
}
/** frames a straight linker takes to lay at the natural pace */
export const straightFrames = () => planFrames(plan(straightChain([0, 0]), 0, BOARD.straight + 1));

// ---------------------------------------------------------------- crossings of the routes

interface Seg {
  x0: number;
  y0: number;
  x1: number;
  y1: number;
}
/** a wire as straight pieces (its corners left out) */
function wireSegs(w: Wire): Seg[] {
  const [x0, y0] = w.from;
  const [x1, y1] = w.to;
  return [
    { x0, y0, x1: x0, y1: w.y },
    { x0, y0: w.y, x1, y1: w.y },
    { x0: x1, y0: w.y, x1, y1 },
  ];
}
export interface Crossing {
  x: number;
  y: number;
  /** the route behind */
  rear: number;
  front: number;
  /** the rear one runs across here (true) or up (false) */
  rearAcross: boolean;
}
/** the halves of the routes in drawing order: the one with the longer way across goes behind */
function wireOrder(ws: { w: Wire; k: number }[]) {
  return [...ws].sort((p, q) => Math.abs(q.w.to[0] - q.w.from[0]) - Math.abs(p.w.to[0] - p.w.from[0]));
}
function crossings(ws: { w: Wire; k: number }[]): Crossing[] {
  const order = wireOrder(ws);
  const out: Crossing[] = [];
  for (let i = 0; i < order.length; i++)
    for (let j = i + 1; j < order.length; j++) {
      for (const s of wireSegs(order[i].w))
        for (const t of wireSegs(order[j].w)) {
          const sv = s.x0 === s.x1;
          const tv = t.x0 === t.x1;
          if (sv === tv) continue;
          const v = sv ? s : t;
          const hz = sv ? t : s;
          const inX = v.x0 > Math.min(hz.x0, hz.x1) + 1 && v.x0 < Math.max(hz.x0, hz.x1) - 1;
          const inY = hz.y0 > Math.min(v.y0, v.y1) + 1 && hz.y0 < Math.max(v.y0, v.y1) - 1;
          if (inX && inY) out.push({ x: v.x0, y: hz.y0, rear: order[i].k, front: order[j].k, rearAcross: !sv });
        }
    }
  return out;
}

// ---------------------------------------------------------------- labels

type Style = { size: number; weight: number; color: string };
const NAME: Style = { size: 26, weight: 600, color: C.fg };
const SUB: Style = { size: 22, weight: 500, color: C.fgMuted };

function Text({ at, text, style = SUB, anchor = 'start', opacity = 1 }: { at: Pt; text: string; style?: Style; anchor?: 'start' | 'end' | 'middle'; opacity?: number }) {
  if (opacity <= 0) return null;
  return (
    <text x={at[0]} y={at[1]} textAnchor={anchor} fontFamily={FONT.sans} fontSize={style.size} fontWeight={style.weight} fill={style.color} opacity={opacity}>
      {text}
    </text>
  );
}
/** a label with a leader that ends just short of the thing it names */
function Leader({ from, to, opacity }: { from: Pt; to: Pt; opacity: number }) {
  if (opacity <= 0) return null;
  return <line x1={from[0]} y1={from[1]} x2={to[0]} y2={to[1]} stroke={C.fgSubtle} strokeWidth={2} strokeLinecap="round" opacity={opacity} />;
}

/** an item's number in the string: a disc in its colour with a white number (as in step 25) */
export function OrderDisc({ at, n, color, r = 17, opacity = 1 }: { at: Pt; n: number; color: string; r?: number; opacity?: number }) {
  if (opacity <= 0) return null;
  return (
    <g transform={`translate(${at[0]} ${at[1]})`} opacity={opacity}>
      <circle r={r + 2.5} fill={C.bgElev} />
      <circle r={r} fill={color} />
      <text y={r * 0.42} textAnchor="middle" fontFamily={FONT.sans} fontWeight={700} fontSize={r * 1.25} fill="#fff">
        {n}
      </text>
    </g>
  );
}

/** the text width of a label (Inter), roughly */
const textW = (s: string, size: number) => s.length * size * 0.53;

// ---------------------------------------------------------------- where an item's number goes

/**
 * Above the middle of the item, or beside it when a stub rises there (the 2 has a stub at both
 * ends). Chosen once, from the packing of step 26; the stubs move with their items.
 */
const BADGE_SIDE: number[] = (() => {
  const pl = placement(M.PACKING);
  const pts = pl.map(itemPts);
  const stubs = [0, 1, 2].flatMap((k) => [pts[k].at(-1)![0], pts[k + 1][0][0]]);
  return pts.map((ps) => {
    const xs = ps.map((p) => p[0]);
    const cands = [(Math.min(...xs) + Math.max(...xs)) / 2, Math.min(...xs) - P, Math.max(...xs) + P];
    const i = cands.findIndex((x) => stubs.every((sx) => Math.abs(sx - x) >= 40));
    return Math.max(0, i);
  });
})();
/** px between consecutive cells of an item as drawn (its beads are drawn to that scale) */
const spacing = (pts: Pt[]) => (pts.length < 2 ? P : Math.hypot(pts[1][0] - pts[0][0], pts[1][1] - pts[0][1]));
export function badgeAt(u: number, pts: Pt[]): { at: Pt; r: number } {
  const s = spacing(pts) / P;
  const xs = pts.map((p) => p[0]);
  const lo = Math.min(...xs);
  const hi = Math.max(...xs);
  const y = pts.reduce((a, p) => a + p[1], 0) / pts.length;
  const x = [(lo + hi) / 2, lo - P * s, hi + P * s][BADGE_SIDE[u]];
  return { at: [x, y - 46 * s], r: 17 * s };
}

// ---------------------------------------------------------------- the board

export interface StraightLinker {
  /** the end of the ribbon it leaves from */
  a: Pt;
  /** 0..1 laid, over `frames` frames */
  grow: number;
  frames?: number;
  /** 0..1: the P's above its first three fade out (when the switchboard comes) */
  topOut?: number;
  /** the item it has to reach ("to ②"), and how much the tag shows */
  to?: number;
  tag?: number;
}

export interface RouteDraw {
  r: Route;
  /** 0..1 laid, in string order, from the end of ribbon k */
  grow: number;
  /** frames that `grow` takes from 0 to 1 (new beads fade in over 6 frames or more) */
  frames?: number;
  /** the stub out of ribbon k is there already: laying starts at its top */
  fromStub?: boolean;
  /** the stub into ribbon k + 1 is there already: laying ends at its top */
  toStub?: boolean;
  /** 0..1: the wires and the loop fade out (the stubs stay) */
  bodyOut?: number;
  /** the two stubs carried along with their items (px) */
  da?: Pt;
  db?: Pt;
  /** 0..1: the linker we follow (the others step back) */
  glow?: number;
  /** 0..1: the whole linker fades out */
  out?: number;
}

export interface BoardItem {
  u: number;
  /** cell centres in string order; the beads are drawn to the scale of their spacing */
  pts: Pt[];
  /** the items' beads fade in and out together, as one layer (the first item's opacity) */
  opacity?: number;
  /** where its number in the string goes (default: above it) */
  badge?: { at: Pt; r: number };
}

export interface BoardProps {
  items: BoardItem[];
  /** the cube: the face row and the rows under it */
  band: number;
  lab?: {
    /** "hole 1", "hole 2" */
    holes?: number;
    /** "front face" and "its two holes end to end" */
    face?: number;
    /** "inside the cube" (the rows under the face) */
    cube?: number;
    /** "in front of the cube" */
    out?: number;
    /** "every node holds an H" */
    full?: number;
    /** "linker" and "all the same length" (straight linkers) */
    linker?: number;
    same?: number;
    switchboard?: number;
    /** "each line is a run of P’s" under "switchboard" (default: with "switchboard") */
    runs?: number;
    /** "routes cross at different depths", and "passes behind" at one crossing */
    depths?: number;
    /** on `hi`: "two ends side by side" and "loop: the P’s left over" */
    sides?: number;
    loop?: number;
    /** "626 P’s each" (step 36) */
    each?: number;
    eachText?: string;
    /** "the bins swapped": the same linkers, only rerouted */
    another?: number;
    /** the items' numbers in the string, and their key */
    order?: number;
  };
  straight?: StraightLinker[];
  routes?: RouteDraw[];
  /** the route the labels sides/loop point at */
  hi?: Route;
  box?: number;
}

/** fades combine: 0.5 then 0.5 is 0.75 */
const fq = (...fs: number[]) => 1 - fs.reduce((a, f) => a * (1 - clamp01(f)), 1);
const mix = (a: string, b: string, t: number) => {
  const pa = parseInt(a.slice(1), 16);
  const pb = parseInt(b.slice(1), 16);
  const ch = (v: number, s: number) => (v >> s) & 255;
  const m = (s: number) => Math.round(ch(pa, s) + (ch(pb, s) - ch(pa, s)) * clamp01(t));
  return `#${((m(16) << 16) | (m(8) << 8) | m(0)).toString(16).padStart(6, '0')}`;
};

const STICK_W = 2 * R_BOND * P;
/** how much the linkers we are not following step back */
const QUIET = 0.62;

/** a bead or stick faded all the way out is left out: faded beads are opaque discs of the background */
const seen = (x: { fade?: number }) => (x.fade ?? 0) < 0.995;

export function LinkerBoard({ items, band, lab = {}, straight = [], routes: rs = [], hi, box = 0 }: BoardProps) {
  const bx = BOARD.box;
  const beads: Bead[] = [];
  const sticks: Stick[] = [];
  /** where the linkers' P's are (for the labels to keep clear of) */
  const pBeads: Pt[] = [];
  const each = lab.each ?? 0;

  /** a P of a linker: it comes and goes by opacity, at full size; `dim` quiets it (it stays) */
  const pushP = (p: Pt, op: number, dim: number) => {
    if (op <= 0.004) return;
    beads.push({ pos: W3(p), color: C.p, hollow: true, fade: dim > 0.004 ? dim : undefined, opacity: op });
  };
  /** a stick, drawn only as far as its fainter bead (`op`); see-through below 1 */
  const pushStick = (a: Pt, b: Pt, op: number, dim: number) => {
    if (op <= 0.004) return;
    const f = 1 - (1 - dim) * op;
    sticks.push({ a: W3(a), b: W3(b), color: C.backbone, fade: f > 0.004 ? f : undefined });
  };
  const itemsO = items.length ? (items[0].opacity ?? 1) : 0;
  const itemAt = items.flatMap((it) => it.pts);

  // ---- the cube: the face row (walls, rods, the holes' empty nodes) and the rows under it
  if (band > 0.004) {
    // the cube comes in as one picture, by opacity; the rows under the face are quieter (dimmed)
    const o = (x: number) => (x < 0.996 ? x : undefined);
    const node = (i: number, y = YS): Pt => [BOARD.row0 + i * P, y];
    const inHole = (i: number) => BOARD.holeAt.some((h0) => i >= h0 && i < h0 + M.B);
    // an empty node goes as an item bead comes over it, so it never peeks out beside the bead
    const free = (p: Pt) => {
      const d = itemAt.reduce((m, q) => Math.min(m, Math.hypot(q[0] - p[0], q[1] - p[1])), Infinity);
      return 1 - itemsO * (1 - clamp01((d - 14) / 16));
    };
    for (let i = 0; i < BOARD.nRow; i++) {
      if (inHole(i)) {
        const v = band * free(node(i));
        if (v > 0.004) beads.push({ pos: W3(node(i), -0.02), color: HOLE_COLOR, r: R_RES * 0.4, opacity: o(v) });
      } else beads.push({ pos: W3(node(i)), color: C.h, opacity: o(band) });
    }
    for (const [i, j] of BOARD.walls) sticks.push({ a: W3(node(i)), b: W3(node(j)), color: C.backbone, fade: band < 0.996 ? 1 - band : undefined });
    BOARD.below.forEach((f0, k) => {
      for (let i = 0; i < BOARD.nRow; i++) beads.push({ pos: W3(node(i, YS + (k + 1) * P)), color: C.h, fade: f0, opacity: o(band) });
    });
  }

  // ---- the linker we follow: the others step back
  const emph = rs.map((d) => clamp01(d.glow ?? 0) * (1 - each));
  const top = Math.max(0, ...emph);
  const quiet = emph.map((e) => QUIET * Math.max(0, top - e));

  // ---- straight linkers (step 26)
  const tips: Pt[] = [];
  straight.forEach((st) => {
    const ch = straightChain(st.a);
    const L = lay(ch, st.grow, st.frames ?? 33, 0);
    const n = ch.pts.length;
    const op = ch.pts.map((_, i) => L.appear[i] * (ch.part[i] === 1 ? 1 - clamp01(st.topOut ?? 0) : 1));
    for (let i = 1; i < n; i++) {
      pushStick(ch.pts[i - 1], ch.pts[i], Math.min(op[i - 1], op[i]), 0);
      pushP(ch.pts[i], op[i], 0);
    }
    tips.push(ch.pts[n - 1]);
  });

  // ---- routes
  const wires: { w: Wire; k: number; t: number; color: string; width: number; o: number }[] = [];
  const drawn: { w: Wire; k: number }[] = [];
  rs.forEach((d, idx) => {
    if ((d.out ?? 0) >= 1) return;
    const ch = routeChain(d.r, d.da ?? [0, 0], d.db ?? [0, 0]);
    const n = ch.pts.length;
    const first = d.fromStub ? BOARD.out : 0;
    const tail = d.toStub ? n - 1 - BOARD.out : n;
    const L = lay(ch, d.grow, d.frames ?? 45, first, tail);
    const body = clamp01(d.bodyOut ?? 0);
    const gone = 1 - clamp01(d.out ?? 0);
    // removing: the wires and the loop (bodyOut) or the whole linker (out) fade out by opacity
    const op = ch.pts.map((_, i) => L.appear[i] * gone * (ch.part[i] === 1 ? 1 - body : 1));
    for (let i = 1; i < n; i++) {
      const w = ch.wire[i];
      if (w) {
        if (L.wire[i] > 0) {
          const e = emph[idx];
          const color = mix(mix(C.backbone, C.fg, 0.55 * e), C.bgElev, quiet[idx]);
          wires.push({ w, k: idx, t: L.wire[i], color, width: STICK_W + 2.6 * e, o: (1 - body) * gone });
          if (L.wire[i] >= 1 && body < 1) drawn.push({ w, k: d.r.k });
        }
      } else pushStick(ch.pts[i - 1], ch.pts[i], Math.min(op[i - 1], op[i]), quiet[idx]);
      if (ch.bead[i] && op[i] > 0.004) {
        pushP(ch.pts[i], op[i], quiet[idx]);
        pBeads.push(ch.pts[i]);
      }
    }
  });
  const order = wireOrder(wires.map((x) => ({ w: x.w, k: x.k }))).map((o) => wires.find((x) => x.w === o.w)!);
  const cross = crossings(drawn);

  // ---- the items: their own layer, so that they fade in and out as one, over whatever is under them
  const itemBeads: Bead[] = [];
  const itemSticks: Stick[] = [];
  for (const it of items) {
    const s = spacing(it.pts) / P;
    it.pts.forEach((p) => itemBeads.push({ pos: W3(p), color: itemColor(it.u), scale: s }));
    for (let i = 0; i + 1 < it.pts.length; i += 2) itemSticks.push({ a: W3(it.pts[i]), b: W3(it.pts[i + 1]), color: C.backbone, r: R_BOND * s });
  }

  // ---- labels
  const holeSpan = (h: number): [number, number] => [HOLE_X[h] - R_RES * P, HOLE_X[h] + (M.B - 1) * P + R_RES * P];
  const rowsBottom = YS + BOARD.below.length * P + R_RES * P;
  const LEFT = BOARD.row0 - 26;
  const tipY = YS - BOARD.straight * P;
  const hiRoute = hi;
  const passNote = (lab.depths ?? 0) > 0 ? pickCrossing(cross) : null;

  return (
    <g>
      {/* under the beads: the switchboard, the routes through it, the guide of the straight linkers */}
      <clipPath id="linker-board-inside">
        <rect x={bx.x0 + 1.5} y={bx.y0 + 1.5} width={bx.x1 - bx.x0 - 3} height={bx.y1 - bx.y0 - 3} rx={7} />
      </clipPath>
      {box > 0 && <rect x={bx.x0} y={bx.y0} width={bx.x1 - bx.x0} height={bx.y1 - bx.y0} rx={8} fill={C.bgElev} stroke={C.ruleStrong} strokeWidth={1.5} opacity={box} />}
      {order.map(({ w, t, color, width, o }, i) => (
        <g key={`w${i}`}>
          {/* a gap in every route behind this one */}
          <path d={wireD(w)} pathLength={1} strokeDasharray={`${t} 2`} fill="none" stroke={C.bgElev} strokeWidth={width + 12} strokeLinecap="butt" clipPath="url(#linker-board-inside)" opacity={o * box} />
          <path d={wireD(w)} pathLength={1} strokeDasharray={`${t} 2`} fill="none" stroke={color} strokeWidth={width} strokeLinecap="butt" strokeLinejoin="round" opacity={o} />
        </g>
      ))}
      {(lab.same ?? 0) > 0 && tips.length > 0 && (
        <line x1={Math.min(...tips.map((p) => p[0])) - 44} x2={Math.max(...tips.map((p) => p[0])) + 44} y1={tipY} y2={tipY} stroke={C.fgSubtle} strokeWidth={2} strokeDasharray="2 8" strokeLinecap="round" opacity={lab.same} />
      )}

      {/* the beads and sticks */}
      <foreignObject x={0} y={0} width={1920} height={1080}>
        <div style={{ position: 'absolute', left: 0, top: 0, width: 1920, height: 1080 }}>
          <Scene3D shot={SHOT} beads={beads.filter(seen)} sticks={sticks.filter(seen)} />
        </div>
      </foreignObject>
      <foreignObject x={0} y={0} width={1920} height={1080}>
        <div style={{ position: 'absolute', left: 0, top: 0, width: 1920, height: 1080, opacity: itemsO }}>
          <Scene3D shot={SHOT} beads={itemBeads} sticks={itemSticks} />
        </div>
      </foreignObject>

      {/* the cube's labels */}
      {/* not a true side view: the two holes, rows of different strips, are put end to end on one row */}
      <Text at={[LEFT, YS + 9]} text="front face" style={NAME} anchor="end" opacity={(lab.face ?? 0) * band} />
      <Text at={[LEFT, YS + 37]} text="its two holes end to end" anchor="end" opacity={(lab.face ?? 0) * band} />
      <Text at={[LEFT, YS + 2 * P + 21]} text="inside the cube" style={NAME} anchor="end" opacity={(lab.cube ?? 0) * band} />
      {[0, 1].map((h) => {
        const [x0, x1] = holeSpan(h);
        const o = (lab.holes ?? 0) * band;
        if (o <= 0) return null;
        const y = rowsBottom + 12;
        return (
          <g key={`h${h}`} opacity={o}>
            <path d={`M ${x0} ${y - 8} L ${x0} ${y} L ${x1} ${y} L ${x1} ${y - 8}`} fill="none" stroke={C.ruleStrong} strokeWidth={2} strokeLinejoin="round" />
            <Text at={[(x0 + x1) / 2, y + 32]} text={`hole ${h + 1}`} style={NAME} anchor="middle" />
          </g>
        );
      })}
      {(lab.full ?? 0) > 0 && (
        <g>
          <Text at={[BOARD.row0 + (BOARD.nRow - 1) * P + 34, YS + P + 4]} text="every node" opacity={lab.full} />
          <Text at={[BOARD.row0 + (BOARD.nRow - 1) * P + 34, YS + P + 30]} text="holds an H" opacity={lab.full} />
        </g>
      )}

      {/* in front of the cube */}
      {(lab.out ?? 0) > 0 && (
        <g opacity={(lab.out ?? 0) * band}>
          <line x1={LEFT + 4} y1={YS - 84} x2={LEFT + 4} y2={bx.y0 + 6} stroke={C.fgSubtle} strokeWidth={2} strokeLinecap="round" />
          <path d={`M ${LEFT - 4} ${bx.y0 + 18} L ${LEFT + 4} ${bx.y0 + 4} L ${LEFT + 12} ${bx.y0 + 18}`} fill="none" stroke={C.fgSubtle} strokeWidth={2} strokeLinecap="round" strokeLinejoin="round" />
          <Text at={[LEFT - 14, (YS - 84 + bx.y0) / 2 + 9]} text="in front of the cube" style={NAME} anchor="end" />
        </g>
      )}

      {/* the items' numbers in the string */}
      {(lab.order ?? 0) > 0 && (
        <g>
          {items.map((it) => {
            const b = it.badge ?? badgeAt(it.u, it.pts);
            return <OrderDisc key={`o${it.u}`} at={b.at} r={b.r} n={it.u + 1} color={itemColor(it.u)} opacity={(lab.order ?? 0) * itemsO} />;
          })}
          <Text at={[LEFT, YS - 46 + 8]} text="order in the string" anchor="end" opacity={(lab.order ?? 0) * band} />
        </g>
      )}

      {/* the straight linkers: "linker", "all the same length", "to ②" */}
      {straight.length > 0 && (
        <>
          {(lab.linker ?? 0) > 0 && (
            <g>
              <Leader from={[straight[0].a[0] - 74, YS - 5 * P]} to={[straight[0].a[0] - R_RES * P - 8, YS - 5 * P]} opacity={lab.linker ?? 0} />
              <Text at={[straight[0].a[0] - 84, YS - 5 * P + 9]} text="linker" style={NAME} anchor="end" opacity={lab.linker} />
            </g>
          )}
          <Text at={[Math.max(...tips.map((p) => p[0])) + 60, tipY + 8]} text="all the same length" opacity={lab.same ?? 0} />
          {straight.map((st, k) =>
            st.to !== undefined && (st.tag ?? 0) > 0 ? (
              <g key={`t${k}`} opacity={st.tag}>
                <Text at={[st.a[0] - 4, tipY - 44 + 8]} text="to" anchor="end" />
                <OrderDisc at={[st.a[0] + 17, tipY - 44]} r={15} n={st.to + 1} color={itemColor(st.to)} />
              </g>
            ) : null,
          )}
        </>
      )}

      {/* the switchboard */}
      {/* the name and its sub-lines keep their places from the start: nothing moves as a line comes in */}
      <Text at={[bx.x1 + 20, bx.y0 + 32]} text="switchboard" style={NAME} opacity={(lab.switchboard ?? 0) * box} />
      <Text at={[bx.x1 + 20, bx.y0 + 60]} text="each line is a run of P’s" opacity={(lab.runs ?? lab.switchboard ?? 0) * box} />
      <Text at={[bx.x1 + 20, bx.y0 + 92]} text="routes cross at" opacity={(lab.depths ?? 0) * box} />
      <Text at={[bx.x1 + 20, bx.y0 + 118]} text="different depths" opacity={(lab.depths ?? 0) * box} />
      {passNote && (
        <g opacity={(lab.depths ?? 0) * box}>
          <Leader from={passNote.from} to={passNote.to} opacity={1} />
          <Text at={passNote.text} text="passes behind" anchor={passNote.anchor} />
        </g>
      )}

      {/* the linker we follow */}
      {hiRoute && (
        <>
          {(lab.sides ?? 0) > 0 &&
            (() => {
              const x = Math.min(hiRoute.ga, hiRoute.gb) - R_RES * P - 8;
              const y = BOARD.loopY;
              return (
                <g>
                  <Leader from={[x - 44, y]} to={[x, y]} opacity={lab.sides ?? 0} />
                  <Text at={[x - 54, y + 8]} text="two ends side by side" anchor="end" opacity={lab.sides} />
                </g>
              );
            })()}
          {(lab.loop ?? 0) > 0 &&
            (() => {
              const [, ty] = loopTop(hiRoute);
              const x = Math.min(hiRoute.ga, hiRoute.gb) - R_RES * P - 8;
              return (
                <g>
                  <Leader from={[x - 44, ty]} to={[x, ty]} opacity={lab.loop ?? 0} />
                  <Text at={[x - 54, ty + 8]} text="loop: the P’s left over" anchor="end" opacity={lab.loop} />
                </g>
              );
            })()}
        </>
      )}
      {each > 0 && rs.length > 0 && (
        <Text at={[bx.x0 + 4, bx.y0 - 18]} text={lab.eachText ?? ''} opacity={each} />
      )}
      {(lab.another ?? 0) > 0 && (
        <g opacity={lab.another}>
          <Text at={[bx.x0, 150]} text="the bins swapped" style={NAME} />
          <Text at={[bx.x0, 180]} text="the same linkers, only rerouted" />
        </g>
      )}
    </g>
  );

  /**
   * A crossing to tie "passes behind" to, and where its label goes: in an empty part of the
   * switchboard or just outside it, with a short leader into the gap of the route behind. The
   * label and the leader keep clear of every route and every P; the shortest leader wins.
   */
  function pickCrossing(cs: Crossing[]) {
    const segs = drawn.flatMap((x) => wireSegs(x.w));
    const w = textW('passes behind', SUB.size);
    const segDist = (p: Pt, sg: Seg) => {
      const x = Math.min(Math.max(p[0], Math.min(sg.x0, sg.x1)), Math.max(sg.x0, sg.x1));
      const y = Math.min(Math.max(p[1], Math.min(sg.y0, sg.y1)), Math.max(sg.y0, sg.y1));
      return Math.hypot(p[0] - x, p[1] - y);
    };
    const free = (p: Pt, pad: number) => segs.every((sg) => segDist(p, sg) > STICK_W / 2 + pad) && pBeads.every((b) => Math.hypot(p[0] - b[0], p[1] - b[1]) > R_RES * P + pad);
    /** the label's box lies wholly inside the switchboard or wholly outside it */
    const placed = (x0: number, x1: number, y0: number, y1: number) =>
      (x0 > bx.x0 + 8 && x1 < bx.x1 - 8 && y0 > bx.y0 + 6 && y1 < bx.y1 - 6) || x1 < bx.x0 - 6 || x0 > bx.x1 + 6 || y1 < bx.y0 - 6 || y0 > bx.y1 + 6;
    let best: { from: Pt; to: Pt; text: Pt; anchor: 'end' | 'start'; len: number } | null = null;
    for (const c of cs.filter((c) => c.rearAcross))
      for (const ty of [c.y + 40, c.y + 54, c.y - 26, c.y - 40, bx.y0 - 18, bx.y1 + 38])
        for (const hs of [1, -1])
          for (const dx of [26, 40]) {
            const tx = c.x + hs * dx;
            const tx0 = hs > 0 ? tx : tx - w;
            if (tx0 < bx.x0 - 120 || tx0 + w > bx.x1) continue;
            if (!placed(tx0 - 4, tx0 + w + 4, ty - 18, ty + 6)) continue;
            const box8: Pt[] = [];
            for (let x = tx0 - 4; x <= tx0 + w + 4; x += 8) box8.push([x, ty - 18], [x, ty - 7], [x, ty + 5]);
            if (!box8.every((p) => free(p, 7))) continue;
            const v = ty < c.y ? -1 : 1;
            const from: Pt = [tx - hs * 7, ty - 7];
            const to: Pt = [c.x + hs * 11, c.y + v * 5];
            let ok = true;
            for (let t = 0; t <= 0.8 && ok; t += 0.05) ok = free([lerp(from[0], to[0], t), lerp(from[1], to[1], t)], 5);
            if (!ok) continue;
            const len = Math.hypot(to[0] - from[0], to[1] - from[1]);
            if (!best || len < best.len) best = { from, to, text: [tx, ty], anchor: hs > 0 ? 'start' : 'end', len };
          }
    return best;
  }
}
