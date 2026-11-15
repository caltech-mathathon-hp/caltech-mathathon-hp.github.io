/**
 * The linkers of the toy's item part, drawn as Berger and Leighton route them in spirit: each
 * linker leaves the front face straight out (a few P's), enters the switchboard (a slab in front
 * of the face; the routes inside are not drawn, except dashed for one highlighted linker), and out
 * of the box's far side the two ends of the linker meet in a loop, which uses up the P's left over.
 * The loops are drawn shortened: every linker has 52n + 2 = 626 P's.
 *
 * Linker k joins the end of ribbon k − 1 (the spaced rod's last H for k = 0) to the start of
 * ribbon k, in string order: paddings, then items (itemPart in toy.ts).
 */
import * as M from '../../model/toy';
import type { V3 } from '../../model/toy';
import { C } from '../../theme/theme';
import type { Draw } from './face';
import { clamp01, easeBack } from '../../lib/anim';
import { R_RES } from '../../three/Scene3D';

/** how far the P's go straight out before the switchboard (a clear gap between face and box) */
export const OUT = 5;
/** the switchboard: a slab in front of the face, covering every linker end */
export const BOX = { x0: -0.6, x1: M.n - 1 + 0.6, y0: 1.3, y1: M.n - 1.3, z0: OUT + 0.5, z1: OUT + 2.5 };
/** the loops stick out of the box's far side, this many steps long */
const LOOP_L = 3;
/** loop k's height on the far side: a staircase, so no loop hides another */
const loopY = (k: number) => 9.6 - 1.5 * k;

export interface Linker {
  k: number;
  from: V3;
  end: V3;
  /** the path in string order, from the H before it to the H after it */
  path: V3[];
  /** per path point: 'h' (a ribbon's H, not drawn here), 'p' (a P), 'gate' (where it crosses the box wall) */
  kind: ('h' | 'p' | 'gate')[];
  /** path indices of the hidden stretch inside the box: [gate in, gate out] for both crossings */
  inside: [number, number][];
  /** the far end of the loop (for labels) */
  tip: V3;
}

const { links } = M.itemPart(M.SIZES, M.PACKING);

export const LINKERS: Linker[] = links.map((l, k) => {
  const F = l.from;
  const E = l.end;
  // loop k takes columns 2k and 2k + 1: the two ends side by side
  const xa = 2 * k;
  const xb = xa + 1;
  const path: V3[] = [];
  const kind: Linker['kind'] = [];
  const push = (p: V3, t: 'h' | 'p' | 'gate') => {
    path.push(p);
    kind.push(t);
  };
  push(F, 'h');
  for (let z = 1; z <= OUT; z++) push([F[0], F[1], z], 'p');
  push([F[0], F[1], BOX.z0], 'gate');
  const in1 = path.length - 1;
  const y = loopY(k);
  push([xa, y, BOX.z1], 'gate');
  for (let i = 1; i <= LOOP_L; i++) push([xa, y, BOX.z1 + i], 'p');
  for (let i = LOOP_L; i >= 1; i--) push([xb, y, BOX.z1 + i], 'p');
  push([xb, y, BOX.z1], 'gate');
  const in2 = path.length - 1;
  push([E[0], E[1], BOX.z0], 'gate');
  for (let z = OUT; z >= 1; z--) push([E[0], E[1], z], 'p');
  push(E, 'h');
  return { k, from: F, end: E, path, kind, inside: [[in1, in1 + 1], [in2, in2 + 1]], tip: [(xa + xb) / 2, y, BOX.z1 + LOOP_L] };
});

export interface LinkerStyle {
  /** 0..1 per linker: how much is laid, in string order */
  grow: number[];
  /** index of a linker to highlight, and how strongly (0..1); the others fade */
  highlight?: number;
  hi?: number;
  /** fade all linkers towards the background */
  fade?: number;
}

const SOFT = 2.5;
/** the linkers are the subject of their views: their P's a little larger than the cube's beads */
const BIG = 1.2;
const STICK = 0.1;

/** P beads and backbone of the linkers (the inside of the box is drawn only for the highlighted one, dashed) */
export function drawLinkers(d: Draw, st: LinkerStyle) {
  const hi = st.hi ?? 0;
  LINKERS.forEach((L, k) => {
    const g = st.grow[k] ?? 0;
    if (g <= 0) return;
    const isHi = st.highlight === k;
    const fade = clamp01((st.fade ?? 0) + (isHi ? 0 : 0.62 * hi));
    const pc = isHi ? mix(C.p, C.accent, hi) : C.p;
    const bc = isHi ? mix(C.backbone, C.accent, hi) : C.backbone;
    const n = L.path.length;
    const head = g * (n - 1 + SOFT);
    const at = (i: number) => clamp01((head - i) / SOFT);
    for (let i = 0; i < n; i++) {
      if (L.kind[i] !== 'p') continue;
      const s = easeBack(at(i));
      if (s <= 0) continue;
      d.beads.push({ pos: L.path[i], color: pc, hollow: true, scale: s * BIG * (isHi ? 1 + 0.1 * hi : 1), fade });
    }
    for (let i = 0; i + 1 < n; i++) {
      const grow = clamp01((head - i - 1) / SOFT + 0.4);
      if (grow <= 0) continue;
      const inside = L.inside.some(([a, b]) => a === i && b === i + 1);
      if (inside) {
        if (isHi && hi > 0) d.sticks.push({ a: L.path[i], b: L.path[i + 1], color: C.accent, r: 0.09, dash: 1.6, grow: grow * hi, fade: 0.05 });
        continue;
      }
      d.sticks.push({ a: L.path[i], b: L.path[i + 1], color: bc, grow, fade, r: STICK + (isHi ? 0.03 * hi : 0) });
    }
  });
}

/** the switchboard: translucent faces and thin edges */
export function drawBox(d: Draw, opacity: number, color: string = C.p) {
  if (opacity <= 0) return;
  const { x0, x1, y0, y1, z0, z1 } = BOX;
  const v = (x: number, y: number, z: number): V3 => [x, y, z];
  const faces: [V3, V3, V3, V3][] = [
    [v(x0, y0, z0), v(x1, y0, z0), v(x1, y1, z0), v(x0, y1, z0)],
    [v(x0, y0, z1), v(x1, y0, z1), v(x1, y1, z1), v(x0, y1, z1)],
    [v(x0, y0, z0), v(x0, y0, z1), v(x0, y1, z1), v(x0, y1, z0)],
    [v(x1, y0, z0), v(x1, y0, z1), v(x1, y1, z1), v(x1, y1, z0)],
    [v(x0, y1, z0), v(x1, y1, z0), v(x1, y1, z1), v(x0, y1, z1)],
    [v(x0, y0, z0), v(x1, y0, z0), v(x1, y0, z1), v(x0, y0, z1)],
  ];
  for (const c of faces) d.panels.push({ corners: c, color, opacity: 0.09 * opacity });
  const corners = [v(x0, y0, z0), v(x1, y0, z0), v(x1, y1, z0), v(x0, y1, z0), v(x0, y0, z1), v(x1, y0, z1), v(x1, y1, z1), v(x0, y1, z1)];
  const e = [
    [0, 1], [1, 2], [2, 3], [3, 0], [4, 5], [5, 6], [6, 7], [7, 4], [0, 4], [1, 5], [2, 6], [3, 7],
  ];
  for (const [i, j] of e) d.lines.push({ a: corners[i], b: corners[j], color, r: 0.05, fade: 1 - 0.9 * opacity });
}

/** a point above the box, for its label */
export const BOX_TOP: V3 = [(BOX.x0 + BOX.x1) / 2, BOX.y1, (BOX.z0 + BOX.z1) / 2];
/** the far-bottom-right corner of the box (for its label) */
export const BOX_FRONT: V3 = [BOX.x1, BOX.y0, BOX.z1];
export const BEAD_R = R_RES;

function mix(a: string, b: string, t: number) {
  const pa = parseInt(a.slice(1), 16);
  const pb = parseInt(b.slice(1), 16);
  const ch = (v: number, s: number) => (v >> s) & 255;
  const m = (s: number) => Math.round(ch(pa, s) + (ch(pb, s) - ch(pa, s)) * clamp01(t));
  return `#${((m(16) << 16) | (m(8) << 8) | m(0)).toString(16).padStart(6, '0')}`;
}
