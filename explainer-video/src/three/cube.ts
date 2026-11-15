/**
 * Beads and sticks of the toy cube (n = 12) for any stage of the construction.
 * A scene passes how far each piece has been laid (0..1, in string order) and gets back what to
 * draw. H's are the game's orange; on the front face, paddings are grey and items keep their
 * bin-packing colours, as in the site's proof figures.
 *
 * P's: every P of a perfect fold sits one step outside the cube, next to its H (that is the point
 * of the proof). Rods put a P on two outer sides of each H, ribbons one P on the outer side.
 */
import * as M from '../model/toy';
import type { V3 } from '../model/toy';
import { C, itemColor } from '../theme/theme';
import type { Bead, Stick, Shot, Solid, Project } from './Scene3D';
import { R_RES, R_BOND, GAME_DIR, yaw } from './Scene3D';
import { clamp01, easeBack } from '../lib/anim';

const add = (a: V3, b: V3): V3 => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
const sub = (a: V3, b: V3): V3 => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
const eq = (a: V3, b: V3) => a[0] === b[0] && a[1] === b[1] && a[2] === b[2];
const isUnit = (v: V3) => Math.abs(v[0]) + Math.abs(v[1]) + Math.abs(v[2]) === 1;

// ------------------------------------------------------------------ chains with their P's

export interface Letter {
  pos: V3;
  h: boolean;
}

/** a rod (PHP)^k along a path of lattice neighbours: each H gets P's on two outer sides */
export function rodChain(hs: V3[], lastNormal?: V3): Letter[] {
  if (!hs.length) return [];
  const opts = hs.map((h) => M.outsideNormals(h));
  // pick (u_i, w_i) with u_{i+1} = w_i, u_i ≠ w_i; backtracking over w
  const w: V3[] = [];
  const u: V3[] = [];
  const solve = (i: number, ui: V3): boolean => {
    for (const wi of opts[i]) {
      if (eq(wi, ui)) continue;
      if (i === hs.length - 1) {
        if (lastNormal && !eq(wi, lastNormal)) continue;
        u[i] = ui;
        w[i] = wi;
        return true;
      }
      if (!isUnit(sub(hs[i + 1], hs[i]))) continue;
      if (!opts[i + 1].some((o) => eq(o, wi))) continue;
      u[i] = ui;
      w[i] = wi;
      if (solve(i + 1, wi)) return true;
    }
    return false;
  };
  let ok = false;
  for (const u0 of opts[0]) if ((ok = solve(0, u0))) break;
  if (!ok) {
    // fall back: two outer sides each, not necessarily chained
    return hs.flatMap((h, i) => [
      { pos: add(h, opts[i][0]), h: false },
      { pos: h, h: true },
      { pos: add(h, opts[i][1] ?? opts[i][0]), h: false },
    ]);
  }
  return hs.flatMap((h, i) => [
    { pos: add(h, u[i]), h: false },
    { pos: h, h: true },
    { pos: add(h, w[i]), h: false },
  ]);
}

/** a ribbon (PHHP)^k along a path of surface nodes: each H has one P on its outer side */
export function ribbonChain(hs: V3[], normal?: V3): Letter[] {
  const out: Letter[] = [];
  for (let i = 0; i + 1 < hs.length; i += 2) {
    const a = hs[i];
    const b = hs[i + 1];
    const na = normal ?? M.outsideNormals(a)[0];
    const nb = normal ?? M.outsideNormals(b).find((x) => eq(x, na)) ?? M.outsideNormals(b)[0];
    out.push({ pos: add(a, na), h: false }, { pos: a, h: true }, { pos: b, h: true }, { pos: add(b, nb), h: false });
  }
  return out;
}

/** a run of H's (the core) */
export const hChain = (hs: V3[]): Letter[] => hs.map((pos) => ({ pos, h: true }));

// ------------------------------------------------------------------ the pieces

export interface PieceDef {
  id: string;
  kind: 'corner' | 'tenth' | 'face' | 'core' | 'wall-rod' | 'wall' | 'spaced' | 'padding' | 'item';
  index: number;
  letters: Letter[];
  /** colour of its H's */
  color: string;
  /** lies on the front face */
  front: boolean;
}

/** the core in a 3D snake order (a path of neighbours), from the back layer forwards */
const coreSnake: V3[] = (() => {
  const m = M.n - 2;
  const out: V3[] = [];
  let rowFlip = false;
  let layerFlip = false;
  for (let zi = 0; zi < m; zi++) {
    const z = -(m - zi);
    const ys = Array.from({ length: m }, (_, i) => (layerFlip ? m - i : i + 1));
    for (const y of ys) {
      const xs = Array.from({ length: m }, (_, i) => (rowFlip ? m - i : i + 1));
      for (const x of xs) out.push([x, y, z]);
      rowFlip = !rowFlip;
    }
    layerFlip = !layerFlip;
  }
  return out;
})();

export function framePieces(): PieceDef[] {
  const out: PieceDef[] = [];
  out.push({ id: 'corner', kind: 'corner', index: 0, letters: rodChain(M.cornerRod), color: C.h, front: false });
  out.push({ id: 'tenth', kind: 'tenth', index: 0, letters: rodChain(M.tenthRod), color: C.h, front: false });
  out.push({ id: 'core', kind: 'core', index: 0, letters: hChain(coreSnake), color: C.h, front: false });
  M.FACES.forEach((f, i) => out.push({ id: `face-${f.name}`, kind: 'face', index: i, letters: ribbonChain(f.nodes, f.normal), color: C.h, front: false }));
  return out;
}

/** the walls of the front face: per period its five pieces in string order, then the spaced rod */
export function wallPieces(): PieceDef[] {
  const out: PieceDef[] = [];
  for (const p of M.periods) {
    out.push({ id: `p${p.p}-q1`, kind: 'wall-rod', index: p.p, letters: rodChain(p.qRod1, [0, 0, 1]), color: C.h, front: true });
    out.push({ id: `p${p.p}-w1`, kind: 'wall', index: p.p, letters: ribbonChain(p.wall1, [0, 0, 1]), color: C.h, front: true });
    out.push({ id: `p${p.p}-q2`, kind: 'wall-rod', index: p.p, letters: rodChain(p.q2Rod, [0, 0, 1]), color: C.h, front: true });
    out.push({ id: `p${p.p}-w2`, kind: 'wall', index: p.p, letters: ribbonChain(p.wall2, [0, 0, 1]), color: C.h, front: true });
    out.push({ id: `p${p.p}-q3`, kind: 'wall-rod', index: p.p, letters: rodChain(p.qRod2, [0, 0, 1]), color: C.h, front: true });
  }
  out.push({
    id: 'spaced',
    kind: 'spaced',
    index: 0,
    letters: M.spacedRod.flatMap((h) => [
      { pos: add(h, [1, 0, 0]), h: false },
      { pos: h, h: true },
      { pos: add(h, [0, 0, 1]), h: false },
    ]),
    color: C.h,
    front: true,
  });
  return out;
}

export function itemPieces(sizes = M.SIZES, packing = M.PACKING): PieceDef[] {
  const { pieces } = M.itemPart(sizes, packing);
  return pieces.map((pc) => ({
    id: pc.kind === 'padding' ? `pad-${pc.index}` : `item-${pc.index}`,
    kind: pc.kind,
    index: pc.index,
    letters: ribbonChain(pc.cells, [0, 0, 1]),
    color: pc.kind === 'padding' ? C.pad : itemColor(pc.index),
    front: true,
  }));
}

// ------------------------------------------------------------------ drawing

export interface PieceStyle {
  /** 0..1, how much of the piece is laid, in string order */
  progress: number;
  /** 0..1, P's shown */
  ps?: number;
  /** 0..1, chain shown */
  chain?: number;
  /** 0..1, towards the background */
  fade?: number;
  /** override the colour of its H's */
  color?: string;
  /** move the whole piece (for flying items in) */
  offset?: V3;
  /** only H's, joined in pairs (dominoes): the face-on look, where P's would sit in front */
  dominoes?: boolean;
  /**
   * How a new bead comes in: 'fade' (the default) fades it in at nearly full size, so no bead is
   * ever a tiny speck; 'pop' scales it up from nothing with a small overshoot (no caller uses it:
   * new beads appear at full size); 'fill'
   * (for a fast fill like the core, laid in front of beads of its own colour) comes in at full
   * colour and 80% of its size and swells to full: a fading bead there would read as a pale P.
   */
  appear?: 'pop' | 'fade' | 'fill';
}

/** how many letters the "pop" of one bead spans, in letters */
const SOFT = 4;

export function drawPiece(piece: PieceDef, st: PieceStyle, beads: Bead[], sticks: Stick[]) {
  const L = piece.letters.length;
  if (st.progress <= 0 || !L) return;
  const color = st.color ?? piece.color;
  const ps = st.ps ?? 1;
  const chain = st.chain ?? 1;
  const fade = st.fade ?? 0;
  const off = st.offset ?? [0, 0, 0];
  const head = st.progress * (L + SOFT);
  const fadeIn = (st.appear ?? 'fade') === 'fade';
  const fill = st.appear === 'fill';
  const scaleAt = (i: number) => (fadeIn || fill ? clamp01((head - i) / SOFT) : easeBack(clamp01((head - i) / SOFT)));
  const P = (i: number): V3 => add(piece.letters[i].pos, off);
  // 'fade': a bead at s (0..1) of its way in is drawn at 0.9 + 0.1 s of its size, s of its colour
  // 'fill': at 0.8 + 0.2 s of its size, in full colour
  const look = (s: number, f: number) => (fadeIn ? { scale: 0.9 + 0.1 * s, fade: 1 - (1 - f) * s } : fill ? { scale: 0.8 + 0.2 * s, fade: f } : { scale: s, fade: f });
  for (let i = 0; i < L; i++) {
    const s = scaleAt(i);
    if (s <= 0) break;
    const l = piece.letters[i];
    if (l.h) beads.push({ pos: P(i), color, ...look(s, fade) });
    else if (ps > 0 && !st.dominoes) {
      const lk = look(s, fade);
      beads.push({ pos: P(i), color: C.p, hollow: true, scale: lk.scale * (fadeIn ? 1 : ps), fade: fadeIn ? 1 - (1 - lk.fade) * ps : lk.fade });
    }
  }
  if (chain <= 0) return;
  for (let i = 0; i + 1 < L; i++) {
    const a = piece.letters[i];
    const b = piece.letters[i + 1];
    if (!isUnit(sub(b.pos, a.pos))) continue;
    if (st.dominoes || ps <= 0) {
      if (!(a.h && b.h)) continue;
    }
    const grow = clamp01((head - i - 1) / SOFT);
    if (grow <= 0) break;
    sticks.push({ a: P(i), b: P(i + 1), color: C.backbone, grow, fade: Math.max(fade, 1 - chain) });
  }
}

/** faint points at lattice nodes (empty nodes of the front face, say) */
export function latticeDots(nodes: V3[], opacity = 1, r = 0.09): Bead[] {
  if (opacity <= 0) return [];
  return nodes.map((pos) => ({ pos, color: '#b9b4a8', r, fade: 1 - opacity }));
}

/**
 * An empty node that should be filled, like a hole in a strip: a small solid grey dot. (Hollow
 * beads mean P's and nothing else.)
 */
export const HOLE_COLOR = '#a9a397';
export function holeBeads(nodes: V3[], opacity = 1, color: string = HOLE_COLOR): Bead[] {
  if (opacity <= 0) return [];
  return nodes.map((pos) => ({ pos, color, r: R_RES * 0.4, fade: 1 - opacity }));
}

/**
 * The outline of the cube, half a step outside its outer nodes. Only the edges on the cube's
 * contour as the camera sees it are drawn; the other six would run across the beads in front of
 * or behind them. `inner` (0..1) draws those too, for a cube that is still empty (a wireframe).
 */
export function cubeOutline(opacity = 1, color: string = C.h, pad = 0.5, inner = 0): Stick[] {
  if (opacity <= 0) return [];
  const a = -pad;
  const b = M.n - 1 + pad;
  const z0 = pad;
  const z1 = -(M.n - 1) - pad;
  const c: V3[] = [
    [a, a, z0],
    [b, a, z0],
    [b, b, z0],
    [a, b, z0],
    [a, a, z1],
    [b, a, z1],
    [b, b, z1],
    [a, b, z1],
  ];
  const e = [
    [0, 1],
    [1, 2],
    [2, 3],
    [3, 0],
    [4, 5],
    [5, 6],
    [6, 7],
    [7, 4],
    [0, 4],
    [1, 5],
    [2, 6],
    [3, 7],
  ];
  const box = { min: c[4], max: c[2], inner };
  return e.map(([i, j]) => ({ a: c[i], b: c[j], color, r: 0.04, fade: 1 - opacity, box }));
}

/**
 * A block `inset` inside the surface layer, so that nothing behind the surface beads (the core,
 * the far faces) shows through their gaps. It has the background's colour: you never see it, only
 * the beads in front of it. (A coloured block showed its own edges between the beads, cutting rows
 * of beads in half.) Pass `color` only for a block that is meant to be seen.
 *   <Scene3D solids={[innerBlock()]} …/>   or   innerBlock({ opacity: t }) to cross-fade from core beads
 */
export function innerBlock(o: { inset?: number; color?: string; opacity?: number; fade?: number; soft?: number } = {}): Solid {
  const d = o.inset ?? 0.45;
  const m = M.n - 1;
  return { min: [d, d, -m + d], max: [m - d, m - d, -d], color: o.color ?? C.bg, opacity: o.opacity, fade: o.color ? o.fade : 1, soft: o.soft };
}

/** a translucent quad (Scene3D's `panels`) */
export interface Panel {
  corners: [V3, V3, V3, V3];
  color: string;
  opacity: number;
}

/**
 * The free edges' one look, from the frame scene to the walls: a soft band in the accent colour
 * along the edge's column of nodes, from corner node to corner node, as wide as a bead.
 *
 * It is drawn in SVG *under* the 3D picture (a scene puts it before its Scene3D; the canvas is
 * transparent), so every bead and stick covers it: it never tints a bead, whatever lies behind the
 * open front face. `y0`..`y1` (node rows, bottom up) give a part of it, e.g. one short rod's stretch.
 * Returns a line for `<line strokeWidth={w} strokeLinecap="butt">`.
 */
export const FREE_BAND = { opacity: 0.26, width: 2 * R_RES };
export function freeEdgeLine(project: Project, side: 0 | 1, y0 = 0, y1 = M.n - 1) {
  const x = side === 0 ? 0 : M.n - 1;
  const a = project([x, y0, 0]);
  const b = project([x, y1, 0]);
  const m = (y0 + y1) / 2;
  const u0 = project([x, m - 0.5, 0]);
  const u1 = project([x, m + 0.5, 0]);
  return { x1: a[0], y1: a[1], x2: b[0], y2: b[1], w: FREE_BAND.width * Math.hypot(u1[0] - u0[0], u1[1] - u0[1]) };
}

/** a pale H: the cube's body in flat drawings (the linkers' side view) */
export const BLOCK_COLOR = '#f1d3c6';

export const FRONT_NODES: V3[] = (() => {
  const out: V3[] = [];
  for (let x = 0; x < M.n; x++) for (let y = 0; y < M.n; y++) out.push([x, y, 0]);
  return out;
})();

/** the cube's surface, for `<Scene3D shell={CUBE_SHELL}>`: beads on faces turned away are not drawn */
export const CUBE_SHELL = { min: [0, 0, -(M.n - 1)] as V3, max: [M.n - 1, M.n - 1, 0] as V3 };

export const CUBE_CENTER: V3 = [(M.n - 1) / 2, (M.n - 1) / 2, -(M.n - 1) / 2];
export const FRONT_CENTER: V3 = [(M.n - 1) / 2, (M.n - 1) / 2, 0];

/**
 * Shared camera shots, so consecutive scenes cut without a jump.
 * FRAME_SHOT(t): the whole cube from the game's direction, turning slowly (t = 0..1 over the
 * "frame" scene); FRAME_SHOT(1) is where the "walls" scene starts.
 * FACE_SHOT: the front face seen straight on, a little above the screen centre so it clears the
 * captions. Use it for every face-on view (walls, padding of the example, items, read-off, no-fit).
 */
export const FRAME_SHOT = (t: number): Shot => ({
  target: [CUBE_CENTER[0], CUBE_CENTER[1] - 1.2, CUBE_CENTER[2]],
  dir: yaw(GAME_DIR, -14 + 28 * t),
  dist: 56,
});
export const FACE_SHOT: Shot = { target: [FRONT_CENTER[0], FRONT_CENTER[1] - 1.6, 0], dir: [0, 0, 1], dist: 40 };
export { R_RES, R_BOND };
