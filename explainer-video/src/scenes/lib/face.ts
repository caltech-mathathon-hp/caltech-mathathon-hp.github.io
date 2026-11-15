/**
 * The front face at any stage, in the look the "frame" scene ends with, for the face-on scenes
 * (walls, forward, backward, no). Everything appends to the arrays a scene passes to Scene3D.
 *
 *   const d = newDraw();
 *   drawFrame(d, { backFade });        // rods, core, five faces (no P's, faces as dominoes)
 *   drawWalls(d, wallsProgress);       // both periods and the spaced rod, in string order
 *   drawPaddings(d, [p0, p1]);         // grey paddings snaking in
 *   drawRibbon(d, cells, color, prog); // an item ribbon on the face
 *   addHoles(d, { opacity, free });    // hollow beads on every front node still empty
 *   lines: faceOutline(backFade)
 *
 * backFade (0..1) fades everything behind the front face, for face-on views: seen straight on,
 * the core and the inner faces would show between the front beads and clutter the picture.
 */
import * as M from '../../model/toy';
import type { V3 } from '../../model/toy';
import { C } from '../../theme/theme';
import { quiet, type Bead, type Stick, type Project, type Solid } from '../../three/Scene3D';
import { framePieces, wallPieces, holeBeads, ribbonChain, innerBlock, HOLE_COLOR, type PieceDef, type PieceStyle } from '../../three/cube';
import { clamp01 } from '../../lib/anim';

export interface Draw {
  beads: Bead[];
  sticks: Stick[];
  lines: Stick[];
  panels: { corners: [V3, V3, V3, V3]; color: string; opacity: number }[];
  /** opaque boxes (the core as one block): pass to Scene3D's `solids` */
  solids: Solid[];
}
export const newDraw = (): Draw => ({ beads: [], sticks: [], lines: [], panels: [], solids: [] });

const N1 = M.n - 1;
const FRAME = framePieces();
const byId = Object.fromEntries(FRAME.map((p) => [p.id, p]));
export const FACE_ORDER = ['face-back', 'face-left', 'face-bottom', 'face-right', 'face-top'];
export const WALLS = wallPieces();

/** progress of each of `weights.length` pieces laid one after another, time shared by weight */
export function sequence(progress: number, weights: number[]): number[] {
  const total = weights.reduce((a, b) => a + b, 0);
  let acc = 0;
  return weights.map((w) => {
    const p = clamp01((progress * total - acc) / w);
    acc += w;
    return p;
  });
}
const hCount = (p: PieceDef) => p.letters.filter((l) => l.h).length;

/**
 * Split a drawing into the front face (z = 0) and what lies behind it, to fade the back as ONE
 * picture: draw `back` in its own Scene3D inside a div with CSS opacity 1 - backFade, and `front`
 * (with the lines and panels) in a second Scene3D on top (Forward does this). Fading bead by bead
 * instead (`drawFrame`'s `backFade`) lets each half-faded bead show the sticks behind it.
 */
export function splitBehind(d: Draw) {
  const isFront = (p: V3) => p[2] > -0.5; // on the face: z = 0, hole dots a hair behind; the cube: z ≤ −1
  const front = (s: Stick) => isFront(s.a) && isFront(s.b);
  return {
    front: { beads: d.beads.filter((b) => isFront(b.pos)), sticks: d.sticks.filter(front) },
    back: { beads: d.beads.filter((b) => !isFront(b.pos)), sticks: d.sticks.filter((s) => !front(s)) },
  };
}

/**
 * Fade what lies behind the front face (z < 0) by `backFade` (1 = gone). The beads go see-through
 * (`opacity`), never paler: a pale bead is an opaque disc that would hide what is behind it. The
 * sticks go first (gone by half way), so they do not show through the half-faded beads in front of
 * them; a stick is never stronger than its beads. (Fading the back as one picture, `splitBehind`,
 * looks better still.)
 */
function fadeBehind(d: Draw, from: { b: number; s: number }, backFade: number) {
  if (backFade <= 0) return;
  const keep = 1 - backFade;
  const keepStick = clamp01(2 * keep - 1);
  const keepB: Bead[] = d.beads.slice(0, from.b);
  for (const b of d.beads.slice(from.b)) {
    if (b.pos[2] > -0.5) keepB.push(b);
    else if (keep > 0.001) keepB.push({ ...b, opacity: (b.opacity ?? 1) * keep });
  }
  const keepS: Stick[] = d.sticks.slice(0, from.s);
  for (const s of d.sticks.slice(from.s)) {
    if (Math.min(s.a[2], s.b[2]) > -0.5) keepS.push(s);
    else if (keepStick > 0.001) keepS.push({ ...s, fade: 1 - (1 - (s.fade ?? 0)) * keepStick });
  }
  d.beads.length = 0;
  d.beads.push(...keepB);
  d.sticks.length = 0;
  d.sticks.push(...keepS);
}

/**
 * How `build` shares its time between the frame's pieces, in string order: corner rod, tenth rod,
 * core, then the faces in FACE_ORDER. A scene whose camera sees only some of them can pass its own
 * (the pieces still go in in this order).
 */
export const FRAME_WEIGHTS = [3, 1, 2.5, 1, 1, 1, 1, 1];

/**
 * The frame as the "frame" scene leaves it. `build` (0..1) lays it in string order, fast:
 * rod 1, rod 2, core, the five faces (for the example, which rebuilds it in a few seconds).
 * The core is one invisible filler block (d.solids, pass them to Scene3D), dropped once `backFade` starts.
 * `context` (0..1, FADE.context when the front face is the subject) quiets rods and faces.
 */
export function drawFrame(
  d: Draw,
  { build = 1, backFade = 0, context = 0, whole = false, weights = FRAME_WEIGHTS }: { build?: number; backFade?: number; context?: number; whole?: boolean; weights?: number[] } = {},
) {
  const mark = { b: d.beads.length, s: d.sticks.length };
  const [corner, tenth, core, ...faces] = sequence(build, weights);
  lay(byId.corner, corner, { ps: 0, chain: 0 }, d, { whole });
  lay(byId.tenth, tenth, { ps: 0, chain: 0 }, d, { whole });
  FACE_ORDER.forEach((id, i) => lay(byId[id], faces[i], { ps: 0, dominoes: true }, d, { whole }));
  if (context > 0) quietFrom(d, mark, context);
  // the core's filler goes as soon as the cube behind the face starts to fade: see-through sticks
  // do not write depth, so a filler drawn after them would paint over every stick in front of it
  // in one frame (the shell already hides the faces turned away, so nothing shows through instead)
  if (core > 0 && backFade <= 0) d.solids.push(innerBlock({ opacity: core < 1 ? core : undefined }));
  fadeBehind(d, mark, backFade);
}

/** quiet everything drawn since `from` by `amount` (FADE.context, …) */
export function quietFrom(d: Draw, from: { b: number; s: number }, amount: number) {
  if (amount <= 0) return;
  d.beads.splice(from.b, d.beads.length - from.b, ...quiet(d.beads.slice(from.b), amount));
  d.sticks.splice(from.s, d.sticks.length - from.s, ...quiet(d.sticks.slice(from.s), amount));
}
export const drawMark = (d: Draw) => ({ b: d.beads.length, s: d.sticks.length });

/**
 * The walls of both periods and the spaced rod, in string order (time shared by H count). Pass
 * `frames`, the frames `progress` takes from 0 to 1 (linear), and every bead fades in over 7 frames
 * or more: the soft tip is made as long as that needs.
 */
export function drawWalls(d: Draw, progress: number, opts: { color?: string; fade?: number; whole?: boolean; frames?: number } = {}) {
  const w = WALLS.map(hCount);
  const total = w.reduce((a, b) => a + b, 0);
  const ps = sequence(progress, w);
  WALLS.forEach((p, i) =>
    lay(p, ps[i], { ps: 0, chain: 1, dominoes: true, color: opts.color, fade: opts.fade }, d, { whole: opts.whole, soft: softFor(p.letters.length, opts.frames && (opts.frames * w[i]) / total) }),
  );
}
/** progress of each wall piece for a global walls progress (to time labels) */
export const wallProgress = (progress: number) => sequence(progress, WALLS.map(hCount));

/** the paddings of the two strips (grey), each in string order; `frames`: as in drawWalls, per padding */
export function drawPaddings(d: Draw, progress: number[], opts: { color?: string; fade?: number; frames?: number } = {}) {
  M.strips.forEach((s, i) => drawRibbon(d, s.padding, opts.color ?? C.pad, progress[i] ?? 0, { fade: opts.fade, frames: opts.frames }));
}

/**
 * A ribbon of H's on the front face (padding, item), face-on look: dominoes, no P's. `frames`: as
 * in drawWalls. `beadOpacity` instead sets each bead's opacity itself (k = its place in the
 * string), for a ribbon that comes in under something else (an item bar giving way to its beads).
 */
export function drawRibbon(d: Draw, cells: V3[], color: string, progress: number, opts: { fade?: number; offset?: V3; frames?: number; beadOpacity?: (k: number) => number } = {}) {
  if (progress <= 0 || !cells.length) return;
  const piece: PieceDef = { id: 'ribbon', kind: 'item', index: 0, letters: ribbonChain(cells, [0, 0, 1]), color, front: true };
  lay(piece, progress, { ps: 0, dominoes: true, fade: opts.fade, offset: opts.offset }, d, { soft: softFor(piece.letters.length, opts.frames), beadOpacity: opts.beadOpacity });
}

/** letters over which a new bead fades in (the soft tip), when the caller does not say how fast it lays */
const SOFT = 4;
/**
 * The soft tip, in letters, for a piece of `letters` letters laid over `frames` frames (linear), so
 * that each bead fades in over 7 frames or more.
 */
export const softFor = (letters: number, frames?: number) => (frames && frames > 8 ? Math.max(SOFT, (7 * letters) / (frames - 7)) : SOFT);

/**
 * Lay a piece `progress` (0..1) of the way, in string order. The string is one chain with one
 * growing tip. A new bead comes in at full size and fades in where it lies (`opacity`, see-through
 * on the way, so it never shows as a pale disc), over `soft` letters of the tip. A stick is never
 * stronger than the weaker of its two beads, so it comes in with them.
 * `whole`: when there is no time to lay it bead by bead, the piece fades in as a whole instead
 * (pieces laid one after another this way still go in string order).
 */
function lay(piece: PieceDef, progress: number, st: Omit<PieceStyle, 'progress' | 'appear'>, d: Draw, o: { whole?: boolean; soft?: number; beadOpacity?: (k: number) => number } = {}) {
  if (progress <= 0) return;
  const letters = piece.letters;
  const L = letters.length;
  if (!L) return;
  const S = o.soft ?? SOFT;
  const head = progress * (L + S);
  const color = st.color ?? piece.color;
  const fade = st.fade ?? 0;
  const off = st.offset ?? [0, 0, 0];
  const P = (i: number): V3 => [letters[i].pos[0] + off[0], letters[i].pos[1] + off[1], letters[i].pos[2] + off[2]];
  const showP = (st.ps ?? 1) > 0 && !st.dominoes;
  // each letter's opacity: the H's in string order, or the soft tip, or the whole piece at once
  const alpha: number[] = [];
  let k = 0;
  for (let i = 0; i < L; i++) alpha.push(o.beadOpacity && letters[i].h ? clamp01(o.beadOpacity(k++)) : o.whole ? clamp01(progress) : clamp01((head - i) / S));
  if (o.beadOpacity) {
    // a P takes the opacity of the H it hangs on
    for (let i = 0; i < L; i++) if (!letters[i].h) alpha[i] = Math.max(i > 0 && letters[i - 1].h ? alpha[i - 1] : 0, i + 1 < L && letters[i + 1].h ? alpha[i + 1] : 0);
  }
  for (let i = 0; i < L; i++) {
    const a = alpha[i];
    if (a <= 0.001) continue;
    const opacity = a < 0.999 ? a : undefined;
    if (letters[i].h) d.beads.push({ pos: P(i), color, fade: fade || undefined, opacity });
    else if (showP) d.beads.push({ pos: P(i), color: C.p, hollow: true, fade: fade || undefined, opacity: (opacity ?? 1) * (st.ps ?? 1) });
  }
  const chain = st.chain ?? 1;
  if (chain <= 0) return;
  for (let i = 0; i + 1 < L; i++) {
    const a = letters[i];
    const b = letters[i + 1];
    if (Math.abs(b.pos[0] - a.pos[0]) + Math.abs(b.pos[1] - a.pos[1]) + Math.abs(b.pos[2] - a.pos[2]) !== 1) continue;
    if (!(a.h && b.h) && !showP) continue;
    const m = Math.min(alpha[i], alpha[i + 1]) * chain;
    if (m <= 0.001) continue;
    const f = 1 - (1 - fade) * m;
    d.sticks.push({ a: P(i), b: P(i + 1), color: C.backbone, fade: f > 0.001 ? f : undefined });
  }
}

/** the nodes of the front face that must be filled (rows 1..n−2; rows 0 and n−1 belong to rod 1) */
export const FRONT_OPEN: V3[] = (() => {
  const out: V3[] = [];
  for (let y = 1; y < N1; y++) for (let x = 0; x <= N1; x++) out.push([x, y, 0]);
  return out;
})();
const isFree = ([x]: V3) => x === 0 || x === N1;

/**
 * A small grey dot on every open front node. A dot fades out as the bead laid on it fades in (gone
 * by the time that bead is half in), so nothing switches on or off between two frames; it sits a
 * hair behind the node, so the bead coming in is drawn over it. The free edges are drawn in the accent colour with a faint accent rail (radius `rail`),
 * as the "frame" scene ends; `free` (0..1) fades that accent out to plain holes, the rail thinning
 * to nothing on the way.
 */
export function addHoles(d: Draw, { opacity = 0.9, free = 1, color = HOLE_COLOR, rail = 0.2, railFade }: { opacity?: number; free?: number; color?: string; rail?: number; railFade?: number } = {}) {
  const cover = new Map<string, number>();
  for (const b of d.beads) {
    if (b.hollow || Math.abs(b.pos[2]) >= 0.01) continue;
    const k = M.key(b.pos);
    cover.set(k, Math.max(cover.get(k) ?? 0, (b.scale ?? 1) * (1 - (b.fade ?? 0)) * (b.opacity ?? 1)));
  }
  const shrink = (beads: Bead[]): Bead[] =>
    beads.flatMap((b) => {
      const s = 1 - clamp01((cover.get(M.key(b.pos)) ?? 0) / 0.5);
      if (s <= 0) return [];
      const pos: V3 = [b.pos[0], b.pos[1], b.pos[2] - 0.02];
      return [s < 1 ? { ...b, pos, opacity: (b.opacity ?? 1) * s } : { ...b, pos }];
    });
  const inner = FRONT_OPEN.filter((p) => !isFree(p));
  const edge = FRONT_OPEN.filter(isFree);
  d.beads.push(...shrink(holeBeads(inner, opacity, color)));
  if (free > 0) {
    // as the "frame" scene ends: the free edges' rings at full strength
    d.beads.push(...shrink(holeBeads(edge, opacity + (1 - opacity) * free, mixHex(color, C.accent, free))));
    for (const e of M.freeEdges) d.lines.push({ a: e[0], b: e[e.length - 1], color: C.accent, r: rail * clamp01(free / 0.25), fade: railFade !== undefined ? 1 - (1 - railFade) * free : 1 - 0.28 * free });
  } else d.beads.push(...shrink(holeBeads(edge, opacity, color)));
}

/** the cube's outline (grey, as the "frame" scene ends); edges not on the front face fade with backFade */
export function faceOutline(opacity = 0.6, backFade = 0, color: string = C.fgSubtle, contour = false): Stick[] {
  const a = -0.5;
  const b = N1 + 0.5;
  const z0 = 0.5;
  const z1 = -N1 - 0.5;
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
  // `contour`: only the cube's outline as the camera sees it (Scene3D's `box`). Seen from a corner,
  // an edge between two faces that both look at the camera passes in front of the beads on them;
  // face-on, the front square is the outline, so it is all there. While the camera turns to the
  // face, the outline goes over from the far edges of the top and right faces to the front square
  // at the moment those faces are edge-on, where the two coincide (so nothing jumps).
  const box = contour ? { min: c[4], max: c[2] } : undefined;
  const out: Stick[] = [];
  e.forEach(([i, j], k) => {
    const o = k < 4 ? opacity : opacity * (1 - backFade);
    if (o > 0.01) out.push({ a: c[i], b: c[j], color, r: 0.04, fade: 1 - o, box });
  });
  return out;
}

/** a soft tinted panel behind strip s (face-on, it reads as a band) */
export function stripPanel(d: Draw, s: number, color: string, opacity: number) {
  if (opacity <= 0) return;
  const rows = M.strips[s].rows;
  const yTop = N1 - rows[0] + 0.45;
  const yBot = N1 - rows[rows.length - 1] - 0.45;
  const z = -0.36;
  d.panels.push({ corners: [[0.55, yBot, z], [N1 - 0.55, yBot, z], [N1 - 0.55, yTop, z], [0.55, yTop, z]], color, opacity });
}

/** screen box [x0, y0, x1, y1] around strip s's nodes (or one of its rows), with a margin in lattice units */
export function stripBox(project: Project, s: number, margin = 0.48, rowsOf?: number[]): [number, number, number, number] {
  const rows = rowsOf ?? M.strips[s].rows;
  const p0 = project([1 - margin, N1 - rows[0] + margin, 0]);
  const p1 = project([N1 - 1 + margin, N1 - rows[rows.length - 1] - margin, 0]);
  return [Math.min(p0[0], p1[0]), Math.min(p0[1], p1[1]), Math.max(p0[0], p1[0]), Math.max(p0[1], p1[1])];
}

/** screen px per lattice unit on the front face (face-on) */
export const unitPx = (project: Project) => project([1, 0, 0])[0] - project([0, 0, 0])[0];

/** the screen centre of a front-face node */
export const nodePx = (project: Project, p: V3) => project(p);

export function mixHex(a: string, b: string, t: number) {
  const pa = parseInt(a.slice(1), 16);
  const pb = parseInt(b.slice(1), 16);
  const ch = (v: number, s: number) => (v >> s) & 255;
  const m = (s: number) => Math.round(ch(pa, s) + (ch(pb, s) - ch(pa, s)) * clamp01(t));
  return `#${((m(16) << 16) | (m(8) << 8) | m(0)).toString(16).padStart(6, '0')}`;
}
