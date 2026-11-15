/**
 * The sketch of a front face with four strips and two bins, shared by the scenes "padding" and
 * "choice" (part 1, the idea). It is the front face of a bigger cube than the toy's: the toy face
 * (12 × 12, two strips) grows into it at the start of "padding". The sketch is 22 × 22 nodes with
 * four periods of five rows; a strip is 3 rows of 20 (60 nodes) and a bin holds 10, so a padding
 * has 60 − 10 = 50 nodes: two rows and the left half of the third. Every hole is the right half
 * of the third row, so the holes line up and the bins can sit beside them.
 *
 * Seen face-on, as the game draws a face: H's are lit beads, ribbons are dominoes (their P's sit
 * in front, towards the viewer, and are not drawn), empty nodes are small neutral beads. The frame
 * (edge rows, walls and rods) is full orange, as in every face-on step.
 * World coordinates as in the toy: x to the right, y up, the face in the plane z = 0.
 */
import React from 'react';
import type { V3 } from '../../model/toy';
import { isEven } from '../../model/toy';
import { projector, R_BOND, R_RES, FADE, type Bead, type Stick, type Shot, type Project } from '../../three/Scene3D';
import { holeBeads } from '../../three/cube';
import { C, FONT, itemColor } from '../../theme/theme';
import { clamp01, lerp } from '../../lib/anim';

export const ROWS = 22;
export const COLS = 22;
export const NSTRIPS = 4;
/** nodes in a hole (= a bin) */
export const BIN = 10;
/** H's in a padding */
export const PAD = 50;
/** the toy face the sketch grows from (12 × 12, the face of the scene "walls") */
export const TOY_N = 12;

/** the plug colour: a light tan, apart from the padding's grey, the items' colours and the P's (hollow, blue) */
export const PLUG = '#c2ae8a';

const range = (a: number, b: number) => Array.from({ length: Math.max(0, b - a) }, (_, i) => a + i);
/** node in column c and row r (r = 0 is the top row) */
export const node = (c: number, r: number): V3 => [c, ROWS - 1 - r, 0];
const add = (a: V3, b: V3): V3 => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
export const isUnit = (a: V3, b: V3) => Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]) + Math.abs(a[2] - b[2]) === 1;
/** a ribbon's cells in string order, starting on the even end (as in the toy) */
const fromEven = (cells: V3[]) => (isEven(cells[0]) ? cells : [...cells].reverse());

export interface SketchStrip {
  s: number;
  /** row of the top wall of its period */
  top: number;
  rows: number[];
  padding: V3[];
  /** the hole (the bottom row), left to right */
  holeLR: V3[];
  /** the hole in string order from its even end (how a plug lies in it) */
  hole: V3[];
  holeRow: number;
}

export const STRIPS: SketchStrip[] = range(0, NSTRIPS).map((s) => {
  const t = 1 + 5 * s;
  const rows = [t + 1, t + 2, t + 3];
  const cols = range(1, COLS - 1);
  // drawn from the top left, row by row like a snake; an even number of cells, so the pairs of H's
  // are the same read from either end
  const snake = rows.flatMap((r, i) => (i % 2 === 0 ? cols : [...cols].reverse()).map((c) => node(c, r)));
  const holeLR = snake.slice(PAD);
  return { s, top: t, rows, padding: snake.slice(0, PAD), holeLR, hole: fromEven(holeLR), holeRow: t + 3 };
});
/** the first column of every hole */
export const HOLE_COL0 = STRIPS[0].holeLR[0][0];

/**
 * A second padding trying strip 1. It is laid from outside the face, two rows to the right of
 * strip 1 (its 40 H's that find no room), then its last 10 H's go into the hole, up to the first
 * padding. Between the two parts it hops over the free edge (no bead is drawn across it).
 */
export const TAIL_COL0 = COLS + 1;
export const ATTEMPT_OUT: V3[] = [
  ...range(TAIL_COL0, TAIL_COL0 + 20).map((c) => node(c, STRIPS[0].rows[1])),
  ...range(TAIL_COL0, TAIL_COL0 + 20)
    .reverse()
    .map((c) => node(c, STRIPS[0].holeRow)),
];
export const ATTEMPT: V3[] = [...ATTEMPT_OUT, ...[...STRIPS[0].holeLR].reverse()];

/** items 6, 2, 8, 4 (as in the plan scene); bin 1 takes 6 + 4, bin 2 takes 2 + 8, left to right */
export const SIZES = [6, 2, 8, 4];
export const BINS = [
  [0, 3],
  [1, 2],
];
export interface PlacedItem {
  u: number;
  bin: number;
  /** first slot of the hole (0..9) */
  slot: number;
  /** cells left to right */
  lr: V3[];
  /** cells in string order (from the even end) */
  cells: V3[];
}
export const PLACED: PlacedItem[] = (() => {
  const out: PlacedItem[] = [];
  BINS.forEach((us, b) => {
    let k = 0;
    for (const u of us) {
      const lr = STRIPS[b].holeLR.slice(k, k + SIZES[u]);
      out.push({ u, bin: b, slot: k, lr, cells: fromEven(lr) });
      k += SIZES[u];
    }
  });
  return out.sort((a, b) => a.u - b.u);
})();

// ------------------------------------------------------------------ camera and screen positions

/** px per lattice step on screen */
export const PITCH = 33;
/** the camera distance that gives `pitch` px per lattice step on the face (fov 30) */
export const distFor = (pitch: number) => 1080 / (2 * Math.tan((15 * Math.PI) / 180) * pitch);
/** a face-on shot with `pitch` px per lattice step that puts the world point `at` on screen at (sx, sy) */
export const faceShot = (at: V3, sx: number, sy: number, pitch: number): Shot => ({
  target: at,
  dir: [0, 0, 1],
  dist: distFor(pitch),
  offset: [sx - 960, sy - 540],
});
/**
 * Screen x of column 0 and screen y of row 0 in the main shot. The face (rows 0..21, y 150..843)
 * sits with the same margin under the title (bottom at y 82) as above the captions (top at y 911).
 */
const X0 = 400;
const Y0 = 150;
/** face-on, the whole face; room for the bins and the legend on the right */
export const SHOT: Shot = faceShot([(COLS - 1) / 2, (ROWS - 1) / 2, 0], X0 + PITCH * (COLS - 1) / 2, Y0 + PITCH * (ROWS - 1) / 2, PITCH);
export const proj = projector(SHOT);
/**
 * The toy face's place in the scene "walls" (FACE_SHOT there), in the sketch's coordinates: the
 * toy's 12 × 12 nodes are the sketch's columns 0..11 and rows 0..11.
 */
export const TOY_SHOT: Shot = { target: [(TOY_N - 1) / 2, ROWS - 1 - (TOY_N - 1) / 2 - 1.6, 0], dir: [0, 0, 1], dist: 40 };
/** screen x of column c, screen y of row r (on the face plane), in the main shot or in `p` */
export const X = (c: number, p: Project = proj) => p([c, 0, 0])[0];
export const Y = (r: number, p: Project = proj) => p([0, ROWS - 1 - r, 0])[1];
/** px per lattice step under the projection p */
export const pitchOf = (p: Project) => p([1, 0, 0])[0] - p([0, 0, 0])[0];
/** where the bins of the puzzle sit: slot k of bin b is at world column BIN_COL + k, on the row of hole b */
export const BIN_COL = 28;
/** the row of a node of the face (0 = top) */
export const rowOf = (v: V3) => ROWS - 1 - v[1];

// ------------------------------------------------------------------ beads

export interface Panel {
  corners: [V3, V3, V3, V3];
  color: string;
  opacity: number;
}
export interface Draw {
  beads: Bead[];
  sticks: Stick[];
  panels: Panel[];
}
export const newDraw = (): Draw => ({ beads: [], sticks: [], panels: [] });

/** how much of row r is shown (0..1, as an opacity: beads fade in at full size); everything by default */
export type RowShow = (r: number) => number;
const all: RowShow = () => 1;
/** a fade made quieter by `q` (fades combine: 0.5 then 0.5 is 0.75) */
const fq = (fade: number, q: number) => 1 - (1 - fade) * (1 - q);

/**
 * How far the face has grown from the toy (0) to the sketch (1): the right free edge moves from
 * column 11 to 21 and the bottom edge from row 11 to 21. A column (row) behind them fades in, at
 * full size, once the moving edge is a bead's width past it, so no two beads ever overlap.
 */
export function growth(g = 1) {
  const xr = TOY_N - 1 + (COLS - TOY_N) * g;
  const rb = TOY_N - 1 + (ROWS - TOY_N) * g;
  const col = (c: number) => (c <= 0 ? 1 : clamp01((xr - c - 0.62) / 0.38));
  const row = (r: number) => (r <= 0 ? 1 : clamp01((rb - r - 0.62) / 0.38));
  return { xr, rb, col, row, done: g >= 1 };
}
export type Growth = ReturnType<typeof growth>;
const FULL = growth(1);

/**
 * The frame of the sketch: the cube's edge rows, the free-edge columns (lone H's of rods) and the
 * walls (dominoes), all full orange. `quiet` fades all of it together (0..1; FADE.context is the
 * shared amount), `show` hides rows, `gr` grows it from the toy face.
 */
export function drawFrame(d: Draw, { quiet = 0, show = all, gr = FULL }: { quiet?: number; show?: RowShow; gr?: Growth } = {}) {
  const edge = fq(0, quiet);
  const wall = fq(0, quiet);
  const push = (pos: V3, fade: number, a: number) => {
    if (a > 0.004) d.beads.push({ pos, color: C.h, fade: 1 - (1 - fade) * a });
  };
  // the edge rows: the top one, and the bottom one (moving down as the face grows)
  for (let c = 0; c < COLS - 1; c++) {
    push(node(c, 0), edge, gr.col(c) * show(0));
    push([c, ROWS - 1 - gr.rb, 0], edge, gr.col(c) * show(gr.rb));
  }
  push([gr.xr, ROWS - 1, 0], edge, show(0));
  push([gr.xr, ROWS - 1 - gr.rb, 0], edge, show(gr.rb));
  // the free-edge columns: the left one, and the right one (moving right as the face grows)
  for (let r = 1; r < ROWS - 1; r++) {
    const a = gr.row(r) * show(r);
    push(node(0, r), wall, a);
    push([gr.xr, ROWS - 1 - r, 0], wall, a);
  }
  // the walls, in pairs (a pair shows when its right bead does)
  for (const st of STRIPS) {
    for (const r of [st.top, st.top + 4]) {
      for (let c = 1; c < COLS - 1; c += 2) {
        const a = gr.col(c + 1) * gr.row(r) * show(r);
        if (a <= 0.004) continue;
        const pa = node(c, r);
        const pb = node(c + 1, r);
        const fade = 1 - (1 - wall) * a;
        d.beads.push({ pos: pa, color: C.h, fade }, { pos: pb, color: C.h, fade });
        d.sticks.push({ a: pa, b: pb, color: C.backbone, fade: fade > 0.004 ? fade : undefined });
      }
    }
  }
}

/** every strip node as an empty node (small neutral bead); filled nodes hide them */
export function drawHoles(d: Draw, { opacity = 1, skip, show = all, gr = FULL }: { opacity?: number; skip?: (p: V3) => boolean; show?: RowShow; gr?: Growth } = {}) {
  for (const st of STRIPS)
    for (const p of [...st.padding, ...st.holeLR]) {
      if (skip?.(p)) continue;
      const r = rowOf(p);
      const a = opacity * gr.col(p[0]) * gr.row(r) * show(r);
      if (a > 0.004) d.beads.push(...holeBeads([p], a));
    }
}

/**
 * Laying a ribbon in string order, with one growing tip: `progress` 0..1 runs along the cells.
 * The first bead fades in at full size (over `lead` steps); every next bead slides out of the bead
 * before it (one step), or fades in where the ribbon hops (cells not side by side). H's are in
 * pairs (PHHP), so a stick joins cells 0–1, 2–3, … Use `layLead` to get fades of 6 frames or more.
 */
export interface RibbonStyle {
  offset?: V3;
  /** the whole ribbon quieter (0..1); 1 = gone */
  fade?: number;
  /** steps a fading bead takes (a sliding bead takes 1) */
  lead?: number;
}
/** whether bead i fades in where it is (the first bead, or after a hop) rather than sliding out of the bead before it */
const fadesIn = (cells: V3[], i: number) => i === 0 || !isUnit(cells[i - 1], cells[i]);
const steps = (cells: V3[], lead: number) => cells.map((_, i) => (fadesIn(cells, i) ? lead : 1));
/** the lead that makes the fades of a ribbon laid over `frames` frames last `fadeFrames` frames */
export function layLead(cells: V3[], frames: number, fadeFrames = 6) {
  const nFade = cells.filter((c, i) => i === 0 || !isUnit(cells[i - 1], c)).length;
  const nSlide = cells.length - nFade;
  const room = Math.max(1, frames - fadeFrames * nFade);
  return Math.max(1, (fadeFrames * nSlide) / room);
}
export function drawRibbon(d: Draw, cells: V3[], color: string, progress: number, st: RibbonStyle = {}) {
  const N = cells.length;
  const base = st.fade ?? 0;
  if (progress <= 0 || N === 0 || base >= 1) return;
  const lead = st.lead ?? 3;
  const cost = steps(cells, lead);
  const total = cost.reduce((a, b) => a + b, 0);
  const head = clamp01(progress) * total;
  const off = st.offset ?? [0, 0, 0];
  const P = (i: number) => add(cells[i], off);
  const at: (V3 | null)[] = [];
  const fades: number[] = [];
  let t0 = 0;
  for (let i = 0; i < N; i++) {
    const t = clamp01((head - t0) / cost[i]);
    t0 += cost[i];
    if (t <= 0) break;
    let pos: V3;
    let fade = base;
    if (fadesIn(cells, i)) {
      pos = P(i);
      fade = 1 - (1 - base) * t;
    } else {
      // out of the bead before it, a little behind it so that one covers it at first
      const a = P(i - 1);
      const b = P(i);
      pos = [lerp(a[0], b[0], t), lerp(a[1], b[1], t), lerp(a[2], b[2], t) - 0.05 * (1 - t)];
    }
    at.push(pos);
    fades.push(fade);
    d.beads.push({ pos, color, fade: fade > 0.004 ? fade : undefined });
  }
  for (let i = 0; i + 1 < at.length; i += 2) {
    if (!isUnit(cells[i], cells[i + 1])) continue;
    const fade = Math.max(fades[i], fades[i + 1]);
    d.sticks.push({ a: at[i]!, b: at[i + 1]!, color: C.backbone, fade: fade > 0.004 ? fade : undefined });
  }
}

// ------------------------------------------------------------------ legend

/**
 * A legend right of the face, below where the bins go, drawn with real beads so it matches:
 * each entry fades in (at full size) with its value (0..1).
 */
export const LEGEND = [
  { key: 'wall', row: 14.1, label: 'walls and rods' },
  { key: 'empty', row: 15.6, label: 'empty node' },
  { key: 'pad', row: 17.1, label: 'padding (H’s)' },
  { key: 'plug', row: 18.6, label: 'plug (H’s)' },
] as const;
export type LegendKey = (typeof LEGEND)[number]['key'];
/** the legend's key column (its left edge lines up with the bins) and two extra rows the scene "choice" uses */
export const LEG_COL = BIN_COL - 0.15;
export const LEG_ROW_ITEMS = 12.6;
export const LEG_ROW_JOIN = 20.1;
/** screen position of a legend label on legend row `row` */
export const legendText = (row: number, p: Project = proj) => p([LEG_COL + 2.15, ROWS - 1 - row, 0]);

export function drawLegend(d: Draw, show: Partial<Record<LegendKey, number>>) {
  for (const e of LEGEND) {
    const k = clamp01(show[e.key] ?? 0);
    if (k <= 0) continue;
    const y = ROWS - 1 - e.row;
    const a: V3 = [LEG_COL, y, 0];
    const b: V3 = [LEG_COL + 1, y, 0];
    if (e.key === 'empty') {
      d.beads.push(...holeBeads([[LEG_COL + 0.5, y, 0]], k));
      continue;
    }
    const color = e.key === 'wall' ? C.h : e.key === 'pad' ? C.pad : PLUG;
    const fade = 1 - k;
    d.beads.push({ pos: a, color, fade: fade > 0.004 ? fade : undefined }, { pos: b, color, fade: fade > 0.004 ? fade : undefined });
    d.sticks.push({ a, b, color: C.backbone, fade: fade > 0.004 ? fade : undefined });
  }
}

/** the legend's entry for the items: one bead of each item's colour, in a row */
export function drawItemsLegend(d: Draw, k: number) {
  if (k <= 0) return;
  const y = ROWS - 1 - LEG_ROW_ITEMS;
  const fade = 1 - clamp01(k);
  SIZES.forEach((_, u) => d.beads.push({ pos: [LEG_COL + 0.5 + 0.6 * (u - 1.5), y, 0], color: itemColor(u), fade: fade > 0.004 ? fade : undefined }));
}

export function LegendLabels({ show, p = proj }: { show: Partial<Record<LegendKey, number>>; p?: Project }) {
  return (
    <g fontFamily={FONT.sans} fontSize={22} fill={C.fgMuted}>
      {LEGEND.map((e) => {
        const k = clamp01(show[e.key] ?? 0);
        if (k <= 0) return null;
        const [x, y] = legendText(e.row, p);
        return (
          <text key={e.key} x={x} y={y + 7.5} opacity={k}>
            {e.label}
          </text>
        );
      })}
    </g>
  );
}

// ------------------------------------------------------------------ labels (SVG)

/**
 * The two label styles of the video: a name (26/600, fg) and a sub-line under it (22/500, muted).
 * Strip and hole labels sit left of the face, right-aligned, the leader leaving the name and
 * running to the thing named: to just before the free-edge bead of a strip's middle row, or
 * through the gap between two rows of beads to the corner of a hole's box.
 */
export const NAME = { fontSize: 26, fontWeight: 600, fill: C.fg } as const;
export const SUB = { fontSize: 22, fontWeight: 500, fill: C.fgMuted } as const;
const LEADER = { stroke: C.fgMuted, strokeWidth: 2, strokeLinecap: 'round' as const };
export function SideLabel({ y, toX, title, sub, opacity, subOpacity = 1, p = proj }: { y: number; toX: number; title: React.ReactNode; sub?: React.ReactNode; opacity: number; subOpacity?: number; p?: Project }) {
  if (opacity <= 0) return null;
  const tx = X(-0.5, p) - 30;
  return (
    <g opacity={opacity} fontFamily={FONT.sans}>
      <line x1={tx + 8} x2={toX} y1={y} y2={y} {...LEADER} />
      <text x={tx} y={y + 9} textAnchor="end" {...NAME}>
        {title}
      </text>
      {sub != null && subOpacity > 0 && (
        <text x={tx} y={y + 37} textAnchor="end" {...SUB} opacity={subOpacity}>
          {sub}
        </text>
      )}
    </g>
  );
}

/** strip s's label: its name on its middle row, and a sub-line ("3 rows × 20") if given */
export function StripLabel({ s, sub, opacity, p = proj }: { s: number; sub?: string; opacity: number; p?: Project }) {
  const rb = R_RES * pitchOf(p);
  return <SideLabel y={Y(STRIPS[s].rows[1], p)} toX={X(0, p) - rb - 8} title={`strip ${s + 1}`} sub={sub} opacity={opacity} p={p} />;
}

/** the box round hole s (its 10 cells), half a step off the beads: drawn behind them */
export function holeBox(s: number, p: Project = proj): [number, number, number, number] {
  const r = STRIPS[s].holeRow;
  return [X(HOLE_COL0 - 0.5, p), Y(r - 0.5, p), X(COLS - 1.5, p), Y(r + 0.5, p)];
}
export const BOX_RX = 10;
export function HoleBox({ s, opacity, p = proj }: { s: number; opacity: number; p?: Project }) {
  if (opacity <= 0) return null;
  const [x0, y0, x1, y1] = holeBox(s, p);
  return <rect x={x0} y={y0} width={x1 - x0} height={y1 - y0} rx={BOX_RX} fill="none" stroke={C.fgMuted} strokeWidth={2.5} opacity={opacity} />;
}

/** hole s's label: the leader runs along the bottom of its box (between the hole's row and the wall under it) */
export function HoleLabel({ s, title, sub, opacity, subOpacity, p = proj }: { s: number; title: React.ReactNode; sub?: React.ReactNode; opacity: number; subOpacity?: number; p?: Project }) {
  const [x0, , , y1] = holeBox(s, p);
  return <SideLabel y={y1} toX={x0 + BOX_RX} title={title} sub={sub} opacity={opacity} subOpacity={subOpacity} p={p} />;
}

/** a short note right of the face on row r, or at screen height `atY` ("cube edge", "wall", "a bin: 10") */
export function RowTag({ r = 0, atY, label, opacity, p = proj }: { r?: number; atY?: number; label: string; opacity: number; p?: Project }) {
  if (opacity <= 0) return null;
  const rb = R_RES * pitchOf(p);
  const x = X(COLS - 1, p) + rb + 22;
  const y = atY ?? Y(r, p);
  return (
    <g opacity={opacity} fontFamily={FONT.sans}>
      <line x1={X(COLS - 1, p) + rb + 7} x2={x - 5} y1={y} y2={y} {...LEADER} />
      <text x={x + 2} y={y + 7.5} {...SUB}>
        {label}
      </text>
    </g>
  );
}

/** step 21: the plugs' holes are only an example (a line above the legend, right of the face) */
export function SpareNote({ opacity, p = proj }: { opacity: number; p?: Project }) {
  if (opacity <= 0) return null;
  const [x] = p([LEG_COL - R_RES, 0, 0]);
  return (
    <text x={x} y={Y(11.2, p) + 7.5} fontFamily={FONT.sans} {...SUB} opacity={opacity}>
      the plugs could go in any 2 holes
    </text>
  );
}

/** the cube's outline round the face (as in "walls" and part 2), behind the beads; `gr` while it grows */
export function FaceOutline({ opacity, gr = FULL, p = proj }: { opacity: number; gr?: Growth; p?: Project }) {
  if (opacity <= 0) return null;
  const a = p([-0.5, ROWS - 0.5, 0.5]);
  const b = p([gr.xr + 0.5, ROWS - 1 - gr.rb - 0.5, 0.5]);
  return <rect x={a[0]} y={a[1]} width={b[0] - a[0]} height={b[1] - a[1]} fill="none" stroke={C.fgSubtle} strokeOpacity={0.6} strokeWidth={0.08 * pitchOf(p)} opacity={opacity} />;
}

/** a rounded outline along a polygon of lattice points (column, row), half a step off the beads */
function roundedPath(pts: [number, number][], p: Project, rad: number) {
  const s = pts.map(([c, r]) => [X(c, p), Y(r, p)] as [number, number]);
  const n = s.length;
  let d = '';
  for (let i = 0; i < n; i++) {
    const a = s[(i + n - 1) % n];
    const b = s[i];
    const c = s[(i + 1) % n];
    const la = Math.hypot(a[0] - b[0], a[1] - b[1]);
    const lc = Math.hypot(c[0] - b[0], c[1] - b[1]);
    const k = Math.min(rad, la / 2, lc / 2);
    const p0 = [b[0] + ((a[0] - b[0]) * k) / la, b[1] + ((a[1] - b[1]) * k) / la];
    const p1 = [b[0] + ((c[0] - b[0]) * k) / lc, b[1] + ((c[1] - b[1]) * k) / lc];
    d += `${i === 0 ? 'M' : 'L'}${p0[0]},${p0[1]} Q${b[0]},${b[1]} ${p1[0]},${p1[1]} `;
  }
  return d + 'Z';
}

/**
 * The outline of strip 1's padding (two rows and the left half of the third), with its name right
 * of the face; the leader reaches the outline between two rod beads.
 */
export function PaddingOutline({ opacity, p = proj }: { opacity: number; p?: Project }) {
  if (opacity <= 0) return null;
  const st = STRIPS[0];
  const [r0, r1, r2] = st.rows;
  const cut = HOLE_COL0 - 0.5;
  const pts: [number, number][] = [
    [0.5, r0 - 0.5],
    [COLS - 1.5, r0 - 0.5],
    [COLS - 1.5, r1 + 0.5],
    [cut, r1 + 0.5],
    [cut, r2 + 0.5],
    [0.5, r2 + 0.5],
  ];
  const u = pitchOf(p);
  const rb = R_RES * u;
  const y = Y(r0 + 0.5, p);
  const x = X(COLS - 1, p) + rb + 22;
  return (
    <g opacity={opacity} fontFamily={FONT.sans}>
      <path d={roundedPath(pts, p, 0.3 * u)} fill="none" stroke={C.pad} strokeWidth={2.5} />
      <line x1={X(COLS - 1.5, p) + 1} x2={x - 5} y1={y} y2={y} {...LEADER} />
      <text x={x + 2} y={y + 7.5} {...SUB}>
        padding: 50 H’s
      </text>
    </g>
  );
}

/** a rounded box (screen px) around the cells c0..c1 × r0..r1, half a step off their beads */
export function cellBox(c0: number, c1: number, r0: number, r1: number, p: Project = proj): [number, number, number, number] {
  return [X(c0 - 0.5, p), Y(r0 - 0.5, p), X(c1 + 0.5, p), Y(r1 + 0.5, p)];
}

/** says that this is a sketch of a bigger cube, top right (where part 2 shows the toy badge) */
export function SketchBadge({ opacity = 1 }: { opacity?: number }) {
  if (opacity <= 0) return null;
  return (
    <div
      style={{
        position: 'absolute',
        right: 64,
        top: 44,
        fontFamily: FONT.sans,
        fontSize: 21,
        color: C.fgMuted,
        background: C.bgElev,
        border: `1.5px solid ${C.ruleStrong}`,
        borderRadius: 8,
        padding: '8px 16px',
        opacity,
        lineHeight: 1.35,
        textAlign: 'right',
      }}
    >
      <b style={{ color: C.fg }}>Sketch</b>: a bigger cube, 4 strips of 3 rows × 20, 2 bins of 10
    </div>
  );
}
