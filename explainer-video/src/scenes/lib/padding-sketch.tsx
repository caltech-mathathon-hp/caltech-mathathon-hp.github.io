/**
 * The sketch of a front face with four strips and two bins, shared by the scenes "padding" and
 * "choice" (part 1, the idea). It is the front face of a bigger cube than the toy's: "padding"
 * opens on the toy face of "walls", which gives way to it. The sketch is 22 × 22 nodes with four
 * periods of five rows; a strip is 3 rows of 20 (60 nodes) and a bin holds 10, so a padding has
 * 60 − 10 = 50 nodes: two rows and the left half of the third. Every hole is the right half of the
 * third row, so the holes line up and the bins can sit beside them.
 *
 * Seen face-on, as the game draws a face: H's are lit beads, ribbons are dominoes (their P's sit
 * in front, towards the viewer, and are not drawn), empty nodes are small grey dots. The frame
 * (edge rows, walls and rods) is full orange, as in every face-on step.
 * World coordinates as in the toy: x to the right, y up, the face in the plane z = 0.
 *
 * Coming and going: a bead fades in or out with `opacity` (see-through, at full size), never by
 * paling or shrinking. A bead is laid at one growing tip, in string order, each bead fading in over
 * BEAD_IN frames; a stick is never stronger than the weaker of its two beads.
 */
import React from 'react';
import type { V3 } from '../../model/toy';
import { isEven } from '../../model/toy';
import { projector, R_RES, type Bead, type Stick, type Shot, type Project } from '../../three/Scene3D';
import { HOLE_COLOR } from '../../three/cube';
import { C, FONT } from '../../theme/theme';
import { clamp01, ramp } from '../../lib/anim';

export const ROWS = 22;
export const COLS = 22;
export const NSTRIPS = 4;
/** nodes in a hole (= a bin) */
export const BIN = 10;
/** H's in a padding */
export const PAD = 50;
/** the toy face of "walls" (12 × 12) */
export const TOY_N = 12;

/** the plug colour (the shared light tan) */
export const PLUG = C.plug;

const range = (a: number, b: number) => Array.from({ length: Math.max(0, b - a) }, (_, i) => a + i);
/** node in column c and row r (r = 0 is the top row) */
export const node = (c: number, r: number): V3 => [c, ROWS - 1 - r, 0];
export const add = (a: V3, b: V3): V3 => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
export const isUnit = (a: V3, b: V3) => Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]) + Math.abs(a[2] - b[2]) === 1;
/** a ribbon's cells in string order, starting on the even end (as in the toy) */
const fromEven = (cells: V3[]) => (isEven(cells[0]) ? cells : [...cells].reverse());

export interface SketchStrip {
  s: number;
  /** row of the top wall of its period */
  top: number;
  rows: number[];
  padding: V3[];
  /** the hole (the right half of the third row), left to right */
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
/** screen x of column c, screen y of row r (on the face plane), in the main shot or in `p` */
export const X = (c: number, p: Project = proj) => p([c, 0, 0])[0];
export const Y = (r: number, p: Project = proj) => p([0, ROWS - 1 - r, 0])[1];
/** px per lattice step under the projection p */
export const pitchOf = (p: Project) => p([1, 0, 0])[0] - p([0, 0, 0])[0];
/** where the bins of the puzzle sit: slot k of bin b is at world column BIN_COL + k, on the row of hole b */
export const BIN_COL = 28;
/** the row of a node of the face (0 = top) */
export const rowOf = (v: V3) => ROWS - 1 - v[1];

// ------------------------------------------------------------------ timing

/** a gentle ease for fades: its top speed is half that of the cubic in-out */
export const easeSine = (t: number) => (1 - Math.cos(Math.PI * clamp01(t))) / 2;
/** a fade from frame `from` over `dur` frames (at least 6), gently eased */
export const fade = (f: number, from: number, dur = 8) => ramp(f, from, dur, easeSine);
/** frames a bead takes to fade in at the growing tip (as the item bars of steps 22, 25 and 35 give way to their beads) */
export const BEAD_IN = 7;
/**
 * A ribbon laid from frame `from`, one bead every `every` frames, each fading in over `fade` frames
 * (BEAD_IN by default, at least 6): the soft tip is fade / every beads long.
 */
export interface Lay {
  from: number;
  every: number;
  fade?: number;
}
/** the opacity of bead i of a ribbon being laid, at frame f */
export const laid = (f: number, lay: Lay, i: number) => easeSine((f - lay.from - i * lay.every) / (lay.fade ?? BEAD_IN));
/** the frame a ribbon of n beads is laid by */
export const layEnd = (n: number, lay: Lay) => lay.from + (n - 1) * lay.every + (lay.fade ?? BEAD_IN);

// ------------------------------------------------------------------ beads

export interface Draw {
  beads: Bead[];
  sticks: Stick[];
  lines: Stick[];
}
export const newDraw = (): Draw => ({ beads: [], sticks: [], lines: [] });

/** how much of row r is shown (0..1, an opacity: beads fade in and out at full size); everything by default */
export type RowShow = (r: number) => number;
const all: RowShow = () => 1;
const soft = (o: number) => (o < 0.999 ? o : undefined);

/**
 * The frame of the sketch: the cube's edge rows, the free-edge columns (lone H's of rods) and the
 * walls (dominoes), all full orange. `show` gives each row's opacity.
 */
export function drawFrame(d: Draw, { show = all }: { show?: RowShow } = {}) {
  const push = (pos: V3, o: number) => {
    if (o > 0.004) d.beads.push({ pos, color: C.h, opacity: soft(o) });
  };
  for (let c = 0; c < COLS; c++) {
    push(node(c, 0), show(0));
    push(node(c, ROWS - 1), show(ROWS - 1));
  }
  for (let r = 1; r < ROWS - 1; r++) {
    push(node(0, r), show(r));
    push(node(COLS - 1, r), show(r));
  }
  for (const st of STRIPS) {
    for (const r of [st.top, st.top + 4]) {
      const o = show(r);
      if (o <= 0.004) continue;
      for (let c = 1; c < COLS - 1; c += 2) {
        const pa = node(c, r);
        const pb = node(c + 1, r);
        d.beads.push({ pos: pa, color: C.h, opacity: soft(o) }, { pos: pb, color: C.h, opacity: soft(o) });
        d.sticks.push({ a: pa, b: pb, color: C.backbone, fade: o < 0.999 ? 1 - o : undefined });
      }
    }
  }
}

/** empty nodes: small grey dots, see-through while they come or go; a bead laid on one covers it */
export function dots(nodes: V3[], o = 1): Bead[] {
  if (o <= 0.004) return [];
  return nodes.map((pos) => ({ pos, color: HOLE_COLOR, r: R_RES * 0.4, opacity: soft(o) }));
}
/** every strip node as an empty node; the beads laid later cover them (and they show through as a bead comes or goes) */
export function drawHoles(d: Draw, { show = all }: { show?: RowShow } = {}) {
  for (const st of STRIPS)
    for (const p of [...st.padding, ...st.holeLR]) {
      const o = show(rowOf(p));
      d.beads.push(...dots([p], o));
    }
}

/**
 * A ribbon: its beads (H's) with opacity `op(i)` (a number for all of them), joined in pairs
 * (PHHP: cells 0–1, 2–3, …); a stick is never stronger than the weaker of its two beads.
 */
export function drawRibbon(d: Draw, cells: V3[], color: string, op: number | ((i: number) => number), { offset }: { offset?: V3 } = {}) {
  const o = typeof op === 'number' ? () => op : op;
  const P = (i: number) => (offset ? add(cells[i], offset) : cells[i]);
  const ops = cells.map((_, i) => clamp01(o(i)));
  cells.forEach((_, i) => {
    if (ops[i] > 0.004) d.beads.push({ pos: P(i), color, opacity: soft(ops[i]) });
  });
  for (let i = 0; i + 1 < cells.length; i += 2) {
    if (!isUnit(cells[i], cells[i + 1])) continue;
    const m = Math.min(ops[i], ops[i + 1]);
    if (m > 0.004) d.sticks.push({ a: P(i), b: P(i + 1), color: C.backbone, fade: m < 0.999 ? 1 - m : undefined });
  }
}

/**
 * The cube's outline round the face, half a step out (as "walls" draws it, a thin grey line in
 * front of the face). `g` grows it from the toy face (12 × 12, top left) to the sketch.
 */
export function outline(o: number, g = 1): Stick[] {
  if (o <= 0.004) return [];
  const right = TOY_N - 0.5 + (COLS - TOY_N) * g;
  const bottom = ROWS - TOY_N - 0.5 - (ROWS - TOY_N) * g;
  const top = ROWS - 0.5;
  const c: V3[] = [
    [-0.5, bottom, 0.5],
    [right, bottom, 0.5],
    [right, top, 0.5],
    [-0.5, top, 0.5],
  ];
  return [0, 1, 2, 3].map((i) => ({ a: c[i], b: c[(i + 1) % 4], color: C.fgSubtle, r: 0.04, fade: 1 - 0.6 * o }));
}

// ------------------------------------------------------------------ legend

/**
 * A legend right of the face, below where the bins go, drawn with real beads so it matches:
 * each entry fades in with its value (0..1).
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
    if (k <= 0.004) continue;
    const y = ROWS - 1 - e.row;
    if (e.key === 'empty') {
      d.beads.push(...dots([[LEG_COL + 0.5, y, 0]], k));
      continue;
    }
    const color = e.key === 'wall' ? C.h : e.key === 'pad' ? C.pad : PLUG;
    drawRibbon(d, [[LEG_COL, y, 0], [LEG_COL + 1, y, 0]], color, k);
  }
}

/** the legend's entry for the items: one bead of each item's colour, in a row */
export function drawItemsLegend(d: Draw, k: number, colors: string[]) {
  if (k <= 0.004) return;
  const y = ROWS - 1 - LEG_ROW_ITEMS;
  colors.forEach((color, u) => d.beads.push({ pos: [LEG_COL + 0.5 + 0.6 * (u - 1.5), y, 0], color, opacity: soft(k) }));
}

export function LegendLabels({ show, p = proj }: { show: Partial<Record<LegendKey, number>>; p?: Project }) {
  return (
    <g fontFamily={FONT.sans} {...SUB}>
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
 * Labels sit left of the face, right-aligned. A thing without a box of its own (a row, a strip, a
 * hole: the hole is the right half of its row, so a leader into its box would run along the row
 * under the padding) gets a short dash to the face border, centred on it. A thing with a box whose
 * corner is at the face's left edge (the padding) gets the name level with the box's top edge and
 * a leader into its top-left corner, as in steps 33–35.
 */
export const NAME = { fontSize: 26, fontWeight: 600, fill: C.fg } as const;
export const SUB = { fontSize: 22, fontWeight: 500, fill: C.fgMuted } as const;
export const LEADER = { stroke: C.fgMuted, strokeWidth: 2, strokeLinecap: 'round' as const };
/** right edge of the label column, left of the face */
export const labelX = (p: Project = proj) => X(-0.5, p) - 30;
/** where a dash to the face border ends: just before the free-edge bead (as "walls" draws it) */
export const dashTo = (p: Project = proj) => X(0, p) - R_RES * pitchOf(p) - 8;

export function SideLabel({ y, toX, title, sub, opacity, subOpacity = 1, p = proj, boxed = false }: { y: number; toX: number; title: React.ReactNode; sub?: React.ReactNode; opacity: number; subOpacity?: number; p?: Project; boxed?: boolean }) {
  if (opacity <= 0) return null;
  const tx = labelX(p);
  return (
    <g opacity={opacity} fontFamily={FONT.sans}>
      <line x1={tx + 8} x2={toX} y1={y} y2={y} {...LEADER} />
      <text x={tx} y={y + (boxed ? 10 : 9)} textAnchor="end" {...NAME}>
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

/** a row's (or a strip's) name: a short dash to the face border, centred on row r */
export function RowLabel({ r, title, sub, opacity, subOpacity, p = proj }: { r: number; title: React.ReactNode; sub?: React.ReactNode; opacity: number; subOpacity?: number; p?: Project }) {
  return <SideLabel y={Y(r, p)} toX={dashTo(p)} title={title} sub={sub} opacity={opacity} subOpacity={subOpacity} p={p} />;
}

/** strip s's label: its name on its middle row, and a sub-line ("3 rows × 20 nodes") if given */
export function StripLabel({ s, sub, opacity, subOpacity, p = proj }: { s: number; sub?: string; opacity: number; subOpacity?: number; p?: Project }) {
  return <RowLabel r={STRIPS[s].rows[1]} title={`strip ${s + 1}`} sub={sub} opacity={opacity} subOpacity={subOpacity} p={p} />;
}

/** the box round hole s (its 10 cells), a little wider and taller than the beads so an item bar fits inside it; drawn behind them */
export const BOX_RX = 10;
const BOX_PADX = 3;
/** half the height of a hole's box, in lattice steps (clear of the beads of the rows above and below) */
const BOX_HALF = 0.59;
export function holeBox(s: number, p: Project = proj): [number, number, number, number] {
  const r = STRIPS[s].holeRow;
  return [X(HOLE_COL0 - 0.5, p) - BOX_PADX, Y(r - BOX_HALF, p), X(COLS - 1.5, p) + BOX_PADX, Y(r + BOX_HALF, p)];
}
export function HoleBox({ s, opacity, p = proj, stroke = C.fgMuted, width = 2.5, grow = 0 }: { s: number; opacity: number; p?: Project; stroke?: string; width?: number; grow?: number }) {
  if (opacity <= 0) return null;
  const [x0, y0, x1, y1] = holeBox(s, p);
  return <rect x={x0 - grow} y={y0 - grow} width={x1 - x0 + 2 * grow} height={y1 - y0 + 2 * grow} rx={BOX_RX + grow} fill="none" stroke={stroke} strokeWidth={width} opacity={opacity} />;
}

/** hole s's label: left of the face, a short dash centred on the hole's row */
export function HoleLabel({ s, title, sub, opacity, subOpacity, p = proj }: { s: number; title: React.ReactNode; sub?: React.ReactNode; opacity: number; subOpacity?: number; p?: Project }) {
  return <RowLabel r={STRIPS[s].holeRow} title={title} sub={sub} opacity={opacity} subOpacity={subOpacity} p={p} />;
}

/**
 * Step 21: which holes the plugs take is only an example. A note left of the face, between the
 * two plugs' labels.
 */
export function SpareNote({ opacity, p = proj }: { opacity: number; p?: Project }) {
  if (opacity <= 0) return null;
  const tx = labelX(p);
  const mid = (Y(STRIPS[2].holeRow, p) + 37 + Y(STRIPS[3].holeRow, p) - 10) / 2;
  return (
    <g fontFamily={FONT.sans} {...SUB} opacity={opacity} textAnchor="end">
      <text x={tx} y={mid - 4}>
        the plugs could go
      </text>
      <text x={tx} y={mid + 24}>
        in any 2 holes
      </text>
    </g>
  );
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
 * The outline of strip 1's padding (two rows and the left half of the third), drawn behind the
 * beads, with its label left of the face: the name level with the outline's top edge, the leader
 * running between two free-edge beads into its top-left corner.
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
  return <path d={roundedPath(pts, p, 0.3 * pitchOf(p))} fill="none" stroke={C.fgMuted} strokeWidth={2.5} opacity={opacity} />;
}
export function PaddingLabel({ opacity, p = proj }: { opacity: number; p?: Project }) {
  const y = Y(STRIPS[0].rows[0] - 0.5, p);
  return <SideLabel y={y} toX={X(0.5, p) + 0.3 * pitchOf(p)} title="padding" sub="50 H’s" opacity={opacity} p={p} boxed />;
}

/** a rounded box (screen px) around the cells c0..c1 × r0..r1, half a step off their beads */
export function cellBox(c0: number, c1: number, r0: number, r1: number, p: Project = proj): [number, number, number, number] {
  return [X(c0 - 0.5, p), Y(r0 - 0.5, p), X(c1 + 0.5, p), Y(r1 + 0.5, p)];
}

/** says that this is a sketch of a bigger cube, top right (where part 2 shows the toy badge, in the same form) */
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
      <b style={{ color: C.fg }}>Sketch</b>: a bigger cube
      <br />4 strips of 3 rows × 20, 2 bins of 10
    </div>
  );
}

// ------------------------------------------------------------------ item bars on the face

/**
 * An item bar that has landed on its hole gives way to its beads, as in step 35: the bar shrinks
 * from the end where its ribbon starts (its first cell in string order), at a steady pace of 2.5
 * frames a cell (at least 12 frames in all), and each bead fades in at full size as the bar's edge
 * reaches it. `t` is frames since it started. Draw the bar with `sliverFade={false}`, so it stays at
 * full colour to its last sliver and nothing pale sits over the beads.
 */
export const wipeFrames = (size: number) => Math.max(12, Math.round(2.5 * size));
export function giveWay(cells: V3[], t: number) {
  const size = cells.length;
  const R = wipeFrames(size);
  const w = clamp01(t / R);
  const leftFirst = cells[0][0] <= cells[size - 1][0];
  const done = size * w;
  return {
    /** the part of the bar still showing, in units from its left end */
    span: (leftFirst ? [done, size] : [0, size - done]) as [number, number],
    gone: w >= 1,
    /** the opacity of bead k (its place in the string) */
    bead: (k: number) => easeSine((t - (R * (k - 0.5)) / size) / BEAD_IN),
  };
}
/** the frame by which a bar of `size` that starts giving way at `from` has all its beads */
export const giveWayEnd = (size: number, from: number) => from + wipeFrames(size) + BEAD_IN;
