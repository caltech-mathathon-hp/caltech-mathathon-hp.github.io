/**
 * Pieces shared by the scenes "plan", "instance" and "end":
 *  - the bin packing puzzle of the running example (items 6, 2, 8, 4; two bins of 10) in the
 *    bin-pack game's look, with each item somewhere between the tray and its bin;
 *  - an HP string drawn flat, as the fold game draws it in 2D;
 *  - a small cube of H's with a few P's sticking out (the "best fold" of the pipeline), drawn in 3D;
 *  - a curved arrow;
 *  - cube boxes (outline + tinted faces) for the cubes of side 80 and 12.
 * Positions are in px of the 1920 × 1080 frame unless said otherwise.
 */
import React from 'react';
import * as M from '../../model/toy';
import type { V3 } from '../../model/toy';
import { C, FONT, itemColor } from '../../theme/theme';
import { Arrow, BAR, BinTrack, ItemBar, slotX, slotY, trackHeight, trackWidth } from '../../ui/Bins';
import { type Letter } from '../../three/cube';
import { yaw, type Bead, type Shot, type Stick } from '../../three/Scene3D';
import { clamp01, easeInOut, lerp } from '../../lib/anim';

// ------------------------------------------------------------------ the puzzle

const GAP = 24;
const U = BAR.unit;
const TH = trackHeight();
/** the items' size chips, in px on screen */
const CHIP_PX = 24;

/**
 * Two layouts of the same puzzle, in px before scaling:
 *  - wide (compact = 0): the four items in one row (the tray), the two bins below;
 *  - compact (compact = 1): the items in two rows, each row the items of one bin in the packing
 *    (6 + 4, then 2 + 8) and exactly as wide as a bin, above the two bins: the narrow form that
 *    fits the pipeline's left stage. (Rows 6, 2 / 8, 4 read as a packing that does not fit.)
 * The bins are named "bin 1", "bin 2" in both.
 */
interface Layout {
  w: number;
  h: number;
  tray: [number, number][];
  binX: number;
  binY: [number, number];
}
const WIDE: Layout = (() => {
  const xs = M.SIZES.reduce<number[]>((acc, _s, i) => [...acc, i === 0 ? 0 : acc[i - 1] + M.SIZES[i - 1] * U + GAP], []);
  const w = xs[xs.length - 1] + M.SIZES[M.SIZES.length - 1] * U;
  const binY: [number, number] = [150, 150 + TH + 72];
  return { w, h: binY[1] + TH, tray: xs.map((x) => [x, 0] as [number, number]), binX: (w - (M.B * U + 9)) / 2, binY };
})();
/** the gap between the two items of a row in the compact layout: a row of 10 units is then as wide as a bin */
const ROW_GAP = 8;
const COMPACT: Layout = (() => {
  const w = trackWidth(M.B);
  const tray: [number, number][] = [];
  M.PACKING.forEach((r, k) => {
    const rowW = r.reduce((t, u) => t + M.SIZES[u] * U, 0) + (r.length - 1) * ROW_GAP;
    let x = (w - rowW) / 2;
    for (const u of r) {
      tray[u] = [x, k * (BAR.h + 14)];
      x += M.SIZES[u] * U + ROW_GAP;
    }
  });
  // room above each bin for its name
  const top = 2 * BAR.h + 14 + 56;
  const binY: [number, number] = [top, top + TH + 48];
  return { w, h: binY[1] + TH, tray, binX: 0, binY };
})();
/** in between: the items first move down to their row, then across, so no two ever overlap */
const mix = (k: number): Layout => ({
  w: lerp(WIDE.w, COMPACT.w, k),
  h: lerp(WIDE.h, COMPACT.h, k),
  tray: WIDE.tray.map((p, u) => [lerp(p[0], COMPACT.tray[u][0], easeInOut(clamp01(k * 2 - 0.8))), lerp(p[1], COMPACT.tray[u][1], easeInOut(clamp01(k * 2)))] as [number, number]),
  binX: lerp(WIDE.binX, COMPACT.binX, k),
  binY: [lerp(WIDE.binY[0], COMPACT.binY[0], k), lerp(WIDE.binY[1], COMPACT.binY[1], k)],
});

/** the bin and slot each item goes to in the packing 6 + 4, 2 + 8 */
const TARGET: { bin: number; slot: number }[] = (() => {
  const out: { bin: number; slot: number }[] = [];
  M.PACKING.forEach((items, b) => {
    let k = 0;
    for (const u of items) {
      out[u] = { bin: b, slot: k };
      k += M.SIZES[u];
    }
  });
  return out;
})();

/** where a puzzle sits: its centre on screen, its scale, and how far it is in its compact layout (0..1) */
export interface PuzzleAt {
  cx: number;
  cy: number;
  scale: number;
  compact: number;
}
/** the pipeline's row: the y of the centres of its three stages */
export const PIPE_Y = 390;
/** full-size puzzle in the middle of the picture (cue 1 of "plan" and "instance") */
export const PUZZLE_BIG: PuzzleAt = { cx: 960, cy: 400, scale: 1.15, compact: 0 };
/** the puzzle as the left stage of the pipeline */
export const PUZZLE_SMALL: PuzzleAt = { cx: 390, cy: PIPE_Y, scale: 0.85, compact: 1 };
export const mixAt = (p: PuzzleAt, q: PuzzleAt, t: number, tc = t): PuzzleAt => ({
  cx: lerp(p.cx, q.cx, t),
  cy: lerp(p.cy, q.cy, t),
  scale: lerp(p.scale, q.scale, t),
  compact: lerp(p.compact, q.compact, tc),
});

export interface PuzzleProps {
  at: PuzzleAt;
  /** per item, 0..1: how far it has moved from the tray into its bin */
  place?: number[];
  /** per item, 0..1: appearance (scale-in) */
  appear?: number[];
  /** the bins' opacity (0..1) */
  bins?: number;
  opacity?: number;
}

export function Puzzle({ at, place = [0, 0, 0, 0], appear = [1, 1, 1, 1], bins = 1, opacity = 1 }: PuzzleProps) {
  if (opacity <= 0) return null;
  const L = mix(clamp01(at.compact));
  const landed = [0, 0];
  const count = [0, 0];
  M.SIZES.forEach((s, u) => {
    if (place[u] >= 1) {
      landed[TARGET[u].bin] += s;
      count[TARGET[u].bin]++;
    }
  });
  // a bin's border turns green as its second item settles (over the last fifth of its flight)
  const fullIn = [0, 1].map((b) => {
    const mine = M.SIZES.map((_, u) => u).filter((u) => TARGET[u].bin === b);
    return mine.length === 2 && mine.reduce((a, u) => a + M.SIZES[u], 0) === M.B ? clamp01((Math.min(...mine.map((u) => place[u])) - 0.8) / 0.2) : 0;
  });
  const items = M.SIZES.map((size, u) => {
    const t = easeInOut(place[u]);
    const tg = TARGET[u];
    const bx = slotX(L.binX, tg.slot);
    const by = slotY(L.binY[tg.bin]);
    const x = lerp(L.tray[u][0], bx, t);
    const arc = Math.sin(Math.PI * t) * 46;
    const y = lerp(L.tray[u][1], by, t) - arc;
    const a = clamp01(appear[u]);
    const lift = Math.sin(Math.PI * t);
    const s = 0.85 + 0.15 * a;
    return { u, size, x, y, a, lift, s, moving: t > 0 && t < 1 };
  });
  // moving items are drawn last, on top
  items.sort((p, q) => Number(p.moving) - Number(q.moving));
  // the bins' names, in the sub-line style of the bins elsewhere (22 px on screen whatever the scale)
  const nameFont = 22 / at.scale;
  // the size chips keep about 24 px on screen whatever the scale (the bar's own chip would shrink with it)
  const chipFont = Math.min(28, Math.max(20, CHIP_PX / at.scale));
  const chipH = Math.min(BAR.h - 6, chipFont * 1.4);
  const chipW = chipFont * 1.45;
  const x0 = at.cx - (L.w * at.scale) / 2;
  const y0 = at.cy - (L.h * at.scale) / 2;
  return (
    <g opacity={opacity} transform={`translate(${x0} ${y0}) scale(${at.scale})`}>
      {[0, 1].map((b) => (
        <BinTrack
          key={b}
          x={L.binX}
          y={L.binY[b]}
          B={M.B}
          opacity={bins}
          covered={landed[b]}
          full={fullIn[b]}
        />
      ))}
      {[0, 1].map((b) => (
        <text key={b} x={L.binX + 2} y={L.binY[b] - 12} fontFamily={FONT.sans} fontSize={nameFont} fontWeight={500} fill={C.fgMuted} opacity={bins}>
          bin {b + 1} · size {M.B}
        </text>
      ))}
      {items.map((it) =>
        it.a <= 0 ? null : (
          <g key={it.u} transform={`translate(${it.x + (it.size * U) / 2} ${it.y + BAR.h / 2}) scale(${it.s}) translate(${-(it.x + (it.size * U) / 2)} ${-(it.y + BAR.h / 2)})`}>
            <ItemBar x={it.x} y={it.y} size={it.size} color={itemColor(it.u)} opacity={it.a} lift={it.lift} chip={false} />
            {it.a > 0 && (
              <g opacity={it.a}>
                <rect x={it.x + (it.size * U) / 2 - chipW / 2} y={it.y + BAR.h / 2 - chipH / 2} width={chipW} height={chipH} rx={5} fill={C.bgElev} />
                <text x={it.x + (it.size * U) / 2} y={it.y + BAR.h / 2 + chipFont * 0.35} textAnchor="middle" fontFamily={FONT.sans} fontWeight={650} fontSize={chipFont} fill={C.fg} style={{ fontVariantNumeric: 'tabular-nums' }}>
                  {it.size}
                </text>
              </g>
            )}
          </g>
        ),
      )}
    </g>
  );
}

/** screen box of a puzzle placement (for arrows and labels) */
export const puzzleBox = (at: PuzzleAt) => {
  const L = mix(clamp01(at.compact));
  const w = L.w * at.scale;
  const h = L.h * at.scale;
  return { left: at.cx - w / 2, right: at.cx + w / 2, top: at.cy - h / 2, bottom: at.cy + h / 2, cx: at.cx, cy: at.cy };
};

// ------------------------------------------------------------------ an HP string, flat

/** how many letters behind the tip a newly written bead of a FlatString takes to fade in */
const FLAT_FADE = 3.5;

/**
 * An HP string as the fold game draws it in 2D: H filled orange, P a white disc with a blue rim,
 * grey backbone. It is written with one tip, left to right: the backbone grows from bead to bead,
 * and each bead appears at full size, fading in as the tip reaches it. The backbone runs between
 * the beads' rims, so nothing shows through a bead while it fades in.
 */
export function FlatString({
  x,
  y,
  seq,
  step = 32,
  progress = 1,
  breakAfter = [],
  tail = true,
}: {
  x: number;
  y: number;
  seq: string;
  step?: number;
  /** 0..1, the string is written left to right */
  progress?: number;
  /** a break mark (the string goes on) after these indices */
  breakAfter?: number[];
  /** "…" at the right end */
  tail?: boolean;
}) {
  const R = 0.27 * step;
  const r0 = R / step;
  const xs: number[] = [];
  let cx = x + R;
  for (let i = 0; i < seq.length; i++) {
    xs.push(cx);
    cx += step + (breakAfter.includes(i) ? step * 0.9 : 0);
  }
  // the tip, in letters: at -r0 it touches the first bead's rim, at seq.length - 1 + 1 the tail is out
  const end = seq.length - 1 + (tail ? 1 : 0) + FLAT_FADE;
  const head = -r0 + clamp01(progress) * (end + r0);
  const beadO = (i: number) => clamp01((head - (i - r0)) / FLAT_FADE);
  const sw = 0.075 * step;
  const parts: React.ReactNode[] = [];
  for (let i = 0; i + 1 < seq.length; i++) {
    // the stick from bead i's rim to bead i + 1's rim, grown by the tip
    const g = clamp01((head - (i + r0)) / (1 - 2 * r0));
    if (g <= 0) break;
    const x1 = xs[i] + R;
    const x2 = xs[i + 1] - R;
    if (breakAfter.includes(i)) {
      const mx = (xs[i] + xs[i + 1]) / 2;
      parts.push(
        <g key={`b${i}`} opacity={g}>
          <line x1={x1} x2={mx - 7} y1={y} y2={y} stroke={C.backbone} strokeWidth={sw} strokeLinecap="butt" />
          <line x1={mx + 7} x2={x2} y1={y} y2={y} stroke={C.backbone} strokeWidth={sw} strokeLinecap="butt" />
          <line x1={mx - 10} x2={mx - 2} y1={y + 10} y2={y - 10} stroke={C.fgSubtle} strokeWidth={2} strokeLinecap="round" />
          <line x1={mx + 2} x2={mx + 10} y1={y + 10} y2={y - 10} stroke={C.fgSubtle} strokeWidth={2} strokeLinecap="round" />
        </g>,
      );
    } else {
      parts.push(<line key={`l${i}`} x1={x1} x2={lerp(x1, x2, g)} y1={y} y2={y} stroke={C.backbone} strokeWidth={sw} strokeLinecap="butt" />);
    }
  }
  for (let i = 0; i < seq.length; i++) {
    const o = beadO(i);
    if (o <= 0) break;
    const h = seq[i] === 'H';
    parts.push(<circle key={`c${i}`} cx={xs[i]} cy={y} r={R} fill={h ? C.h : C.bgElev} stroke={h ? C.h : C.p} strokeWidth={0.07 * step} opacity={o} />);
  }
  if (tail) {
    const t = clamp01((head - (seq.length - 1 + r0)) / FLAT_FADE);
    const ex = xs[xs.length - 1] + R + 14;
    parts.push(
      <g key="tail" opacity={t}>
        {[0, 1, 2].map((k) => (
          <circle key={k} cx={ex + k * 11} cy={y} r={2.6} fill={C.fgSubtle} />
        ))}
      </g>,
    );
  }
  return <g>{parts}</g>;
}
/** width of a FlatString in px */
export const flatStringWidth = (seq: string, step = 32, breaks = 0, tail = true) => (seq.length - 1) * step + 0.54 * step + breaks * step * 0.9 + (tail ? 14 + 22 + 3 : 0);

/** the string of the pipeline: a rod piece, a ribbon piece, a run of P's */
export const PIPE_SEQ = 'PHPPHPPHHPPHHP';
export const PIPE_BREAKS = [7];

// ------------------------------------------------------------------ the small cube of H's

const SIDE = 3;
/** a snake through a SIDE³ cube, as one chain of neighbours */
const SNAKE: V3[] = (() => {
  const out: V3[] = [];
  let rowFlip = false;
  let layerFlip = false;
  for (let zi = 0; zi < SIDE; zi++) {
    const ys = Array.from({ length: SIDE }, (_, i) => (layerFlip ? SIDE - 1 - i : i));
    for (const y of ys) {
      const xs = Array.from({ length: SIDE }, (_, i) => (rowFlip ? SIDE - 1 - i : i));
      for (const x of xs) out.push([x, y, -zi]);
      rowFlip = !rowFlip;
    }
    layerFlip = !layerFlip;
  }
  return out;
})();
/**
 * The best fold of the pipeline: the H's fill the cube and the P's stick out of it, as in a real
 * fold: a tail at each end and a short loop on the top face.
 */
const SMALL_LETTERS: Letter[] = (() => {
  const H = (pos: V3): Letter => ({ pos, h: true });
  const P = (pos: V3): Letter => ({ pos, h: false });
  const hs = SNAKE.map(H);
  return [
    P([0, 0, 2]),
    P([0, 0, 1]),
    ...hs.slice(0, 11), // (0,0,0) … (1,2,−1)
    P([1, 3, -1]),
    P([0, 3, -1]),
    ...hs.slice(11), // (0,2,−1) … (2,2,−2)
    P([2, 3, -2]),
    P([2, 4, -2]),
  ];
})();
const SMALL_CENTER: V3 = [(SIDE - 1) / 2, (SIDE - 1) / 2, -(SIDE - 1) / 2];

/** where the pipeline's cube sits on screen */
export const CUBE_SCREEN = { x: 1636, y: PIPE_Y };

/**
 * The view of a 3 × 3 × 3 cube of beads used in "plan", "cube" and "end": about 36° round from
 * straight on and 20° from above. From the game's usual view a bead of the back layer sits almost
 * exactly behind one of the front layer, and the cube reads as a heap; from here the 27 beads
 * stand apart as far as they can, and the three faces read as grids.
 */
export const CUBE3_DIR: V3 = (() => {
  const az = (36 * Math.PI) / 180;
  const el = (20 * Math.PI) / 180;
  return [Math.sin(az) * Math.cos(el), Math.sin(el), Math.cos(az) * Math.cos(el)];
})();

// ------------------------------------------------------------------ laying a chain, one tip at a time

/** frames a newly laid bead takes to fade in, at full size */
export const BEAD_FADE = 6;

/**
 * When the tip of a chain being laid reaches each of its `n` letters, laying from frame `from` for
 * `dur` frames as one eased move: the tip starts and ends at about a third of its top speed (a
 * full ease would crawl over the first beads and then rush the middle).
 */
export function chainTimes(n: number, from: number, dur: number): number[] {
  const a = 0.6;
  // the tip has gone a fraction s(t) of the way at time fraction t; speed 1 − a at the ends, 1 + a in the middle
  const s = (t: number) => t - (a * Math.sin(2 * Math.PI * t)) / (2 * Math.PI);
  const inv = (x: number) => {
    let lo = 0;
    let hi = 1;
    for (let k = 0; k < 40; k++) {
      const m = (lo + hi) / 2;
      if (s(m) < x) lo = m;
      else hi = m;
    }
    return (lo + hi) / 2;
  };
  return Array.from({ length: n }, (_, i) => (n <= 1 ? from : from + dur * inv(i / (n - 1))));
}

/** one letter of a chain to lay: where it goes and how its bead looks */
export interface ChainLetter {
  pos: V3;
  color: string;
  hollow?: boolean;
  r?: number;
}

/**
 * A chain laid with one growing tip, in string order (the protein is one string): the stick from
 * letter i grows to letter i + 1 between their times, and each bead appears at full size, fading
 * in from the moment the tip reaches its surface. `fade` (0..1) fades the whole chain out.
 * Sticks join only letters that are lattice neighbours.
 */
export function layChain(f: number, times: number[], letters: ChainLetter[], beads: Bead[], sticks: Stick[], opts: { fade?: number; stickR?: number; joinAll?: boolean } = {}) {
  const fade = opts.fade ?? 0;
  if (fade >= 1) return;
  const n = letters.length;
  const unit = (a: V3, b: V3) => Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]) + Math.abs(a[2] - b[2]) === 1;
  for (let i = 0; i + 1 < n; i++) {
    const g = clamp01((f - times[i]) / Math.max(1e-3, times[i + 1] - times[i]));
    if (g <= 0) break;
    if (!opts.joinAll && !unit(letters[i].pos, letters[i + 1].pos)) continue;
    sticks.push({ a: letters[i].pos, b: letters[i + 1].pos, color: C.backbone, r: opts.stickR, grow: g, fade: fade > 0 ? fade : undefined });
  }
  for (let i = 0; i < n; i++) {
    const l = letters[i];
    const o = beadIn(f, times, i, l.r);
    if (o <= 0) break;
    beads.push({ pos: l.pos, color: l.color, hollow: l.hollow, r: l.r, fade: 1 - o * (1 - fade) });
  }
}

/** how far bead i of a chain laid with `times` has faded in (0..1): from when the tip touches its surface */
export function beadIn(f: number, times: number[], i: number, r = 0.3): number {
  const start = i === 0 ? times[0] : lerp(times[i - 1], times[i], 1 - r);
  return clamp01((f - start) / BEAD_FADE);
}

/** the radius of a dashed link: a contact (gold) or a contact lost (red) */
export const R_LINK = 0.05;
/**
 * A dashed link from a bead at `a` towards `b`: a contact in gold, or a contact lost in red. It is
 * drawn as separate short sticks that start and end a small gap away from the beads' surfaces
 * (`ra`, `rb`: how far from a and from b the dashes may go), so no dash is ever cut by a bead.
 * `grow` 0..1 draws it from a towards b.
 */
export function dashLink(a: V3, b: V3, color: string, opts: { ra?: number; rb?: number; grow?: number; fade?: number; r?: number } = {}): Stick[] {
  const { ra = 0.3, rb = 0.3, grow = 1, fade, r = R_LINK } = opts;
  const GAP = 0.055;
  const DASH = 0.07;
  const d: V3 = [b[0] - a[0], b[1] - a[1], b[2] - a[2]];
  const len = Math.hypot(d[0], d[1], d[2]);
  const s0 = ra + GAP;
  const avail = len - rb - GAP - s0;
  if (avail <= 0 || grow <= 0 || (fade ?? 0) >= 1) return [];
  const n = Math.max(1, Math.round((avail + GAP) / (DASH + GAP)));
  const dash = (avail - (n - 1) * GAP) / n;
  const reach = s0 + clamp01(grow) * avail;
  const at = (s: number): V3 => [a[0] + (d[0] * s) / len, a[1] + (d[1] * s) / len, a[2] + (d[2] * s) / len];
  const out: Stick[] = [];
  for (let k = 0; k < n; k++) {
    const st = s0 + k * (dash + GAP);
    const en = Math.min(st + dash, reach);
    if (en <= st + 1e-3) break;
    out.push({ a: at(st), b: at(en), color, r, fade: fade && fade > 0 ? fade : undefined });
  }
  return out;
}

/** the small cube's letters, as a chain to lay */
const SMALL_CHAIN: ChainLetter[] = SMALL_LETTERS.map((l) => (l.h ? { pos: l.pos, color: C.h } : { pos: l.pos, color: C.p, hollow: true }));

/**
 * Beads and sticks of the small cube, laid in chain order with one tip from frame `from` for `dur`
 * frames, and a faint outline of its cube (the contour only) with opacity `box`.
 */
export function smallCube(f: number, from: number, dur: number, box = 0): { beads: Bead[]; sticks: Stick[]; lines: Stick[] } {
  const beads: Bead[] = [];
  const sticks: Stick[] = [];
  if (f >= from) layChain(f, chainTimes(SMALL_CHAIN.length, from, dur), SMALL_CHAIN, beads, sticks);
  const lines = box > 0 ? contourBox([-0.5, -0.5, -SIDE + 0.5], [SIDE - 0.5, SIDE - 0.5, 0.5], box) : [];
  return { beads, sticks, lines };
}

/**
 * The outline of a box as the camera sees it (its contour: Scene3D leaves out the edges that
 * would cross the beads inside), faint grey, `opacity` 0..1.
 */
export function contourBox(min: V3, max: V3, opacity: number, r = 0.016): Stick[] {
  if (opacity <= 0) return [];
  const corner = (m: number): V3 => [m & 1 ? max[0] : min[0], m & 2 ? max[1] : min[1], m & 4 ? max[2] : min[2]];
  const out: Stick[] = [];
  for (let m = 0; m < 8; m++) for (const bit of [1, 2, 4]) if (!(m & bit)) out.push({ a: corner(m), b: corner(m | bit), color: C.fgSubtle, r, fade: 1 - 0.8 * opacity, box: { min, max } });
  return out;
}

/** a shot that puts the small cube at CUBE_SCREEN; `turn` in degrees (a slow yaw) */
export function smallCubeShot(turn = 0): Shot {
  return { target: SMALL_CENTER, dir: yaw(CUBE3_DIR, turn), dist: 28, offset: [CUBE_SCREEN.x - 960, CUBE_SCREEN.y - 540] };
}
/** half the cube's size on screen, roughly (for arrows and labels) */
export const CUBE_HALF = 150;

// ------------------------------------------------------------------ arrows and labels

/** a curved arrow along a quadratic curve from `a` through control `c` to `b` */
export function CurvedArrow({
  a,
  c,
  b,
  progress = 1,
  opacity = 1,
  color = C.fgMuted,
  width = 2.5,
}: {
  a: [number, number];
  c: [number, number];
  b: [number, number];
  progress?: number;
  opacity?: number;
  color?: string;
  width?: number;
}) {
  if (progress <= 0 || opacity <= 0) return null;
  // the arrow fades in over the first quarter of its growth, so its head never shows alone as a speck
  opacity *= clamp01(progress / 0.25);
  const N = 40;
  const pts: [number, number][] = [];
  const at = (t: number): [number, number] => [(1 - t) * (1 - t) * a[0] + 2 * (1 - t) * t * c[0] + t * t * b[0], (1 - t) * (1 - t) * a[1] + 2 * (1 - t) * t * c[1] + t * t * b[1]];
  for (let i = 0; i <= N; i++) pts.push(at((i / N) * progress));
  const end = pts[pts.length - 1];
  const prev = pts[pts.length - 2];
  const ang = Math.atan2(end[1] - prev[1], end[0] - prev[0]);
  const hl = 15;
  const p1 = [end[0] - hl * Math.cos(ang - 0.45), end[1] - hl * Math.sin(ang - 0.45)];
  const p2 = [end[0] - hl * Math.cos(ang + 0.45), end[1] - hl * Math.sin(ang + 0.45)];
  return (
    <g opacity={opacity}>
      <path d={`M${pts.map((p) => `${p[0].toFixed(1)},${p[1].toFixed(1)}`).join(' L')}`} fill="none" stroke={color} strokeWidth={width} strokeLinecap="round" strokeLinejoin="round" />
      <path d={`M${p1[0]},${p1[1]} L${end[0]},${end[1]} L${p2[0]},${p2[1]}`} fill="none" stroke={color} strokeWidth={width} strokeLinecap="round" strokeLinejoin="round" />
    </g>
  );
}

/** the two label styles on pictures: a name, and a sub-line under it */
export const NAME = { size: 26, weight: 600, color: C.fg } as const;
export const SUB = { size: 22, weight: 500, color: C.fgMuted } as const;

export function Label({ x, y, children, opacity = 1, anchor = 'middle', size = 24, color = C.fgMuted, weight = 500 }: { x: number; y: number; children: React.ReactNode; opacity?: number; anchor?: 'start' | 'middle' | 'end'; size?: number; color?: string; weight?: number }) {
  if (opacity <= 0) return null;
  return (
    <text x={x} y={y} textAnchor={anchor} fontFamily={FONT.sans} fontSize={size} fontWeight={weight} fill={color} opacity={opacity}>
      {children}
    </text>
  );
}

// ------------------------------------------------------------------ cube boxes

/**
 * A cube from `min` to `min + side` as a solid-looking box: the three faces the game's camera
 * sees (top, front, right) lightly tinted, and the twelve edges. `px` is the stroke width wanted
 * on screen and `unitPx` how many px one lattice unit spans, so lines keep their width when the
 * camera moves.
 */
export function cubeBox(min: V3, side: number, opts: { color?: string; opacity?: number; linePx?: number; unitPx: number; tint?: number }) {
  const { color = C.h, opacity = 1, linePx = 1.6, unitPx, tint = 1 } = opts;
  const r = linePx / 2 / unitPx;
  const [x0, y0, z0] = min;
  const x1 = x0 + side;
  const y1 = y0 + side;
  const zb = z0 - side;
  const c: V3[] = [
    [x0, y0, z0],
    [x1, y0, z0],
    [x1, y1, z0],
    [x0, y1, z0],
    [x0, y0, zb],
    [x1, y0, zb],
    [x1, y1, zb],
    [x0, y1, zb],
  ];
  const E = [
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
  // the three edges at the back-bottom-left corner (c[4]) are hidden from the game's camera; leaving
  // them out keeps the box from reading as an open room
  const lines: Stick[] = opacity <= 0 ? [] : E.filter(([i, j]) => i !== 4 && j !== 4).map(([i, j]) => ({ a: c[i], b: c[j], color, r, fade: 1 - opacity }));
  const panels: { corners: [V3, V3, V3, V3]; color: string; opacity: number }[] =
    opacity <= 0 || tint <= 0
      ? []
      : [
          { corners: [c[3], c[2], c[6], c[7]], color, opacity: 0.12 * opacity * tint }, // top
          { corners: [c[0], c[1], c[2], c[3]], color, opacity: 0.2 * opacity * tint }, // front
          { corners: [c[1], c[5], c[6], c[2]], color, opacity: 0.3 * opacity * tint }, // right
        ];
  return { lines, panels };
}

/** px per lattice unit at the target of a shot (FOV 30, 1080 px high) */
export const unitPxAt = (dist: number, fov = 30) => 1080 / (2 * dist * Math.tan(((fov / 2) * Math.PI) / 180));

// ------------------------------------------------------------------ the whole pipeline (plan, end)

const STEP = 32;
const STR_W = flatStringWidth(PIPE_SEQ, STEP, PIPE_BREAKS.length);
const STR_X = 815;
/** centre x of the pipeline's string */
export const STRING_CX = STR_X + STR_W / 2;
/** the stages' names, under the row */
export const PIPE_LABEL_Y = PIPE_Y + 196;
/** a stage's second line, small and grey, under its name */
export const PIPE_SUB_Y = PIPE_LABEL_Y + 32;
/** the arrow back from the fold to the puzzle: where its ends are, its lowest point, and its label just above it */
const BACK_END_Y = PIPE_SUB_Y + 28;
const BACK_Y = 905;
const BACK_LABEL_Y = 730;

export interface PipelineProps {
  /** the puzzle's placement (it moves in "plan") */
  at?: PuzzleAt;
  place?: number[];
  appear?: number[];
  /**
   * 0..1 each: the puzzle's opacity, its name, its second line ("a hard puzzle"), arrow 1, the
   * string, arrow 2, the cube's name, the arrow back, its label, the note under the fold arrow
   * ("a fast program?") and the cube's second line ("at least as hard")
   */
  puzzle?: number;
  puzzleLabel?: number;
  hard?: number;
  a1?: number;
  str?: number;
  a2?: number;
  cubeLabel?: number;
  a3?: number;
  l3?: number;
  fast?: number;
  asHard?: number;
}

/**
 * The SVG half of the pipeline puzzle → HP string → best fold, and the arrow back
 * ("fits / does not fit"). The cube itself is 3D: draw smallCube() in a Scene3D with smallCubeShot().
 * Layout (px): puzzle 182–598, arrow, string 815–1316, arrow, cube 1486–1786; names at PIPE_LABEL_Y,
 * second lines at PIPE_SUB_Y.
 */
export function Pipeline({ at = PUZZLE_SMALL, place, appear, puzzle = 1, puzzleLabel = 1, hard = 1, a1 = 1, str = 1, a2 = 1, cubeLabel = 1, a3 = 1, l3 = 1, fast = 0, asHard = 0 }: PipelineProps) {
  const box = puzzleBox(PUZZLE_SMALL);
  const y = PIPE_Y;
  const mid = (box.cx + CUBE_SCREEN.x) / 2;
  const foldFrom = STR_X + STR_W + 25;
  const foldTo = CUBE_SCREEN.x - CUBE_HALF - 25;
  return (
    <g>
      <Puzzle at={at} place={place} appear={appear} opacity={puzzle} />
      <Label x={box.cx} y={PIPE_LABEL_Y} opacity={puzzleLabel} {...NAME}>
        bin packing puzzle
      </Label>
      <Label x={box.cx} y={PIPE_SUB_Y} opacity={hard} {...SUB}>
        a hard puzzle
      </Label>
      <Arrow from={[box.right + 25, y]} to={[STR_X - 25, y]} progress={a1} opacity={clamp01(a1 / 0.25)} label="we write" />
      {str > 0 && <FlatString x={STR_X} y={y} seq={PIPE_SEQ} step={STEP} breakAfter={PIPE_BREAKS} progress={str} />}
      <Label x={STRING_CX} y={PIPE_LABEL_Y} opacity={clamp01(str * 2 - 1)} {...NAME}>
        HP string
      </Label>
      <Arrow from={[foldFrom, y]} to={[foldTo, y]} progress={a2} opacity={clamp01(a2 / 0.25)} label="fold" />
      <Label x={(foldFrom + foldTo) / 2} y={y + 36} opacity={fast} {...SUB}>
        a fast program?
      </Label>
      <Label x={CUBE_SCREEN.x} y={PIPE_LABEL_Y} opacity={cubeLabel} {...NAME}>
        best fold
      </Label>
      <Label x={CUBE_SCREEN.x} y={PIPE_SUB_Y} opacity={asHard} {...SUB}>
        at least as hard
      </Label>
      {/* the arrow back is a step of logic, not the next stage: accent, as the arrows of steps 23–25 */}
      <CurvedArrow a={[CUBE_SCREEN.x, BACK_END_Y]} c={[mid, BACK_Y]} b={[box.cx, BACK_END_Y]} progress={a3} color={C.accent} />
      <Label x={mid} y={BACK_LABEL_Y} opacity={l3} {...NAME} color={C.accent}>
        fits / does not fit
      </Label>
    </g>
  );
}
