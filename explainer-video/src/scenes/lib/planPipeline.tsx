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
import { clamp01, lerp } from '../../lib/anim';

// ------------------------------------------------------------------ the puzzle

const GAP = 24;
const U = BAR.unit;
const TH = trackHeight();
const BW = trackWidth(M.B);

/**
 * One layout, in px before scaling (the puzzle only moves and scales, so it looks the same in
 * every step): the four items in one row in their order (the tray), and below it the two bins side
 * by side, exactly as wide as the tray. Between the tray and the bins runs a lane as high as an
 * item, clear of both: an item goes down into the lane, along it, and down into its bin, so it never
 * passes over another item, a bin it does not go into, or a label. The bins' names sit under them.
 */
const TRAY_X = M.SIZES.reduce<number[]>((acc, _s, i) => [...acc, i === 0 ? 0 : acc[i - 1] + M.SIZES[i - 1] * U + GAP], []);
const PW = TRAY_X[TRAY_X.length - 1] + M.SIZES[M.SIZES.length - 1] * U;
/** the top of an item in the lane, and the bins' top */
const LANE_Y = 66;
const BIN_Y = 150;
const BIN_X = [0, PW - BW];
const PH = BIN_Y + TH;
/** the radius of the path's corners, in px before scaling */
const TURN_R = 46;

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

/**
 * Item u's way from the tray to its bin (the top-left corner of the bar): down into the lane,
 * along it, down into the bin, with rounded corners, as one smooth path. `at(s)` is the point at
 * arc length s.
 */
const PATHS = M.SIZES.map((_, u) => {
  const x0 = TRAY_X[u];
  const tg = TARGET[u];
  const x1 = slotX(BIN_X[tg.bin], tg.slot);
  const y1 = slotY(BIN_Y);
  const dx = x1 - x0;
  const sx = Math.sign(dx);
  const r = Math.min(TURN_R, Math.abs(dx) / 2);
  type Seg = { len: number; at: (s: number) => [number, number] };
  const line = (a: [number, number], b: [number, number]): Seg => {
    const len = Math.hypot(b[0] - a[0], b[1] - a[1]);
    return { len, at: (s) => [lerp(a[0], b[0], len ? s / len : 0), lerp(a[1], b[1], len ? s / len : 0)] };
  };
  const segs: Seg[] = [];
  if (r < 1) segs.push(line([x0, 0], [x1, y1]));
  else {
    const q = (r * Math.PI) / 2;
    segs.push(line([x0, 0], [x0, LANE_Y - r]));
    // down, turning towards the bin
    segs.push({ len: q, at: (s) => [x0 + sx * r * (1 - Math.cos(s / r)), LANE_Y - r + r * Math.sin(s / r)] });
    segs.push(line([x0 + sx * r, LANE_Y], [x1 - sx * r, LANE_Y]));
    // along, turning down into the bin
    segs.push({ len: q, at: (s) => [x1 - sx * r + sx * r * Math.sin(s / r), LANE_Y + r - r * Math.cos(s / r)] });
    segs.push(line([x1, LANE_Y + r], [x1, y1]));
  }
  const len = segs.reduce((t, g) => t + g.len, 0);
  const at = (s: number): [number, number] => {
    let rest = Math.min(Math.max(0, s), len);
    for (const g of segs) {
      if (rest <= g.len) return g.at(rest);
      rest -= g.len;
    }
    return [x1, y1];
  };
  return { len, at };
});
/**
 * Frames for each item's way into its bin: one eased move at a calm speed (at least 24 frames,
 * the longest about 1.8 s). Callers pass `place` as plain time (0..1 over these frames); the
 * puzzle eases it, once, at the two ends of the path.
 */
export const FLIGHT_FRAMES = PATHS.map((p) => Math.round(Math.min(56, Math.max(24, 14 + p.len / 16))));
/** an ease with no flat ends and a gentle middle (top speed 1.57 times the mean) */
const sine = (t: number) => (1 - Math.cos(Math.PI * clamp01(t))) / 2;

/** where a puzzle sits: its centre on screen, its scale, and how far its bins' names have gone (0..1) */
export interface PuzzleAt {
  cx: number;
  cy: number;
  scale: number;
  /** 0 = the bins' names under the bins (the puzzle on its own), 1 = without them (a stage of the pipeline) */
  compact: number;
}
/** the pipeline's row: the y of the centres of its three stages */
export const PIPE_Y = 390;
/** full-size puzzle in the middle of the picture (cue 1 of "plan" and "instance") */
export const PUZZLE_BIG: PuzzleAt = { cx: 960, cy: 400, scale: 1.15, compact: 0 };
/** the puzzle as the left stage of the pipeline: the same picture, smaller, from x = 60 */
export const PUZZLE_SMALL: PuzzleAt = { cx: 60 + (PW * 0.6) / 2, cy: PIPE_Y, scale: 0.6, compact: 1 };
export const mixAt = (p: PuzzleAt, q: PuzzleAt, t: number, tc = t): PuzzleAt => ({
  cx: lerp(p.cx, q.cx, t),
  cy: lerp(p.cy, q.cy, t),
  scale: lerp(p.scale, q.scale, t),
  compact: lerp(p.compact, q.compact, tc),
});

export interface PuzzleProps {
  at: PuzzleAt;
  /** per item, 0..1, plain time: how far it is on its way from the tray into its bin */
  place?: number[];
  /** per item, 0..1: its opacity (an item comes and goes by fading, at full size) */
  appear?: number[];
  /** the bins' opacity (0..1) */
  bins?: number;
  opacity?: number;
}

export function Puzzle({ at, place = [0, 0, 0, 0], appear = [1, 1, 1, 1], bins = 1, opacity = 1 }: PuzzleProps) {
  if (opacity <= 0) return null;
  // a bin's border turns green as its second item settles (over the last fifth of its way), and
  // goes with its items when they fade
  const fullIn = [0, 1].map((b) => {
    const mine = M.SIZES.map((_, u) => u).filter((u) => TARGET[u].bin === b);
    if (mine.length !== 2 || mine.reduce((a, u) => a + M.SIZES[u], 0) !== M.B) return 0;
    return clamp01((Math.min(...mine.map((u) => place[u])) - 0.8) / 0.2) * Math.min(...mine.map((u) => clamp01(appear[u])));
  });
  const items = M.SIZES.map((size, u) => {
    const t = clamp01(place[u]);
    const [x, y] = PATHS[u].at(sine(t) * PATHS[u].len);
    return { u, size, x, y, a: clamp01(appear[u]), lift: Math.sin(Math.PI * t), moving: t > 0 && t < 1 };
  });
  // a moving item is drawn last, on top (it passes over nothing, but its shadow may)
  items.sort((p, q) => Number(p.moving) - Number(q.moving));
  // the size chips: at least 20 px on screen whatever the scale, and never taller than the bar
  const chipFont = Math.max(20 / at.scale, Math.min(28, 24 / at.scale));
  const chipH = Math.min(BAR.h - 6, chipFont * 1.2);
  const chipW = chipFont * 1.45;
  // the bins' names: a name and a sub-line, at their usual size on screen whatever the scale
  const names = bins * clamp01(1 - 2.5 * at.compact);
  const k = 1 / at.scale;
  const x0 = at.cx - (PW * at.scale) / 2;
  const y0 = at.cy - (PH * at.scale) / 2;
  return (
    <g opacity={opacity} transform={`translate(${x0} ${y0}) scale(${at.scale})`}>
      {[0, 1].map((b) => (
        <BinTrack key={b} x={BIN_X[b]} y={BIN_Y} B={M.B} opacity={bins} full={fullIn[b]} />
      ))}
      {names > 0 &&
        [0, 1].map((b) => (
          <g key={b} opacity={names} fontFamily={FONT.sans}>
            <text x={BIN_X[b] + 2} y={PH + 32 * k} fontSize={26 * k} fontWeight={600} fill={C.fg}>
              bin {b + 1}
            </text>
            <text x={BIN_X[b] + 2} y={PH + 61 * k} fontSize={22 * k} fontWeight={500} fill={C.fgMuted}>
              size {M.B}
            </text>
          </g>
        ))}
      {items.map((it) =>
        it.a <= 0 ? null : (
          <g key={it.u} opacity={it.a}>
            <ItemBar x={it.x} y={it.y} size={it.size} color={itemColor(it.u)} lift={it.lift} chip={false} />
            <rect x={it.x + (it.size * U) / 2 - chipW / 2} y={it.y + BAR.h / 2 - chipH / 2} width={chipW} height={chipH} rx={5} fill={C.bgElev} />
            <text x={it.x + (it.size * U) / 2} y={it.y + BAR.h / 2 + chipFont * 0.35} textAnchor="middle" fontFamily={FONT.sans} fontWeight={650} fontSize={chipFont} fill={C.fg} style={{ fontVariantNumeric: 'tabular-nums' }}>
              {it.size}
            </text>
          </g>
        ),
      )}
    </g>
  );
}

/** screen box of a puzzle placement, without the bins' names (for arrows and labels) */
export const puzzleBox = (at: PuzzleAt) => {
  const w = PW * at.scale;
  const h = PH * at.scale;
  return { left: at.cx - w / 2, right: at.cx + w / 2, top: at.cy - h / 2, bottom: at.cy + h / 2, cx: at.cx, cy: at.cy };
};


// ------------------------------------------------------------------ an HP string, flat

/**
 * How many letters behind the tip a newly written bead of a FlatString takes to fade in: the
 * string's soft tip. A caller gives the string at least 2 frames per letter at its fastest, so a
 * bead takes at least 6 frames.
 */
const FLAT_FADE = 3;

/**
 * An HP string as the fold game draws it in 2D: H filled orange, P a white disc with a blue rim,
 * grey backbone. It is written with one tip, left to right: each bead fades in at full size as the
 * tip reaches it, and the backbone to it (and a break mark before it) comes with it, never
 * stronger than the fainter of the two beads it joins. The backbone runs between the beads' rims,
 * so nothing shows through a bead while it fades in.
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
  const xs: number[] = [];
  let cx = x + R;
  for (let i = 0; i < seq.length; i++) {
    xs.push(cx);
    cx += step + (breakAfter.includes(i) ? step * 0.9 : 0);
  }
  // the tip, in letters: it reaches bead i at i; the tail ("…") counts as one more letter
  const n = seq.length;
  const end = n - 1 + (tail ? 1 : 0) + FLAT_FADE;
  const head = clamp01(progress) * end;
  const beadO = (i: number) => sine(clamp01((head - i) / FLAT_FADE));
  const sw = 0.075 * step;
  const parts: React.ReactNode[] = [];
  for (let i = 0; i + 1 < n; i++) {
    const o = Math.min(beadO(i), beadO(i + 1));
    if (o <= 0) break;
    const x1 = xs[i] + R;
    const x2 = xs[i + 1] - R;
    if (breakAfter.includes(i)) {
      const mx = (xs[i] + xs[i + 1]) / 2;
      parts.push(
        <g key={`b${i}`} opacity={o}>
          <line x1={x1} x2={mx - 7} y1={y} y2={y} stroke={C.backbone} strokeWidth={sw} strokeLinecap="butt" />
          <line x1={mx + 7} x2={x2} y1={y} y2={y} stroke={C.backbone} strokeWidth={sw} strokeLinecap="butt" />
          <line x1={mx - 10} x2={mx - 2} y1={y + 10} y2={y - 10} stroke={C.fgSubtle} strokeWidth={2} strokeLinecap="round" />
          <line x1={mx + 2} x2={mx + 10} y1={y + 10} y2={y - 10} stroke={C.fgSubtle} strokeWidth={2} strokeLinecap="round" />
        </g>,
      );
    } else {
      parts.push(<line key={`l${i}`} x1={x1} x2={x2} y1={y} y2={y} stroke={C.backbone} strokeWidth={sw} strokeLinecap="butt" opacity={o} />);
    }
  }
  for (let i = 0; i < n; i++) {
    const o = beadO(i);
    if (o <= 0) break;
    const h = seq[i] === 'H';
    parts.push(<circle key={`c${i}`} cx={xs[i]} cy={y} r={R} fill={h ? C.h : C.bgElev} stroke={h ? C.h : C.p} strokeWidth={0.07 * step} opacity={o} />);
  }
  if (tail) {
    const t = beadO(n);
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
/**
 * The ease for writing a FlatString or laying a chain: the tip starts and ends at 0.7 of its mean
 * speed and is never faster than 1.3 times it, so its soft tip keeps the same length.
 */
export const gentle = (t: number) => {
  t = clamp01(t);
  return t - (0.3 * Math.sin(2 * Math.PI * t)) / (2 * Math.PI);
};
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
export const CUBE_SCREEN = { x: 1690, y: PIPE_Y };

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

/** frames a newly laid bead takes to fade in, at full size (eased) */
export const BEAD_FADE = 6;

/**
 * When the tip of a chain being laid reaches each of its `n` letters, laying from frame `from` for
 * `dur` frames as one move: the tip's speed is 1 − a times its mean at the two ends and 1 + a
 * times it in the middle (a full ease would crawl over the first beads and then rush the middle).
 * With BEAD_FADE = 6, a tip that reaches a new bead every 2 frames or more at its fastest has at
 * most three beads fading in at once.
 */
export function chainTimes(n: number, from: number, dur: number, a = 0.6): number[] {
  // the tip has gone a fraction s(t) of the way at time fraction t
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
 * A chain laid with one tip, in string order (the protein is one string): each bead fades in at
 * its node, at full size, when the tip reaches it (by opacity, so it is see-through while it comes
 * and never a pale disc), and the stick from the bead before comes with it, never stronger than
 * the fainter of its two beads. `fade` (0..1) takes the whole chain away, the same way.
 * Sticks join only letters that are lattice neighbours, unless `joinAll`.
 */
export function layChain(f: number, times: number[], letters: ChainLetter[], beads: Bead[], sticks: Stick[], opts: { fade?: number; stickR?: number; joinAll?: boolean } = {}) {
  const keep = 1 - clamp01(opts.fade ?? 0);
  if (keep <= 0) return;
  const n = letters.length;
  const unit = (a: V3, b: V3) => Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]) + Math.abs(a[2] - b[2]) === 1;
  const o = letters.map((_, i) => beadIn(f, times, i) * keep);
  for (let i = 0; i + 1 < n; i++) {
    const m = Math.min(o[i], o[i + 1]);
    if (m <= 0) break;
    if (!opts.joinAll && !unit(letters[i].pos, letters[i + 1].pos)) continue;
    sticks.push({ a: letters[i].pos, b: letters[i + 1].pos, color: C.backbone, r: opts.stickR, fade: m < 0.999 ? 1 - m : undefined });
  }
  for (let i = 0; i < n; i++) {
    if (o[i] <= 0) break;
    const l = letters[i];
    beads.push({ pos: l.pos, color: l.color, hollow: l.hollow, r: l.r, opacity: o[i] < 0.999 ? o[i] : undefined });
  }
}

/** how far bead i of a chain laid with `times` has faded in (0..1, eased): from when the tip reaches it */
export function beadIn(f: number, times: number[], i: number): number {
  const t = clamp01((f - times[i]) / BEAD_FADE);
  return (1 - Math.cos(Math.PI * t)) / 2;
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

/** frames the small cube takes to lay: a new bead every 2 frames, at an even pace */
export const SMALL_CUBE_FRAMES = 2 * (SMALL_CHAIN.length - 1);

/**
 * Beads and sticks of the small cube, laid in chain order with one tip from frame `from` (a new
 * bead every 2 frames, so at most three fade in at once), and a faint outline of its cube (the
 * contour only) with opacity `box`.
 */
export function smallCube(f: number, from: number, box = 0): { beads: Bead[]; sticks: Stick[]; lines: Stick[] } {
  const beads: Bead[] = [];
  const sticks: Stick[] = [];
  if (f >= from) layChain(f, chainTimes(SMALL_CHAIN.length, from, SMALL_CUBE_FRAMES, 0), SMALL_CHAIN, beads, sticks);
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

const STEP = 30;
const STR_W = flatStringWidth(PIPE_SEQ, STEP, PIPE_BREAKS.length);
const BOX_S = puzzleBox(PUZZLE_SMALL);
/** arrow 1 ("we write") and the string */
const A1_FROM = BOX_S.right + 25;
const STR_X = A1_FROM + 90 + 25;
/** centre x of the pipeline's string */
export const STRING_CX = STR_X + STR_W / 2;
/** arrow 2 ("fold"): long enough for "a fast program?" under it, clear of the string and the cube */
const A2_FROM = STR_X + STR_W + 25;
const A2_TO = CUBE_SCREEN.x - CUBE_HALF - 10;
/** the stages' names, under the row */
export const PIPE_LABEL_Y = PIPE_Y + 196;
/** a stage's second line, small and grey, under its name */
export const PIPE_SUB_Y = PIPE_LABEL_Y + 32;
/** the arrow back from the fold to the puzzle: where its ends are, its lowest point, and its label just above it */
const BACK_END_Y = PIPE_SUB_Y + 28;
const BACK_Y = 905;
const BACK_LABEL_Y = 730;
const BACK_MID = (BOX_S.cx + CUBE_SCREEN.x) / 2;

/** a polyline through a curve, and the point at arc length s along it */
type Track = { pts: [number, number][]; cum: number[]; len: number };
const track = (pts: [number, number][]): Track => {
  const cum = [0];
  for (let i = 1; i < pts.length; i++) cum.push(cum[i - 1] + Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]));
  return { pts, cum, len: cum[cum.length - 1] };
};
const trackAt = (t: Track, s: number): [number, number] => {
  s = Math.max(0, Math.min(t.len, s));
  let i = 1;
  while (i < t.pts.length - 1 && t.cum[i] < s) i++;
  const g = t.cum[i] - t.cum[i - 1];
  const k = g > 0 ? (s - t.cum[i - 1]) / g : 0;
  return [lerp(t.pts[i - 1][0], t.pts[i][0], k), lerp(t.pts[i - 1][1], t.pts[i][1], k)];
};
const line = (a: [number, number], b: [number, number]) => track(Array.from({ length: 21 }, (_, i) => [lerp(a[0], b[0], i / 20), lerp(a[1], b[1], i / 20)] as [number, number]));
const quad = (a: [number, number], c: [number, number], b: [number, number]) =>
  track(
    Array.from({ length: 81 }, (_, i) => {
      const t = i / 80;
      return [(1 - t) * (1 - t) * a[0] + 2 * (1 - t) * t * c[0] + t * t * b[0], (1 - t) * (1 - t) * a[1] + 2 * (1 - t) * t * c[1] + t * t * b[1]] as [number, number];
    }),
  );
/**
 * The loop a fast program would run, as three legs: write the string, fold it, read off the
 * answer. Each leg: when it starts (frames after the run starts), how long its move takes, its
 * track (it ends where the arrow's head is) and the length of its trail.
 */
const RUN_LEGS = [
  { from: 0, dur: 18, tr: line([A1_FROM, PIPE_Y], [STR_X - 25, PIPE_Y]), trail: 50 },
  { from: 20, dur: 20, tr: line([A2_FROM, PIPE_Y], [A2_TO, PIPE_Y]), trail: 70 },
  { from: 42, dur: 58, tr: quad([CUBE_SCREEN.x, BACK_END_Y], [BACK_MID, BACK_Y], [BOX_S.cx, BACK_END_Y]), trail: 140 },
];
/** frames from the start of the run until its last leg has faded at the puzzle */
export const RUN_FRAMES = RUN_LEGS[2].from + RUN_LEGS[2].dur + 8;

/**
 * One pass of the loop: an accent dot with a short fading trail runs along each arrow in turn,
 * as one eased move per arrow, and fades in at the arrow's tail and out at its head. `run` is
 * frames since the pass started.
 */
function RunPulse({ run }: { run: number }) {
  const out: React.ReactNode[] = [];
  RUN_LEGS.forEach((leg, k) => {
    const t = (run - leg.from) / leg.dur;
    if (t <= 0 || run > leg.from + leg.dur + 8) return;
    const o = clamp01((run - leg.from) / 7) * clamp01((leg.from + leg.dur + 8 - run) / 8);
    if (o <= 0) return;
    const s = sine(t) * leg.tr.len;
    const N = 10;
    const tail = Math.min(leg.trail, s);
    const segs: React.ReactNode[] = [];
    for (let i = 0; i < N; i++) {
      const p = trackAt(leg.tr, s - tail + (tail * i) / N);
      const q = trackAt(leg.tr, s - tail + (tail * (i + 1)) / N);
      segs.push(<line key={i} x1={p[0]} y1={p[1]} x2={q[0]} y2={q[1]} stroke={C.accent} strokeWidth={5} strokeLinecap="round" opacity={((i + 1) / N) * 0.9} />);
    }
    const [hx, hy] = trackAt(leg.tr, s);
    out.push(
      <g key={k} opacity={o}>
        {segs}
        <circle cx={hx} cy={hy} r={8} fill={C.accent} stroke={C.bg} strokeWidth={3} />
      </g>,
    );
  });
  return <g>{out}</g>;
}

export interface PipelineProps {
  /** the puzzle's placement (it moves in "plan") */
  at?: PuzzleAt;
  place?: number[];
  appear?: number[];
  /**
   * 0..1 each: the puzzle's opacity, its name, its second line ("a hard puzzle"), arrow 1, the
   * string, arrow 2, the cube's name, the arrow back, its label, the name under the fold arrow
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
  /** frames since one pass of the loop started (a dot runs along the three arrows in turn); none if undefined */
  run?: number;
}

/**
 * The SVG half of the pipeline puzzle → HP string → best fold, and the arrow back
 * ("fits / does not fit"). The cube itself is 3D: draw smallCube() in a Scene3D with smallCubeShot().
 * Layout (px): puzzle 60–679, arrow 1 ("we write"), string 819–1291, arrow 2 ("fold", with
 * "a fast program?" under it), cube about 1567–1814; names at PIPE_LABEL_Y, second lines at PIPE_SUB_Y.
 */
export function Pipeline({ at = PUZZLE_SMALL, place, appear, puzzle = 1, puzzleLabel = 1, hard = 1, a1 = 1, str = 1, a2 = 1, cubeLabel = 1, a3 = 1, l3 = 1, fast = 0, asHard = 0, run }: PipelineProps) {
  const box = BOX_S;
  const y = PIPE_Y;
  return (
    <g>
      <Puzzle at={at} place={place} appear={appear} opacity={puzzle} />
      <Label x={box.cx} y={PIPE_LABEL_Y} opacity={puzzleLabel} {...NAME}>
        bin packing puzzle
      </Label>
      <Label x={box.cx} y={PIPE_SUB_Y} opacity={hard} {...SUB}>
        a hard puzzle
      </Label>
      <Arrow from={[A1_FROM, y]} to={[STR_X - 25, y]} progress={a1} opacity={clamp01(a1 / 0.25)} label="we write" />
      {str > 0 && <FlatString x={STR_X} y={y} seq={PIPE_SEQ} step={STEP} breakAfter={PIPE_BREAKS} progress={str} />}
      <Label x={STRING_CX} y={PIPE_LABEL_Y} opacity={clamp01(str * 2 - 1)} {...NAME}>
        HP string
      </Label>
      <Arrow from={[A2_FROM, y]} to={[A2_TO, y]} progress={a2} opacity={clamp01(a2 / 0.25)} label="fold" />
      <Label x={(A2_FROM + A2_TO) / 2} y={y + 48} opacity={fast} {...NAME}>
        a fast program?
      </Label>
      <Label x={CUBE_SCREEN.x} y={PIPE_LABEL_Y} opacity={cubeLabel} {...NAME}>
        best fold
      </Label>
      <Label x={CUBE_SCREEN.x} y={PIPE_SUB_Y} opacity={asHard} {...SUB}>
        at least as hard
      </Label>
      {/* the arrow back is a step of logic, not the next stage: accent, as the arrows of steps 23–25; its words are a dark name */}
      <CurvedArrow a={[CUBE_SCREEN.x, BACK_END_Y]} c={[BACK_MID, BACK_Y]} b={[box.cx, BACK_END_Y]} progress={a3} color={C.accent} />
      <Label x={BACK_MID} y={BACK_LABEL_Y} opacity={l3} {...NAME}>
        fits / does not fit
      </Label>
      {run !== undefined && run > 0 && <RunPulse run={run} />}
    </g>
  );
}
