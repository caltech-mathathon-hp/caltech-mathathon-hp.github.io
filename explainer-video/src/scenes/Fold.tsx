/**
 * Scene "fold": what an HP string and a fold are, and what a contact is.
 * Cue 1: a 12-letter string lies straight, then slides head first along its fold onto the grid
 *        (every letter follows the same self-avoiding track, so the chain never crosses itself).
 * Cue 2: the four contacts of this fold appear one by one, with a counter.
 * Cue 3: the grid grows into a block of cubic cells below the floor; the camera pulls back.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, type Bead, type Stick, type Shot } from '../three/Scene3D';
import { ramp, sec, clamp01, lerp, easeOut } from '../lib/anim';
import { C, FONT } from '../theme/theme';
import type { V3 } from '../model/toy';
import type { SceneTime } from '../script';
import { chainTimes, layChain, beadIn, dashLink } from './lib/planPipeline';

const STR = 'PHHPPHHPPHHP';
/**
 * A flat fold on the floor: three arms joined by two hairpin turns, so the H's of neighbouring arms
 * face each other and every contact lies in the floor, where it can be seen.
 */
const PATH: V3[] = [
  [0, 0, 0],
  [1, 0, 0],
  [2, 0, 0],
  [3, 0, 0],
  [3, 0, -1],
  [2, 0, -1],
  [1, 0, -1],
  [0, 0, -1],
  [0, 0, -2],
  [1, 0, -2],
  [2, 0, -2],
  [3, 0, -2],
];
const L = STR.length;
const isH = (i: number) => STR[i] === 'H';
const dist1 = (a: V3, b: V3) => Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]) + Math.abs(a[2] - b[2]);

// checks: unit steps, no node twice
PATH.forEach((p, i) => {
  if (i > 0 && dist1(p, PATH[i - 1]) !== 1) throw new Error(`fold: step ${i} is not a unit step`);
  if (PATH.findIndex((q) => dist1(p, q) === 0) !== i) throw new Error(`fold: node ${i} used twice`);
});
/** contacts: H's on neighbouring nodes that are not next to each other in the string */
const CONTACTS: [number, number][] = [];
for (let i = 0; i < L; i++) for (let j = i + 2; j < L; j++) if (isH(i) && isH(j) && dist1(PATH[i], PATH[j]) === 1) CONTACTS.push([i, j]);
if (CONTACTS.length !== 4) throw new Error(`fold: expected 4 contacts, got ${CONTACTS.length}`);
// show them in an order that walks round the fold
CONTACTS.sort((a, b) => a[0] - b[0] || a[1] - b[1]);

/**
 * The track the letters slide along: a straight run along −x ending at the first node, then the
 * fold's path, with its corners rounded on quarter circles of radius `r` (0 ≤ r ≤ 0.5). `trackAt(s, r)`
 * is the point at arc length s from the first node (s < 0: on the straight run).
 *
 * Letter i sits at s = i − 12(1 − u): at u = 0 the string lies straight, at u = 1 every letter is on
 * its node. Letters one apart along a track with sharp corners close up to 0.71 of a spacing where
 * they straddle a corner (they nearly touch); on corners of radius 0.5 they stay at least 0.84 apart.
 * The corners sharpen over the last half spacing of the slide, so the letters at the corners land on
 * their nodes.
 */
type Piece = { len: number; at: (s: number) => V3 };
const sub3 = (a: V3, b: V3): V3 => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
const add3 = (a: V3, b: V3, k = 1): V3 => [a[0] + k * b[0], a[1] + k * b[1], a[2] + k * b[2]];
const len3 = (a: V3) => Math.hypot(a[0], a[1], a[2]);
const roundedPath = (r: number): Piece[] => {
  const out: Piece[] = [];
  const line = (a: V3, b: V3): Piece => {
    const l = len3(sub3(b, a));
    return { len: l, at: (s) => add3(a, sub3(b, a), l > 0 ? s / l : 0) };
  };
  let cur = PATH[0];
  for (let k = 1; k < PATH.length; k++) {
    const din = sub3(PATH[k], PATH[k - 1]);
    const dout = k + 1 < PATH.length ? sub3(PATH[k + 1], PATH[k]) : null;
    const turns = dout !== null && din[0] * dout[0] + din[1] * dout[1] + din[2] * dout[2] === 0;
    if (turns && r > 1e-6) {
      const a = add3(PATH[k], din, -r);
      out.push(line(cur, a));
      // a quarter circle from a (heading din) to PATH[k] + r·dout (heading dout)
      const c = add3(a, dout, r);
      out.push({ len: (Math.PI / 2) * r, at: (s) => add3(add3(c, dout, -r * Math.cos(s / r)), din, r * Math.sin(s / r)) });
      cur = add3(PATH[k], dout, r);
    } else {
      out.push(line(cur, PATH[k]));
      cur = PATH[k];
    }
  }
  return out;
};
const trackAt = (pieces: Piece[], s: number): V3 => {
  if (s <= 0) return [s, 0, 0];
  for (let k = 0; k < pieces.length; k++) {
    const p = pieces[k];
    if (s <= p.len || k === pieces.length - 1) return p.at(s);
    s -= p.len;
  }
  return PATH[PATH.length - 1];
};
/** where the letters are at slide progress u (0..1) */
const lettersAt = (u: number): V3[] => {
  const rest = L * (1 - u);
  const pieces = roundedPath(0.5 * clamp01(rest / 0.5));
  return Array.from({ length: L }, (_, i) => trackAt(pieces, i - rest));
};

const FOLD_CENTER: V3 = [1.5, 0, -1];
/** the camera's height over the fold, in degrees: high enough that the contacts show between the beads */
const EL_FOLD = 58;
/** and over the cubic grid: low enough to see its sides, high enough that the contacts still show */
const EL_GRID = 48;
/** when the legend fades in (s into cue 1): once the grid has slid past its place */
const LEGEND_AT = 6.4;
const STRAIGHT_CENTER: V3 = [-(L + 1) / 2, 0, 0];

/**
 * The grid as unit segments. The floor (y = 0) round the fold is there from cue 1; in cue 3 it grows
 * into a block of cubic cells below the floor, drawn on the three faces we see (top, front, right),
 * so the fold lies on top of the cubic grid and no line passes in front of it.
 */
const FLOOR = { x: [-1, 4], z: [-3, 1] };
const BLOCK = { x: [-2, 5], y: [-2, 0], z: [-4, 1] };
interface Seg {
  a: V3;
  b: V3;
  floor: boolean;
  d: number;
}
const SEGS: Seg[] = (() => {
  const out: Seg[] = [];
  const inFloor = (p: V3) => p[1] === 0 && p[0] >= FLOOR.x[0] && p[0] <= FLOOR.x[1] && p[2] >= FLOOR.z[0] && p[2] <= FLOOR.z[1];
  const onFace = (a: V3, b: V3) => (a[1] === BLOCK.y[1] && b[1] === BLOCK.y[1]) || (a[2] === BLOCK.z[1] && b[2] === BLOCK.z[1]) || (a[0] === BLOCK.x[1] && b[0] === BLOCK.x[1]);
  const push = (a: V3, b: V3) => {
    if (!onFace(a, b)) return;
    const m: V3 = [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2, (a[2] + b[2]) / 2];
    out.push({ a, b, floor: inFloor(a) && inFloor(b), d: Math.hypot(m[0] - FOLD_CENTER[0], m[1] - FOLD_CENTER[1], m[2] - FOLD_CENTER[2]) });
  };
  for (let x = BLOCK.x[0]; x <= BLOCK.x[1]; x++)
    for (let y = BLOCK.y[0]; y <= BLOCK.y[1]; y++)
      for (let z = BLOCK.z[0]; z <= BLOCK.z[1]; z++) {
        if (x < BLOCK.x[1]) push([x, y, z], [x + 1, y, z]);
        if (y < BLOCK.y[1]) push([x, y, z], [x, y + 1, z]);
        if (z < BLOCK.z[1]) push([x, y, z], [x, y, z + 1]);
      }
  return out;
})();
const D_MAX = Math.max(...SEGS.filter((s) => !s.floor).map((s) => s.d));
/**
 * The grid is drawn just below the beads (their radius is 0.3, a little more while one swells), so
 * its lines pass under the beads instead of through their lower half.
 */
const GRID_DROP = 0.34;
const down = (p: V3): V3 => [p[0], p[1] - GRID_DROP, p[2]];

/** the view from (yaw, elevation) in degrees */
const dirOf = (yawDeg: number, elDeg: number): V3 => {
  const a = (yawDeg * Math.PI) / 180;
  const e = (elDeg * Math.PI) / 180;
  return [Math.sin(a) * Math.cos(e), Math.sin(e), Math.cos(a) * Math.cos(e)];
};

/** a bead in the legend, shaded as the 3D beads are: an H, or a P (white with a blue ring) */
function LegendBead({ x, y, h = false }: { x: number; y: number; h?: boolean }) {
  const id = h ? 'fold-legend-h' : 'fold-legend-p';
  return (
    <g>
      <defs>
        <radialGradient id={id} cx="0.36" cy="0.32" r="0.75">
          {h ? (
            <>
              <stop offset="0" stopColor="#e48a72" />
              <stop offset="0.35" stopColor="#c8592f" />
              <stop offset="1" stopColor="#9c3f20" />
            </>
          ) : (
            <>
              <stop offset="0" stopColor="#fbfcfe" />
              <stop offset="1" stopColor="#d4d7db" />
            </>
          )}
        </radialGradient>
      </defs>
      {h ? <circle cx={x} cy={y} r={15} fill={`url(#${id})`} /> : <circle cx={x} cy={y} r={13} fill={`url(#${id})`} stroke={C.p} strokeWidth={4} />}
    </g>
  );
}

export default function FoldScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1, c2] = scene.cueTimes;

  // cue 1: the string is laid straight with one growing tip (each bead fades in at full size as the
  // tip reaches it), the grid fades in, then the string slides onto its fold
  const times = chainTimes(L, c0.from + sec(0.15), sec(1.8));
  const letters = 1 - ramp(f, c0.from + sec(2.6), sec(0.6));
  const u = ramp(f, c0.from + sec(3.0), sec(4.2));
  const grid = ramp(f, c0.from + sec(1.6), sec(1.0));
  const bigGrid = ramp(f, c2.from + sec(0.6), sec(2.4));

  const pos = lettersAt(u);

  // camera: from the straight string to the fold (high enough that the contacts between the arms
  // show between the beads), then out and lower for the cubic grid, raised clear of the caption
  const camIn = ramp(f, c0.from + sec(2.8), sec(4.6));
  const camOut = ramp(f, c2.from + sec(0.3), sec(3.0));
  const target: V3 = [lerp(STRAIGHT_CENTER[0], FOLD_CENTER[0], camIn), lerp(STRAIGHT_CENTER[1], FOLD_CENTER[1], camIn), lerp(STRAIGHT_CENTER[2], FOLD_CENTER[2] - 0.4 * camOut, camIn)];
  const shot: Shot = {
    target,
    dir: dirOf(lerp(-4, 16, camIn) + 10 * camOut, lerp(EL_FOLD, EL_GRID, camOut)),
    dist: lerp(lerp(24, 12.2, camIn), 20, camOut),
    offset: [-90 * camIn - 70 * camOut, lerp(-70, -120, camOut)],
  };

  // cue 2: contacts one by one
  const contactAt = (k: number) => c1.from + sec(0.9 + k * 1.15);
  const grown = CONTACTS.map((_, k) => ramp(f, contactAt(k), sec(0.45), easeOut));
  const shown = grown.filter((g) => g > 0.5).length;
  const pulse = (i: number) => {
    let s = 0;
    CONTACTS.forEach(([a, b], k) => {
      if (a !== i && b !== i) return;
      const t = (f - contactAt(k)) / sec(0.7);
      if (t > 0 && t < 1) s = Math.max(s, Math.sin(Math.PI * t));
    });
    return s;
  };

  const beads: Bead[] = [];
  const sticks: Stick[] = [];
  layChain(
    f,
    times,
    pos.map((p, i) => ({ pos: p, color: isH(i) ? C.h : C.p, hollow: !isH(i) })),
    beads,
    sticks,
    { joinAll: true },
  );
  // a bead touched by a new contact swells a little (never into its dashes)
  beads.forEach((b, i) => {
    const s = pulse(i);
    if (s > 0) b.scale = 1 + 0.07 * s;
  });
  CONTACTS.forEach(([a, b], k) => sticks.push(...dashLink(PATH[a], PATH[b], C.bond, { grow: grown[k] })));
  // the grid: the floor round the fold, then (cue 3) the block of cubic cells below it
  const lines: Stick[] = [];
  for (const sg of SEGS) {
    const o = sg.floor ? grid : clamp01(bigGrid * 1.6 - (sg.d / D_MAX) * 0.6);
    if (o > 0) lines.push({ a: down(sg.a), b: down(sg.b), color: C.lattice, r: 0.016, fade: 1 - 0.8 * o });
  }

  return (
    <SceneFrame scene={scene}>
      <Scene3D shot={shot} beads={beads} sticks={sticks} lines={lines}>
        {(project) => {
          const els: React.ReactNode[] = [];
          // the letters above the straight string, each with its bead
          if (letters > 0)
            for (let i = 0; i < L; i++) {
              const a = beadIn(f, times, i);
              if (a <= 0) continue;
              const [x, y0] = project(pos[i]);
              const y = y0 - 38;
              els.push(
                <text key={`l${i}`} x={x} y={y} textAnchor="middle" fontFamily={FONT.sans} fontWeight={650} fontSize={30} fill={isH(i) ? C.h : C.p} opacity={letters * a}>
                  {STR[i]}
                </text>,
              );
            }
          // right of the fold, fixed on the screen and unboxed, as the legend of steps 20–25: what
          // the two colours mean (drawn as the beads look), then the contact count. The legend comes
          // once the grid has slid past the place where it sits.
          const LX = 1400;
          const legend = ramp(f, c0.from + sec(LEGEND_AT), sec(0.5));
          if (legend > 0) {
            const y = 344;
            els.push(
              <g key="legend" opacity={legend} fontFamily={FONT.sans} fontSize={26} fontWeight={650}>
                <LegendBead x={LX + 16} y={y} h />
                <text x={LX + 44} y={y + 9} fill={C.h}>
                  H
                </text>
                <LegendBead x={LX + 116} y={y} />
                <text x={LX + 144} y={y + 9} fill={C.p}>
                  P
                </text>
              </g>,
            );
          }
          const counter = ramp(f, c1.from + sec(0.3), sec(0.5));
          if (counter > 0) {
            const y = 412;
            const most = ramp(f, contactAt(CONTACTS.length - 1) + sec(0.7), sec(0.5));
            els.push(
              <g key="counter" opacity={counter} fontFamily={FONT.sans}>
                <line x1={LX} x2={LX + 34} y1={y} y2={y} stroke={C.bond} strokeWidth={6} strokeDasharray="7 6" strokeLinecap="butt" />
                <text x={LX + 44} y={y + 9} fontSize={26} fontWeight={600} fill={C.fg}>
                  contacts: {shown}
                </text>
                {most > 0 && (
                  <text x={LX + 44} y={y + 43} fontSize={22} fontWeight={500} fill={C.fgMuted} opacity={most}>
                    the most possible
                  </text>
                )}
              </g>,
            );
          }
          return <>{els}</>;
        }}
      </Scene3D>
    </SceneFrame>
  );
}
