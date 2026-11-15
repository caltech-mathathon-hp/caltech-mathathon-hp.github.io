/**
 * Scene "cube": why a best fold of n³ H's is a cube.
 * Cue 1: one H and its six neighbours (empty nodes, small grey dots, joined to it by faint lattice
 *        lines). Three fill with H's (two joined in the chain, one a contact); the other three stay
 *        empty: dashed red rings, each with a red dashed stub, "contact lost".
 * Cue 2: 27 H's are laid as a flat 9 × 3 slab, with one tip, and show 78 lost contacts (red stubs).
 *        The slab slides left; where it was, a copy of the chain fades in and folds into a 3 × 3 × 3
 *        cube, a third at a time, which shows 54. The two stand side by side, each with its count.
 * Cue 3: the whole picture of cue 2 fades out; the 12-cube full of H's fades in as one picture (a
 *        perfect fold) and the view turns a few degrees, slowly, onto FRAME_SHOT(0). Its inside is
 *        closed off and the faces turned away are hidden, so the scene ends on exactly the picture
 *        the "local" scene starts with (FRAME_SHOT(0), no outline, no depth cue).
 *
 * Every bead comes and goes by `opacity` (see-through), never by `fade` or by scaling.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, yaw, mixShot, R_BOND, R_RES, type Bead, type Stick, type Shot, type Solid } from '../three/Scene3D';
import { innerBlock, FRAME_SHOT, HOLE_COLOR, CUBE_SHELL } from '../three/cube';
import { ramp, sec, clamp01, lerp } from '../lib/anim';
import { C, FONT } from '../theme/theme';
import * as M from '../model/toy';
import type { V3 } from '../model/toy';
import type { SceneTime } from '../script';
import { chainTimes, layChain, dashLink, NAME, SUB } from './lib/planPipeline';

const add = (a: V3, b: V3): V3 => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
const neg = (a: V3): V3 => [-a[0], -a[1], -a[2]];
const DIRS: V3[] = [
  [1, 0, 0],
  [-1, 0, 0],
  [0, 1, 0],
  [0, -1, 0],
  [0, 0, 1],
  [0, 0, -1],
];

// ---------------------------------------------------------------- cue 1: one H, six neighbours
const C0: V3 = [5, 5, -5];
/** the six neighbours: which are H's, and how they are joined to the centre */
const NBR: { d: V3; kind: 'chain' | 'contact' | 'lost' }[] = [
  { d: [-1, 0, 0], kind: 'chain' },
  { d: [0, 1, 0], kind: 'chain' },
  { d: [0, 0, 1], kind: 'contact' },
  { d: [1, 0, 0], kind: 'lost' },
  { d: [0, -1, 0], kind: 'lost' },
  { d: [0, 0, -1], kind: 'lost' },
];

// ---------------------------------------------------------------- cue 2: slab → cube
/**
 * 27 H's as a chain snaking through a 9 × 3 slab, column by column (up, down, up, …). The slab folds
 * like an accordion: the left third swings 180° forwards about the hinge between columns 3 and 4,
 * the right third 180° backwards about the hinge between columns 6 and 7. Each third turns rigidly,
 * so the chain stays joined, and the result is the 3 × 3 × 3 cube (the chain still a path in it).
 */
const SLAB: { from: V3; block: number; hinge: [number, number] }[] = [];
for (let i = 0; i < 9; i++)
  for (let jj = 0; jj < 3; jj++) {
    const j = i % 2 === 0 ? jj : 2 - jj;
    const block = Math.floor(i / 3);
    const hinge: [number, number] = block === 0 ? [3.5, -4.5] : [6.5, -5.5];
    SLAB.push({ from: [1 + i, 4 + j, -5], block, hinge });
  }
/** where a slab bead is when the left third has turned by θL and the right third by θR (0..π) */
const folded = (c: (typeof SLAB)[number], thL: number, thR = thL): V3 => {
  if (c.block === 1) return c.from;
  const th = c.block === 0 ? thL : thR;
  const ox = c.from[0] - c.hinge[0];
  const oz = c.from[2] - c.hinge[1];
  const cs = Math.cos(th);
  const sn = Math.sin(th);
  return [c.hinge[0] + ox * cs + oz * sn, c.from[1], c.hinge[1] - ox * sn + oz * cs];
};
const CUBE_AT = SLAB.map((c) => folded(c, Math.PI).map((v) => Math.round(v)) as V3);
const keyOf = (p: V3) => `${Math.round(p[0])},${Math.round(p[1])},${Math.round(p[2])}`;
/** the sides of a set of beads that do not touch another bead: where contacts are lost */
function exposed(ps: V3[]): { at: V3; d: V3 }[] {
  const s = new Set(ps.map(keyOf));
  const out: { at: V3; d: V3 }[] = [];
  for (const p of ps) for (const d of DIRS) if (!s.has(keyOf(add(p, d)))) out.push({ at: p, d });
  return out;
}
const SLAB_SIDES = exposed(SLAB.map((c) => c.from));
const CUBE_SIDES = exposed(CUBE_AT);
CUBE_AT.forEach((p, i) => {
  if (i > 0 && Math.abs(p[0] - CUBE_AT[i - 1][0]) + Math.abs(p[1] - CUBE_AT[i - 1][1]) + Math.abs(p[2] - CUBE_AT[i - 1][2]) !== 1) throw new Error('cube scene: the folded chain breaks');
});
if (SLAB_SIDES.length !== 78 || CUBE_SIDES.length !== 54) throw new Error(`cube scene: surfaces ${SLAB_SIDES.length}, ${CUBE_SIDES.length}`);

// ---------------------------------------------------------------- cue 3: the 12-cube
/** the 12-cube as the later scenes draw it: its three faces towards the camera (+x, +y, +z) */
const FACES12: V3[] = [];
for (let x = 0; x < M.n; x++)
  for (let y = 0; y < M.n; y++)
    for (let z = -(M.n - 1); z <= 0; z++) if (x === M.n - 1 || y === M.n - 1 || z === 0) FACES12.push([x, y, z]);
if (FACES12.length !== 3 * M.n * M.n - 3 * M.n + 1) throw new Error('cube scene: the 12-cube faces');

const lostColor = C.invalid;
/**
 * In cue 2 the slab slides SHIFT units to the left on screen (left of the view at the end of cue 2,
 * so the slab and the cube end at the same depth and side by side), and its copy folds into the cube.
 * The view at the end of cue 2 (END_DIR) keeps the 27 beads of the cube apart.
 */
const SHIFT = 10;
/**
 * The view of cue 2: about 36° round from straight on and 28° from above (a little higher than the
 * plan's small cube), so the three faces of the 3-cube read as grids and the top face's stubs stand
 * apart from the row behind.
 */
const END_DIR: V3 = (() => {
  const az = (36 * Math.PI) / 180;
  const el = (28 * Math.PI) / 180;
  return [Math.sin(az) * Math.cos(el), Math.sin(el), Math.cos(az) * Math.cos(el)];
})();
const LEFT: V3 = (() => {
  const l = Math.hypot(END_DIR[0], END_DIR[2]);
  return [(-END_DIR[2] / l) * SHIFT, 0, (END_DIR[0] / l) * SHIFT];
})();
/** an empty node: a small solid grey dot, as holeBeads draws them */
const R_EMPTY = R_RES * 0.4;
/** for the six neighbours: close to the cube's diagonal, so no axis points at the camera */
const ISO: V3 = [0.6, 0.52, 0.6];
/** fade-in over `dur` seconds from `from` (frames), linear: 0 = not there, 1 = full */
const fadeIn = (f: number, from: number, dur = 0.3) => clamp01((f - from) / sec(dur));

/** the lens for cue 2, and how much farther the camera stands to keep the same size (tan 15° / tan 11°) */
const MID_FOV = 22;
const MID_LENS = Math.tan((15 * Math.PI) / 180) / Math.tan(((MID_FOV / 2) * Math.PI) / 180);
/** a stub of a lost contact: how far it reaches beyond the bead's rim */
const STUB = 0.34;
/** the eased s-curve of a move */
const ease = (t: number) => (1 - Math.cos(Math.PI * clamp01(t))) / 2;
/** the corners of the perfect fold's cube */
const CORNERS: V3[] = [0, 1, 2, 3, 4, 5, 6, 7].map((m) => [m & 1 ? M.n - 0.5 : -0.5, m & 2 ? M.n - 0.5 : -0.5, m & 4 ? -M.n + 0.5 : 0.5]);

export default function CubeScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1, c2] = scene.cueTimes;
  const beads: Bead[] = [];
  const sticks: Stick[] = [];
  const lines: Stick[] = [];

  // ---------------- cue 1: every bead and dot fades in at full size; the picture leaves by fading
  const t0 = (s: number) => c0.from + sec(s);
  const out1 = ramp(f, c1.from, sec(0.7));
  const keep1 = 1 - out1;
  const centre = fadeIn(f, t0(0.1));
  /** the lattice lines to the six neighbours fade in at full length */
  const star = fadeIn(f, t0(0.8), 0.6);
  /** neighbour k (of the three H's) fills from fillAt(k): its H fades in round the dot (with its chain stick), then a contact's gold link draws */
  const fillAt = (k: number) => t0(3.3 + k * 0.45);
  const H_IN = sec(0.3);
  const LINK = sec(0.4);
  const lostIn = ramp(f, t0(5.2), sec(0.6));
  const label6 = Math.min(ramp(f, t0(1.6), sec(0.5)), 1 - ramp(f, t0(2.7), sec(0.4)));
  const labelLost = Math.min(ramp(f, t0(5.6), sec(0.5)), 1 - out1);
  const labelH = (k: number) => Math.min(ramp(f, fillAt(k) + H_IN, sec(0.4)), 1 - out1);
  // ---------------- cue 2
  const t1 = (s: number) => c1.from + sec(s);
  const t2 = (s: number) => c2.from + sec(s);
  const out2 = ramp(f, c2.from, sec(0.5)); // the whole picture leaves: slab, cube, stubs and both counts
  const slabTimes = chainTimes(SLAB.length, t1(0.8), sec(2.4), 0.45); // a soft tip of about 3 beads
  const stubsA = ramp(f, t1(3.3), sec(0.6));
  const labelA = Math.min(ramp(f, t1(3.6), sec(0.5)), 1 - out2);
  // a gentle ease: a slab moving fast strobes (its beads line up with where their neighbours were)
  const split = ramp(f, t1(4.3), sec(2.2), ease);
  // the copy fades in, as one piece, once the slab has slid clear of the place
  const copyIn = fadeIn(f, t1(6.1), 0.4);
  // the accordion closes a third at a time: the left third swings forwards, then the right third backwards
  const turnL = ramp(f, t1(6.7), sec(1.0), ease);
  const turnR = ramp(f, t1(7.85), sec(1.0), ease);
  const stubsB = ramp(f, t1(9), sec(0.6));
  const labelB = Math.min(ramp(f, t1(9.3), sec(0.5)), 1 - out2);
  const off: V3 = [LEFT[0] * split, 0, LEFT[2] * split];
  const slabAt = (c: (typeof SLAB)[number]): V3 => add(c.from, off);
  const cubeAt = SLAB.map((c) => folded(c, Math.PI * turnL, Math.PI * turnR));

  // ---------------- camera (needed here: the stubs on faces turned away from it are left out)
  const close: Shot = { target: C0, dir: yaw(ISO, -8 + 12 * ramp(f, t0(0), sec(6.5))), dist: 11 };
  const mid: Shot = {
    target: [5 + off[0] / 2, 4.6, -5 + off[2] / 2],
    dir: yaw(END_DIR, -8 + 8 * ramp(f, t1(0.2), sec(7.0))),
    // a narrower lens from farther away (same size on screen): the slab, off to the left, and the
    // cube, off to the right, are then seen from nearly the same side, so their stubs lie the same way
    dist: lerp(21, 24, split) * MID_LENS,
    fov: MID_FOV,
    offset: [0, -40],
  };
    let shot = mixShot(close, mid, ramp(f, t1(0.2), sec(1.8)));
  // once the picture of cue 2 is gone (nothing is seen while the camera changes), the 12-cube's view;
  // it turns 3.4° onto FRAME_SHOT(0), eased, landing on the pause, and stays there to the cut
  const drift = ramp(f, t2(0.6), c2.to - 10 - t2(0.6), ease);
  if (f >= t2(0.55)) shot = FRAME_SHOT(-0.12 * (1 - drift));
  const dn = Math.hypot(...shot.dir);
  const toCam: V3 = [shot.dir[0] / dn, shot.dir[1] / dn, shot.dir[2] / dn];

  /**
   * How far from a bead's centre a dashed link in direction `d` must start so that, seen from the
   * camera, its first dash is clear of the bead's disc (a link pointing at the camera would
   * otherwise start on top of its own bead, as a red or gold fleck). The 0.055 is dashLink's gap.
   */
  const clearOf = (d: V3) => {
    const c = d[0] * toCam[0] + d[1] * toCam[1] + d[2] * toCam[2];
    if (c <= 0) return R_RES;
    return Math.max(R_RES, (R_RES * 1.1) / Math.sqrt(Math.max(1e-4, 1 - c * c)) - 0.055);
  };

  // ---------------- cue 1 (drawn here: its links need the camera)
  if (out1 < 1) {
    if (centre > 0) beads.push({ pos: C0, color: C.h, opacity: centre * keep1 });
    let hk = 0;
    NBR.forEach((nb, i) => {
      const p = add(C0, nb.d);
      const dotIn = fadeIn(f, t0(0.9 + i * 0.12));
      // the grid edge to the neighbour: a faint lattice line (not a stick: grey sticks join a chain),
      // its ends hidden inside the beads. A chain stick covers it; a dashed link (contact or contact
      // lost) takes its place, so it fades as the link draws
      const gridEdge = (taken: number) => {
        const o = star * keep1 * (1 - taken);
        if (o > 0) lines.push({ a: C0, b: p, color: C.lattice, r: 0.018, fade: 1 - o });
      };
      if (nb.kind === 'lost') {
        gridEdge(lostIn);
        // an empty node; it stays empty, gets a dashed red ring (drawn on the overlay) and a red stub
        if (dotIn > 0) beads.push({ pos: p, color: HOLE_COLOR, r: R_EMPTY, opacity: dotIn * keep1 });
        sticks.push(...dashLink(C0, p, lostColor, { ra: clearOf(nb.d), rb: clearOf(neg(nb.d)), grow: lostIn, fade: out1 }));
      } else {
        const k = hk++;
        const T = fillAt(k);
        // the H fades in at full size round the dot (which it hides once solid; the dot is dropped
        // then), its chain stick with it at full length; a contact's gold link draws only once the
        // H is there
        const hIn = clamp01((f - T) / H_IN);
        if (dotIn > 0 && hIn < 1) beads.push({ pos: p, color: HOLE_COLOR, r: R_EMPTY, opacity: dotIn * keep1 });
        if (hIn > 0) beads.push({ pos: p, color: C.h, opacity: hIn * keep1 });
        if (nb.kind === 'chain') {
          gridEdge(0);
          const fd = 1 - hIn * keep1;
          if (hIn > 0) sticks.push({ a: C0, b: p, color: C.backbone, r: R_BOND, fade: fd > 0 ? fd : undefined });
        } else {
          const g = clamp01((f - T - H_IN) / LINK);
          gridEdge(g);
          sticks.push(...dashLink(C0, p, C.bond, { ra: clearOf(nb.d), rb: clearOf(neg(nb.d)), grow: g, fade: out1 }));
        }
      }
    });
  }

  /** red stubs on the sides that touch no H; those on faces turned away from the camera would only poke out between the beads */
  const sideStubs = (sides: { at: V3; d: V3 }[], g: number, o: V3) => {
    if (g <= 0 || out2 >= 1) return;
    for (const { at, d } of sides) {
      if (d[0] * toCam[0] + d[1] * toCam[1] + d[2] * toCam[2] < 0.05) continue;
      const a = add(at, o);
      const ra = clearOf(d);
      const l = ra + STUB;
      sticks.push(...dashLink(a, add(a, [d[0] * l, d[1] * l, d[2] * l]), lostColor, { ra, rb: 0, grow: g, fade: out2 }));
    }
  };
  if (f >= t1(0.8) && out2 < 1) {
    // the slab (A): laid with one tip in string order, then slides left with its stubs; it leaves
    // see-through, at full size
    if (out2 <= 0) layChain(f, slabTimes, SLAB.map((c) => ({ pos: slabAt(c), color: C.h })), beads, sticks);
    else
      SLAB.forEach((c, i) => {
        beads.push({ pos: slabAt(c), color: C.h, opacity: 1 - out2 });
        if (i > 0) sticks.push({ a: slabAt(SLAB[i - 1]), b: slabAt(c), color: C.backbone, fade: out2 });
      });
    sideStubs(SLAB_SIDES, stubsA, off);
  }
  if (copyIn > 0 && out2 < 1) {
    // its copy (B) fades in where the slab was and folds into the cube, which keeps its chain
    SLAB.forEach((c, i) => {
      const o = copyIn * (1 - out2);
      beads.push({ pos: cubeAt[i], color: C.h, opacity: o < 1 ? o : undefined });
      if (i > 0) sticks.push({ a: cubeAt[i - 1], b: cubeAt[i], color: C.backbone, fade: o < 1 ? 1 - o : undefined });
    });
  }
  sideStubs(CUBE_SIDES, stubsB, [0, 0, 0]);

  // ---------------- cue 3: the 12-cube fades in, at full size, as one picture; its inside is closed
  // off by a block in the background colour (unseen until the beads are there) and the faces turned
  // away are hidden, as in the "local" scene
  const in3 = ramp(f, t2(0.75), sec(0.6), ease);
  const block = f >= t2(0.55) ? 1 : 0;
  if (in3 > 0) for (const p of FACES12) beads.push({ pos: p, color: C.h, opacity: in3 < 1 ? in3 : undefined });
  const solids: Solid[] = block > 0 ? [innerBlock({ opacity: block })] : [];
  const labelPerfect = Math.min(ramp(f, t2(1.6), sec(0.6)), 1 - ramp(f, c2.to, sec(0.4)));

  return (
    <SceneFrame scene={scene}>
      <Scene3D shot={shot} beads={beads} sticks={sticks} lines={lines} solids={solids} shell={{ ...CUBE_SHELL, amount: block }}>
        {(project) => {
          const els: React.ReactNode[] = [];
          const side: V3 = [toCam[2], 0, -toCam[0]];
          /** a bead's radius on screen at `p` */
          const radiusPx = (p: V3, r = R_RES) => {
            const [x, y] = project(p);
            const [x2, y2] = project(add(p, [side[0] * r, side[1] * r, side[2] * r]));
            return Math.hypot(x2 - x, y2 - y) / Math.hypot(side[0], side[2]);
          };
          if (label6 > 0) {
            // centred just above the top neighbour
            const top = add(C0, [0, 1, 0]);
            const [x, y] = project(top);
            els.push(
              <text key="six" x={x} y={y - radiusPx(top) - 22} textAnchor="middle" fontFamily={FONT.sans} fontSize={NAME.size} fontWeight={NAME.weight} fill={NAME.color} opacity={label6}>
                6 neighbours
              </text>,
            );
          }
          // the empty sockets: a dashed red ring the size of a bead round the empty node
          NBR.forEach((nb, i) => {
            if (nb.kind !== 'lost' || lostIn <= 0 || out1 >= 1) return;
            const p = add(C0, nb.d);
            const [x, y] = project(p);
            els.push(<circle key={`sock${i}`} cx={x} cy={y} r={radiusPx(p)} fill="none" stroke={lostColor} strokeWidth={3.5} strokeDasharray="7 5" opacity={lostIn * (1 - out1)} />);
          });
          // every neighbour gets a word: chain, contact or contact lost
          let hk2 = 0;
          NBR.forEach((nb, i) => {
            const o = nb.kind === 'lost' ? labelLost : labelH(hk2++);
            if (o <= 0) return;
            // the direction from the scene's own camera, so a label keeps its side of its bead
            // when the viewer turns the picture (a neighbour seen end-on has no direction of its own)
            const c = project(C0);
            const b = project(add(C0, nb.d));
            const p = project(add(C0, nb.d));
            const dx = b[0] - c[0];
            const dy = b[1] - c[1];
            const l = Math.hypot(dx, dy) || 1;
            const x = p[0] + (dx / l) * 78;
            const y = p[1] + (dy / l) * 80 + 9;
            const word = nb.kind === 'lost' ? 'contact lost' : nb.kind === 'contact' ? 'contact' : 'chain';
            els.push(
              <text key={`nb${i}`} x={x} y={y} textAnchor={dx > 8 ? 'start' : dx < -8 ? 'end' : 'middle'} fontFamily={FONT.sans} fontWeight={NAME.weight} fontSize={NAME.size} fill={NAME.color} opacity={o}>
                {word}
              </text>,
            );
          });
          // under the slab and under the cube: what it is, how many H's, how many contacts it loses
          const count = (key: string, at: V3, name: string, n: number, o: number) => {
            if (o <= 0) return;
            const [x, y] = project(at);
            els.push(
              <g key={key} opacity={o} fontFamily={FONT.sans} textAnchor="middle">
                <text x={x} y={y + 44} fontSize={NAME.size} fontWeight={NAME.weight} fill={NAME.color}>
                  {name}
                </text>
                <text x={x} y={y + 44 + 30} fontSize={SUB.size} fontWeight={SUB.weight} fill={SUB.color}>
                  27 H’s
                </text>
                <text x={x} y={y + 44 + 64} fontSize={NAME.size} fontWeight={NAME.weight} fill={NAME.color} style={{ fontVariantNumeric: 'tabular-nums' }}>
                  {n} contacts lost
                </text>
              </g>,
            );
          };
          count('slabN', add([5, 3, -5], off), '9 × 3 slab', SLAB_SIDES.length, labelA);
          count('cubeN', [5, 3, -4], '3 × 3 × 3 cube, so n = 3', CUBE_SIDES.length, labelB);
          if (labelPerfect > 0) {
            // left of the cube, whichever way the viewer turned it
            const left = Math.min(...CORNERS.map((q) => project(q)[0])) - 10;
            const [x0, y] = project([-1.2, M.n - 1, 0]);
            const x = Math.min(x0, left);
            els.push(
              <g key="perfect" opacity={labelPerfect} fontFamily={FONT.sans}>
                <text x={x - 20} y={y} textAnchor="end" fontSize={NAME.size} fontWeight={NAME.weight} fill={NAME.color}>
                  a perfect fold
                </text>
                <text x={x - 20} y={y + 32} textAnchor="end" fontSize={SUB.size} fontWeight={SUB.weight} fill={SUB.color}>
                  every node holds an H
                </text>
              </g>,
            );
          }
          return <>{els}</>;
        }}
      </Scene3D>
    </SceneFrame>
  );
}
