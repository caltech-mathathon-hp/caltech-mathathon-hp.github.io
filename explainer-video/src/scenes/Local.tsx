/**
 * Scene "local": in a perfect fold every P is outside the cube, and that decides where each piece goes.
 * The cube is drawn as its outer layer of beads, in full H colour (an invisible filler hides the far
 * side). It opens on the last frame of "cube-shape": the whole cube, no outline.
 *
 * Cue 1: the camera turns a little, so three faces show. Twelve H's on the cube's outline each get a
 *        P one step out of a face we see, out in the empty space; the stem and the P come together.
 * Cue 2: the camera turns to the cube's front-right edge, so the front and right faces fall away on
 *        either side: a rod (PHP PHP …) is laid up that edge from the bottom corner, each H with a P
 *        off the front face and one off the right face.
 * Cue 3: back to the three faces: a ribbon (PHHP PHHP …) is laid along the back row of the top face,
 *        a P above each H.
 * Cue 4: the outer layer of the cube's back-top-right corner goes, in a wave, and the corner is empty;
 *        then the core fades in, filling the inside: it shows in the cut and between all the beads.
 * Tail (after the pause): the beads go, the camera moves back unseen, and the empty cube's
 * wireframe fades in: the first frame of the "frame" scene.
 *
 * The camera never passes a face edge-on or face-on, and there is no depth cue: the cube stays
 * red-orange. Every P comes and goes by opacity, at full size, with its sticks.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, mixShot, R_RES, type Bead, type Stick, type Shot, type Project } from '../three/Scene3D';
import { cubeOutline, ribbonChain, framePieces, FRAME_SHOT, CUBE_SHELL, type Letter } from '../three/cube';
import { ramp, sec } from '../lib/anim';
import { C, FONT } from '../theme/theme';
import * as M from '../model/toy';
import type { V3 } from '../model/toy';
import type { SceneTime } from '../script';

const N1 = M.n - 1;
const keyOf = (p: V3) => p.join(',');
const add = (a: V3, b: V3): V3 => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
const onSurface = (p: V3) => p[0] === 0 || p[0] === N1 || p[1] === 0 || p[1] === N1 || p[2] === 0 || p[2] === -N1;

/** the outer layer of the cube, drawn as beads */
const SHELL: V3[] = [];
for (let x = 0; x <= N1; x++) for (let y = 0; y <= N1; y++) for (let z = -N1; z <= 0; z++) if (onSurface([x, y, z])) SHELL.push([x, y, z]);

/** a viewing direction: turned `yawDeg` from the front towards the right, raised `elDeg` */
const dirOf = (yawDeg: number, elDeg: number): V3 => {
  const a = (yawDeg * Math.PI) / 180;
  const e = (elDeg * Math.PI) / 180;
  return [Math.sin(a) * Math.cos(e), Math.sin(e), Math.cos(a) * Math.cos(e)];
};

// ---------------------------------------------------------------- cue 1: twelve P's
/**
 * Twelve H's on the cube's outline as THREE sees it, two per outline edge, going round. Each P is
 * one step out of a face we see (top, right or front), so it stands in the empty space next to the
 * cube, clear of every bead.
 */
const SAMPLE: { h: V3; p: V3 }[] = [];
for (const z of [-3, -8]) SAMPLE.push({ h: [0, N1, z], p: [0, N1 + 1, z] });
for (const x of [3, 8]) SAMPLE.push({ h: [x, N1, -N1], p: [x, N1 + 1, -N1] });
for (const y of [8, 3]) SAMPLE.push({ h: [N1, y, -N1], p: [N1 + 1, y, -N1] });
for (const z of [-8, -3]) SAMPLE.push({ h: [N1, 0, z], p: [N1 + 1, 0, z] });
for (const x of [8, 3]) SAMPLE.push({ h: [x, 0, 0], p: [x, 0, 1] });
for (const y of [3, 8]) SAMPLE.push({ h: [0, y, 0], p: [0, y, 1] });
/** the P that the label "every P" points at: out of the right face, low on its back edge */
const SAMPLE_NAMED = SAMPLE.findIndex((s) => keyOf(s.h) === keyOf([N1, 3, -N1]));

// ---------------------------------------------------------------- cue 2: a rod up the front-right edge
/**
 * The rod's H's run up the front-right edge from its bottom corner. Each H has a P off the front face
 * and one off the right face, alternating so that the string is a walk: P H P, P H P, …
 */
const ROD_H: V3[] = Array.from({ length: N1 }, (_, y) => [N1, y, 0] as V3);
const OFF_FRONT: V3 = [0, 0, 1];
const OFF_RIGHT: V3 = [1, 0, 0];
const ROD: Letter[] = ROD_H.flatMap((h, i) => {
  const [u, w] = i % 2 ? [OFF_RIGHT, OFF_FRONT] : [OFF_FRONT, OFF_RIGHT];
  return [
    { pos: add(h, u), h: false },
    { pos: h, h: true },
    { pos: add(h, w), h: false },
  ];
});

// ---------------------------------------------------------------- cue 3: a ribbon on the top face
/** along the back row of the top face (one row in from its back edge): each H has one outer side, up */
const RIB_H: V3[] = [2, 3, 4, 5, 6, 7, 8, 9].map((x) => [x, N1, -(N1 - 1)] as V3);
const RIBBON: Letter[] = ribbonChain(RIB_H, [0, 1, 0]);

// checks: both chains are walks on the lattice, and every P is outside the cube
const outsideCube = (p: V3) => p[0] < 0 || p[0] > N1 || p[1] < 0 || p[1] > N1 || p[2] > 0 || p[2] < -N1;
for (const chain of [ROD, RIBBON])
  chain.forEach((l, i) => {
    if (!l.h && !outsideCube(l.pos)) throw new Error('local: a P inside the cube');
    if (i > 0) {
      const q = chain[i - 1].pos;
      if (Math.abs(q[0] - l.pos[0]) + Math.abs(q[1] - l.pos[1]) + Math.abs(q[2] - l.pos[2]) !== 1) throw new Error('local: a chain breaks');
    }
  });

// ---------------------------------------------------------------- cue 4: the cut corner and the core
/**
 * The cube's front-top-right corner (7 × 7 × 7 nodes) is cut away: its outer layer goes, and the core
 * is never drawn there. The cut's three walls all face the camera, and they are the core's beads.
 */
const inCut = (p: V3) => p[0] >= 5 && p[1] >= 5 && p[2] >= -6;
const CUT_CORNER: V3 = [N1, N1, 0];
const cutOrder = (p: V3) => (Math.abs(p[0] - CUT_CORNER[0]) + Math.abs(p[1] - CUT_CORNER[1]) + Math.abs(p[2] - CUT_CORNER[2])) / 18;
/**
 * The core, as the frame scene draws it, but only where the cut lays it bare: its beads on the cut's
 * three walls (and along the walls' inner edges), joined where they follow one another in the
 * string. Nothing else of the inside is drawn, and the faces seen through the gaps from the cut are
 * the far ones, which the cube's shell hides, so the gaps show the background (no filler block: a
 * filler is drawn after see-through sticks and would hide them while they fade).
 */
const CORE_LETTERS = framePieces().find((p) => p.id === 'core')!.letters;
const onCutWall = (p: V3) => {
  if (inCut(p)) return false;
  for (let dx = 0; dx <= 1; dx++)
    for (let dy = 0; dy <= 1; dy++)
      for (let dz = 0; dz <= 1; dz++) if ((dx || dy || dz) && inCut([p[0] + dx, p[1] + dy, p[2] + dz])) return true;
  return false;
};
const CORE_BEADS: V3[] = CORE_LETTERS.map((l) => l.pos).filter(onCutWall);
const CORE_STICKS: [V3, V3][] = [];
CORE_LETTERS.forEach((l, i) => {
  if (i === 0 || !onCutWall(l.pos)) return;
  const q = CORE_LETTERS[i - 1].pos;
  if (onCutWall(q) && Math.abs(q[0] - l.pos[0]) + Math.abs(q[1] - l.pos[1]) + Math.abs(q[2] - l.pos[2]) === 1) CORE_STICKS.push([q, l.pos]);
});
/** the core's bead the label points at: the top-right corner of the cut's back wall */
const CORE_NAMED: V3 = [N1 - 1, N1 - 1, -7];

// ---------------------------------------------------------------- shots
const WHOLE = FRAME_SHOT(0);
/** three faces, the front one widest (raised a little, so the cube clears the caption band) */
const THREE: Shot = { target: WHOLE.target, dir: dirOf(30, 26), dist: 54, offset: [0, -40] };
/**
 * The front-right edge, looked at from outside it: the edge runs down the middle, the front face
 * falls away on one side and the right face on the other, so the two P's of each H stick out on
 * either side. Far enough back, and raised, to leave room below the cube for the labels.
 */
const EDGE: Shot = { target: [5.5, 5.5, -5.5], dir: dirOf(45, 20), dist: 64, offset: [0, -165] };

/** the shared label styles: a name and a sub-line */
const NAME = { fontFamily: FONT.sans, fontSize: 26, fontWeight: 600, fill: C.fg } as const;
const SUB = { fontFamily: FONT.sans, fontSize: 22, fontWeight: 500, fill: C.fgMuted } as const;

/** coloured letters, "PHP PHP …", as a sub-line */
function Spelled({ x, y, text, anchor = 'start' }: { x: number; y: number; text: string; anchor?: 'start' | 'middle' | 'end' }) {
  return (
    <text x={x} y={y} textAnchor={anchor} fontFamily={FONT.sans} fontWeight={600} fontSize={22} letterSpacing={1.5}>
      {[...text].map((ch, i) => (
        <tspan key={i} fill={ch === 'H' ? C.h : ch === 'P' ? C.p : C.fgMuted}>
          {ch}
        </tspan>
      ))}
    </text>
  );
}

/** the letters of a chain laid by one tip: letter k is reached at `at + k * dt` and comes in over 8 frames */
interface Tip {
  at: number;
  dt: number;
}

export default function LocalScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1, c2, c3] = scene.cueTimes;
  const t0 = (s: number) => c0.from + sec(s);
  const t1 = (s: number) => c1.from + sec(s);
  const t2 = (s: number) => c2.from + sec(s);
  const t3 = (s: number) => c3.from + sec(s);
  const end = scene.duration - 1;

  const beads: Bead[] = [];
  const sticks: Stick[] = [];
  const lines: Stick[] = [];

  // ---------------- timing
  // cue 1: each P and its stem come in together (10 frames), one after another
  const popAt = (i: number) => t0(2.2) + i * 5;
  const pGone = 1 - ramp(f, c1.from, 10);
  // cues 2 and 3: one tip each
  const ROD_T: Tip = { at: t1(2.0), dt: 2.5 };
  const RIB_T: Tip = { at: t2(2.0), dt: 3 };
  const rodGone = 1 - ramp(f, c2.from, 10);
  const ribGone = 1 - ramp(f, c3.from, 10);
  // cue 4: the corner's outer layer goes in a wave (each bead over 8 frames), then the core comes in
  const cutAt = (p: V3) => t3(0.6) + cutOrder(p) * sec(0.8);
  const coreAt = t3(1.9);
  const coreIn = ramp(f, coreAt, 15);
  // the tail, after the pause (c3.to - 10): the beads go (12 frames), the camera moves back while
  // nothing is drawn, then the empty cube's wireframe comes in, ending on the frame scene's first frame
  const tailAt = c3.to - 8;
  const kept = 1 - ramp(f, tailAt, 12);
  const camBack = ramp(f, tailAt + 12, 6);
  const wireAt = tailAt + 19;
  const wire = ramp(f, wireAt, Math.max(6, end - wireAt));

  // The core comes in, and in the tail the whole cube goes, as one picture under the rest, faded
  // as a whole: bead by bead, a see-through bead paints over the see-through sticks in front of it
  // (they write no depth), and half-faded beads show each other. The core lies inside the faces
  // the camera sees, so drawing it under them changes nothing while both are opaque.
  const tailing = f >= tailAt;
  const cubeBeads: Bead[] = [];
  const cubeSticks: Stick[] = [];
  const cubeO = tailing ? kept : coreIn;

  // ---------------- the outer layer, in full colour (the cut corner's beads go one by one)
  if (kept > 0)
    for (const p of SHELL) {
      const o = inCut(p) ? 1 - ramp(f, cutAt(p), 8) : 1;
      if (o > 0) (tailing ? cubeBeads : beads).push({ pos: p, color: C.h, opacity: o < 1 ? o : undefined });
    }

  // ---------------- the core on the cut's walls
  if (kept > 0 && coreIn > 0) {
    for (const p of CORE_BEADS) cubeBeads.push({ pos: p, color: C.h });
    for (const [a, b] of CORE_STICKS) cubeSticks.push({ a, b, color: C.backbone });
  }

  // ---------------- cue 1: P's one step outside, each with its stem
  if (pGone > 0)
    SAMPLE.forEach(({ h, p }, i) => {
      const o = ramp(f, popAt(i), 10) * pGone;
      if (o <= 0) return;
      beads.push({ pos: p, color: C.p, hollow: true, opacity: o });
      sticks.push({ a: h, b: p, color: C.backbone, fade: 1 - o });
    });

  // ---------------- cues 2 and 3: a rod, then a ribbon, laid letter by letter from one tip
  const lay = (chain: Letter[], T: Tip, gone: number) => {
    if (gone <= 0) return;
    const inAt = (k: number) => ramp(f, T.at + k * T.dt, 8);
    chain.forEach((l, k) => {
      const o = inAt(k) * gone;
      if (o <= 0) return;
      // the H's are the cube's own beads; the P's come in at full size
      if (!l.h) beads.push({ pos: l.pos, color: C.p, hollow: true, opacity: o });
      if (k > 0) {
        const s = Math.min(inAt(k - 1), inAt(k)) * gone;
        if (s > 0) sticks.push({ a: chain[k - 1].pos, b: l.pos, color: C.backbone, fade: 1 - s });
      }
    });
  };
  lay(ROD, ROD_T, rodGone);
  lay(RIBBON, RIB_T, ribGone);

  // ---------------- the wireframe of the empty cube, in the tail
  if (wire > 0) lines.push(...cubeOutline(0.6 * wire, C.fgSubtle, 0.5, 1));

  // ---------------- camera: small, eased moves; never through a face-on or edge-on view
  let shot = mixShot(WHOLE, THREE, ramp(f, t0(0.2), sec(1.8)));
  shot = mixShot(shot, EDGE, ramp(f, t1(0.2), sec(1.6)));
  shot = mixShot(shot, THREE, ramp(f, t2(0.2), sec(1.6)));
  shot = mixShot(shot, WHOLE, camBack);

  // ---------------- labels: each fades out (8 frames) before the next one comes in
  const outAt = (to: number) => 1 - ramp(f, to, 8);
  const lab1H = Math.min(ramp(f, t0(1.6), sec(0.5)), outAt(c1.from));
  const lab1P = Math.min(ramp(f, t0(4.6), sec(0.5)), outAt(c1.from));
  const labRod = Math.min(ramp(f, t1(5.0), sec(0.5)), outAt(c2.from));
  const labMark = Math.min(ramp(f, t1(5.6), sec(0.5)), outAt(c2.from));
  const labRib = Math.min(ramp(f, t2(4.0), sec(0.5)), outAt(c3.from));
  const labCore = Math.min(ramp(f, t3(2.6), sec(0.5)), outAt(tailAt));

  return (
    <SceneFrame scene={scene}>
      {cubeO > 0 && cubeBeads.length > 0 && (
        <div style={{ position: 'absolute', inset: 0, opacity: cubeO }}>
          <Scene3D shot={shot} beads={cubeBeads} sticks={cubeSticks} shell={CUBE_SHELL} />
        </div>
      )}
      <Scene3D shot={shot} beads={beads} sticks={sticks} lines={lines} shell={CUBE_SHELL}>
        {(project) => <Labels project={project} o={{ lab1H, lab1P, labRod, labMark, labRib, labCore }} />}
      </Scene3D>
    </SceneFrame>
  );
}

function Labels({ project, o }: { project: Project; o: Record<'lab1H' | 'lab1P' | 'labRod' | 'labMark' | 'labRib' | 'labCore', number> }) {
  const els: React.ReactNode[] = [];
  /** a bead's radius on screen */
  const rpx = (p: V3) => Math.abs(project([p[0], p[1] + R_RES, p[2]])[1] - project(p)[1]);
  const corners: V3[] = [0, 1, 2, 3, 4, 5, 6, 7].map((m) => [m & 1 ? N1 : 0, m & 2 ? N1 : 0, m & 4 ? -N1 : 0]);
  const xsOf = (ps: V3[]) => ps.map((c) => project(c)[0]);
  /** a leader from a bead's edge (a gap of 5 px) to a point */
  const leader = (key: string, at: V3, x2: number, y2: number) => {
    const [x, y] = project(at);
    const d = Math.hypot(x2 - x, y2 - y) || 1;
    const s = rpx(at) + 5;
    return <line key={key} x1={x + ((x2 - x) * s) / d} y1={y + ((y2 - y) * s) / d} x2={x2} y2={y2} stroke={C.fgMuted} strokeWidth={2} />;
  };
  /** a name with its sub-line, left or right of a level leader from a bead */
  const sideLabel = (key: string, at: V3, x: number, side: 'left' | 'right', opacity: number, name: React.ReactNode, sub: React.ReactNode) => {
    const [, y] = project(at);
    const tx = side === 'left' ? x - 8 : x + 8;
    const anchor = side === 'left' ? 'end' : 'start';
    return (
      <g key={key} opacity={opacity}>
        {leader(`${key}-l`, at, x, y)}
        <text x={tx} y={y + 9} textAnchor={anchor} {...NAME}>
          {name}
        </text>
        {sub}
      </g>
    );
  };

  if (o.lab1H > 0) {
    // left of the cube, level with a bead on its left edge
    const at: V3 = [0, 6, 0];
    const x = project(at)[0] - rpx(at) - 36;
    els.push(
      sideLabel('h', at, x, 'left', o.lab1H, 'the cube', (
        <text x={x - 8} y={project(at)[1] + 39} textAnchor="end" {...SUB}>
          full of <tspan fill={C.h}>H</tspan>’s
        </text>
      )),
    );
  }
  if (o.lab1P > 0) {
    // right of one of the P's on the right
    const at = SAMPLE[SAMPLE_NAMED].p;
    const x = project(at)[0] + rpx(at) + 36;
    els.push(
      sideLabel('p', at, x, 'right', o.lab1P, (
        <>
          every <tspan fill={C.p}>P</tspan>
        </>
      ), (
        <text x={x + 8} y={project(at)[1] + 39} {...SUB}>
          one step outside
        </text>
      )),
    );
  }
  if (o.labRod > 0 || o.labMark > 0) {
    // under the cube: the rod's name below its first H (the bottom corner), its first H's two P's
    // named on either side
    const h = ROD_H[0];
    const [hx, hy] = project(h);
    const pa = add(h, OFF_FRONT);
    const pb = add(h, OFF_RIGHT);
    const [ax] = project(pa);
    const [bx] = project(pb);
    const bottom = Math.max(project(pa)[1] + rpx(pa), hy + rpx(h));
    const y = bottom + 46;
    if (o.labMark > 0)
      els.push(
        <g key="mark" opacity={o.labMark}>
          {leader('la', pa, ax - 18, y - 24)}
          <text x={ax - 22} y={y} textAnchor="end" {...NAME}>
            a <tspan fill={C.p}>P</tspan> outside one face
          </text>
          {leader('lb', pb, bx + 18, y - 24)}
          <text x={bx + 22} y={y} {...NAME}>
            a <tspan fill={C.p}>P</tspan> outside the other face
          </text>
        </g>,
      );
    if (o.labRod > 0) {
      const ry = y + 62;
      els.push(
        <g key="rod" opacity={o.labRod}>
          {leader('lr', h, hx, ry - 28)}
          <text x={hx} y={ry} textAnchor="middle" {...NAME}>
            rod, on an edge
          </text>
          <Spelled x={hx} y={ry + 30} text="PHP PHP PHP …" anchor="middle" />
        </g>,
      );
    }
  }
  if (o.labRib > 0) {
    // right of the cube, level with the ribbon's last P (it stands up out of the top face)
    const at = RIBBON[RIBBON.length - 1].pos;
    const x = Math.max(...xsOf(corners)) + 36;
    els.push(
      sideLabel('rib', at, x, 'right', o.labRib, 'ribbon, on a face', <Spelled x={x + 8} y={project(at)[1] + 39} text="PHHP PHHP …" />),
    );
  }
  if (o.labCore > 0) {
    // right of the cube, level with a core bead at the back of the cut
    const at = CORE_NAMED;
    const x = Math.max(...xsOf(corners)) + 36;
    els.push(sideLabel('core', at, x, 'right', o.labCore, 'core, inside', <Spelled x={x + 8} y={project(at)[1] + 39} text="HHHHHHHH …" />));
  }
  return <>{els}</>;
}
