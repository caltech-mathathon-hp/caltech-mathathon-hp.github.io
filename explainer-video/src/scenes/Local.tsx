/**
 * Scene "local": in a perfect fold every P is outside the cube, and that decides where each piece goes.
 * The cube is drawn as its outer layer of beads (an invisible filler hides the far side).
 * Cue 1: the cube turns so three faces show; the outline goes, and twelve H's on the cube's outline
 *        each get a P one step out of a face we see, on a stem, out in the empty space.
 * Cue 2: the camera turns to the cube's front-left edge: a rod (PHP PHP …) is laid along it, each H
 *        with a P off each of the two faces.
 * Cue 3: from higher up, a ribbon (PHHP PHHP …) is laid across the middle of the top face.
 * Cue 4: back to the whole cube; the outer layer of its front-top-right corner is taken away in a
 *        wave, and the core's beads show there in H red. In the tail (after the pause) the beads go
 *        and the empty cube's wireframe comes back: the first frame of the "frame" scene.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, mixShot, FADE, R_RES, type Bead, type Stick, type Shot, type Solid } from '../three/Scene3D';
import { cubeOutline, innerBlock, rodChain, ribbonChain, framePieces, FRAME_SHOT, CUBE_SHELL, type Letter } from '../three/cube';
import { ramp, sec, clamp01, easeIn } from '../lib/anim';
import { C, FONT } from '../theme/theme';
import * as M from '../model/toy';
import type { V3 } from '../model/toy';
import type { SceneTime } from '../script';

const N1 = M.n - 1;
const keyOf = (p: V3) => p.join(',');
const inside = (v: number) => v >= 1 && v <= N1 - 1;
const isCore = (p: V3) => inside(p[0]) && inside(p[1]) && inside(-p[2]);

/** the outer layer of the cube, drawn as beads */
const SHELL: V3[] = [];
for (let x = 0; x <= N1; x++) for (let y = 0; y <= N1; y++) for (let z = -N1; z <= 0; z++) if (!isCore([x, y, z])) SHELL.push([x, y, z]);

/** a viewing direction: turned `yawDeg` from the front towards the right, raised `elDeg` */
const dirOf = (yawDeg: number, elDeg: number): V3 => {
  const a = (yawDeg * Math.PI) / 180;
  const e = (elDeg * Math.PI) / 180;
  return [Math.sin(a) * Math.cos(e), Math.sin(e), Math.cos(a) * Math.cos(e)];
};

// ---------------------------------------------------------------- cue 1: twelve P's
/**
 * Twelve H's on the cube's outline as THREE_FACES sees it, two per outline edge, going round. Each
 * P is one step out of a face we see (top, right or front), so it stands in the empty space next
 * to the cube, clear of every bead.
 */
const SAMPLE: { h: V3; p: V3 }[] = [];
for (const z of [-3, -8]) SAMPLE.push({ h: [0, N1, z], p: [0, N1 + 1, z] });
for (const x of [3, 8]) SAMPLE.push({ h: [x, N1, -N1], p: [x, N1 + 1, -N1] });
for (const y of [8, 3]) SAMPLE.push({ h: [N1, y, -N1], p: [N1 + 1, y, -N1] });
for (const z of [-8, -3]) SAMPLE.push({ h: [N1, 0, z], p: [N1 + 1, 0, z] });
for (const x of [8, 3]) SAMPLE.push({ h: [x, 0, 0], p: [x, 0, 1] });
for (const y of [3, 8]) SAMPLE.push({ h: [0, y, 0], p: [0, y, 1] });
const SAMPLE_AT = new Map(SAMPLE.map((s, i) => [keyOf(s.h), i]));

// ---------------------------------------------------------------- cue 2: a rod on the front-left edge
const ROD_H: V3[] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map((y) => [0, y, 0] as V3);
const ROD: Letter[] = rodChain(ROD_H);
/** where along the rod each of its H's is */
const ROD_AT = new Map(ROD.map((l, k) => [l.h ? keyOf(l.pos) : '', k]).filter(([s]) => s !== '') as [string, number][]);

// ---------------------------------------------------------------- cue 3: a ribbon across the top face
/** a straight row in the middle of the top face: each H has one outer side, up */
const RIB_H: V3[] = [2, 3, 4, 5, 6, 7, 8, 9].map((x) => [x, N1, -5] as V3);
const RIBBON: Letter[] = ribbonChain(RIB_H, [0, 1, 0]);
const RIB_AT = new Map(RIBBON.map((l, k) => [l.h ? keyOf(l.pos) : '', k]).filter(([s]) => s !== '') as [string, number][]);

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

// ---------------------------------------------------------------- cue 4: the cut corner
/** the outer layer of the cube's front-top-right octant is taken away, to show the core there */
const inCut = (p: V3) => p[0] >= 6 && p[1] >= 6 && p[2] >= -5;
const CORNER: V3 = [N1, N1, 0];
const cutOrder = (p: V3) => (Math.abs(p[0] - CORNER[0]) + Math.abs(p[1] - CORNER[1]) + Math.abs(p[2] - CORNER[2])) / 15;
/**
 * The core's beads in that octant and one layer round it (the walls of the cut show core, too),
 * with its chain sticks, as the frame scene draws the core.
 */
const nearCut = (p: V3) => p[0] >= 5 && p[1] >= 5 && p[2] >= -6;
const CORE_LETTERS = framePieces().find((p) => p.id === 'core')!.letters;
const CORE_BEADS: V3[] = CORE_LETTERS.map((l) => l.pos).filter(nearCut);
const CORE_STICKS: [V3, V3][] = [];
CORE_LETTERS.forEach((l, i) => {
  if (i > 0 && nearCut(l.pos) && nearCut(CORE_LETTERS[i - 1].pos)) CORE_STICKS.push([CORE_LETTERS[i - 1].pos, l.pos]);
});
/** the invisible filler, without that region (else it would hide the core's beads there) */
const FILL_CUT: [V3, V3][] = (() => {
  const lo = 0.45;
  const hi = N1 - 0.45;
  const m = 4.5;
  const mz = 6.5;
  return [
    [[lo, lo, -hi], [m, hi, -lo]],
    [[m, lo, -hi], [hi, m, -lo]],
    [[m, m, -hi], [hi, hi, -mz]],
  ];
})();

// ---------------------------------------------------------------- shots
const WHOLE = FRAME_SHOT(0);
/** all three faces at a fair angle, so every P's stem shows */
const THREE_FACES: Shot = { target: WHOLE.target, dir: dirOf(40, 30), dist: 52 };
/**
 * The front-left edge, looked at from outside the corner: the edge runs down the middle of the box,
 * the left face falls away on one side and the front face on the other, so the two P's of each H
 * stick out on either side, one off each face. Far enough back to leave room below the cube for
 * the two labels of the rod's lowest P's.
 */
const EDGE: Shot = { target: [5.5, 5.5, -5.5], dir: dirOf(-45, 22), dist: 54, offset: [0, -110] };
/** high enough that the top face reads as a flat table */
const TOP: Shot = { target: [5.5, 7.5, -5.5], dir: dirOf(24, 50), dist: 50, offset: [-60, -125] };

/** the shared label styles: a name, and coloured letters */
const NAME = { fontFamily: FONT.sans, fontSize: 26, fontWeight: 600, fill: C.fg } as const;

/** coloured letters, "PHP PHP …" */
function Spelled({ x, y, text, anchor = 'start' }: { x: number; y: number; text: string; anchor?: 'start' | 'middle' | 'end' }) {
  return (
    <text x={x} y={y} textAnchor={anchor} fontFamily={FONT.sans} fontWeight={600} fontSize={26} letterSpacing={1.5}>
      {[...text].map((ch, i) => (
        <tspan key={i} fill={ch === 'H' ? C.h : ch === 'P' ? C.p : C.fgMuted}>
          {ch}
        </tspan>
      ))}
    </text>
  );
}

/**
 * A P leaving (g: 0..1). Each P sits right in front of a bead of the cube, and a bead can't be
 * see-through: a P paled all the way to the background would leave a pale disc biting into the
 * bead behind it. So the P pales only a little and shrinks to its centre, and the bead behind
 * shows again around it. Its sticks fade out (faded sticks are drawn see-through).
 */
const outLook = (g: number) => ({ fade: 0.4 * clamp01(g), scale: 1 - clamp01(g) ** 2, stick: clamp01(g * 1.5) });

export default function LocalScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1, c2, c3] = scene.cueTimes;
  const t0 = (s: number) => c0.from + sec(s);
  const t1 = (s: number) => c1.from + sec(s);
  const t2 = (s: number) => c2.from + sec(s);
  const t3 = (s: number) => c3.from + sec(s);
  /** linear, for values that are eased where they are used (ramp does not clamp a custom ease) */
  const lin = (t: number) => clamp01(t);

  const beads: Bead[] = [];
  const sticks: Stick[] = [];
  const lines: Stick[] = [];

  // ---------------- how quiet the cube is, and when each piece is the subject
  const q = FADE.context * ramp(f, t0(1.0), sec(0.6));
  // the tail, after the pause (c3.to - 10): the beads go, then the empty cube's wireframe comes in,
  // so the last frame is the first frame of "frame"
  const tail = ramp(f, c3.to - 6, 16, easeIn);
  const wire = ramp(f, c3.to + 10, 10);

  // cue 1: each P's stem grows from its H, then the P fades in at full size
  const popAt = (i: number) => t0(2.2) + i * 5;
  const pOut = ramp(f, c1.from, 12, lin);
  // cues 2 and 3: the tip reaches letter k at at + k * dt
  const ROD_T = { at: t1(2.6), dt: 2.5 };
  const RIB_T = { at: t2(2.4), dt: 3 };
  const reached = (T: { at: number; dt: number }, k: number) => T.at + k * T.dt;
  const rodOut = ramp(f, c2.from, 12, lin);
  const ribOut = ramp(f, c3.from, 12, lin);
  // cue 4: the core shows (unseen behind the outer layer, it fades in from the background), then
  // the outer layer of the octant goes in a wave from the corner
  const coreIn = ramp(f, t3(2.0), sec(0.5));
  const cutAt = (p: V3) => t3(2.5) + cutOrder(p) * sec(0.9);

  // ---------------- the outer layer
  if (tail < 1)
    for (const p of SHELL) {
      let scale = 1;
      let extra = 0;
      if (inCut(p) && f >= t3(2.5)) {
        const g = clamp01((f - cutAt(p)) / 10);
        if (g >= 1) continue;
        scale = 1 - easeIn(g);
        extra = 0.5 * g;
      }
      const k = keyOf(p);
      let hi = 0;
      const si = SAMPLE_AT.get(k);
      if (si !== undefined) hi = ramp(f, popAt(si), 6) * (1 - pOut);
      const ri = ROD_AT.get(k);
      if (ri !== undefined) hi = Math.max(hi, ramp(f, reached(ROD_T, ri), 6) * (1 - rodOut));
      const bi = RIB_AT.get(k);
      if (bi !== undefined) hi = Math.max(hi, ramp(f, reached(RIB_T, bi), 6) * (1 - ribOut));
      const base = q * (1 - hi);
      const fade = base + (1 - base) * Math.max(extra, tail);
      beads.push({ pos: p, color: C.h, fade, scale });
    }

  // ---------------- the filler, and the core's corner
  const solids: Solid[] = [];
  if (tail < 1) {
    if (f < t3(2.0)) solids.push(innerBlock({ opacity: 1 - tail }));
    else
      for (const [min, max] of FILL_CUT) solids.push({ min, max, color: C.bg, fade: 1, opacity: 1 - tail });
    if (f >= t3(2.0)) {
      const fade = 1 - coreIn * (1 - tail);
      for (const p of CORE_BEADS) beads.push({ pos: p, color: C.h, fade });
      for (const [a, b] of CORE_STICKS) sticks.push({ a, b, color: C.backbone, fade });
    }
  }

  // ---------------- cue 1: P's one step outside
  if (pOut < 1)
    SAMPLE.forEach(({ h, p }, i) => {
      const grow = ramp(f, popAt(i), 6);
      if (grow <= 0) return;
      const pf = ramp(f, popAt(i) + 4, 8);
      // these P's are out in the empty space, with no bead behind them: they fade out at full size
      if (pf > 0) beads.push({ pos: p, color: C.p, hollow: true, r: R_RES, scale: 0.9 + 0.1 * pf, fade: 1 - pf * (1 - pOut) });
      sticks.push({ a: h, b: p, color: C.backbone, grow, fade: clamp01(pOut * 1.5) });
    });

  // ---------------- cues 2 and 3: a rod, then a ribbon, laid letter by letter from one tip
  const lay = (chain: Letter[], T: { at: number; dt: number }, gone: number) => {
    if (gone >= 1) return;
    const out = outLook(gone);
    chain.forEach((l, k) => {
      const t = reached(T, k);
      if (k > 0) {
        const grow = clamp01((f - reached(T, k - 1)) / T.dt);
        if (grow > 0) sticks.push({ a: chain[k - 1].pos, b: l.pos, color: C.backbone, grow, fade: out.stick });
      }
      if (!l.h) {
        const pf = ramp(f, t, 8);
        if (pf > 0) beads.push({ pos: l.pos, color: C.p, hollow: true, scale: (0.9 + 0.1 * pf) * out.scale, fade: 1 - pf * (1 - out.fade) });
      }
    });
  };
  lay(ROD, ROD_T, rodOut);
  lay(RIBBON, RIB_T, ribOut);

  // ---------------- the outline: it would cross the P's of cue 1, so it goes; it comes back in the tail
  const outline = 0.6 * Math.max(1 - ramp(f, t0(0.9), sec(0.5)), ramp(f, c3.to - 6, 16));
  if (outline > 0) lines.push(...cubeOutline(outline, C.fgSubtle, 0.5, wire));

  // ---------------- camera
  let shot = mixShot(WHOLE, THREE_FACES, ramp(f, t0(0.2), sec(1.8)));
  shot = mixShot(shot, EDGE, ramp(f, t1(0.3), sec(2.0)));
  shot = mixShot(shot, TOP, ramp(f, t2(0.3), sec(1.8)));
  shot = mixShot(shot, WHOLE, ramp(f, t3(0.3), sec(2.0)));

  // ---------------- labels: each fades out (8 frames) before the next one comes in
  const outAt = (to: number) => 1 - ramp(f, to, 8);
  const lab1H = Math.min(ramp(f, t0(1.6), sec(0.5)), outAt(c1.from));
  const lab1P = Math.min(ramp(f, t0(4.6), sec(0.5)), outAt(c1.from));
  const labRod = Math.min(ramp(f, t1(5.0), sec(0.5)), outAt(c2.from));
  const labMark = Math.min(ramp(f, t1(5.6), sec(0.5)), outAt(c2.from));
  const labRib = Math.min(ramp(f, t2(4.3), sec(0.5)), outAt(c3.from));
  const labCore = Math.min(ramp(f, t3(3.8), sec(0.5)), 1 - tail);

  return (
    <SceneFrame scene={scene}>
      <Scene3D shot={shot} beads={beads} sticks={sticks} lines={lines} solids={solids} shell={CUBE_SHELL} depthCue>
        {(project) => {
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
          if (lab1H > 0) {
            // left of the cube and of its P's
            const x = Math.min(...xsOf(corners), ...xsOf(SAMPLE.map((s) => s.p))) - 40;
            const y = project([0, 6, 0])[1];
            els.push(
              <text key="h" x={x} y={y} textAnchor="end" opacity={lab1H} {...NAME}>
                inside: only <tspan fill={C.h}>H</tspan>’s
              </text>,
            );
          }
          if (lab1P > 0) {
            const x = Math.max(...xsOf(corners), ...xsOf(SAMPLE.map((s) => s.p))) + 40;
            const y = project([N1, 6, -5.5])[1];
            els.push(
              <g key="p" opacity={lab1P} {...NAME}>
                <text x={x} y={y - 4}>
                  every <tspan fill={C.p}>P</tspan> sits
                </text>
                <text x={x} y={y + 30}>one step outside</text>
              </g>,
            );
          }
          if (labRod > 0) {
            // left of the cube, level with the rod (the one thing in full colour)
            const x = Math.min(...xsOf(corners)) - 36;
            const y = project([0, 5.5, 0])[1];
            els.push(
              <g key="rod" opacity={labRod}>
                <text x={x} y={y - 6} textAnchor="end" {...NAME}>
                  rod, on an edge
                </text>
                <Spelled x={x} y={y + 30} text="PHP PHP PHP …" anchor="end" />
              </g>,
            );
          }
          if (labMark > 0) {
            // the lowest H's two P's, each off its own face; the labels sit under the cube
            const h = ROD_H[0];
            const pOn = (d: V3) => ROD.find((l) => !l.h && keyOf(l.pos) === keyOf([h[0] + d[0], h[1] + d[1], h[2] + d[2]]))!.pos;
            const pa = pOn([-1, 0, 0]);
            const pb = pOn([0, 0, 1]);
            const bottom = project([0, 0, 0])[1] + rpx([0, 0, 0]);
            const y = bottom + 48;
            const [ax] = project(pa);
            const [bx] = project(pb);
            els.push(
              <g key="mark" opacity={labMark}>
                {leader('la', pa, ax - 16, y - 24)}
                <text x={ax - 20} y={y} textAnchor="end" {...NAME}>
                  a <tspan fill={C.p}>P</tspan> outside one face
                </text>
                {leader('lb', pb, bx + 16, y - 24)}
                <text x={bx + 20} y={y} {...NAME}>
                  a <tspan fill={C.p}>P</tspan> outside the other face
                </text>
              </g>,
            );
          }
          if (labRib > 0) {
            // right of the cube, level with the ribbon (the one thing in full colour)
            const x = Math.max(...xsOf(corners)) + 36;
            const y = project(RIBBON[RIBBON.length - 1].pos)[1];
            els.push(
              <g key="rib" opacity={labRib}>
                <text x={x} y={y - 6} {...NAME}>
                  ribbon, on a face
                </text>
                <Spelled x={x} y={y + 30} text="PHHP PHHP …" />
              </g>,
            );
          }
          if (labCore > 0) {
            // right of the cube, level with the core's corner (the one thing in full colour)
            const x = Math.max(...xsOf(corners)) + 36;
            const y = project([N1 - 1, 8, -1])[1];
            els.push(
              <g key="core" opacity={labCore}>
                <text x={x} y={y - 6} {...NAME}>
                  core, inside
                </text>
                <Spelled x={x} y={y + 30} text="HHHHHHHH …" />
              </g>,
            );
          }
          return <>{els}</>;
        }}
      </Scene3D>
    </SceneFrame>
  );
}
