/**
 * Scene "walls": the camera turns from the finished frame to the open front face. The walls are
 * laid in string order (rod up the right free edge, wall right to left, rod down the left free
 * edge, wall back, rod up; then the second period; then the spaced rod).
 *
 * Face-on the frame is in full colour (it was quieted while the front face was the subject); the
 * free edges keep their band from the "frame" scene, under the rods laid on them. Labels name the
 * free edges, rod 1 (the cube's top and bottom edge rows), the walls and one short rod, and say
 * that the P's are not drawn.
 * Cue 2: every short rod is marked with a bracket and its length, in string order: each free edge
 * is filled by rods exactly, so the walls have no slack. Then the strips between the walls light up
 * and are named on the left, as in the later face-on steps.
 * The tail, after the pause: the brackets, the bands and the strips' sub-lines go, and the strip
 * names move to their middle row, so the last frame is the first frame of "padding".
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, mixShot, FADE, projector, R_RES, type Project } from '../three/Scene3D';
import { FRAME_SHOT, FACE_SHOT, CUBE_SHELL, freeEdgeLine, FREE_BAND } from '../three/cube';
import { ramp, sec, clamp01, easeOut } from '../lib/anim';
import { C, FONT } from '../theme/theme';
import * as M from '../model/toy';
import type { SceneTime } from '../script';
import { newDraw, drawFrame, drawWalls, addHoles, faceOutline, stripBox, wallProgress, WALLS } from './lib/face';

const N1 = M.n - 1;
/** global walls progress at which period 1, then period 2 is done (by H count); the spaced rod is last */
const [P1, P2] = (() => {
  const hs = WALLS.map((w) => w.letters.filter((l) => l.h).length);
  const sum = (k: number) => hs.slice(0, k).reduce((a, b) => a + b, 0) / hs.reduce((a, b) => a + b, 0);
  return [sum(5), sum(10)];
})();

/** row (0 = top) of a front-face node */
const rowOf = (p: M.V3) => N1 - p[1];

/**
 * The short rods on the free edges, in string order: per period a rod up the right edge, the long
 * one down the left edge and a rod up the right edge; then the spaced rod's H's, one per period.
 * `side` 0 is the left edge, 1 the right; `r0`..`r1` its rows (top to bottom).
 */
const SHORT: { side: 0 | 1; r0: number; r1: number }[] = (() => {
  const out: { side: 0 | 1; r0: number; r1: number }[] = [];
  const span = (ps: M.V3[], side: 0 | 1) => {
    const rows = ps.map(rowOf);
    out.push({ side, r0: Math.min(...rows), r1: Math.max(...rows) });
  };
  for (const p of M.periods) {
    span(p.qRod1, 1);
    span(p.q2Rod, 0);
    span(p.qRod2, 1);
  }
  for (const h of M.spacedRod) span([h], 1);
  return out;
})();
// check: the rods fill every node of both free edges between the top and bottom wall, once
for (const side of [0, 1] as const) {
  const rows = SHORT.filter((s) => s.side === side).flatMap((s) => Array.from({ length: s.r1 - s.r0 + 1 }, (_, i) => s.r0 + i));
  if (new Set(rows).size !== rows.length || rows.length !== N1 - 1) throw new Error('walls: the short rods do not fill a free edge');
}

/** the shared label styles */
const NAME = { fontFamily: FONT.sans, fontSize: 26, fontWeight: 600, fill: C.fg } as const;
const SUB = { fontFamily: FONT.sans, fontSize: 22, fontWeight: 500, fill: C.fgMuted } as const;

/**
 * Under the 3D picture (the beads cover it): the free edges' band, from the "frame" scene, and the
 * strips' boxes, drawn as "padding" draws them (it opens on this face).
 */
function Under({ project, band, strips }: { project: Project; band: number; strips: number[] }) {
  return (
    <svg width={1920} height={1080} viewBox="0 0 1920 1080" style={{ position: 'absolute', inset: 0 }}>
      {band > 0 &&
        ([0, 1] as const).map((side) => {
          const l = freeEdgeLine(project, side);
          return <line key={side} x1={l.x1} y1={l.y1} x2={l.x2} y2={l.y2} stroke={C.accent} strokeOpacity={FREE_BAND.opacity * band} strokeWidth={l.w} />;
        })}
      {strips.map((o, s) => {
        if (o <= 0) return null;
        const [x0, y0, x1, y1] = stripBox(project, s, 0.5);
        return <rect key={s} x={x0} y={y0} width={x1 - x0} height={y1 - y0} rx={STRIP_RX} fill={C.fgSubtle} fillOpacity={0.13} stroke={C.fgMuted} strokeWidth={2.5} opacity={o} />;
      })}
    </svg>
  );
}
const STRIP_RX = 12;

export default function WallsScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1] = scene.cueTimes;
  const turn = ramp(f, 4, sec(2.0));
  const shot = mixShot(FRAME_SHOT(1), FACE_SHOT, turn);
  const backFade = ramp(f, 10, sec(1.6));

  // period 1 slowly (so the order can be followed), period 2 faster, then the spaced rod's two H's
  const t1 = c0.from + sec(1.9);
  const d1 = sec(4.2);
  const d2 = sec(2.2);
  const d3 = sec(0.8);
  const walls =
    f < t1 + d1
      ? P1 * clamp01((f - t1) / d1)
      : f < t1 + d1 + d2
        ? P1 + (P2 - P1) * clamp01((f - t1 - d1) / d2)
        : P2 + (1 - P2) * clamp01((f - t1 - d1 - d2) / d3);

  const d = newDraw();
  // the frame as the "frame" scene leaves it, quiet as a whole; face-on it is in full colour again
  drawFrame(d, { backFade, context: FADE.context * (1 - turn) });
  // without the core's filler block, as the "frame" scene leaves it (the shell hides the faces
  // turned away): the block, in the background colour, would cover the free edges' band and the
  // quieted sticks in front of it
  d.solids.length = 0;
  drawWalls(d, walls);
  d.lines.push(...faceOutline(0.6, backFade, C.fgSubtle, true));

  // cue 2: the strips light up, after the short rods are marked
  const stripAt = (s: number) => c1.from + sec(4.0 + s * 0.5);
  const strips = [0, 1].map((s) => ramp(f, stripAt(s), sec(0.7)));
  // the tail, after the pause (c1.to - 10): brackets, bands and sub-lines go; the strip names'
  // leaders pull back out of the boxes (in the gap above the strip's first row), then the names
  // move down to the strips' middle rows, where "padding" has them
  // (all done by c1.to + 11, so the last 8 frames hold the first frame of "padding")
  const tail = ramp(f, c1.to - 6, 12);
  const retract = ramp(f, c1.to - 9, 8);
  const slide = ramp(f, c1.to - 1, 12);
  // the empty nodes as "frame" leaves them (0.9), as "padding" has them (1) at the end
  addHoles(d, { opacity: 0.9 + 0.1 * tail, free: 0 });

  const wp = wallProgress(walls);
  /** "wall" labels: one per wall, once it is laid */
  const wallIdx = WALLS.map((w, i) => (w.kind === 'wall' ? i : -1)).filter((i) => i >= 0);
  // cue 1's labels leave together at cue 2 (8 frames), before anything new comes in
  const out1 = 1 - ramp(f, c1.from, 8);
  const freeLab = ramp(f, sec(2.2), sec(0.6)) * out1;
  const edgeLab = ramp(f, sec(2.8), sec(0.6)) * out1;
  const rodLab = ramp(f, t1 + sec(1.2), sec(0.5));
  const pNote = ramp(f, t1 + d1 - sec(1.0), sec(0.6)) * out1;
  // cue 2: the rods' brackets come in string order (the first one is cue 1's "short rod" bracket);
  // the left ones make room for the strip names
  const shortIn = SHORT.map((_, i) => (i === 0 ? rodLab : ramp(f, c1.from + sec(0.5) + (i - 1) * 6, 8)));
  const numIn = SHORT.map((_, i) => ramp(f, c1.from + sec(0.5) + Math.max(0, i - 1) * 6 + (i === 0 ? -sec(0.2) : 0), 8));
  const leftOut = 1 - ramp(f, c1.from + sec(3.5), 8);

  const project = projector(shot);

  return (
    <SceneFrame scene={scene}>
      <Under project={project} band={1 - tail} strips={strips} />
      <Scene3D shot={shot} beads={d.beads} sticks={d.sticks} lines={d.lines} panels={d.panels} solids={d.solids} shell={CUBE_SHELL} depthCue={0.4 * (1 - turn)}>
        {(project) => {
          const u = project([1, 0, 0])[0] - project([0, 0, 0])[0];
          const r = R_RES * u;
          const left = project([0, 0, 0])[0];
          const right = project([N1, 0, 0])[0];
          const rowY = (row: number) => project([0, N1 - row, 0])[1];
          /** a row's name on the left of the face, with a short leader to the row's end */
          const rowName = (key: string, row: number, text: string, opacity: number) =>
            opacity > 0 && (
              <g key={key} opacity={opacity}>
                <line x1={left - r - 34} x2={left - r - 8} y1={rowY(row)} y2={rowY(row)} stroke={C.fgMuted} strokeWidth={2} />
                <text x={left - r - 42} y={rowY(row) + 9} textAnchor="end" {...NAME}>
                  {text}
                </text>
              </g>
            );
          /** a bracket along a short rod, just outside the face's outline, and (`num`) its length */
          const bracketX = (side: 0 | 1) => (side === 0 ? left - 0.5 * u - 16 : right + 0.5 * u + 16);
          const bracket = (i: number, o: number, num: number, key = `b${i}`) => {
            const s = SHORT[i];
            if (o <= 0 && num <= 0) return null;
            const dir = s.side === 0 ? -1 : 1;
            const x = bracketX(s.side);
            const y0 = rowY(s.r0) - 0.38 * u;
            const y1 = rowY(s.r1) + 0.38 * u;
            const tick = -dir * 7;
            return (
              <g key={key}>
                {o > 0 && <path d={`M ${x + tick} ${y0} H ${x} V ${y1} H ${x + tick}`} fill="none" stroke={C.fgMuted} strokeWidth={2} opacity={o} />}
                {num > 0 && (
                  <text x={x + dir * 12} y={(y0 + y1) / 2 + 9} textAnchor={s.side === 0 ? 'end' : 'start'} opacity={num} {...NAME}>
                    {s.r1 - s.r0 + 1}
                  </text>
                )}
              </g>
            );
          };
          const els: React.ReactNode[] = [];
          // cue 1: walls, rod 1, the free edges, a short rod, the P's
          wallIdx.forEach((i) => {
            const w = WALLS[i];
            const o = easeOut(clamp01((wp[i] - 0.85) / 0.15)) * out1;
            els.push(rowName(`w${i}`, rowOf(w.letters.find((l) => l.h)!.pos), 'wall', o));
          });
          els.push(rowName('e0', 0, 'rod 1', edgeLab), rowName('e1', N1, 'rod 1', edgeLab));
          if (freeLab > 0) {
            const y = rowY(3);
            els.push(
              rowName('fl', 3, 'free edge', freeLab),
              <g key="fr" opacity={freeLab}>
                <line x1={right + r + 8} x2={right + r + 34} y1={y} y2={y} stroke={C.fgMuted} strokeWidth={2} />
                <text x={right + r + 42} y={y + 9} {...NAME}>
                  free edge
                </text>
              </g>,
            );
          }
          // the first short rod: its bracket stays into cue 2, where it gets its length
          els.push(bracket(0, shortIn[0] * (1 - tail), 0));
          const shortName = rodLab * out1;
          if (shortName > 0) {
            const s = SHORT[0];
            els.push(
              <text key="sr" x={bracketX(1) + 12} y={(rowY(s.r0) + rowY(s.r1)) / 2 + 9} opacity={shortName} {...NAME}>
                short rod
              </text>,
            );
          }
          if (pNote > 0) {
            const x = (left + right) / 2;
            const y = rowY(N1) + 64;
            els.push(
              <g key="pn" opacity={pNote}>
                <text x={x} y={y} textAnchor="middle" {...NAME}>
                  The <tspan fill={C.p}>P</tspan>’s are not drawn.
                </text>
                <text x={x} y={y + 30} textAnchor="middle" {...SUB}>
                  Between the pairs of H’s, they stick out in front of the cube.
                </text>
              </g>,
            );
          }
          // cue 2: every short rod and its length; the left ones then give way to the strip names
          SHORT.forEach((s, i) => {
            const o = s.side === 0 ? leftOut : 1 - tail;
            // its own key: the bracket's path is already in the list under b0 (cue 1)
            if (i === 0) els.push(bracket(0, 0, numIn[0] * o, 'b0-num'));
            else els.push(bracket(i, shortIn[i] * o, numIn[i] * o));
          });
          // the strips' names, left of the face: the leader runs along the box's top edge into it;
          // in the tail it pulls back clear of the beads, then the name moves to the middle row
          [0, 1].forEach((s) => {
            const o = strips[s];
            if (o <= 0) return;
            const [x0, y0] = stripBox(project, s, 0.5);
            const rows = M.strips[s].rows;
            const y = y0 + (rowY(rows[1]) - y0) * slide;
            const tx = project([-0.5, 0, 0])[0] - 30;
            const to = x0 + STRIP_RX + (left - r - 8 - x0 - STRIP_RX) * retract;
            els.push(
              <g key={`s${s}`} opacity={o}>
                <line x1={tx + 8} x2={to} y1={y} y2={y} stroke={C.fgMuted} strokeWidth={2} strokeLinecap="round" />
                <text x={tx} y={y + 9} textAnchor="end" {...NAME}>
                  {`strip ${s + 1}`}
                </text>
                {retract < 1 && (
                  <text x={tx} y={y + 37} textAnchor="end" opacity={1 - retract} {...SUB}>
                    {`${rows.length} rows × ${M.n - 2} nodes`}
                  </text>
                )}
              </g>,
            );
          });
          return <g fontFamily={FONT.sans}>{els}</g>;
        }}
      </Scene3D>
    </SceneFrame>
  );
}
