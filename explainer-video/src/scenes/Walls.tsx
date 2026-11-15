/**
 * Scene "walls": the camera turns from the finished frame to the open front face. The walls are
 * laid in string order (rod up the right free edge, wall right to left, rod down the left free
 * edge, wall back, rod up; then the second period; then the spaced rod).
 *
 * The frame stays in full colour; what lies behind the front face goes (see-through) in the first
 * frames of the turn, before its faces come near edge-on. The free edges keep their band from the
 * "frame" scene (a pale accent band just behind the edge's nodes), under the rods laid on them.
 * Every wall bead fades in at its node by opacity (8 frames, one soft tip in string order), its
 * stick with it, and the empty node under it fades out as it comes. Where the string leaves the
 * face (two consecutive H's of the walls string that are not neighbours: it runs through P's in
 * front of the face), a dashed arc shows the jump as the tip makes it. Labels name the free edges,
 * rod 1 (the cube's top and bottom edge rows), the walls and one short rod, and say that the P's
 * are not drawn.
 * Cue 2: every short rod is marked with a bracket and its length, in string order; then, on the
 * right, one bracket over each period's three rods: 2 + 1 + 2 = 5, as long as the rod on the left,
 * so the walls have no slack. Then the strips between the walls light up as outlined boxes and are
 * named on the left; both sides' lengths stay to the pause.
 * The tail, after the pause: the brackets, the bands and the strips' sub-lines go, and the strip
 * names move to their middle row, so the last frame is the first frame of "padding".
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, mixShot, projector, R_RES, type Project } from '../three/Scene3D';
import { FRAME_SHOT, FACE_SHOT, CUBE_SHELL, freeEdgeBands } from '../three/cube';
import { ramp, sec, clamp01 } from '../lib/anim';
import { C, FONT } from '../theme/theme';
import * as M from '../model/toy';
import type { SceneTime } from '../script';
import { newDraw, drawFrame, addHoles, faceOutline, stripBox, WALLS } from './lib/face';

const N1 = M.n - 1;
/** global walls progress at which period 1, then period 2 is done (by H count); the spaced rod is last */
const H_TOTAL = WALLS.reduce((a, w) => a + w.letters.filter((l) => l.h).length, 0);
const [P1, P2] = (() => {
  const hs = WALLS.map((w) => w.letters.filter((l) => l.h).length);
  const sum = (k: number) => hs.slice(0, k).reduce((a, b) => a + b, 0) / H_TOTAL;
  return [sum(5), sum(10)];
})();

/** row (0 = top) of a front-face node */
const rowOf = (p: M.V3) => N1 - p[1];

/**
 * The walls string: every letter of every wall piece, in string order, with its H number (k: the
 * k-th H of the string; its bead starts to come in when the walls progress reaches k / H_TOTAL).
 */
const STRING: { pos: M.V3; h: boolean; k: number }[] = (() => {
  let k = 0;
  return WALLS.flatMap((w) => w.letters.map((l) => ({ pos: l.pos, h: l.h, k: l.h ? k++ : -1 })));
})();
const HS = STRING.filter((l) => l.h);
/** per wall piece, the H number of its last H (its name comes in as that bead does) */
const LAST_H: number[] = (() => {
  let k = -1;
  return WALLS.map((w) => (k += w.letters.filter((l) => l.h).length));
})();
const dist = (a: M.V3, b: M.V3) => Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]) + Math.abs(a[2] - b[2]);
/** where the string leaves the face: consecutive H's that are not neighbours (k: the H it lands on) */
const JUMPS = HS.slice(1)
  .map((l, i) => ({ a: HS[i].pos, b: l.pos, k: l.k }))
  .filter((j) => dist(j.a, j.b) > 1);
if (JUMPS.some((j) => j.a[0] !== N1 || j.b[0] !== N1)) throw new Error('walls: a jump off the right free edge');

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
/** per period, the rows its right-edge rods fill together (as many as its rod on the left) */
const RIGHT_SUM = M.periods.map((p) => ({ r0: p.top, r1: p.bottom }));
for (const r of RIGHT_SUM) {
  const n = SHORT.filter((s) => s.side === 1 && s.r0 >= r.r0 && s.r1 <= r.r1).reduce((a, s) => a + s.r1 - s.r0 + 1, 0);
  if (n !== r.r1 - r.r0 + 1) throw new Error('walls: the right rods of a period do not add up');
}

/** the shared label styles */
const NAME = { fontFamily: FONT.sans, fontSize: 26, fontWeight: 600, fill: C.fg } as const;
const SUB = { fontFamily: FONT.sans, fontSize: 22, fontWeight: 500, fill: C.fgMuted } as const;

/** under the 3D picture (the beads cover them): the strips' boxes, outline only, as "padding" draws them */
function Under({ project, strips }: { project: Project; strips: number[] }) {
  return (
    <svg width={1920} height={1080} viewBox="0 0 1920 1080" style={{ position: 'absolute', inset: 0 }}>
      {strips.map((o, s) => {
        if (o <= 0) return null;
        const [x0, y0, x1, y1] = stripBox(project, s, 0.5);
        return <rect key={s} x={x0} y={y0} width={x1 - x0} height={y1 - y0} rx={STRIP_RX} fill="none" stroke={C.fgMuted} strokeWidth={2.5} opacity={o} />;
      })}
    </svg>
  );
}
const STRIP_RX = 12;
const smooth = (t: number) => t * t * (3 - 2 * t);

export default function WallsScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1] = scene.cueTimes;
  const turn = ramp(f, 4, sec(2.0));
  const shot = mixShot(FRAME_SHOT(1), FACE_SHOT, turn);
  // what lies behind the front face goes early in the turn (16 frames), long before its faces are
  // edge-on, so they never smear
  const backFade = ramp(f, 4, 16);

  // period 1 slowly (so the order can be followed), period 2 faster, then the spaced rod's two H's
  const t1 = c0.from + sec(1.9);
  const d1 = sec(4.2);
  const d2 = sec(2.2);
  const d3 = sec(0.8);
  /** the frame at which the walls progress (by H count, 0..1) reaches x */
  const timeAt = (x: number) => (x < P1 ? t1 + (d1 * x) / P1 : x < P2 ? t1 + d1 + (d2 * (x - P1)) / (P2 - P1) : t1 + d1 + d2 + (d3 * (x - P2)) / (1 - P2));
  /** H number k: how far its bead is in (8 frames, eased) */
  const hIn = (k: number) => smooth(clamp01((f - timeAt(k / H_TOTAL)) / 8));

  const d = newDraw();
  // the frame as the "frame" scene leaves it, in full colour (what lies behind the front face is
  // split off below and fades as one picture)
  drawFrame(d);
  // without the core's filler block, as the "frame" scene leaves it (the shell hides the faces
  // turned away)
  d.solids.length = 0;
  // the walls, one soft tip in string order: H's only (face-on the P's would sit in front of them),
  // joined where two H's follow each other in the string; a stick never stronger than its beads
  STRING.forEach((l, i) => {
    if (!l.h) return;
    const o = hIn(l.k);
    if (o > 0.001) d.beads.push({ pos: l.pos, color: C.h, opacity: o < 0.999 ? o : undefined });
    const n = STRING[i + 1];
    if (n?.h && dist(l.pos, n.pos) === 1) {
      const m = Math.min(o, hIn(n.k));
      if (m > 0.001) d.sticks.push({ a: l.pos, b: n.pos, color: C.backbone, fade: m < 0.999 ? 1 - m : undefined });
    }
  });
  d.lines.push(...faceOutline(0.6, backFade, C.fgSubtle, true));

  // cue 2: the strips light up, after the short rods are marked
  const stripAt = (s: number) => c1.from + sec(4.0 + s * 0.5);
  const strips = [0, 1].map((s) => ramp(f, stripAt(s), sec(0.7)));
  // the tail, after the pause (c1.to - 10): brackets, bands and sub-lines go; the strip names'
  // leaders pull back out of the boxes (in the gap above the strip's first row), then the names
  // move to the strips' middle rows and in to the face, where "padding" has them
  // (all done by c1.to + 14, so the last 6 frames hold the first frame of "padding")
  const tail = ramp(f, c1.to - 6, 12);
  const retract = ramp(f, c1.to - 10, 12);
  const slide = ramp(f, c1.to + 2, 12);
  // the empty nodes, as "frame" leaves them; each fades out as the wall bead laid on it comes in
  addHoles(d, { opacity: 1, free: 0 });
  // the free edges' bands, as "frame" leaves them
  d.lines.push(...freeEdgeBands(1 - tail));

  /** "wall" labels: one per wall, once it is laid */
  const wallIdx = WALLS.map((w, i) => (w.kind === 'wall' ? i : -1)).filter((i) => i >= 0);
  // cue 1's labels leave together at cue 2 (8 frames), before anything new comes in
  const out1 = 1 - ramp(f, c1.from, 8);
  const freeLab = ramp(f, sec(2.2), sec(0.6)) * out1;
  const edgeLab = ramp(f, sec(2.8), sec(0.6)) * out1;
  const rodLab = ramp(f, t1 + sec(1.2), sec(0.5));
  const pNote = ramp(f, t1 + d1 - sec(1.0), sec(0.6)) * out1;
  // the jumps: each arc comes in as the tip makes the jump (with the bead it lands on)
  const jumpIn = JUMPS.map((j) => ramp(f, timeAt(j.k / H_TOTAL) - 2, 10) * out1);
  // cue 2: the rods' brackets come in string order (the first one is cue 1's "short rod" bracket),
  // then each period's sum on the right
  const shortIn = SHORT.map((_, i) => (i === 0 ? rodLab : ramp(f, c1.from + sec(0.5) + (i - 1) * 6, 8)));
  const numIn = SHORT.map((_, i) => ramp(f, c1.from + sec(0.5) + Math.max(0, i - 1) * 6 + (i === 0 ? -sec(0.2) : 0), 8));
  const sumIn = RIGHT_SUM.map((_, p) => ramp(f, c1.from + sec(2.4 + 0.3 * p), 10) * (1 - tail));

  const project = projector(shot);
  // the cube behind the front face is its own picture, under the face's: it fades out as a whole
  // (its sticks with their beads), never bead by bead, which let half-faded beads show each other.
  // The front picture keeps the face's beads, the empty nodes' dots (just behind it) and the lines.
  const isFront = (p: M.V3) => p[2] > -0.5;
  const frontStick = (s: { a: M.V3; b: M.V3 }) => isFront(s.a) && isFront(s.b);
  const back = { beads: d.beads.filter((b) => !isFront(b.pos)), sticks: d.sticks.filter((s) => !frontStick(s)) };
  const front = { beads: d.beads.filter((b) => isFront(b.pos)), sticks: d.sticks.filter(frontStick) };

  return (
    <SceneFrame scene={scene}>
      <Under project={project} strips={strips} />
      {backFade < 1 && (
        <div style={{ position: 'absolute', inset: 0, opacity: 1 - backFade }}>
          <Scene3D shot={shot} beads={back.beads} sticks={back.sticks} shell={CUBE_SHELL} />
        </div>
      )}
      <Scene3D shot={shot} beads={front.beads} sticks={front.sticks} lines={d.lines} panels={d.panels} shell={CUBE_SHELL}>
        {(project) => {
          const u = project([1, 0, 0])[0] - project([0, 0, 0])[0];
          const r = R_RES * u;
          const left = project([0, 0, 0])[0];
          const right = project([N1, 0, 0])[0];
          const rowY = (row: number) => project([0, N1 - row, 0])[1];
          /** a row's name beside the face, with a short leader to the row's end */
          const rowName = (key: string, row: number, text: string, opacity: number, side: 0 | 1 = 0) =>
            opacity > 0 && (
              <g key={key} opacity={opacity}>
                {side === 0 ? (
                  <>
                    <line x1={left - r - 34} x2={left - r - 8} y1={rowY(row)} y2={rowY(row)} stroke={C.fgMuted} strokeWidth={2} />
                    <text x={left - r - 42} y={rowY(row) + 9} textAnchor="end" {...NAME}>
                      {text}
                    </text>
                  </>
                ) : (
                  <>
                    <line x1={right + r + 8} x2={right + r + 34} y1={rowY(row)} y2={rowY(row)} stroke={C.fgMuted} strokeWidth={2} />
                    <text x={right + r + 42} y={rowY(row) + 9} {...NAME}>
                      {text}
                    </text>
                  </>
                )}
              </g>
            );
          /** a bracket along rows r0..r1 at x, opening towards the face */
          const bracketPath = (x: number, r0: number, r1: number, dir: number) => {
            const y0 = rowY(r0) - 0.38 * u;
            const y1 = rowY(r1) + 0.38 * u;
            const tick = -dir * 7;
            return `M ${x + tick} ${y0} H ${x} V ${y1} H ${x + tick}`;
          };
          /** a bracket along a short rod, just outside the face's outline, and (`num`) its length */
          const bracketX = (side: 0 | 1) => (side === 0 ? left - 0.5 * u - 16 : right + 0.5 * u + 16);
          const bracket = (i: number, o: number, num: number, key = `b${i}`) => {
            const s = SHORT[i];
            if (o <= 0 && num <= 0) return null;
            const dir = s.side === 0 ? -1 : 1;
            const x = bracketX(s.side);
            const y0 = rowY(s.r0) - 0.38 * u;
            const y1 = rowY(s.r1) + 0.38 * u;
            return (
              <g key={key}>
                {o > 0 && <path d={bracketPath(x, s.r0, s.r1, dir)} fill="none" stroke={C.fgMuted} strokeWidth={2} opacity={o} />}
                {num > 0 && (
                  <text x={x + dir * 12} y={(y0 + y1) / 2 + 9} textAnchor={s.side === 0 ? 'end' : 'start'} opacity={num} {...NAME}>
                    {s.r1 - s.r0 + 1}
                  </text>
                )}
              </g>
            );
          };
          // the strips' names, left of the face: level with the box's top edge, the leader running
          // into its top-left corner (over the left rod's bracket); in the tail the leader pulls
          // back clear of the beads, then the name moves to the middle row and in to the face
          const nameX = (s: number) => {
            const near = project([-0.5, 0, 0])[0] - 30;
            const far = bracketX(0) - 50;
            return far + (near - far) * slide;
          };
          const nameY = (s: number) => {
            const [, y0] = stripBox(project, s, 0.5);
            return y0 + (rowY(M.strips[s].rows[1]) - y0) * slide;
          };

          const els: React.ReactNode[] = [];
          // cue 1: walls, rod 1, the free edges, a short rod, the P's
          wallIdx.forEach((i) => {
            const w = WALLS[i];
            const o = ramp(f, timeAt(LAST_H[i] / H_TOTAL) - 2, 8) * out1;
            els.push(rowName(`w${i}`, rowOf(w.letters.find((l) => l.h)!.pos), 'wall', o));
          });
          els.push(rowName('e0', 0, 'rod 1', edgeLab), rowName('e1', N1, 'rod 1', edgeLab));
          // the free edges, named where no jump or bracket is in the way
          els.push(rowName('fl', 3, 'free edge', freeLab), rowName('fr', 9, 'free edge', freeLab, 1));
          // the jumps: a dashed arc right of the face, from the H the string leaves to the H it
          // comes back to, with an arrowhead there
          JUMPS.forEach((j, i) => {
            const o = jumpIn[i];
            if (o <= 0) return;
            const x0 = right + r + 6;
            const ya = rowY(rowOf(j.a));
            const yb = rowY(rowOf(j.b));
            const k = 30 + 10 * Math.abs(rowOf(j.b) - rowOf(j.a));
            els.push(
              <g key={`j${i}`} opacity={0.85 * o} fill="none" stroke={C.p} strokeWidth={2.5} strokeLinecap="round">
                <path d={`M ${x0} ${ya} C ${x0 + k} ${ya}, ${x0 + k} ${yb}, ${x0} ${yb}`} strokeDasharray="7 7" />
                <path d={`M ${x0 + 11} ${yb - 7} L ${x0 + 1} ${yb} L ${x0 + 11} ${yb + 7}`} strokeLinejoin="round" />
              </g>,
            );
          });
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
                  the <tspan fill={C.p}>P</tspan>’s are not drawn
                </text>
                <text x={x} y={y + 30} textAnchor="middle" {...SUB}>
                  they stick out in front of the cube, between pairs of H’s and along each dashed jump
                </text>
              </g>,
            );
          }
          // cue 2: every short rod and its length, to the pause
          SHORT.forEach((_, i) => {
            const o = 1 - tail;
            // its own key: the bracket's path is already in the list under b0 (cue 1)
            if (i === 0) els.push(bracket(0, 0, numIn[0] * o, 'b0-num'));
            else els.push(bracket(i, shortIn[i] * o, numIn[i] * o));
          });
          // each period's right-edge rods together: as long as its rod on the left
          RIGHT_SUM.forEach((p, i) => {
            const o = sumIn[i];
            if (o <= 0) return;
            const x = bracketX(1) + 44;
            const ym = (rowY(p.r0) + rowY(p.r1)) / 2;
            els.push(
              <g key={`sum${i}`} opacity={o}>
                <path d={bracketPath(x, p.r0, p.r1, 1)} fill="none" stroke={C.fgMuted} strokeWidth={2} />
                <text x={x + 12} y={ym + 9} {...NAME}>
                  {p.r1 - p.r0 + 1}
                </text>
              </g>,
            );
          });
          [0, 1].forEach((s) => {
            const o = strips[s];
            if (o <= 0) return;
            const [x0] = stripBox(project, s, 0.5);
            const rows = M.strips[s].rows;
            const y = nameY(s);
            const tx = nameX(s);
            const to = x0 + STRIP_RX + (left - r - 8 - x0 - STRIP_RX) * retract;
            // where the leader passes over the left rod's bracket, the bracket gives way (a short
            // gap in the background colour, coming in with the name)
            const bx = bracketX(0);
            els.push(
              <g key={`s${s}`} opacity={o}>
                {tx + 8 < bx - 4 && <line x1={bx} x2={bx} y1={y - 8} y2={y + 8} stroke={C.bg} strokeWidth={6} />}
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
