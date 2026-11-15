/**
 * Scene "frame": the pieces of the frame each have one place. A parts list on the left names the
 * pieces, in string order, and ticks each off as it is laid: rod 1 round nine edges and all eight
 * corners, ribbon 1 on the top face, rod 2 on a tenth edge, ribbons 2–5 on four more faces, the
 * core inside. What is left is the front face with its two free edges (in the accent colour, as
 * the caption colours them).
 *
 * One string: every piece is laid with one growing tip, one piece after another, in string order,
 * each bead coming in at full size. The free edges have one look from here to the walls scene: a
 * soft accent band along the edge's nodes, corner to corner, drawn under the beads. Rod H's are
 * never joined by sticks (a rod is PHP PHP …, its H's are not neighbours in the string); P's are
 * not drawn from here on, and a note says so.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, FADE, quiet, projector, R_RES, type Bead, type Stick, type Project } from '../three/Scene3D';
import { framePieces, drawPiece, cubeOutline, holeBeads, freeEdgeLine, FREE_BAND, FRONT_NODES, FRAME_SHOT, HOLE_COLOR, CUBE_SHELL, type PieceDef } from '../three/cube';
import { ramp, sec, easeOut, clamp01 } from '../lib/anim';
import { C, FONT } from '../theme/theme';
import * as M from '../model/toy';
import type { SceneTime } from '../script';

const pieces = framePieces();
const byId = Object.fromEntries(pieces.map((p) => [p.id, p]));
/** the five face ribbons in string order (the model's order): top, then left, back, right, bottom */
const FACE_ORDER = M.FACES.map((f) => `face-${f.name}`);

// ------------------------------------------------------------------ the parts list

type Glyph = 'rod' | 'ribbon' | 'core' | 'open';
/** a little run of beads in the game's colours: rod PHP PHP…, ribbon PHHP PHHP…, core HHH… */
function Icon({ x, y, kind, opacity }: { x: number; y: number; kind: Glyph; opacity: number }) {
  const seq = kind === 'rod' ? 'PHPPHPPHP' : kind === 'ribbon' ? 'PHHPPHHP' : kind === 'core' ? 'HHHHHHHH' : 'oooooooo';
  const step = 19;
  const r = 7;
  const xs = [...seq].map((_, i) => x + i * step);
  return (
    <g opacity={opacity}>
      {kind !== 'open' && <line x1={xs[0]} x2={xs[xs.length - 1]} y1={y} y2={y} stroke={C.backbone} strokeWidth={3} />}
      {[...seq].map((ch, i) =>
        ch === 'H' ? (
          <circle key={i} cx={xs[i]} cy={y} r={r} fill={C.h} />
        ) : ch === 'P' ? (
          // a P as everywhere else in the video: white, with a blue ring
          <circle key={i} cx={xs[i]} cy={y} r={r - 1} fill={C.bgElev} stroke={C.p} strokeWidth={2.6} />
        ) : (
          <circle key={i} cx={xs[i]} cy={y} r={3.2} fill={HOLE_COLOR} />
        ),
      )}
    </g>
  );
}

interface Row {
  kind: Glyph;
  name: string;
  where: string;
  /** 0 = not yet shown … */
  appear: number;
  /** being laid now (0..1 highlight) */
  active: number;
  /** laid (0..1 tick) */
  done: number;
  /** 0..1, the sub-line saying where the piece goes (it comes in as the piece goes on) */
  sub: number;
  accent?: boolean;
}

const LIST = { x: 96, y0: 282, dy: 86 };

function PartsList({ rows }: { rows: Row[] }) {
  const { x, y0, dy } = LIST;
  return (
    <g fontFamily={FONT.sans}>
      {rows.map((r, i) => {
        if (r.appear <= 0) return null;
        // the front face is not a piece: set apart below a rule
        const apart = r.accent ? 30 : 0;
        const y = y0 + i * dy + apart + (1 - easeOut(r.appear)) * 14;
        const ink = r.accent ? C.accent : r.done > 0.5 || r.active > 0.5 ? C.fg : C.fgMuted;
        return (
          <g key={r.name} opacity={r.appear}>
            {r.accent && <line x1={x - 22} x2={x + 470} y1={y - 56} y2={y - 56} stroke={C.rule} strokeWidth={1.5} />}
            <rect x={x - 22} y={y - 32} width={6} height={64} rx={3} fill={r.accent ? C.accent : C.h} opacity={r.accent ? 1 : r.active * 0.9} />
            <text x={x} y={y - 6} fontSize={26} fontWeight={600} fill={ink}>
              {r.name}
            </text>
            <text x={x} y={y + 24} fontSize={22} fontWeight={500} fill={r.accent ? C.accent : C.fgMuted} opacity={r.sub}>
              {r.where}
            </text>
            {r.kind !== 'open' && <Icon x={x + 250} y={y - 2} kind={r.kind} opacity={1} />}
            {r.done > 0 && (
              <path
                d={`M${x + 440},${y - 2} l9,10 l18,-22`}
                opacity={Math.min(1, r.done * 4)}
                fill="none"
                stroke={C.ok}
                strokeWidth={4.5}
                strokeLinecap="round"
                strokeLinejoin="round"
                strokeDasharray={60}
                strokeDashoffset={60 * (1 - r.done)}
              />
            )}
          </g>
        );
      })}
    </g>
  );
}

// ------------------------------------------------------------------ labels on the cube

type V3 = [number, number, number];

/**
 * "rod 2", in the empty front face, left of rod 2's lower half, with a short leader to its fifth
 * bead. Rod 2 lies on the back-left edge, seen through the open front face; its upper half is
 * behind rod 1's front-top edge, so the label stays below that.
 */
function Rod2Label({ project, opacity }: { project: Project; opacity: number }) {
  if (opacity <= 0) return null;
  const at: V3 = [0, 4, -(M.n - 1)];
  const [x, y] = project(at);
  const r = Math.abs(project([0, 4 + R_RES, -(M.n - 1)])[1] - y);
  return (
    <g opacity={opacity} fontFamily={FONT.sans}>
      <line x1={x - r - 6} y1={y} x2={x - r - 34} y2={y} stroke={C.fgMuted} strokeWidth={1.6} />
      <text x={x - r - 42} y={y + 9} textAnchor="end" fontSize={26} fontWeight={600} fill={C.fg}>
        rod 2
      </text>
    </g>
  );
}

/**
 * Drawn under the 3D picture: the front face's tint (while the cube is still empty) and its two
 * free edges as bands (see `freeEdgeLine`). Beads always cover them.
 */
function UnderFace({ project, tint, band }: { project: Project; tint: number; band: number }) {
  if (tint <= 0 && band <= 0) return null;
  const lo = -0.5;
  const hi = M.n - 0.5;
  const quad = ([[lo, lo], [hi, lo], [hi, hi], [lo, hi]] as const).map(([x, y]) => project([x, y, 0.5]).join(',')).join(' ');
  return (
    <svg width={1920} height={1080} viewBox="0 0 1920 1080" style={{ position: 'absolute', inset: 0 }}>
      {tint > 0 && <polygon points={quad} fill={C.accent} opacity={0.07 * tint} />}
      {band > 0 &&
        ([0, 1] as const).map((side) => {
          const l = freeEdgeLine(project, side);
          return <line key={side} x1={l.x1} y1={l.y1} x2={l.x2} y2={l.y2} stroke={C.accent} strokeOpacity={FREE_BAND.opacity * band} strokeWidth={l.w} />;
        })}
    </svg>
  );
}

// ------------------------------------------------------------------ the scene

export default function FrameScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1, c2] = scene.cueTimes;
  const shot = FRAME_SHOT(f / (scene.duration - 1));
  const project = projector(shot);
  const beads: Bead[] = [];
  const sticks: Stick[] = [];

  // [start, duration] of each piece, in frames, in string order, one growing tip at a time:
  // rod 1, ribbon 1 (top face) and rod 2 with the rods' cue; ribbons 2–5 and the core with the next
  const later = FACE_ORDER.slice(1).map((_, i) => [c2.from + sec(0.4 + i * 1.15), sec(1.05)]);
  const T = {
    corner: [c1.from + sec(0.5), sec(4.3)],
    top: [c1.from + sec(4.95), sec(1.0)],
    tenth: [c1.from + sec(6.1), sec(1.4)],
    faces: later,
    core: [c2.from + sec(5.1), sec(1.9)],
  };
  // linear progress: one tip moving at an even pace
  const R = ([s0, d]: number[]) => clamp01((f - s0) / d);
  const end = ([s0, d]: number[]) => s0 + d;
  const coreEnd = end(T.core);
  const tenthEnd = end(T.tenth);
  const pieceOrder: [PieceDef, number[], 'rod' | 'face'][] = [
    [byId.corner, T.corner, 'rod'],
    [byId[FACE_ORDER[0]], T.top, 'face'],
    [byId.tenth, T.tenth, 'rod'],
    ...FACE_ORDER.slice(1).map((id, i) => [byId[id], T.faces[i], 'face'] as [PieceDef, number[], 'face']),
  ];
  // the faces turned away are hidden once the core is in front of them
  const shellAmount = ramp(f, coreEnd - sec(0.4), sec(0.6));
  // then the front face becomes the subject: the rods and faces step back, the core goes, and the
  // open face's empty nodes and its two free edges come (back) in, as the walls scene starts
  const front = ramp(f, c2.from + sec(7.3), sec(0.6));
  const ctx = FADE.context * front;
  const holesIn = ramp(f, c2.from + sec(8.0), sec(0.6));

  // the front face, tinted while the cube is empty, and its free edges: shown in the first cue;
  // the free edges stay while the rods go on, step aside while the faces and the core fill what
  // lies behind the open face, and come back with the empty nodes
  const shown = ramp(f, c0.from + sec(2.6), sec(0.8));
  const tint = shown * (1 - ramp(f, c1.from, 14));
  const band = shown * (1 - ramp(f, c2.from, 9)) + holesIn;
  // the empty cube's wireframe: its inner edges give way before rod 1 reaches any of them
  const inner = 1 - ramp(f, c1.from, 14);

  // rod 2 swells once when it is in, and is named; the name goes as the next cue starts
  const rodLabel = ramp(f, tenthEnd + 4, 14) * (1 - ramp(f, c2.from, 8, clamp01));
  const pulse = 1 + 0.16 * Math.sin(Math.PI * clamp01((f - tenthEnd) / 20));
  // and while rod 2 is the subject, the far side of the cube (where it lies) is not faded by depth
  const focus = ramp(f, T.tenth[0] - 6, 15) * (1 - ramp(f, c2.from, 15));
  const cue = { amount: 0.4 * (1 - 0.7 * focus) };
  // the P's are not drawn from here on: said once, as rod 1 goes on
  const pNote = ramp(f, T.corner[0] + sec(1.2), sec(0.5)) * (1 - ramp(f, c2.from + sec(7.3), sec(0.5)));

  for (const [piece, span, kind] of pieceOrder) {
    const got: Bead[] = [];
    drawPiece(piece, kind === 'rod' ? { progress: R(span), ps: 0, chain: 0, appear: 'fade' } : { progress: R(span), ps: 0, dominoes: true, appear: 'fade' }, got, sticks);
    beads.push(...(piece === byId.tenth ? got.map((b) => ({ ...b, scale: (b.scale ?? 1) * pulse })) : got));
  }
  const laid: [Bead[], Stick[]] = [quiet(beads.splice(0), ctx), quiet(sticks.splice(0), ctx)];
  beads.push(...laid[0]);
  sticks.push(...laid[1]);
  // the core: a run of H's, joined bead to bead, laid back to front; it fades into the background
  // as the front face becomes the subject, and is gone before the empty nodes come in
  if (front < 1) drawPiece(byId.core, { progress: R(T.core), ps: 0, appear: 'fill', fade: front }, beads, sticks);

  // the open front face: its empty nodes, the free edges' nodes included
  const open = FRONT_NODES.filter(([, y]) => y > 0 && y < M.n - 1);
  beads.push(...holeBeads(open, 0.9 * holesIn));
  // the empty cube's wireframe, then only its contour
  const lines: Stick[] = [...cubeOutline(0.6, C.fgSubtle, 0.5, inner)];

  const row = (kind: Glyph, name: string, where: string): Row => ({ kind, name, where, appear: 0, active: 0, done: 0, sub: 0 });
  const rows: Row[] = [
    row('rod', 'rod 1', '9 edges, 8 corners'),
    row('ribbon', 'ribbon 1', 'the top face'),
    row('rod', 'rod 2', '1 more edge'),
    row('ribbon', 'ribbons 2–5', '4 more faces'),
    row('core', 'core', 'the inside'),
    { ...row('open', 'front face', 'and its 2 free edges: kept for the puzzle'), accent: true },
  ];
  const listIn = (i: number) => ramp(f, c0.from + sec(0.6 + i * 0.4), sec(0.5));
  const spans: [number, number][] = [
    [T.corner[0], end(T.corner)],
    [T.top[0], end(T.top)],
    [T.tenth[0], tenthEnd],
    [T.faces[0][0], end(T.faces[T.faces.length - 1])],
    [T.core[0], coreEnd],
  ];
  spans.forEach(([from, to], i) => {
    rows[i].appear = listIn(i);
    // where a piece goes is said as it goes there (the caption explains it then)
    rows[i].sub = ramp(f, from - 8, 12);
    rows[i].active = ramp(f, from, 6) * (1 - ramp(f, to, 6));
    rows[i].done = ramp(f, to, 10);
  });
  rows[5].appear = shown;
  rows[5].sub = shown;
  const listBottom = LIST.y0 + 5 * LIST.dy + 30;
  // the tail, after the pause (c2.to - 10): the parts list goes, so the last frame is the first
  // frame of "walls"
  const listOut = 1 - ramp(f, c2.to - 6, 12);

  return (
    <SceneFrame scene={scene}>
      <UnderFace project={project} tint={tint} band={band} />
      <Scene3D shot={shot} beads={beads} sticks={sticks} lines={lines} shell={{ ...CUBE_SHELL, amount: shellAmount }} depthCue={cue}>
        {(proj) => (
          <>
            {listOut > 0 && (
              <g opacity={listOut}>
                <PartsList rows={rows} />
              </g>
            )}
            {pNote > 0 && (
              <text x={LIST.x - 22} y={listBottom + 84} fontFamily={FONT.sans} fontSize={22} fontWeight={500} fill={C.fgMuted} opacity={pNote}>
                <tspan x={LIST.x - 22}>From here on, the cube shows only its H’s.</tspan>
                <tspan x={LIST.x - 22} dy={30}>
                  The <tspan fill={C.p}>P</tspan>’s all sit outside it, not drawn.
                </tspan>
              </text>
            )}
            <Rod2Label project={proj} opacity={rodLabel} />
          </>
        )}
      </Scene3D>
    </SceneFrame>
  );
}
