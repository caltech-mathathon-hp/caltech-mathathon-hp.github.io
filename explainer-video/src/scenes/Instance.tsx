/**
 * Scene "instance": the example puzzle (items 6, 2, 8, 4; two bins of 10), then the size of its
 * cube.
 * Cue 1: the bins, then the four items fade in one after the other, in the puzzle's own look.
 * Cue 2: the puzzle moves left and shrinks, in one eased move. The recipe's cube of side 80 comes
 * in as a thin grey wireframe (as in step 40), with "side 80". Our cube of side 12 comes in, in its
 * corner, as beads from its first frame: the frame and the walls, every node an H, its front face
 * empty where the two strips go (small grey dots: steps 33–35 fill them). It fades in as one
 * picture, at full size and never through a pale block. The recipe's cube then fades out, the
 * camera moves in to ours, and the two strips get a thin outline. Notes under the puzzle give the recipe's count and ours. "side 12"
 * stays under the small cube's front edge all through the move. No depth cue: the whole cube is at
 * one brightness, since here it stands for its size, not for its parts.
 *
 * The toy badge is not shown here (the notes say the same thing); it comes in with the next scene.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, GAME_DIR, mixShot, yaw, projector, type Bead, type Stick, type Shot } from '../three/Scene3D';
import { framePieces, wallPieces, itemPieces, drawPiece, holeBeads, innerBlock, CUBE_SHELL } from '../three/cube';
import { ramp, sec, lerp, clamp01 } from '../lib/anim';
import { C, FONT, W, H } from '../theme/theme';
import * as M from '../model/toy';
import type { V3 } from '../model/toy';
import type { SceneTime } from '../script';
import { Puzzle, PUZZLE_BIG, PUZZLE_SMALL, mixAt, cubeBox, unitPxAt, Label } from './lib/planPipeline';

const BIG = M.REAL.n; // 80
const TOY = M.n; // 12
const N1 = TOY - 1;
const OFFSET: [number, number] = [300, -70];

/** a gentle ease for moves (top speed 1.57 times the mean) */
const sine = (t: number) => (1 - Math.cos(Math.PI * clamp01(t))) / 2;

/**
 * Our cube, drawn once: the frame (rods and face ribbons; the core is closed off by a block in the
 * background colour) and the walls of the front face, H's only, at full strength. The nodes the
 * paddings and items will fill are left empty: small grey dots.
 */
const CUBE = (() => {
  const beads: Bead[] = [];
  const sticks: Stick[] = [];
  for (const p of framePieces().filter((p) => p.kind !== 'core')) drawPiece(p, { progress: 1, ps: 0, dominoes: p.kind === 'face', appear: 'opacity' }, beads, sticks);
  for (const p of wallPieces()) drawPiece(p, { progress: 1, ps: 0, dominoes: true, appear: 'opacity' }, beads, sticks);
  const empty: V3[] = itemPieces().flatMap((p) => p.letters.filter((l) => l.h).map((l) => l.pos));
  beads.push(...holeBeads(empty, 0.9));
  return { beads, sticks, empty };
})();

/** each strip's empty nodes, as a rectangle on the front face half a step outside them (lattice units) */
const STRIP_RECTS = M.strips.map((s) => {
  const ys = s.rows.map((r) => N1 - r);
  const cells = CUBE.empty.filter((p) => ys.includes(p[1]));
  const xs = cells.map((p) => p[0]);
  const yy = cells.map((p) => p[1]);
  const m = 0.5;
  return { x0: Math.min(...xs) - m, x1: Math.max(...xs) + m, y0: Math.min(...yy) - m, y1: Math.max(...yy) + m };
});

/** the notes under the puzzle in cue 2: the recipe's count, then ours and what it changes */
const NOTE_X = 182;
const NOTE_Y = 610;
function Note({ x, y, opacity, head, sub }: { x: number; y: number; opacity: number; head: string; sub?: string }) {
  if (opacity <= 0) return null;
  return (
    <g opacity={opacity} fontFamily={FONT.sans}>
      <text x={x} y={y} fontSize={26} fontWeight={600} fill={C.fg}>
        {head}
      </text>
      {sub && (
        <text x={x} y={y + 34} fontSize={22} fontWeight={500} fill={C.fgMuted}>
          {sub}
        </text>
      )}
    </g>
  );
}

export default function InstanceScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1] = scene.cueTimes;

  // cue 1: the puzzle, empty bins; the items fade in one after the other (12 frames each, 8 apart)
  const bins = ramp(f, sec(0.2), sec(0.6));
  const appear = [0, 1, 2, 3].map((u) => ramp(f, c0.from + u * 8, 12));
  const same = ramp(f, c0.from + sec(1.4), sec(0.6));

  // cue 2: the puzzle moves left and shrinks in one gentle move (its bins' names fade on the way)
  const shrink = ramp(f, c1.from, sec(1.6), sine);
  const at = mixAt(PUZZLE_BIG, PUZZLE_SMALL, shrink);
  const bigIn = ramp(f, c1.from + sec(1.2), sec(0.8));
  const toyIn = ramp(f, c1.from + sec(3.0), sec(0.6));
  // the recipe's cube leaves before the camera picks up speed, so its edges never sweep across the picture
  const bigOut = ramp(f, c1.from + sec(4.3), sec(0.5));
  const zoom = ramp(f, c1.from + sec(4.4), sec(2.4));
  const stripsIn = ramp(f, c1.from + sec(6.9), sec(0.5));
  // the notes: the recipe's count (with the cube of 80), then ours (with the cube of 12)
  const noteRecipe = ramp(f, c1.from + sec(1.8), sec(0.6));
  const noteToy = ramp(f, c1.from + sec(3.4), sec(0.6));

  const turn = -6 + 10 * (f / scene.duration);
  const shotBig: Shot = { target: [BIG / 2 - 0.5, BIG / 2 - 0.5, -(BIG / 2 - 0.5)], dir: yaw(GAME_DIR, turn), dist: 470, offset: OFFSET };
  const shotToy: Shot = { target: [TOY / 2 - 0.5, TOY / 2 - 1.2, -(TOY / 2 - 0.5)], dir: yaw(GAME_DIR, turn), dist: 62, offset: OFFSET };
  const shot = mixShot(shotBig, shotToy, zoom);
  shot.dist = Math.exp(lerp(Math.log(shotBig.dist), Math.log(shotToy.dist), zoom));
  const unitPx = unitPxAt(shot.dist);
  const project = projector(shot);

  // the recipe's cube: a thin wireframe, no tint
  const bigO = bigIn * (1 - bigOut);
  const big = cubeBox([-0.5, -0.5, 0.5], BIG, { color: C.fgSubtle, opacity: bigO, unitPx, linePx: 1.6, tint: 0 });

  const bRight = project([BIG - 0.5, BIG / 2, -BIG + 0.5]);
  const tBottom = project([TOY / 2 - 0.5, -0.5, 0.5]);

  return (
    <SceneFrame scene={scene}>
      {bigO > 0 && (
        <div style={{ position: 'absolute', inset: 0 }}>
          <Scene3D shot={shot} lines={big.lines} />
        </div>
      )}
      {/* our cube: one picture, coming in as a whole */}
      {toyIn > 0 && (
        <div style={{ position: 'absolute', inset: 0, opacity: toyIn }}>
          <Scene3D shot={shot} beads={CUBE.beads} sticks={CUBE.sticks} solids={[innerBlock()]} shell={CUBE_SHELL} />
        </div>
      )}
      <svg width={W} height={H} viewBox={`0 0 ${W} ${H}`} style={{ position: 'absolute', inset: 0 }}>
        <Puzzle at={at} appear={appear} bins={bins} />
        <Label x={960} y={662} opacity={same * (1 - clamp01(shrink * 3))} size={25}>
          the same puzzle as before: 6 + 4 and 2 + 8 fill the two bins
        </Label>
        <Note x={NOTE_X} y={NOTE_Y} opacity={noteRecipe} head="the recipe: 6 strips, side 80" />
        <Note x={NOTE_X} y={NOTE_Y + 58} opacity={noteToy} head="we use: 2 strips, side 12" sub="one strip per bin, so no plugs are needed" />
        <Label x={bRight[0] + 22} y={bRight[1] + 8} anchor="start" opacity={bigO} size={26} color={C.fg} weight={600}>
          side 80
        </Label>
        {/* the two strips our cube has, outlined on its empty front face once the camera is close */}
        {stripsIn > 0 &&
          STRIP_RECTS.map((r, s) => {
            const pts = ([[r.x0, r.y0], [r.x1, r.y0], [r.x1, r.y1], [r.x0, r.y1]] as const).map(([x, y]) => project([x, y, 0]));
            return <polygon key={s} points={pts.map((p) => `${p[0]},${p[1]}`).join(' ')} fill="none" stroke={C.fgMuted} strokeWidth={2.5} strokeLinejoin="round" opacity={stripsIn} />;
          })}
        {/* our cube's label: under the small cube's front edge all through the move, never faded */}
        <Label x={tBottom[0]} y={tBottom[1] + lerp(40, 62, zoom)} opacity={toyIn} size={26} color={C.fg} weight={600}>
          side 12
        </Label>
      </svg>
    </SceneFrame>
  );
}
