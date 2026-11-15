/**
 * Scene "instance": the example puzzle (items 6, 2, 8, 4; two bins of 10), then the size of its
 * cube. The recipe's cube of side 80 is drawn to scale with the toy's cube of side 12 in its
 * corner; the camera then moves in to the small cube, which turns into the toy's fold in the game's
 * look (beads on the surface, the core as one block, a grey outline), all at one brightness. A
 * note under the puzzle gives the recipe's count and the toy's. "side 12" stays under the small
 * cube's front edge all through the move. The toy badge appears and stays for the rest of the
 * video.
 */
import React from 'react';
import { AbsoluteFill, useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { ToyBadge } from '../ui/Caption';
import { Scene3D, GAME_DIR, mixShot, yaw, type Bead, type Stick, type Shot } from '../three/Scene3D';
import { framePieces, wallPieces, itemPieces, drawPiece, cubeOutline, innerBlock, CUBE_SHELL } from '../three/cube';
import { ramp, sec, lerp, stagger, clamp01 } from '../lib/anim';
import { C, FONT } from '../theme/theme';
import * as M from '../model/toy';
import type { SceneTime } from '../script';
import { Puzzle, PUZZLE_BIG, PUZZLE_SMALL, mixAt, cubeBox, unitPxAt, Label } from './lib/planPipeline';

const BIG = M.REAL.n; // 80
const TOY = M.n; // 12
const OFFSET: [number, number] = [300, -70];

/** the toy's fold: the frame (rods and face ribbons; the core is drawn as one block) and the front face */
const FRAME = framePieces().filter((p) => p.kind !== 'core');
const FRONT = [...wallPieces(), ...itemPieces()];

/** the note under the puzzle in cue 2: the recipe's count, then the toy's and what it changes */
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

  // cue 1: the puzzle, empty bins
  const bins = ramp(f, sec(0.2), sec(0.6));
  const appear = [0, 1, 2, 3].map((u) => stagger(f, c0.from, sec(1.0), u, 4, 10));
  const same = ramp(f, c0.from + sec(1.4), sec(0.6));

  // cue 2: the cubes
  const shrink = ramp(f, c1.from, sec(1.0));
  const at = mixAt(PUZZLE_BIG, PUZZLE_SMALL, shrink);
  const bigIn = ramp(f, c1.from + sec(0.8), sec(1.0));
  const toyIn = ramp(f, c1.from + sec(3.0), sec(0.7));
  const zoom = ramp(f, c1.from + sec(4.2), sec(2.4));
  // during the second half of the move the box turns into the fold, done when the camera stops
  const foldIn = ramp(f, c1.from + sec(5.4), sec(1.2));
  const badge = ramp(f, c1.from + sec(5.2), sec(0.8));
  // the note under the puzzle: the recipe's count (with the cube of 80), then the toy's (with the cube of 12)
  const noteRecipe = ramp(f, c1.from + sec(1.8), sec(0.6));
  const noteToy = ramp(f, c1.from + sec(3.4), sec(0.6));

  const turn = -6 + 10 * (f / scene.duration);
  const shotBig: Shot = { target: [BIG / 2 - 0.5, BIG / 2 - 0.5, -(BIG / 2 - 0.5)], dir: yaw(GAME_DIR, turn), dist: 470, offset: OFFSET };
  const shotToy: Shot = { target: [TOY / 2 - 0.5, TOY / 2 - 1.2, -(TOY / 2 - 0.5)], dir: yaw(GAME_DIR, turn), dist: 62, offset: OFFSET };
  const shot = mixShot(shotBig, shotToy, zoom);
  shot.dist = Math.exp(lerp(Math.log(shotBig.dist), Math.log(shotToy.dist), zoom));
  const unitPx = unitPxAt(shot.dist);

  const big = cubeBox([-0.5, -0.5, 0.5], BIG, { color: C.fgSubtle, opacity: bigIn * (1 - clamp01(zoom * 1.6)), unitPx, linePx: 1.6, tint: 0.7 });
  const toy = cubeBox([-0.5, -0.5, 0.5], TOY, { color: C.h, opacity: toyIn * (1 - foldIn), unitPx, linePx: 2, tint: 1.6 });
  const beads: Bead[] = [];
  const sticks: Stick[] = [];
  if (foldIn > 0) {
    // the whole cube at one brightness: here it stands for its size, not for its parts
    const fade = 1 - foldIn;
    for (const p of FRAME) drawPiece(p, { progress: 1, ps: 0, dominoes: p.kind === 'face', fade }, beads, sticks);
    for (const p of FRONT) drawPiece(p, { progress: 1, ps: 0, dominoes: true, fade }, beads, sticks);
  }
  const outline = cubeOutline(0.5 * foldIn, C.fgSubtle);

  return (
    <SceneFrame scene={scene}>
      <Scene3D
       
        shot={shot}
        beads={beads}
        sticks={sticks}
        lines={[...big.lines, ...toy.lines, ...outline]}
        panels={[...big.panels, ...toy.panels]}
        solids={foldIn > 0 ? [innerBlock({ opacity: foldIn, soft: 0.15 })] : []}
        shell={{ ...CUBE_SHELL, amount: foldIn }}
        depthCue={0.4 * foldIn}
      >
        {(project) => {
          const bRight = project([BIG - 0.5, BIG / 2, -BIG + 0.5]);
          const tBottom = project([TOY / 2 - 0.5, -0.5, 0.5]);
          return (
            <g>
              <Puzzle at={at} appear={appear} bins={bins} />
              <Label x={960} y={662} opacity={same * (1 - clamp01(shrink * 3))} size={25}>
                the same puzzle as before: 6 + 4 and 2 + 8 fill the two bins
              </Label>
              <Note x={NOTE_X} y={NOTE_Y} opacity={noteRecipe} head="Recipe: 6 strips, side 80" />
              <Note x={NOTE_X} y={NOTE_Y + 58} opacity={noteToy} head="Toy: 2 strips, side 12" sub="one strip per bin, so no plugs are needed" />
              <Label x={bRight[0] + 22} y={bRight[1] + 8} anchor="start" opacity={bigIn * (1 - clamp01(zoom * 3))} size={26} color={C.fg} weight={600}>
                side 80
              </Label>
              {/* the toy cube's label: under the small cube's front edge all through the move, never faded */}
              <Label x={tBottom[0]} y={tBottom[1] + lerp(40, 62, zoom)} opacity={toyIn} size={26} color={C.fg} weight={600}>
                side 12
              </Label>
            </g>
          );
        }}
      </Scene3D>
      {badge > 0 && (
        <AbsoluteFill style={{ pointerEvents: 'none' }}>
          <ToyBadge opacity={badge} />
        </AbsoluteFill>
      )}
    </SceneFrame>
  );
}
