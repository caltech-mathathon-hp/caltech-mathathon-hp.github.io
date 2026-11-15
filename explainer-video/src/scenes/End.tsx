/**
 * Scene "end": first the recipe's cube of side 80 next to the toy's cube of side 12, to scale, with
 * their H counts (n³ each), and one plain sentence on why that size is fine; then the plan's
 * pipeline once more, compact (puzzle → HP string → best fold → "fits / does not fit"), with the
 * reference in small type. The last picture holds.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, GAME_DIR, yaw, type Shot } from '../three/Scene3D';
import { ramp, sec, clamp01 } from '../lib/anim';
import { C, FONT } from '../theme/theme';
import * as M from '../model/toy';
import type { V3 } from '../model/toy';
import type { SceneTime } from '../script';
import { Label, NAME, SUB, Pipeline, cubeBox, smallCube, smallCubeShot, unitPxAt } from './lib/planPipeline';

const BIG = M.REAL.n; // 80
const TOY = M.n; // 12
/**
 * The game's camera looks at the cube from about 30° right of straight on, so "to the right on
 * screen" is the floor direction RIGHT. The toy cube stands on the same floor, on that line through
 * the big cube's centre, at about the same distance from the camera.
 */
const RIGHT: [number, number] = [Math.cos((31 * Math.PI) / 180), -Math.sin((31 * Math.PI) / 180)];
const BIG_C: V3 = [BIG / 2 - 0.5, BIG / 2 - 0.5, -(BIG / 2 - 0.5)];
const TOY_D = 82;
const TOY_C: V3 = [BIG_C[0] + TOY_D * RIGHT[0], TOY / 2 - 0.5, BIG_C[2] + TOY_D * RIGHT[1]];
const TOY_MIN: V3 = [TOY_C[0] - TOY / 2, -0.5, TOY_C[2] + TOY / 2];
const MID = 18;
const fmt = (k: number) => k.toLocaleString('en-US');

/** right of the cubes: why a cube that big is fine, in one sentence */
const NOTE_X = 1030;
const NOTE_Y = 450;
const sine = (t: number) => (1 - Math.cos(Math.PI * clamp01(t))) / 2;

export default function EndScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1] = scene.cueTimes;

  // cue 1: the two cubes
  const bigIn = ramp(f, c0.from, sec(1.0));
  const bigLabel = ramp(f, c0.from + sec(0.8), sec(0.6));
  const toyIn = ramp(f, c0.from + sec(1.8), sec(0.7));
  const toyLabel = ramp(f, c0.from + sec(2.3), sec(0.6));
  const note = ramp(f, c0.from + sec(3.2), sec(0.6));
  const out = ramp(f, c1.from, sec(0.5));
  const cubes = 1 - out;

  // cue 2: the pipeline again, quicker than in "plan" (all motion done long before the pause)
  const t = c1.from + sec(0.6);
  const puzzle = ramp(f, t, sec(0.5));
  const ref = ramp(f, t + sec(6.2), sec(0.6));

  const turn = -8 + 14 * (f / scene.duration);
  const cubeTurn = -4 + 8 * (f / scene.duration);
  const cubesShot: Shot = {
    target: [BIG_C[0] + MID * RIGHT[0], BIG_C[1], BIG_C[2] + MID * RIGHT[1]],
    dir: yaw(GAME_DIR, turn),
    dist: 520,
    offset: [-430, -100],
  };
  const second = f >= c1.from + sec(0.5);
  const shot = second ? smallCubeShot(cubeTurn) : cubesShot;
  const unitPx = unitPxAt(cubesShot.dist);
  // both cubes as plain outlines (a cube of beads would be too small to read here), the toy's in orange
  const big = cubeBox([-0.5, -0.5, 0.5], BIG, { color: C.fgSubtle, opacity: bigIn * cubes, unitPx, linePx: 2, tint: 0 });
  const toy = cubeBox(TOY_MIN, TOY, { color: C.h, opacity: toyIn * cubes, unitPx, linePx: 2.5, tint: 0 });
  const small = second ? smallCube(f, t + sec(2.3), sec(1.5)) : { beads: [], sticks: [], lines: [] };

  return (
    <SceneFrame scene={scene}>
      <Scene3D
       
        shot={shot}
        beads={small.beads}
        sticks={small.sticks}
        lines={second ? small.lines : [...big.lines, ...toy.lines]}
        panels={second ? [] : [...big.panels, ...toy.panels]}
      >
        {(project) => {
          if (!second) {
            // labels under each cube: centred on the cube, below its lowest corner
            const bLow = project([BIG - 0.5, -0.5, 0.5])[1];
            const tLow = project([TOY_MIN[0] + TOY, -0.5, TOY_MIN[2]])[1];
            const low = Math.max(bLow, tLow);
            const bBottom = [project(BIG_C)[0], low];
            const tBottom = [project(TOY_C)[0], low];
            return (
              <g opacity={cubes}>
                <g opacity={note} fontFamily={FONT.sans} fontSize={SUB.size} fontWeight={SUB.weight} fill={SUB.color}>
                  <text x={NOTE_X} y={NOTE_Y}>Bigger sizes make a bigger cube,</text>
                  <text x={NOTE_X} y={NOTE_Y + 32}>but bin packing is hard even with small sizes.</text>
                </g>
                <Label x={bBottom[0]} y={bBottom[1] + 52} opacity={bigLabel} {...NAME}>
                  side n = {BIG}
                </Label>
                <Label x={bBottom[0]} y={bBottom[1] + 84} opacity={bigLabel} {...SUB}>
                  {`${BIG}³ = ${fmt(BIG ** 3)} H’s`}
                </Label>
                <Label x={tBottom[0]} y={tBottom[1] + 52} opacity={toyLabel} {...NAME}>
                  side n = {TOY}
                </Label>
                <Label x={tBottom[0]} y={tBottom[1] + 84} opacity={toyLabel} {...SUB}>
                  {`${TOY}³ = ${fmt(TOY ** 3)} H’s`}
                </Label>
              </g>
            );
          }
          return (
            <g>
              <Pipeline
                puzzle={puzzle}
                puzzleLabel={ramp(f, t + sec(0.3), sec(0.4))}
                hard={ramp(f, t + sec(0.5), sec(0.4))}
                a1={ramp(f, t + sec(0.7), sec(0.5))}
                str={ramp(f, t + sec(1.0), sec(1.2), sine)}
                a2={ramp(f, t + sec(2.1), sec(0.5))}
                cubeLabel={ramp(f, t + sec(3.7), sec(0.5))}
                a3={ramp(f, t + sec(4.0), sec(1.0))}
                l3={ramp(f, t + sec(4.7), sec(0.5))}
                fast={ramp(f, t + sec(5.2), sec(0.5))}
                asHard={ramp(f, t + sec(5.6), sec(0.5))}
              />
              <Label x={960} y={826} opacity={ref} {...SUB}>
                Berger and Leighton, J. Comput. Biol. 5(1), 1998
              </Label>
            </g>
          );
        }}
      </Scene3D>
    </SceneFrame>
  );
}
