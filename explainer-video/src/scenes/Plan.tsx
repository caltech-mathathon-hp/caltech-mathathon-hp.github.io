/**
 * Scene "plan": the bin packing puzzle (the items go one by one into the bins: 6 + 4, 2 + 8), then
 * the plan as a pipeline read left to right: puzzle → HP string → best fold, and an arrow back from
 * the fold to the puzzle ("fits / does not fit"). Then what a fast folding program would mean:
 * "a fast program?" under the fold arrow, one pass of the loop (a dot runs along the three arrows in
 * turn), and "at least as hard" under the best fold.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D } from '../three/Scene3D';
import { ramp, clamp01 } from '../lib/anim';
import type { SceneTime } from '../script';
import { FLIGHT_FRAMES, Pipeline, PUZZLE_BIG, PUZZLE_SMALL, RUN_FRAMES, gentle, mixAt, smallCube, smallCubeShot } from './lib/planPipeline';

const lin = (t: number) => clamp01(t);
const sine = (t: number) => (1 - Math.cos(Math.PI * clamp01(t))) / 2;

/** the order the items go into the bins: 6, 4, 2, 8 */
const ORDER = [0, 3, 1, 2];
/** frames between one item landing and the next one setting off */
const FLIGHT_GAP = 10;

export default function PlanScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1, c2] = scene.cueTimes;

  // cue 1: the four items fade in at full size in their order (10 frames each), then go one by
  // one into their bins, each along its own path (`place` is plain time; the puzzle eases it)
  const place = [0, 0, 0, 0];
  let t = c0.from + 33;
  for (const u of ORDER) {
    place[u] = ramp(f, t, FLIGHT_FRAMES[u], lin);
    t += FLIGHT_FRAMES[u] + FLIGHT_GAP;
  }
  // cue 2 opens with the packed puzzle fading out (8 frames) and the unpacked one, the items in
  // their row as in cue 1, fading in after it; then the puzzle moves to the left stage
  const packedOut = ramp(f, c1.from, 8, lin);
  const unpacked = f >= c1.from + 8;
  const appear = [0, 1, 2, 3].map((u) =>
    unpacked ? ramp(f, c1.from + 9 + 3 * u, 8, sine) : ramp(f, c0.from + 5 * u, 10, sine) * (1 - packedOut),
  );
  if (unpacked) place.fill(0);
  // the bins' names go while the items come back (they are not part of the pipeline's stage)
  const compact = ramp(f, c1.from + 10, 30, lin);
  const shrink = ramp(f, c1.from + 24, 30, sine);
  const at = mixAt(PUZZLE_BIG, PUZZLE_SMALL, shrink, compact);

  // the best fold, laid with one soft tip from the end of the string's arrow
  const turn = -4 + 8 * (f / scene.duration);
  const { beads, sticks } = smallCube(f, c1.from + 104);

  return (
    <SceneFrame scene={scene}>
      <Scene3D shot={smallCubeShot(turn)} beads={beads} sticks={sticks}>
        {() => (
          <Pipeline
            at={at}
            place={place}
            appear={appear}
            puzzleLabel={ramp(f, c1.from + 46, 12)}
            hard={ramp(f, c1.from + 54, 12)}
            a1={ramp(f, c1.from + 50, 14)}
            str={gentle(ramp(f, c1.from + 56, 48, lin))}
            a2={ramp(f, c1.from + 98, 14)}
            cubeLabel={ramp(f, c1.from + 158, 12)}
            a3={ramp(f, c1.from + 162, 24)}
            l3={ramp(f, c1.from + 180, 12)}
            fast={ramp(f, c2.from + 10, 12)}
            run={f - (c2.from + 36)}
            asHard={ramp(f, c2.from + 36 + RUN_FRAMES + 4, 12)}
          />
        )}
      </Scene3D>
    </SceneFrame>
  );
}
