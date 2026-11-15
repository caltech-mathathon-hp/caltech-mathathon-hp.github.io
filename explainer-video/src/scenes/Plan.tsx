/**
 * Scene "plan": the bin packing puzzle (items slide into the bins: 6 + 4, 2 + 8), then the plan
 * as a pipeline read left to right: puzzle → HP string → best fold, and an arrow back from the
 * fold to the puzzle ("fits / does not fit"). Then what a fast folding program would mean: "a fast
 * program?" under the fold arrow, and "at least as hard" under the best fold.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D } from '../three/Scene3D';
import { ramp, sec, stagger, clamp01 } from '../lib/anim';
import type { SceneTime } from '../script';
import { Pipeline, PUZZLE_BIG, PUZZLE_SMALL, mixAt, smallCube, smallCubeShot } from './lib/planPipeline';

const lin = (t: number) => clamp01(t);
/** a gentle ease for writing and laying (a cubic ease makes the middle too fast for the beads' fades) */
const sine = (t: number) => (1 - Math.cos(Math.PI * clamp01(t))) / 2;

/** the order the items go into the bins: 6, 4, 2, 8 */
const ORDER = [0, 3, 1, 2];

export default function PlanScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1, c2] = scene.cueTimes;

  // cue 1: the puzzle, solved. `place` is linear: the puzzle eases each item's flight itself
  // (easing it here too made the middle of a flight a blur of a few frames)
  const appear = [0, 1, 2, 3].map((u) => stagger(f, c0.from, sec(0.7), u, 4, 10));
  // cue 2 opens with the items lifting back out of the bins, each to a row above its bin
  const back = ramp(f, c1.from, sec(1.0), lin);
  const place = [0, 0, 0, 0];
  ORDER.forEach((u, k) => {
    place[u] = ramp(f, c0.from + sec(1.0 + k * 1.05), sec(1.1), lin) * (1 - back);
  });

  // cue 2: the pipeline (all motion done 1.2 s before the pause)
  // the puzzle takes its compact form (the items in rows above their bins) as they lift, then moves to the left stage
  const compact = ramp(f, c1.from, sec(0.9));
  const shrink = ramp(f, c1.from + sec(0.6), sec(1.0));
  const at = mixAt(PUZZLE_BIG, PUZZLE_SMALL, shrink, compact);
  const cubeFrom = c1.from + sec(3.2);
  const cubeDur = sec(1.6);
  const turn = -4 + 8 * (f / scene.duration);
  const { beads, sticks } = smallCube(f, cubeFrom, cubeDur);

  return (
    <SceneFrame scene={scene}>
      <Scene3D shot={smallCubeShot(turn)} beads={beads} sticks={sticks}>
        {() => (
          <Pipeline
            at={at}
            place={place}
            appear={appear}
            puzzleLabel={ramp(f, c1.from + sec(1.3), sec(0.5))}
            hard={ramp(f, c1.from + sec(1.5), sec(0.5))}
            a1={ramp(f, c1.from + sec(1.6), sec(0.5))}
            str={ramp(f, c1.from + sec(1.9), sec(1.2), sine)}
            a2={ramp(f, c1.from + sec(3.0), sec(0.5))}
            cubeLabel={ramp(f, c1.from + sec(4.6), sec(0.5))}
            a3={ramp(f, c1.from + sec(4.9), sec(1.0))}
            l3={ramp(f, c1.from + sec(5.6), sec(0.5))}
            fast={ramp(f, c2.from + sec(0.5), sec(0.5))}
            asHard={ramp(f, c2.from + sec(1.6), sec(0.5))}
          />
        )}
      </Scene3D>
    </SceneFrame>
  );
}
