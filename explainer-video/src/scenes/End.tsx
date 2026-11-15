/**
 * Scene "end": first how big the recipe's cube gets, to scale: the cube for our items 6, 2, 8, 4
 * next to the cube for the same items with every size tripled, as thin grey wireframes, each with
 * its items and its side and number of H's. Then the plan's pipeline once more (puzzle → HP string
 * → best fold → "fits / does not fit"), one pass of the loop, and the reference in small type. The
 * last picture holds.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, GAME_DIR, yaw } from '../three/Scene3D';
import { ramp, clamp01 } from '../lib/anim';
import { C } from '../theme/theme';
import * as M from '../model/toy';
import type { V3 } from '../model/toy';
import type { SceneTime } from '../script';
import { Label, NAME, SUB, Pipeline, RUN_FRAMES, gentle, smallCube, smallCubeShot } from './lib/planPipeline';

const lin = (t: number) => clamp01(t);
const fmt = (k: number) => k.toLocaleString('en-US');

/**
 * The cubes compared: our items, and the same items with every size multiplied (the bins too).
 * Doubling gives the same cube as our items (B = 20 still has ⌈B^(1/3)⌉ = 3, so q = 6 and n = 80),
 * so the second cube is for every size tripled (B = 30: q = 8, n = 138).
 */
const MULT = [1, 3];
const CUBES = MULT.map((k) => {
  const r = M.recipe(M.K, M.B * k);
  return { sizes: M.SIZES.map((s) => s * k), n: r.n, h: r.h };
});

// an orthographic view of the cubes from the game's camera direction, turned by `deg` degrees
const cross = (a: V3, b: V3): V3 => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
const unit = (v: V3): V3 => {
  const l = Math.hypot(v[0], v[1], v[2]);
  return [v[0] / l, v[1] / l, v[2] / l];
};
const dot = (a: V3, b: V3) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const view = (deg: number) => {
  const d = unit(yaw(GAME_DIR, deg));
  const right = unit(cross([0, 1, 0], d));
  const up = cross(d, right);
  return { d, right, up };
};
/** the cube's screen size per lattice unit of side, from the unturned view */
const V0 = view(0);
const H_PER = Math.abs(V0.up[0]) + Math.abs(V0.up[1]) + Math.abs(V0.up[2]);
const W_PER = Math.abs(V0.right[0]) + Math.abs(V0.right[1]) + Math.abs(V0.right[2]);
/** px per lattice unit: the largest cube is 500 px high */
const PX = 500 / (H_PER * Math.max(...CUBES.map((c) => c.n)));
/** the cubes stand on one line, side by side with a gap, centred in the picture */
const BOTTOM_Y = 690;
const GAP = 190;
const LAYOUT = (() => {
  const ws = CUBES.map((c) => c.n * W_PER * PX);
  let x = 960 - (ws.reduce((a, b) => a + b, 0) + GAP * (CUBES.length - 1)) / 2;
  return CUBES.map((c, i) => {
    const cx = x + ws[i] / 2;
    x += ws[i] + GAP;
    // the screen point of the cube's centre: its lowest corner on BOTTOM_Y in the unturned view
    return { cx, cy: BOTTOM_Y - (c.n * H_PER * PX) / 2 };
  });
})();

/** a cube of side n as a thin wireframe, its centre at (cx, cy); the three edges at its hidden corner are left out */
function WireCube({ n, cx, cy, deg, opacity }: { n: number; cx: number; cy: number; deg: number; opacity: number }) {
  if (opacity <= 0) return null;
  const v = view(deg);
  const centre: V3 = [n / 2, n / 2, -n / 2];
  const corner = (m: number): V3 => [m & 1 ? n : 0, m & 2 ? n : 0, m & 4 ? -n : 0];
  const at = (p: V3): [number, number] => {
    const q: V3 = [p[0] - centre[0], p[1] - centre[1], p[2] - centre[2]];
    return [cx + dot(q, v.right) * PX, cy - dot(q, v.up) * PX];
  };
  // the corner farthest from the camera is hidden behind the cube
  let hidden = 0;
  for (let m = 1; m < 8; m++) if (dot(corner(m), v.d) < dot(corner(hidden), v.d)) hidden = m;
  const lines: React.ReactNode[] = [];
  for (let m = 0; m < 8; m++)
    for (const bit of [1, 2, 4]) {
      if (m & bit) continue;
      if (m === hidden || (m | bit) === hidden) continue;
      const a = at(corner(m));
      const b = at(corner(m | bit));
      lines.push(<line key={`${m}-${bit}`} x1={a[0]} y1={a[1]} x2={b[0]} y2={b[1]} />);
    }
  return (
    <g opacity={opacity} stroke={C.fgSubtle} strokeWidth={2} strokeLinecap="round" fill="none">
      {lines}
    </g>
  );
}

export default function EndScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1] = scene.cueTimes;

  // cue 1: the two cubes, one after the other, each with its labels; they fade out at the cut to
  // cue 2 before the pipeline comes
  const deg = -4 + 8 * (f / scene.duration);
  const out = ramp(f, c1.from, 15, lin);
  const cubeIn = (k: number) => ramp(f, c0.from + 75 * k, 18) * (1 - out);
  const nameIn = (k: number) => ramp(f, c0.from + 75 * k + 16, 12) * (1 - out);
  const subIn = (k: number) => ramp(f, c0.from + 75 * k + 22, 12) * (1 - out);

  // cue 2: the pipeline built again, quicker than in "plan", then one pass of the loop; all done
  // before the pause
  const t = c1.from + 16;
  const second = f >= t;
  const cubeTurn = -4 + 8 * (f / scene.duration);
  const small = smallCube(f, t + 62);

  return (
    <SceneFrame scene={scene}>
      <Scene3D shot={smallCubeShot(cubeTurn)} beads={second ? small.beads : []} sticks={second ? small.sticks : []}>
        {() =>
          !second ? (
            <g>
              {CUBES.map((c, k) => (
                <g key={k}>
                  <WireCube n={c.n} cx={LAYOUT[k].cx} cy={LAYOUT[k].cy} deg={deg} opacity={cubeIn(k)} />
                  <Label x={LAYOUT[k].cx} y={BOTTOM_Y + 52} opacity={nameIn(k)} {...NAME}>
                    {`items ${c.sizes.join(', ')}`}
                  </Label>
                  <Label x={LAYOUT[k].cx} y={BOTTOM_Y + 84} opacity={subIn(k)} {...SUB}>
                    {`side ${c.n}, ${c.n}³ = ${fmt(c.h)} H’s`}
                  </Label>
                </g>
              ))}
            </g>
          ) : (
            <g>
              <Pipeline
                puzzle={ramp(f, t, 12)}
                puzzleLabel={ramp(f, t + 6, 12)}
                hard={ramp(f, t + 10, 12)}
                a1={ramp(f, t + 12, 14)}
                str={gentle(ramp(f, t + 18, 44, lin))}
                a2={ramp(f, t + 54, 14)}
                cubeLabel={ramp(f, t + 108, 12)}
                a3={ramp(f, t + 118, 24)}
                l3={ramp(f, t + 136, 12)}
                fast={ramp(f, t + 150, 12)}
                run={f - (t + 160)}
                asHard={ramp(f, t + 160 + RUN_FRAMES + 2, 12)}
              />
              <Label x={960} y={826} opacity={ramp(f, t + 144, 14)} {...SUB}>
                Berger and Leighton, J. Comput. Biol. 5(1), 1998
              </Label>
            </g>
          )
        }
      </Scene3D>
    </SceneFrame>
  );
}
