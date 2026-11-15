/** Scene "title": what the video shows, beside the finished toy fold turning slowly. */
import React from 'react';
import { AbsoluteFill, useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, GAME_DIR, yaw, type Bead, type Stick, type Shot } from '../three/Scene3D';
import { framePieces, wallPieces, itemPieces, drawPiece, innerBlock, CUBE_CENTER, CUBE_SHELL } from '../three/cube';
import { ramp, sec, easeOut } from '../lib/anim';
import { C, FONT } from '../theme/theme';
import type { SceneTime } from '../script';

const front = [...wallPieces(), ...itemPieces()];
const frame = framePieces();

export default function TitleScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const t = f / Math.max(1, scene.duration - 1);
  const shot: Shot = {
    target: [CUBE_CENTER[0], CUBE_CENTER[1] - 0.6, CUBE_CENTER[2]],
    // the three faces in view stay well turned to the camera (a face near edge-on fades out)
    dir: yaw(GAME_DIR, -6 + 8 * t),
    dist: 64,
    offset: [430, -30],
  };
  // the finished fold, every bead in its full colour; it fades in as one picture
  const beads: Bead[] = [];
  const sticks: Stick[] = [];
  const cubeIn = ramp(f, 0, sec(1.2));
  for (const p of frame) if (p.kind !== 'core') drawPiece(p, { progress: 1, ps: 0, dominoes: p.kind === 'face' }, beads, sticks);
  for (const p of front) drawPiece(p, { progress: 1, ps: 0, dominoes: true }, beads, sticks);

  const a = ramp(f, sec(0.3), sec(0.9));
  const b = ramp(f, sec(0.9), sec(0.9));
  const c = ramp(f, sec(1.5), sec(0.9));
  const up = (x: number) => (1 - easeOut(x)) * 16;
  return (
    <SceneFrame scene={scene} band={false}>
      <AbsoluteFill style={{ opacity: cubeIn }}>
        <Scene3D shot={shot} beads={beads} sticks={sticks} solids={[innerBlock({ soft: 0.15 })]} shell={CUBE_SHELL} />
      </AbsoluteFill>
      <AbsoluteFill style={{ left: 150, top: 300, width: 860, fontFamily: FONT.sans }}>
        <div style={{ opacity: a, transform: `translateY(${up(a)}px)`, fontSize: 24, fontWeight: 600, letterSpacing: '0.08em', textTransform: 'uppercase', color: C.accent }}>
          Berger and Leighton, 1998
        </div>
        <div style={{ opacity: b, transform: `translateY(${up(b)}px)`, marginTop: 22, fontFamily: FONT.serif, fontSize: 76, lineHeight: 1.08, fontWeight: 600, color: C.fg }}>
          Every bin packing puzzle is a folding problem
        </div>
        <div style={{ opacity: c, transform: `translateY(${up(c)}px)`, marginTop: 30, fontSize: 30, lineHeight: 1.4, color: C.fgMuted, maxWidth: 760 }}>
          Their proof that finding a best fold of an <span style={{ color: C.h, fontWeight: 600 }}>H</span>
          <span style={{ color: C.p, fontWeight: 600 }}>P</span> string on the cubic grid is NP-complete
        </div>
      </AbsoluteFill>
    </SceneFrame>
  );
}
