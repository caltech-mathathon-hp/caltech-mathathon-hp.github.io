import React from 'react';
import { AbsoluteFill } from 'remotion';
import { C, FONT } from '../theme/theme';
import { SceneFrame } from '../ui/SceneFrame';
import type { SceneTime } from '../script';

/** stands in for a scene that is not built yet */
export default function Placeholder({ scene }: { scene: SceneTime }) {
  return (
    <SceneFrame scene={scene}>
      <AbsoluteFill style={{ alignItems: 'center', justifyContent: 'center', fontFamily: FONT.sans, color: C.fgSubtle, fontSize: 28 }}>
        [{scene.id}] {scene.cueTimes.map((c) => c.visual).join(' / ').slice(0, 160)}…
      </AbsoluteFill>
    </SceneFrame>
  );
}
