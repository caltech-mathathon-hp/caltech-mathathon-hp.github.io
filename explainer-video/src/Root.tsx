import React from 'react';
import { Composition } from 'remotion';
import './theme/theme';
import { FPS, W, H } from './theme/theme';
import { TIMELINE, TOTAL_FRAMES } from './script';
import { SCENE_COMPONENTS } from './scenes';
import Placeholder from './scenes/Placeholder';
import { Explainer } from './Video';

export function Root() {
  return (
    <>
      <Composition id="Explainer" component={Explainer} durationInFrames={TOTAL_FRAMES} fps={FPS} width={W} height={H} />
      {TIMELINE.map((s) => {
        const Comp = SCENE_COMPONENTS[s.id] ?? Placeholder;
        return <Composition key={s.id} id={`scene-${s.id}`} component={() => <Comp scene={s} />} durationInFrames={s.duration} fps={FPS} width={W} height={H} />;
      })}
    </>
  );
}
