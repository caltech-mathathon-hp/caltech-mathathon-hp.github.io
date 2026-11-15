/** The whole video: every scene in order. Used by the render (Root.tsx) and by the step-through page (stepper/). */
import React from 'react';
import { Series } from 'remotion';
import './theme/theme';
import { TIMELINE } from './script';
import { SCENE_COMPONENTS } from './scenes';
import Placeholder from './scenes/Placeholder';

export function Explainer() {
  return (
    <Series>
      {TIMELINE.map((s) => {
        const Comp = SCENE_COMPONENTS[s.id] ?? Placeholder;
        return (
          // premountFor: in the step page (a Player) each scene is mounted, hidden, 1.5 s before it
          // starts, so its 3D canvas is ready at the cut instead of showing blank for a moment.
          // Renders ignore it.
          <Series.Sequence key={s.id} durationInFrames={s.duration} name={s.id} premountFor={45}>
            <Comp scene={s} />
          </Series.Sequence>
        );
      })}
    </Series>
  );
}
