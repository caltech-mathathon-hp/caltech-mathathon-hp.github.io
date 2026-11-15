/**
 * The steps of the page: one per caption. A step plays from where the previous one paused (or
 * from the start of its scene) and pauses 10 frames before its caption ends, where the caption is
 * still fully visible and the picture has settled.
 */
import { TIMELINE, type SceneTime } from '../src/script';

export const PAUSE_BEFORE_END = 10;

export interface Step {
  /** 1, 2, … */
  n: number;
  scene: SceneTime;
  /** the caption, without colour marks */
  text: string;
  /** absolute frames */
  start: number;
  end: number;
}

const plain = (t: string) => t.replace(/\[\[[a-z0-9]+:([^\]]*)\]\]/g, '$1');

export const STEPS: Step[] = [];
for (const s of TIMELINE) {
  let prev = s.start;
  s.cueTimes.forEach((c, i) => {
    const end = Math.max(s.start + c.to - PAUSE_BEFORE_END, prev + 1);
    STEPS.push({ n: STEPS.length + 1, scene: s, text: plain(c.text), start: i === 0 ? s.start : prev, end });
    prev = end;
  });
}

/** the title card: shown (its last frame) before step 1 */
const title = TIMELINE.find((s) => s.id === 'title');
export const TITLE_FRAME = title ? title.start + title.duration - PAUSE_BEFORE_END : 0;

/** steps grouped by scene, in order, for the step strip */
export const GROUPS = TIMELINE.filter((s) => s.cueTimes.length).map((s) => ({ scene: s, steps: STEPS.filter((st) => st.scene.id === s.id) }));
