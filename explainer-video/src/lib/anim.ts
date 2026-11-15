/** Small, deterministic animation helpers (everything is a function of the frame). */
import { FPS } from '../theme/theme';

export const sec = (s: number) => Math.round(s * FPS);
export const clamp01 = (x: number) => Math.min(1, Math.max(0, x));
export const lerp = (a: number, b: number, t: number) => a + (b - a) * t;

export const easeInOut = (t: number) => {
  t = clamp01(t);
  return t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
};
export const easeOut = (t: number) => 1 - Math.pow(1 - clamp01(t), 3);
export const easeIn = (t: number) => Math.pow(clamp01(t), 3);
/** a small overshoot, for beads popping in */
export const easeBack = (t: number) => {
  t = clamp01(t);
  const c1 = 1.4;
  const c3 = c1 + 1;
  return 1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2);
};

/** eased progress 0..1 of an animation that starts at frame `from` and lasts `dur` frames */
export const ramp = (frame: number, from: number, dur: number, ease = easeInOut) => (dur <= 0 ? (frame >= from ? 1 : 0) : ease((frame - from) / dur));

/**
 * Progress of element i of `count` appearing one after another over `dur` frames from `from`.
 * Each element takes `each` frames to appear.
 */
export const stagger = (frame: number, from: number, dur: number, i: number, count: number, each = 8, ease = easeBack) => {
  const start = from + (count <= 1 ? 0 : (i / (count - 1)) * Math.max(0, dur - each));
  return ease((frame - start) / each);
};

/** fade in at `from`, fade out at `to` (frames), each over `f` frames */
export const window01 = (frame: number, from: number, to: number, f = 8) => clamp01(Math.min((frame - from) / f, (to - frame) / f));
