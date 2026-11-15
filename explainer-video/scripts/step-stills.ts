/**
 * Renders the picture each step of the step page stops on (10 frames before its caption ends) to
 * out/steps/step-NN.png, plus the title card as step-00.png. Bundles once, then renders every
 * frame, so it is much faster than one `remotion still` per step.
 *
 *   node scripts/step-stills.ts            # every step
 *   node scripts/step-stills.ts 7 12-15    # some steps
 */
import { mkdirSync } from 'node:fs';
import path from 'node:path';
import { bundle } from '@remotion/bundler';
import { renderStill, selectComposition } from '@remotion/renderer';
import { TIMELINE } from '../src/script.ts';

const PAUSE_BEFORE_END = 10; // as in stepper/steps.ts

const frames: { n: number; frame: number }[] = [];
for (const s of TIMELINE) {
  let prev = s.start;
  for (const c of s.cueTimes) {
    const end = Math.max(s.start + c.to - PAUSE_BEFORE_END, prev + 1);
    frames.push({ n: frames.length + 1, frame: end });
    prev = end;
  }
}
const title = TIMELINE.find((s) => s.id === 'title');
if (title) frames.unshift({ n: 0, frame: title.start + title.duration - 1 });

const want = new Set<number>();
for (const a of process.argv.slice(2)) {
  const [lo, hi] = a.split('-').map(Number);
  for (let k = lo; k <= (hi ?? lo); k++) want.add(k);
}
const todo = want.size ? frames.filter((f) => want.has(f.n)) : frames;

const root = path.resolve(import.meta.dirname, '..');
const outDir = path.join(root, 'out', 'steps');
mkdirSync(outDir, { recursive: true });

const serveUrl = await bundle({ entryPoint: path.join(root, 'src', 'index.ts') });
const chromiumOptions = { gl: 'angle' as const };
const composition = await selectComposition({ serveUrl, id: 'Explainer', chromiumOptions });
for (const { n, frame } of todo) {
  const output = path.join(outDir, `step-${String(n).padStart(2, '0')}.png`);
  await renderStill({ serveUrl, composition, frame, output, chromiumOptions, overwrite: true });
  console.log(`step ${n} (frame ${frame}) → ${path.relative(root, output)}`);
}
