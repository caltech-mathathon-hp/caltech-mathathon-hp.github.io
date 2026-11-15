/**
 * Renders chosen frames at full size, for looking closely at a moment of the video.
 *
 *   node scripts/stills-at.ts <outDir> 1704 1755 3600-3700:20
 *
 * A range a-b:k takes every k-th frame from a to b. Files are <outDir>/f-NNNNN.png.
 */
import { mkdirSync } from 'node:fs';
import path from 'node:path';
import { bundle } from '@remotion/bundler';
import { renderStill, selectComposition } from '@remotion/renderer';

const [outArg, ...specs] = process.argv.slice(2);
if (!outArg || !specs.length) throw new Error('usage: node scripts/stills-at.ts <outDir> <frame|a-b[:k]> ...');
const frames: number[] = [];
for (const s of specs) {
  const [range, by] = s.split(':');
  const [lo, hi] = range.split('-').map(Number);
  for (let k = lo; k <= (hi ?? lo); k += Number(by ?? 1)) frames.push(k);
}
const root = path.resolve(import.meta.dirname, '..');
const outDir = path.resolve(outArg);
mkdirSync(outDir, { recursive: true });
const serveUrl = await bundle({ entryPoint: path.join(root, 'src', 'index.ts') });
const chromiumOptions = { gl: 'angle' as const };
const composition = await selectComposition({ serveUrl, id: 'Explainer', chromiumOptions });
for (const frame of frames) {
  const output = path.join(outDir, `f-${String(frame).padStart(5, '0')}.png`);
  await renderStill({ serveUrl, composition, frame, output, chromiumOptions, overwrite: true });
  console.log(output);
}
