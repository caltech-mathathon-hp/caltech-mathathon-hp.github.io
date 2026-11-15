/**
 * Renders every frame of a range of the video at half size, for the flicker check
 * (scripts/flicker.py), into the given folder.
 *
 *   node scripts/flicker-frames.ts <outDir> <from> <to>
 */
import { mkdirSync } from 'node:fs';
import path from 'node:path';
import { bundle } from '@remotion/bundler';
import { renderFrames, selectComposition } from '@remotion/renderer';

const [outDir, from, to] = process.argv.slice(2);
if (!outDir || from === undefined || to === undefined) throw new Error('usage: flicker-frames.ts <outDir> <from> <to>');
mkdirSync(outDir, { recursive: true });

const root = path.resolve(import.meta.dirname, '..');
const serveUrl = await bundle({ entryPoint: path.join(root, 'src', 'index.ts') });
const chromiumOptions = { gl: 'angle' as const };
const composition = await selectComposition({ serveUrl, id: 'Explainer', chromiumOptions });
let last = 0;
await renderFrames({
  serveUrl,
  composition,
  inputProps: {},
  outputDir: outDir,
  imageFormat: 'png',
  scale: 0.5,
  frameRange: [Number(from), Number(to)],
  chromiumOptions,
  onStart: ({ frameCount }) => console.log(`rendering ${frameCount} frames`),
  onFrameUpdate: (done) => {
    if (done - last >= 200) {
      last = done;
      console.log(`${done} frames`);
    }
  },
});
console.log('done');
