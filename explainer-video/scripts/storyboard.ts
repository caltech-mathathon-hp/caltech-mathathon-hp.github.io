/**
 * Writes storyboard.md from src/script.ts: every scene with its time, every caption with what the
 * picture does under it. Run: node scripts/storyboard.ts
 */
import { writeFileSync } from 'node:fs';
import { TIMELINE, TOTAL_FRAMES } from '../src/script.ts';
import { FPS } from '../src/theme/consts.ts';

const plain = (t: string) => t.replace(/\[\[[a-z0-9]+:([^\]]*)\]\]/g, '$1');
const mmss = (frames: number) => {
  const s = Math.round(frames / FPS);
  return `${Math.floor(s / 60)}:${String(s % 60).padStart(2, '0')}`;
};
const part = ['', 'Part 1, the idea', 'Part 2, an example', 'Part 3, in general'];

const out: string[] = [];
out.push('# Storyboard');
out.push('');
out.push(`Generated from \`src/script.ts\` by \`node scripts/storyboard.ts\`. Length ${mmss(TOTAL_FRAMES)} at ${FPS} fps.`);
out.push('Captions are the only text; each stays up for its reading time (15 characters a second) plus a pause to look.');
out.push('');
let lastPart = -1;
for (const s of TIMELINE) {
  if (s.part !== lastPart && s.part > 0) {
    out.push(`## ${part[s.part]}`);
    out.push('');
    lastPart = s.part;
  }
  out.push(`### ${mmss(s.start)} · ${s.title || 'Title card'} (\`${s.id}\`, ${(s.duration / FPS).toFixed(1)} s)`);
  out.push('');
  if (!s.cueTimes.length) out.push('No caption.');
  for (const c of s.cueTimes) {
    out.push(`- **${mmss(s.start + c.from)}** “${plain(c.text)}”`);
    out.push(`  *Picture:* ${c.visual}`);
  }
  out.push('');
}
writeFileSync(new URL('../storyboard.md', import.meta.url), out.join('\n'));
console.log(`storyboard.md: ${TIMELINE.length} scenes, ${mmss(TOTAL_FRAMES)}`);
