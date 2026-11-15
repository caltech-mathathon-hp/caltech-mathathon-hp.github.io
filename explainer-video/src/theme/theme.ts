/**
 * The site's light palette as plain hex values, for three.js (which cannot read CSS variables
 * inside a shader) and for SVG drawn in the video. Same values as tokens.css.
 */
import '@fontsource-variable/inter';
import '@fontsource-variable/source-serif-4';
import './tokens.css';

export const C = {
  bg: '#fbfaf7',
  bgElev: '#ffffff',
  bgSunk: '#f2f0eb',
  fg: '#1c1c21',
  fgMuted: '#55555f',
  fgSubtle: '#8b8b95',
  rule: '#e2ded5',
  ruleStrong: '#c9c3b7',
  accent: '#1f4f8f',
  h: '#c4532f',
  hWeak: '#f6e1d8',
  p: '#4f7aa3',
  pWeak: '#e3ebf3',
  bond: '#d99a1e',
  backbone: '#6d6d78',
  lattice: '#d8d4cb',
  invalid: '#b3261e',
  ok: '#2b6844',
  no: '#93232e',
  /** items u1..u4, as the bin-packing game colours them: --item-(u % 4 + 1) */
  items: ['#0f6f73', '#d99a1e', '#7a4b9e', '#a34f61'],
  /** padding: --item-pad */
  pad: '#8b8b95',
  /** plug: a light tan, apart from the padding's grey and from the white P's */
  plug: '#c2ae8a',
} as const;

export const itemColor = (u: number) => C.items[u % 4];

export const FONT = {
  serif: "'Source Serif 4 Variable', 'Source Serif Pro', Georgia, serif",
  sans: "'Inter Variable', Inter, system-ui, sans-serif",
  mono: "'JetBrains Mono', ui-monospace, Menlo, monospace",
};

export { W, H, FPS } from './consts.ts';
