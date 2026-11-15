/**
 * Geometry shared by the proof figures: points, the oblique projection of the cube pictures,
 * braces and break marks. Item k (0-based) is drawn in colour var(--pmf-i<k+1>) (fig.css).
 */
export type Pt = [number, number];
export type P3 = [number, number, number];

export const itemColor = (k: number) => `var(--pmf-i${(k % 4) + 1})`;

/** Oblique projection: x right, y up, z into the page (drawn up and right). */
export const oblique =
  (ox: number, oy: number, u: number, dx = 0.55, dy = 0.4) =>
  ([x, y, z]: P3): Pt => [ox + u * x + dx * u * z, oy - u * y - dy * u * z];

export const pts = (a: Pt[]) => a.map(([x, y]) => `${+x.toFixed(1)},${+y.toFixed(1)}`).join(' ');

/**
 * A curly brace along a horizontal line y from x1 to x2. d = -1 opens downward with its point up
 * (label above), d = 1 points down (label below). h: how far the point stands off.
 */
export const hbrace = (x1: number, x2: number, y: number, d: -1 | 1 = -1, h = 6) => {
  const r = Math.min(h, (x2 - x1) / 4);
  const m = (x1 + x2) / 2;
  const y1 = y + (d * h) / 2;
  const y2 = y + d * h;
  return `M${x1} ${y}Q${x1} ${y1} ${x1 + r} ${y1}L${m - r} ${y1}Q${m} ${y1} ${m} ${y2}Q${m} ${y1} ${m + r} ${y1}L${x2 - r} ${y1}Q${x2} ${y1} ${x2} ${y}`;
};

/** A curly brace along a vertical line x from y1 to y2. d = -1 points left, d = 1 points right. */
export const vbrace = (x: number, y1: number, y2: number, d: -1 | 1 = -1, h = 6) => {
  const r = Math.min(h, (y2 - y1) / 4);
  const m = (y1 + y2) / 2;
  const x1 = x + (d * h) / 2;
  const x2 = x + d * h;
  return `M${x} ${y1}Q${x1} ${y1} ${x1} ${y1 + r}L${x1} ${m - r}Q${x1} ${m} ${x2} ${m}Q${x1} ${m} ${x1} ${m + r}L${x1} ${y2 - r}Q${x1} ${y2} ${x} ${y2}`;
};

/** Break mark across a horizontal run at (x, y): two short slanted strokes. */
export const hbreak = (x: number, y: number, h = 7) =>
  `M${x - 4} ${y + h}L${x - 1} ${y - h}M${x + 1} ${y + h}L${x + 4} ${y - h}`;

/** Break mark across a vertical run at (x, y). */
export const vbreak = (x: number, y: number, w = 7) =>
  `M${x - w} ${y - 1}L${x + w} ${y - 4}M${x - w} ${y + 4}L${x + w} ${y + 1}`;
