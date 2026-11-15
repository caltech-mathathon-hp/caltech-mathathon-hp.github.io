/**
 * The front face of the cube as the wall figures draw it (BL "Making the bins", Fig. 8), shortened.
 * Columns: 0 is the free edge of the (2q+1)-rods, 1 … inner the n − 2 columns between the free
 * edges, inner + 1 the free edge of the q-rods and the spaced rod. A break after column `split`
 * stands for the columns left out.
 * Rows: 0 the top edge (filled before), then periods of five rows each: wall, three strip rows, wall.
 * A break after each period but the last stands for the periods left out; the last row is the
 * bottom edge. Five rows per period is the period for q = 2 (2q + 1 = 5); labels give the general sizes.
 *
 * One period of the string, in string order: a q-rod up the right free edge (2 H's here), a wall
 * across, a (2q+1)-rod down the left free edge, a wall back, a q-rod up. The H between the two
 * q-rods belongs to the spaced rod. The walls of a period bound one strip.
 */
import type { Pt } from '../lib';

export interface FaceOpts {
  ox: number;
  oy: number;
  s: number;
  /** Width of the column break and height of the row break. */
  gx: number;
  gy: number;
  inner?: number;
  split?: number;
  periods?: number;
}

export const faceGeom = ({ ox, oy, s, gx, gy, inner = 8, split = 4, periods = 2 }: FaceOpts) => {
  const right = inner + 1;
  const bottom = 5 * periods + 1;
  const X = (c: number) => ox + c * s + (c > split ? gx : 0);
  const Y = (r: number) => oy + r * s + (r < 1 ? 0 : Math.min(Math.floor((r - 1) / 5), periods - 1) * gy);
  const at = (c: number, r: number): Pt => [X(c), Y(r)];
  const top = (p: number) => 1 + 5 * p; // first wall of period p
  const bot = (p: number) => 5 + 5 * p; // second wall of period p
  const stripRows = (p: number) => [top(p) + 1, top(p) + 2, top(p) + 3];
  /** The H's of period p in string order, split into its five pieces. */
  const period = (p: number) => {
    const t = top(p);
    const b = bot(p);
    const cols = Array.from({ length: inner }, (_, i) => i + 1);
    return {
      qRod1: [at(right, t + 1), at(right, t)],
      wall1: [...cols].reverse().map((c) => at(c, t)),
      q2Rod: [t, t + 1, t + 2, t + 3, b].map((r) => at(0, r)),
      wall2: cols.map((c) => at(c, b)),
      qRod2: [at(right, b), at(right, b - 1)],
      spaced: at(right, t + 2),
    };
  };
  const edgeRows = [0, bottom];
  /** Cells of the strip of period p in snake order (left to right, back, left to right). */
  const stripSnake = (p: number) => {
    const cols = Array.from({ length: inner }, (_, i) => i + 1);
    return stripRows(p).flatMap((r, k) => (k % 2 === 0 ? cols : [...cols].reverse()).map((c) => at(c, r)));
  };
  const box = {
    x: X(0) - s / 2 - 2,
    y: Y(0) - s / 2 - 2,
    w: X(right) - X(0) + s + 4,
    h: Y(bottom) - Y(0) + s + 4,
  };
  /** x of the column break, and y of the row break after period p. */
  const colBreak = (X(split) + X(split + 1)) / 2;
  const rowBreak = (p: number) => (Y(bot(p)) + Y(bot(p) + 1)) / 2;
  return { X, Y, at, right, bottom, top, bot, stripRows, period, edgeRows, stripSnake, box, colBreak, rowBreak, inner, split, s, periods };
};
