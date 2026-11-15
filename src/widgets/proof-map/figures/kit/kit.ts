/**
 * The figure kit: the pieces every proof figure is drawn from, in the style of the fold game and
 * the explainer video. A letter is a lit bead (H burnt orange, P hollow with a blue rim, padding
 * grey, plug light grey, an item in its colour), the chain a thick grey stick, a contact a dashed
 * gold stick, an empty node a small lattice dot, a bin a rounded track like the bin packing game.
 *
 * Sizes follow from the bead radius r: stick 0.5 r wide, contact 0.3 r, empty node 0.28 r.
 * Colours are CSS variables from tokens.css (through fig.css), so dark mode needs nothing here.
 */
import type { Pt } from '../lib';

export type Kind = 'H' | 'P' | 'pad' | 'plug' | 'item';

/** Colour of a bead: an item k (0-based) uses var(--pmf-i<k+1>), repeating every four. */
export const beadColor = (kind: Kind, k = 0) =>
  kind === 'H'
    ? 'var(--h)'
    : kind === 'P'
      ? 'var(--p)'
      : kind === 'pad'
        ? 'var(--pmf-pad)'
        : kind === 'plug'
          ? 'var(--pmf-plug)'
          : `var(--pmf-i${(k % 4) + 1})`;

/** "PHHP" → ['P','H','H','P']; anything else passes through. */
export const kindsOf = (s: string | Kind[], n: number, item?: boolean): Kind[] => {
  const a = typeof s === 'string' ? (s.split('') as ('H' | 'P')[]) : s;
  return Array.from({ length: n }, (_, i) => {
    const k = a[i % a.length] as Kind;
    return item && k === 'H' ? 'item' : k;
  });
};

/** Segment from a to b with both ends pulled in by t (to stop at the bead rims). */
export const trim = (a: Pt, b: Pt, t: number, t2 = t) => {
  const dx = b[0] - a[0];
  const dy = b[1] - a[1];
  const L = Math.hypot(dx, dy) || 1;
  return {
    x1: +(a[0] + (dx * t) / L).toFixed(2),
    y1: +(a[1] + (dy * t) / L).toFixed(2),
    x2: +(b[0] - (dx * t2) / L).toFixed(2),
    y2: +(b[1] - (dy * t2) / L).toFixed(2),
  };
};

export const f = (v: number) => +v.toFixed(2);
