/**
 * The words and symbols the figures print, in one place, following the page's notation table
 * (our name first; Berger–Leighton's symbol or term in the comment). Labels are plain strings drawn
 * through Tx.astro, which sets single letters (n, q, B, K, u …) in italic.
 */
const SUB = '₀₁₂₃₄₅₆₇₈₉';
export const sub = (i: number | string) =>
  String(i)
    .split('')
    .map((d) => (/\d/.test(d) ? SUB[+d] : d))
    .join('');

export const N = {
  /** Side of the cube. BL: n. */
  n: 'n',
  /** Number of bins of the instance. BL: K. */
  K: 'K',
  /** Size of a bin. BL: B. */
  B: 'B',
  /** Number of strips on the front face. BL: q. */
  q: 'q',
  /** Free nodes in one strip, (2q − 1)(n − 2). BL: T. */
  T: 'T',
  /** Item number i. BL: u ∈ U. */
  item: (i: number | string) => `u${sub(i)}`,
  /** Size of an item. BL: s(u). */
  size: (u = 'u') => `s(${u})`,
  /** One of the q regions between walls. BL: bin B_i. */
  strip: 'strip',
  /** (PHP)^q, a short rod. BL: q-string. */
  qRod: 'short rod',
  /** (PHP)^(2q+1), a long rod. BL: (2q+1)-string. */
  q2Rod: 'long rod',
  /** PH(P^(2q+6)H)^(q−1)P. BL: special q-string. */
  spaced: 'spaced rod',
  /** (PHP)^(9n−10). BL: no name. */
  corner: 'corner rod',
  /** (PHP)^(n−2). BL: no name. */
  tenth: 'tenth-edge rod',
  /** (PHHP)^((T−B)/2). BL: (T−B)-item-string. */
  padding: 'padding',
  /** (PHHP)^(B/2). BL: B-item-string. */
  plug: 'plug',
  /** The P's between two consecutive ribbons of the item part. BL: path of cn + 2 P's, c = 52. */
  linker: 'linker',
  linkerLen: '52n + 2',
};
