/**
 * A (partial) fold of an HP string: residues 0..k-1 placed on distinct lattice points,
 * consecutive residues on neighbouring points (a self-avoiding walk). Mutable and cheap;
 * the GameController wraps it with history and change notifications.
 *
 * Scoring follows the usual HP convention: a CONTACT is a pair of H's on neighbouring
 * points that are NOT consecutive in the string. (Berger–Leighton count all H–H bonds,
 * chain neighbours included; that differs by a constant of the string, `chainBonds`.)
 */
import { type Lattice, type Vec, key, neighbours, stepIndex, stepFrom, stepsAt, stepNamesAt, degree } from './lattice.ts';

export type Residue = 'H' | 'P';

export interface Contact {
  /** residue indices, i < j - 1 */
  i: number;
  j: number;
}

export function parseSequence(s: string): Residue[] {
  const clean = s.toUpperCase().replace(/[^HP]/g, '');
  return [...clean] as Residue[];
}

export class Fold {
  readonly lattice: Lattice;
  readonly seq: Residue[];
  /** positions of the placed residues 0..placed-1 */
  readonly path: number[][] = [];
  private occ = new Map<string, number>();

  constructor(lattice: Lattice, seq: Residue[] | string, origin?: Vec) {
    this.lattice = lattice;
    this.seq = typeof seq === 'string' ? parseSequence(seq) : seq;
    if (this.seq.length > 0) this.place(origin ? [...origin] : lattice.steps[0].map(() => 0));
  }

  get length(): number {
    return this.seq.length;
  }
  get placed(): number {
    return this.path.length;
  }
  get complete(): boolean {
    return this.path.length === this.seq.length;
  }
  get last(): number[] | undefined {
    return this.path[this.path.length - 1];
  }

  /** residue index at a lattice point, or undefined */
  at(v: Vec): number | undefined {
    return this.occ.get(key(v));
  }

  isFree(v: Vec): boolean {
    return !this.occ.has(key(v));
  }

  /** free neighbours of the last placed residue: where the next residue may go */
  options(): number[][] {
    if (this.complete || !this.last) return [];
    return neighbours(this.lattice, this.last).filter((v) => this.isFree(v));
  }

  /** no legal next position although residues remain: the walk is trapped */
  get stuck(): boolean {
    return !this.complete && this.options().length === 0;
  }

  /** place the next residue at v; returns false (and does nothing) if illegal */
  extendTo(v: Vec): boolean {
    if (this.complete) return false;
    if (!this.isFree(v)) return false;
    if (this.last && stepIndex(this.lattice, this.last, v) < 0) return false;
    this.place([...v]);
    return true;
  }

  /** place the next residue one step from the last, along the k-th step at the last residue */
  extendStep(k: number): boolean {
    const last = this.last;
    if (!last) return false;
    const v = stepFrom(this.lattice, last, k);
    return v ? this.extendTo(v) : false;
  }

  /** remove the last residue (residue 0 stays) */
  retract(): boolean {
    if (this.path.length <= 1) return false;
    const v = this.path.pop()!;
    this.occ.delete(key(v));
    return true;
  }

  private place(v: number[]) {
    this.occ.set(key(v), this.path.length);
    this.path.push(v);
  }

  /** all H–H contacts among the placed residues (non-consecutive neighbours) */
  contacts(): Contact[] {
    const out: Contact[] = [];
    for (let i = 0; i < this.path.length; i++) {
      if (this.seq[i] !== 'H') continue;
      for (const w of neighbours(this.lattice, this.path[i])) {
        const j = this.occ.get(key(w));
        if (j !== undefined && j > i + 1 && this.seq[j] === 'H') out.push({ i, j });
      }
    }
    return out;
  }

  score(): number {
    return this.contacts().length;
  }

  /** the move string of this fold (see encodeMoves) */
  moves(): string {
    return encodeMoves(this.lattice, this.path);
  }

  /** a copy (for history snapshots) */
  clone(): Fold {
    const f = new Fold(this.lattice, this.seq, this.path[0]);
    for (let k = 1; k < this.path.length; k++) f.extendTo(this.path[k]);
    return f;
  }

  /**
   * Build a fold from explicit positions (e.g. a precomputed construction).
   * Throws if the positions are not a self-avoiding walk.
   */
  static fromPositions(lattice: Lattice, seq: Residue[] | string, positions: Vec[]): Fold {
    const f = new Fold(lattice, seq, positions[0]);
    for (let k = 1; k < positions.length; k++)
      if (!f.extendTo(positions[k])) throw new Error(`invalid step to residue ${k} at ${key(positions[k])}`);
    return f;
  }

  /** Build a fold from a move string (see encodeMoves). Stops at the first illegal move. */
  static fromMoves(lattice: Lattice, seq: Residue[] | string, moves: string): Fold {
    const f = new Fold(lattice, seq);
    for (const k of decodeMoves(lattice, moves)) if (!f.extendStep(k)) break;
    return f;
  }
}

/**
 * Number of chain-neighbour H–H pairs: a constant of the string. Adding it to the contact
 * count gives Berger–Leighton's "bonds".
 */
export function chainBonds(seq: Residue[]): number {
  let c = 0;
  for (let i = 0; i + 1 < seq.length; i++) if (seq[i] === 'H' && seq[i + 1] === 'H') c++;
  return c;
}

/**
 * An upper bound on the number of contacts of any complete fold.
 * Each H can have at most z−2 non-chain neighbours (z−1 at the two ends of the string).
 * On a bipartite lattice contacts join residues of opposite parity, so the bound is the
 * smaller of the two parity classes' totals (the parity bound of Hart and Istrail);
 * otherwise it is half the total.
 */
export function upperBound(lattice: Lattice, seq: Residue[]): number {
  const z = degree(lattice);
  const n = seq.length;
  const free = (i: number) => z - (i === 0 || i === n - 1 ? 1 : 2);
  if (n < 2) return 0;
  if (lattice.bipartite) {
    let even = 0;
    let odd = 0;
    for (let i = 0; i < n; i++) if (seq[i] === 'H') (i % 2 === 0 ? (even += free(i)) : (odd += free(i)));
    return Math.min(even, odd);
  }
  let total = 0;
  for (let i = 0; i < n; i++) if (seq[i] === 'H') total += free(i);
  return Math.floor(total / 2);
}

/**
 * Most pairs of neighbouring nodes that k nodes can have, on the square and cubic lattices
 * (null on the others). Along one line of the grid, m nodes make at most m − 1 pairs, so k
 * nodes make at most d·k minus the number of lines that meet them. On the square lattice the
 * nodes fit in the rows × columns they meet, so rows + columns ≥ min{a + b : ab ≥ k}. On the
 * cubic lattice the Loomis–Whitney inequality gives k² ≤ Lx·Ly·Lz for the numbers of lines
 * meeting them in the three directions, so Lx + Ly + Lz ≥ min{a + b + c : abc ≥ k²}.
 * A square or a cube reaches the bound (2×2: 4 pairs, 2×2×2: 12, 3×3×3: 54).
 */
export function maxPairs(lattice: Lattice, k: number): number | null {
  if (k <= 1) return lattice.id === 'square' || lattice.id === 'cubic' ? 0 : null;
  if (lattice.id === 'square') return 2 * k - minLines(k, 2);
  if (lattice.id === 'cubic') return 3 * k - minLines(k * k, 3);
  return null;
}

/** min a + b (d = 2) or a + b + c (d = 3) over positive integers whose product is at least t */
function minLines(t: number, d: 2 | 3): number {
  let best = Infinity;
  if (d === 2) {
    for (let a = 1; a * a <= t || a === 1; a++) best = Math.min(best, a + Math.ceil(t / a));
    return best;
  }
  for (let a = 1; a * a * a <= t || a === 1; a++)
    for (let b = a; a * b * b <= t || b === a; b++) best = Math.min(best, a + b + Math.max(b, Math.ceil(t / (a * b))));
  return best;
}

/**
 * The cube bound on the contacts of any complete fold (square and cubic lattices; null on the
 * others): the H's have at most maxPairs neighbouring pairs, and the H–H pairs joined by the
 * chain (chainBonds) are among them but are not contacts. For PHHPPHHPPHHPPHHP on the cubic
 * lattice: 8 H's, at most 12 pairs, 4 joined by the chain, so at most 8 contacts.
 */
export function shapeBound(lattice: Lattice, seq: Residue[]): number | null {
  const k = seq.filter((r) => r === 'H').length;
  const pairs = maxPairs(lattice, k);
  return pairs === null ? null : Math.max(0, pairs - chainBonds(seq));
}

/**
 * Moves as a compact string: one character per step after residue 0. Lattices whose step
 * names are single characters use them (square: RLUD, cubic: RLUDFB, hexagonal: RLU at
 * one kind of point and RLD at the other); others use base-36 step indices (triangular,
 * FCC, diamond). Example on the square lattice: "RRUL".
 */
export function encodeMoves(lattice: Lattice, path: Vec[]): string {
  const single = singleCharNames(lattice);
  let out = '';
  for (let k = 1; k < path.length; k++) {
    const i = stepIndex(lattice, path[k - 1], path[k]);
    out += single ? stepNamesAt(lattice, path[k - 1])[i] : i.toString(36);
  }
  return out;
}

/**
 * Step indices of a move string, read from the origin (index k = the k-th step at the point
 * reached so far). An unknown character gives -1; on a lattice with two kinds of points the
 * moves after it are not read (the walk's position is lost).
 */
export function decodeMoves(lattice: Lattice, moves: string): number[] {
  const single = singleCharNames(lattice);
  if (!lattice.stepsAt) {
    const names = lattice.stepNames.map((n) => n.toUpperCase());
    return [...moves].map((c) => (single ? names.indexOf(c.toUpperCase()) : parseInt(c, 36)));
  }
  const out: number[] = [];
  let v: number[] = lattice.steps[0].map(() => 0);
  for (const c of moves) {
    const names = stepNamesAt(lattice, v);
    const k = single ? names.findIndex((n) => n.toUpperCase() === c.toUpperCase()) : parseInt(c, 36);
    const s = k >= 0 ? stepsAt(lattice, v)[k] : undefined;
    if (!s) {
      out.push(-1);
      break;
    }
    out.push(k);
    v = v.map((x, i) => x + s[i]);
  }
  return out;
}

function singleCharNames(lattice: Lattice): boolean {
  const kinds = lattice.stepsAt ? [lattice.steps[0].map(() => 0), lattice.steps[0]] : [lattice.steps[0].map(() => 0)];
  return kinds.every((v) => stepNamesAt(lattice, v).every((s) => s.length === 1));
}
