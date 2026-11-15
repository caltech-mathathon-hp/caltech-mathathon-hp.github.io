/**
 * GameController: the single source of truth that UI panels and renderers share.
 * It owns a Fold, an undo/redo history, a hover/focus state, a truncation preview and change
 * notifications. (The game shows undo only; redo stays for scripts and the dev harness.)
 * Renderers never mutate the fold directly; they call controller actions and redraw on
 * `subscribe`. No DOM code here, so it runs (and is tested) in Node.
 */
import { Fold, type Residue, parseSequence, upperBound, chainBonds, decodeMoves } from './fold.ts';
import { type Lattice, type Vec, getLattice } from './lattice.ts';

export interface ControllerOptions {
  lattice: Lattice | string;
  sequence: string;
  /** optional initial moves (see encodeMoves) */
  moves?: string;
}

export type Listener = (c: GameController) => void;

export class GameController {
  lattice: Lattice;
  seq: Residue[];
  fold: Fold;
  /** residue under the pointer / keyboard focus, shared between panels (null = none) */
  hover: number | null = null;
  /**
   * Preview of "go back to residue `cut`": the residues after it would be removed. Set while the
   * reader points at a residue in a way that would truncate (null = no preview). Cleared by every
   * change of the fold.
   */
  cut: number | null = null;
  /** increases on every change; handy as a render key */
  version = 0;

  private redoStack: number[][] = [];
  private listeners = new Set<Listener>();

  constructor(opts: ControllerOptions) {
    this.lattice = typeof opts.lattice === 'string' ? getLattice(opts.lattice) : opts.lattice;
    this.seq = parseSequence(opts.sequence);
    this.fold = new Fold(this.lattice, this.seq);
    if (opts.moves) this.applyMoves(opts.moves);
  }

  // ---------- reading ----------
  get score(): number {
    return this.fold.score();
  }
  /** an upper bound on the score of any complete fold of this string on this lattice */
  get bound(): number {
    return upperBound(this.lattice, this.seq);
  }
  /** Berger–Leighton's bond count = contacts + this constant */
  get chainBonds(): number {
    return chainBonds(this.seq);
  }
  get complete(): boolean {
    return this.fold.complete;
  }
  get stuck(): boolean {
    return this.fold.stuck;
  }
  get canUndo(): boolean {
    return this.fold.placed > 1;
  }
  get canRedo(): boolean {
    return this.redoStack.length > 0;
  }
  options(): number[][] {
    return this.fold.options();
  }

  // ---------- actions ----------
  /** place the next residue at v (must be a free neighbour of the last one) */
  extendTo(v: Vec): boolean {
    const ok = this.fold.extendTo(v);
    if (ok) {
      this.redoStack = [];
      this.changed();
    }
    return ok;
  }

  /** place the next residue along the k-th step at the last residue (see stepsAt) */
  extendStep(k: number): boolean {
    const ok = this.fold.extendStep(k);
    if (ok) {
      this.redoStack = [];
      this.changed();
    }
    return ok;
  }

  undo(): boolean {
    const v = this.fold.last;
    if (!v || !this.fold.retract()) return false;
    this.redoStack.push(v);
    this.changed();
    return true;
  }

  redo(): boolean {
    const v = this.redoStack.pop();
    if (!v) return false;
    const ok = this.fold.extendTo(v);
    if (!ok) this.redoStack = [];
    this.changed();
    return ok;
  }

  /** back to residue 0 only */
  reset(): void {
    this.fold = new Fold(this.lattice, this.seq);
    this.redoStack = [];
    this.changed();
  }

  /** retract to the first k residues (k ≥ 1), e.g. when the user clicks residue k−1 */
  truncate(k: number): void {
    k = Math.max(1, k);
    const removed: number[][] = [];
    while (this.fold.placed > k) {
      removed.push(this.fold.last!);
      this.fold.retract();
    }
    if (removed.length) {
      this.redoStack = removed; // popped in reverse order by redo → original order
      this.changed();
    }
  }

  /** replace the fold by the one given by a move string (from the first residue) */
  applyMoves(moves: string): void {
    this.fold = new Fold(this.lattice, this.seq);
    for (const k of decodeMoves(this.lattice, moves)) if (!this.fold.extendStep(k)) break;
    this.redoStack = [];
    this.changed();
  }

  /** replace the fold by explicit positions (e.g. a precomputed construction) */
  loadPositions(positions: Vec[]): void {
    this.fold = Fold.fromPositions(this.lattice, this.seq, positions);
    this.redoStack = [];
    this.changed();
  }

  setSequence(sequence: string): void {
    this.seq = parseSequence(sequence);
    this.reset();
  }

  setLattice(lattice: Lattice | string): void {
    this.lattice = typeof lattice === 'string' ? getLattice(lattice) : lattice;
    this.reset();
  }

  setHover(i: number | null): void {
    if (i === this.hover) return;
    this.hover = i;
    this.emit();
  }

  /** preview of truncating after residue i (see `cut`); null clears it */
  setCut(i: number | null): void {
    if (i !== null && (i < 0 || i >= this.fold.placed - 1)) i = null;
    if (i === this.cut) return;
    this.cut = i;
    this.emit();
  }

  // ---------- notifications ----------
  subscribe(fn: Listener): () => void {
    this.listeners.add(fn);
    return () => this.listeners.delete(fn);
  }

  /** the fold changed: drop the truncation preview and notify */
  private changed() {
    this.cut = null;
    this.emit();
  }

  private emit() {
    this.version++;
    for (const fn of this.listeners) fn(this);
  }
}
