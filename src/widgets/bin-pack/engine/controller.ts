/**
 * PackController: the state of the bin-packing game, shared by the UI, with an undo history,
 * the selected item and change notifications (the same shape as the folding game's
 * GameController). No DOM code here, so it runs (and is tested) in Node.
 */
import { type Assignment, type Instance, PackState } from './pack.ts';

export type Listener = (c: PackController) => void;

export class PackController {
  inst: Instance;
  state: PackState;
  /** the item picked up by a click or a key (null = none); the next click on a bin puts it there */
  selected: number | null = null;
  /** increases on every change; handy as a render key */
  version = 0;

  private history: number[][][] = [];
  private listeners = new Set<Listener>();

  constructor(inst: Instance, from?: Assignment) {
    this.inst = inst;
    this.state = from ? PackState.fromAssignment(inst, from) : new PackState(inst);
  }

  get canUndo(): boolean {
    return this.history.length > 0;
  }

  /** a new instance: empty bins, no history */
  setInstance(inst: Instance): void {
    this.inst = inst;
    this.state = new PackState(inst);
    this.history = [];
    this.selected = null;
    this.changed();
  }

  /** put item u into bin b (from the loose items or from another bin) */
  place(u: number, b: number): boolean {
    const snap = this.snapshot();
    if (!this.state.place(u, b)) return false;
    this.history.push(snap);
    this.selected = null;
    this.changed();
    return true;
  }
  /** take item u out of its bin */
  remove(u: number): boolean {
    const snap = this.snapshot();
    if (!this.state.remove(u)) return false;
    this.history.push(snap);
    this.selected = null;
    this.changed();
    return true;
  }
  undo(): boolean {
    const snap = this.history.pop();
    if (!snap) return false;
    this.state = new PackState(this.inst, snap);
    this.selected = null;
    this.changed();
    return true;
  }
  /** every item back out (one undo step) */
  reset(): boolean {
    if (this.state.packed() === 0) return false;
    this.history.push(this.snapshot());
    this.state.clear();
    this.selected = null;
    this.changed();
    return true;
  }
  /** replace the bins by these contents (no undo step: used to show a solution and come back) */
  load(contents: number[][]): void {
    this.state = new PackState(this.inst, contents);
    this.selected = null;
    this.changed();
  }
  snapshot(): number[][] {
    return this.state.contents.map((c) => [...c]);
  }
  select(u: number | null): void {
    if (u === this.selected) return;
    this.selected = u;
    this.changed();
  }

  subscribe(fn: Listener): () => void {
    this.listeners.add(fn);
    return () => this.listeners.delete(fn);
  }
  private changed(): void {
    this.version++;
    for (const fn of this.listeners) fn(this);
  }
}
