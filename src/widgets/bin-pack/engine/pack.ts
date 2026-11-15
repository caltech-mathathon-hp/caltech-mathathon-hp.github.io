/**
 * Bin packing, as Berger and Leighton use it (§2, p. 31): K bins of capacity B, items of
 * even sizes s(u) with Σ s(u) = K·B. A packing puts every item into a bin so that each bin
 * is filled to exactly B. Since the sizes add up to K·B, that is the same as packing every
 * item without overfilling a bin.
 *
 * A state lists, for each bin, its items in the order they went in (bins never overflow).
 * No DOM code here, so it runs (and is tested) in Node.
 */

export interface Instance {
  /** number of bins, K */
  bins: number;
  /** capacity of each bin, B */
  capacity: number;
  /** sizes of the items; item u has size sizes[u] */
  sizes: number[];
}

/** for each item, its bin (0-based) or null when it is not in a bin */
export type Assignment = (number | null)[];

/** what is wrong with an instance, or null. `even`: also require even sizes and capacity */
export function instanceError(inst: Instance, even = false): string | null {
  const { bins, capacity, sizes } = inst;
  if (!Number.isInteger(bins) || bins < 1) return 'The number of bins must be a positive whole number.';
  if (!Number.isInteger(capacity) || capacity < 1) return 'The capacity must be a positive whole number.';
  if (!sizes.length) return 'There are no items.';
  if (sizes.some((s) => !Number.isInteger(s) || s < 1)) return 'Every size must be a positive whole number.';
  if (sizes.some((s) => s > capacity)) return 'An item is larger than a bin.';
  const total = sizes.reduce((a, b) => a + b, 0);
  if (total !== bins * capacity) return `The sizes add up to ${total}, not ${bins} × ${capacity} = ${bins * capacity}.`;
  if (even && (capacity % 2 || sizes.some((s) => s % 2))) return 'Berger and Leighton use even sizes only.';
  return null;
}

export const total = (inst: Instance) => inst.bins * inst.capacity;

export class PackState {
  readonly inst: Instance;
  /** contents[b] = the items in bin b, in the order they went in */
  readonly contents: number[][];

  constructor(inst: Instance, contents?: number[][]) {
    this.inst = inst;
    this.contents = contents ? contents.map((c) => [...c]) : Array.from({ length: inst.bins }, () => []);
  }

  static fromAssignment(inst: Instance, a: Assignment): PackState {
    const s = new PackState(inst);
    a.forEach((b, u) => {
      if (b !== null && b !== undefined && !s.place(u, b)) throw new Error(`item ${u} does not fit in bin ${b}`);
    });
    return s;
  }

  clone(): PackState {
    return new PackState(this.inst, this.contents);
  }

  /** the bin of item u, or null */
  binOf(u: number): number | null {
    const b = this.contents.findIndex((c) => c.includes(u));
    return b < 0 ? null : b;
  }
  assignment(): Assignment {
    return this.inst.sizes.map((_, u) => this.binOf(u));
  }
  /** units used in bin b */
  load(b: number): number {
    return this.contents[b].reduce((a, u) => a + this.inst.sizes[u], 0);
  }
  free(b: number): number {
    return this.inst.capacity - this.load(b);
  }
  /** the first unit of bin b that item u takes or would take (items fill a bin from the left) */
  offset(b: number, u: number): number {
    let x = 0;
    for (const v of this.contents[b]) {
      if (v === u) return x;
      x += this.inst.sizes[v];
    }
    return x;
  }
  /** total size of the items in bins */
  packed(): number {
    return this.contents.reduce((a, _, b) => a + this.load(b), 0);
  }
  /** items not in a bin, in item order */
  loose(): number[] {
    const inBins = new Set(this.contents.flat());
    return this.inst.sizes.map((_, u) => u).filter((u) => !inBins.has(u));
  }
  /** can item u go into bin b (counting the room it frees if it is already in b)? */
  fits(u: number, b: number): boolean {
    if (b < 0 || b >= this.inst.bins) return false;
    const here = this.binOf(u) === b ? this.inst.sizes[u] : 0;
    return this.inst.sizes[u] <= this.free(b) + here;
  }
  /** every item is in a bin (so every bin is exactly full) */
  get complete(): boolean {
    return this.loose().length === 0;
  }
  /** some item is loose and none of the loose items fits in any bin */
  get stuck(): boolean {
    const loose = this.loose();
    if (!loose.length) return false;
    const room = Math.max(...this.contents.map((_, b) => this.free(b)));
    return loose.every((u) => this.inst.sizes[u] > room);
  }
  fullBins(): number {
    return this.contents.filter((_, b) => this.free(b) === 0).length;
  }

  // ---------- changes (return false and change nothing when not allowed) ----------
  /** put item u at the end of bin b (taking it out of its own bin first) */
  place(u: number, b: number): boolean {
    if (u < 0 || u >= this.inst.sizes.length || !this.fits(u, b)) return false;
    const from = this.binOf(u);
    if (from === b) return false;
    if (from !== null) this.contents[from].splice(this.contents[from].indexOf(u), 1);
    this.contents[b].push(u);
    return true;
  }
  /** take item u out of its bin */
  remove(u: number): boolean {
    const from = this.binOf(u);
    if (from === null) return false;
    this.contents[from].splice(this.contents[from].indexOf(u), 1);
    return true;
  }
  clear(): void {
    for (const c of this.contents) c.length = 0;
  }
}

/** "6 + 4" */
export const sumText = (inst: Instance, items: number[]) => items.map((u) => inst.sizes[u]).join(' + ');
