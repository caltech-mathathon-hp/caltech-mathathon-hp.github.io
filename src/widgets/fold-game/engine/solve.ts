/**
 * Exhaustive branch-and-bound search for an optimal fold, small enough to run in the browser.
 * The same search as scripts/hp-optimum.ts (which certifies the levels), written as a loop
 * with an explicit stack so that it can run in slices and stop after a budget:
 *
 *   const s = new Solver(square, 'HPHPPHHPHPPH');
 *   while (!s.run(50_000)) {}            // or solveAsync(...) to keep the page responsive
 *   s.best, s.moves()                     // the optimum (s.done: the search finished)
 *
 * It visits every self-avoiding walk up to the symmetries that fix the first step, and prunes
 * a branch when an optimistic count of the contacts still possible cannot beat the best fold
 * found so far. When it finishes, `best` is the optimum, proved by exhaustion.
 *
 * Lattices with two kinds of points (hexagonal, diamond): residue d sits on a point of kind
 * d mod 2 (every step changes the kind), so the search keeps one table of steps per kind.
 */
import { type Lattice, getLattice, stepsAt, degree } from './lattice.ts';
import { type Residue, parseSequence, encodeMoves } from './fold.ts';

export interface SolveResult {
  /** best score found (the optimum when `exhaustive`) */
  score: number;
  /** move string of a fold with that score (see encodeMoves) */
  moves: string;
  /** true if the search finished, so `score` is the optimum */
  exhaustive: boolean;
  /** search nodes visited */
  nodes: number;
}

export class Solver {
  readonly lattice: Lattice;
  readonly n: number;
  /** best score found so far (-1 before the first complete fold) */
  best = -1;
  /** search nodes visited so far */
  nodes = 0;
  /** true once the whole search space has been visited */
  done = false;

  private z: number;
  /** grid offsets of the steps at a point of kind 0 and of kind 1 (the same table for Bravais lattices) */
  private offs: [number[], number[]];
  private occ: Int32Array;
  private isH: boolean[];
  private suf: Int32Array[];
  private bip: boolean;
  private sym: (k: number, state: number) => number; // next state, or -1 if the step is excluded
  private placedCap = [0, 0];
  private pos: Int32Array;
  private iter: Int32Array;
  private gain: Int32Array;
  private fcap: Int32Array;
  private symState: Int32Array;
  private step: Int32Array;
  private bestSteps: number[] | null = null;
  private d = 1;
  private fresh = true;
  private score = 0;

  constructor(lattice: Lattice | string, sequence: Residue[] | string) {
    const lat = typeof lattice === 'string' ? getLattice(lattice) : lattice;
    const seq = typeof sequence === 'string' ? parseSequence(sequence) : sequence;
    this.lattice = lat;
    const n = (this.n = seq.length);
    const dim = lat.steps[0].length;
    const R = n + 2; // coordinates stay in [-n, n]
    const W = 2 * R + 1;
    const stride = Array.from({ length: dim }, (_, i) => W ** i);
    const offsetsAt = (v: readonly number[]) => stepsAt(lat, v).map((s) => s.reduce((acc, x, i) => acc + x * stride[i], 0));
    const off0 = offsetsAt(lat.steps[0].map(() => 0));
    this.offs = [off0, lat.stepsAt ? offsetsAt(lat.steps[0]) : off0];
    this.z = degree(lat);
    this.occ = new Int32Array(W ** dim).fill(-1);
    this.isH = seq.map((c) => c === 'H');
    const z = this.z;
    const cap = (i: number) => (this.isH[i] ? z - (i === 0 || i === n - 1 ? 1 : 2) : 0);
    this.suf = [new Int32Array(n + 1), new Int32Array(n + 1)];
    for (let i = n - 1; i >= 0; i--) {
      this.suf[0][i] = this.suf[0][i + 1] + (i % 2 === 0 ? cap(i) : 0);
      this.suf[1][i] = this.suf[1][i + 1] + (i % 2 === 1 ? cap(i) : 0);
    }
    this.bip = lat.bipartite;
    this.sym = symmetry(lat);
    this.pos = new Int32Array(n + 1);
    this.iter = new Int32Array(n + 1);
    this.gain = new Int32Array(n + 1);
    this.fcap = new Int32Array(n + 1);
    this.symState = new Int32Array(n + 1);
    this.step = new Int32Array(n + 1);

    const origin = stride.reduce((s, x) => s + R * x, 0);
    this.pos[0] = origin;
    if (n === 0) {
      this.done = true;
      return;
    }
    this.occ[origin] = 0;
    if (this.isH[0]) this.placedCap[0] += z;
    if (n === 1) {
      this.best = 0;
      this.bestSteps = [];
      this.done = true;
    }
  }

  /** search for at most `maxNodes` more nodes; returns true when the search has finished */
  run(maxNodes: number): boolean {
    if (this.done) return true;
    const { n, z, offs, occ, isH, suf, pos, iter, gain, fcap, symState, step } = this;
    const pc = this.placedCap;
    const stop = this.nodes + maxNodes;
    let d = this.d;
    let fresh = this.fresh;
    let score = this.score;
    for (;;) {
      if (fresh) {
        if (this.nodes >= stop) break;
        fresh = false;
        this.nodes++;
        if (d === n) {
          if (score > this.best) {
            this.best = score;
            this.bestSteps = Array.from(step.subarray(1, n));
          }
          iter[d] = z;
        } else {
          // every future contact has an unplaced end; on a bipartite lattice it joins the two classes
          const uE = suf[0][d];
          const uO = suf[1][d];
          let bound = uE + uO;
          if (this.bip) bound = Math.min(bound, uE + pc[0], uO + pc[1]);
          else bound = Math.min(bound, Math.floor((uE + uO + pc[0] + pc[1]) / 2));
          iter[d] = score + bound <= this.best ? z : 0;
        }
      }
      // try the next child of the node with d residues placed (it places residue d)
      let advanced = false;
      while (iter[d] < z) {
        const s = iter[d]++;
        if (d === 1 && s !== 0) {
          iter[d] = z; // the first step is fixed
          break;
        }
        const st = this.sym(s, symState[d - 1]);
        if (st < 0) continue;
        const q = pos[d - 1] + offs[(d - 1) & 1][s];
        if (occ[q] >= 0) continue;
        const off = offs[d & 1];
        let g = 0;
        // placing q removes one free side from each H around it
        for (let t = 0; t < z; t++) {
          const j = occ[q + off[t]];
          if (j >= 0 && isH[j]) {
            pc[j & 1]--;
            if (isH[d] && j !== d - 1) g++;
          }
        }
        occ[q] = d;
        let f = 0;
        if (isH[d]) for (let t = 0; t < z; t++) if (occ[q + off[t]] < 0) f++;
        pc[d & 1] += f;
        pos[d] = q;
        gain[d] = g;
        fcap[d] = f;
        symState[d] = st;
        step[d] = s;
        score += g;
        d++;
        fresh = true;
        advanced = true;
        break;
      }
      if (advanced) continue;
      // all children done: take back residue d - 1
      if (d === 1) {
        this.done = true;
        break;
      }
      const r = d - 1;
      const q = pos[r];
      const off = offs[r & 1];
      pc[r & 1] -= fcap[r];
      occ[q] = -1;
      score -= gain[r];
      for (let t = 0; t < z; t++) {
        const j = occ[q + off[t]];
        if (j >= 0 && isH[j]) pc[j & 1]++;
      }
      d = r;
    }
    this.d = d;
    this.fresh = fresh;
    this.score = score;
    return this.done;
  }

  /** move string of the best fold found (empty before the first complete fold) */
  moves(): string {
    if (!this.bestSteps) return '';
    const lat = this.lattice;
    const pts: number[][] = [lat.steps[0].map(() => 0)];
    for (const k of this.bestSteps) {
      const v = pts[pts.length - 1];
      const s = stepsAt(lat, v)[k];
      pts.push(v.map((x, i) => x + s[i]));
    }
    return encodeMoves(lat, pts);
  }

  result(): SolveResult {
    return { score: Math.max(0, this.best), moves: this.moves(), exhaustive: this.done, nodes: this.nodes };
  }
}

/**
 * Symmetry breaking (as in scripts/hp-optimum.ts). Square and cubic: the first step is R; the
 * first step off the x-axis is U; the first step off the xy-plane is F. Triangular: the first
 * step is E; the first step off the E–W line goes up (NE or NW).
 * Hexagonal: the first step is R; the second is R too (the mirror through the first bond swaps
 * it with D). Diamond: the first step is +++ (index 0); the rotations about that bond permute
 * the three next steps, so the second is index 3, which keeps the walk in the plane x = y. The
 * mirror x ↔ y fixes that plane and swaps steps 1 and 2: the first step out of the plane is 1.
 * Other lattices: only the first step is fixed.
 * Returns the next state, or -1 when the step is the image of an allowed one.
 */
function symmetry(lat: Lattice): (k: number, state: number) => number {
  const name = (k: number) => lat.stepNames[k];
  const dim = lat.steps[0].length;
  if (lat.id === 'square' || lat.id === 'cubic')
    return (k, st) => {
      const nm = name(k);
      if (st === 0) return nm === 'R' ? 0 : nm === 'U' ? 1 : -1;
      if (st === 1 && dim === 3) return nm === 'B' ? -1 : nm === 'F' ? 2 : 1;
      return st;
    };
  if (lat.id === 'triangular')
    return (k, st) => {
      const nm = name(k);
      if (st === 0) return nm === 'E' ? 0 : nm === 'NE' || nm === 'NW' ? 1 : -1;
      return st;
    };
  if (lat.id === 'hexagonal')
    // states: 0 before the first step, 1 before the second, 2 free
    return (k, st) => (st === 0 ? 1 : st === 1 ? (name(k) === 'R' ? 2 : -1) : st);
  if (lat.id === 'diamond')
    // states: 0 before the first step, 1 before the second, 2 in the plane x = y, 3 free
    return (k, st) => {
      if (st === 0) return 1;
      if (st === 1) return k === 3 ? 2 : -1;
      if (st === 2) return k === 0 || k === 3 ? 2 : k === 1 ? 3 : -1;
      return st;
    };
  return (_k, st) => st;
}

/** run the search to the end (or until `maxNodes` nodes), synchronously */
export function solve(lattice: Lattice | string, sequence: Residue[] | string, maxNodes = Infinity): SolveResult {
  const s = new Solver(lattice, sequence);
  s.run(maxNodes);
  return s.result();
}

/**
 * Run the search in short slices so that the page stays responsive. Resolves with the result
 * when the search finishes or `timeMs` has passed (then `exhaustive` is false).
 */
export function solveAsync(
  lattice: Lattice | string,
  sequence: Residue[] | string,
  { timeMs = 3000, sliceMs = 14 }: { timeMs?: number; sliceMs?: number } = {},
): { promise: Promise<SolveResult>; cancel: () => void } {
  const s = new Solver(lattice, sequence);
  let cancelled = false;
  let timer: ReturnType<typeof setTimeout> | undefined;
  const t0 = performance.now();
  const promise = new Promise<SolveResult>((resolve) => {
    const slice = () => {
      if (cancelled) return;
      const end = performance.now() + sliceMs;
      while (!s.run(20000) && performance.now() < end) {}
      if (s.done || performance.now() - t0 > timeMs) resolve(s.result());
      else timer = setTimeout(slice, 0);
    };
    timer = setTimeout(slice, 0);
  });
  return {
    promise,
    cancel: () => {
      cancelled = true;
      clearTimeout(timer);
    },
  };
}
