/**
 * An exact solver for small bin-packing instances: it finds a packing that puts the most total
 * size into the bins. When that total is K·B, every item is packed and the answer is yes;
 * otherwise no packing exists and the result shows the best one can do.
 *
 * Depth-first search over the items, largest first. Each item goes into a bin where it fits or
 * stays out. Two bins with the same free space are interchangeable, so only the first is tried.
 * A branch stops when even packing every remaining item could not beat the best found.
 * The levels are small (at most a dozen items), so this takes well under a millisecond there.
 */
import { type Assignment, type Instance, PackState } from './pack.ts';

export interface SolveResult {
  /** the best packing found: bin of each item, or null for an item left out */
  assignment: Assignment;
  /** its total size in bins */
  packed: number;
  /** every item is packed (the answer is yes) */
  complete: boolean;
  /** the search finished, so `packed` is the most possible (and `complete: false` means no) */
  exhaustive: boolean;
  /** search nodes visited */
  nodes: number;
}

export interface SolveOptions {
  /** items already in bins stay where they are (default: start from empty bins) */
  from?: Assignment;
  /** stop after this many nodes (default 2,000,000) */
  maxNodes?: number;
}

export function solve(inst: Instance, opts: SolveOptions = {}): SolveResult {
  const { bins: K, capacity: B, sizes } = inst;
  const start = opts.from ? PackState.fromAssignment(inst, opts.from) : new PackState(inst);
  const maxNodes = opts.maxNodes ?? 2_000_000;
  const free = start.contents.map((_, b) => start.free(b));
  const fixed = start.assignment();
  // loose items, largest first (ties: item order, so the result is deterministic)
  const order = start.loose().sort((u, v) => sizes[v] - sizes[u] || u - v);
  // rest[i] = total size of order[i..]
  const rest = new Array(order.length + 1).fill(0);
  for (let i = order.length - 1; i >= 0; i--) rest[i] = rest[i + 1] + sizes[order[i]];

  const cur: Assignment = [...fixed];
  let best: Assignment = [...fixed];
  let bestPacked = start.packed();
  const goal = K * B;
  let nodes = 0;
  let aborted = false;

  const dfs = (i: number, packed: number): void => {
    if (bestPacked === goal || aborted) return;
    if (++nodes > maxNodes) {
      aborted = true;
      return;
    }
    if (packed > bestPacked) {
      bestPacked = packed;
      best = [...cur];
      if (packed === goal) return;
    }
    if (i === order.length) return;
    // bound: the free space and the remaining items both cap what can still go in
    const room = free.reduce((a, f) => a + f, 0);
    if (packed + Math.min(rest[i], room) <= bestPacked) return;
    const u = order[i];
    const s = sizes[u];
    const tried = new Set<number>();
    for (let b = 0; b < K; b++) {
      if (free[b] < s || tried.has(free[b])) continue;
      tried.add(free[b]);
      free[b] -= s;
      cur[u] = b;
      dfs(i + 1, packed + s);
      cur[u] = null;
      free[b] += s;
      if (bestPacked === goal || aborted) return;
    }
    // leave u out
    dfs(i + 1, packed);
  };
  dfs(0, bestPacked);

  return { assignment: best, packed: bestPacked, complete: bestPacked === goal, exhaustive: !aborted, nodes };
}

/** can the items already in bins stay there in some packing of every item? */
export function extendable(inst: Instance, from: Assignment): boolean | null {
  const r = solve(inst, { from });
  return r.complete ? true : r.exhaustive ? false : null;
}
