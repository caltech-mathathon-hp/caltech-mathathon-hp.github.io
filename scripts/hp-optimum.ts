/**
 * Exhaustive branch-and-bound search for the best fold of an HP string on a lattice.
 * Used to certify the "best" score of the levels of the folding game
 * (src/widgets/fold-game/levels/*.json, bestKind: "computed").
 *
 * Run (Node >= 23 runs TypeScript directly):
 *   node scripts/hp-optimum.ts square HPHPPHHPHPPHPHHPPHPH
 *   node scripts/hp-optimum.ts cubic PHHPPHHPPHHPPHHP --atleast 8 --time 600
 *
 * Score = number of H-H contacts (pairs of H's on neighbouring lattice points that are not
 * consecutive in the string), the convention of the game. The search visits every
 * self-avoiding walk up to the symmetries of the lattice that fix the first step, pruning a
 * branch when even an optimistic bound cannot beat the best score found so far. If it
 * finishes, the printed score is the OPTIMUM (proved by exhaustion); if the time limit stops
 * it, the score is only a lower bound and the output says so.
 *
 * --atleast K seeds the search with "best so far = K-1": faster when K is known to be
 * reachable; if no fold reaches K the output says so and the optimum is below K.
 */
import { getLattice, encodeMoves } from '../src/widgets/fold-game/engine/index.ts';

const args = process.argv.slice(2);
const flag = (name: string, def: number) => {
  const i = args.indexOf(name);
  return i >= 0 ? Number(args[i + 1]) : def;
};
const [latticeId, seqArg] = args.filter((a, i) => !a.startsWith('--') && !args[i - 1]?.startsWith('--'));
if (!latticeId || !seqArg) {
  console.error('usage: node scripts/hp-optimum.ts <square|cubic|triangular|fcc> <HP string> [--atleast K] [--time seconds]');
  process.exit(1);
}
const lattice = getLattice(latticeId);
const seq = seqArg.toUpperCase().replace(/[^HP]/g, '');
const n = seq.length;
const timeLimit = flag('--time', 300) * 1000;
const atLeast = flag('--atleast', 0);

// ---- grid: lattice points packed into integers ----
const d = lattice.steps[0].length;
const R = n + 2; // coordinates stay in [-n, n]
const W = 2 * R + 1;
const stride = Array.from({ length: d }, (_, i) => W ** i);
const encode = (v: number[]) => v.reduce((s, x, i) => s + (x + R) * stride[i], 0);
const off = lattice.steps.map((s) => s.reduce((acc, x, i) => acc + x * stride[i], 0));
const z = off.length;
const occ = new Int32Array(W ** d).fill(-1);

const isH = [...seq].map((c) => c === 'H');
// capacity of a residue: how many contacts it can still make at most
const cap = (i: number) => (isH[i] ? z - (i === 0 || i === n - 1 ? 1 : 2) : 0);
// suffix sums of capacities of unplaced H's, by parity class
const suf = [new Int32Array(n + 1), new Int32Array(n + 1)];
for (let i = n - 1; i >= 0; i--) {
  suf[0][i] = suf[0][i + 1] + (i % 2 === 0 ? cap(i) : 0);
  suf[1][i] = suf[1][i + 1] + (i % 2 === 1 ? cap(i) : 0);
}
const bip = lattice.bipartite;

// ---- symmetry breaking (square, cubic, triangular): fix the first step and reflections ----
// square/cubic: first step R; first step off the x-axis is U; first step off the xy-plane is F.
// triangular: first step E; first step off the E-W line goes up (NE or NW).
const name = (k: number) => lattice.stepNames[k];
type Sym = (k: number, state: number) => { ok: boolean; state: number };
const sym: Sym = (() => {
  if (latticeId === 'square' || latticeId === 'cubic')
    return (k, st) => {
      const nm = name(k);
      if (st === 0) return { ok: nm === 'R' || nm === 'U', state: nm === 'U' ? 1 : 0 };
      if (st === 1 && d === 3) return { ok: nm !== 'B', state: nm === 'F' ? 2 : 1 };
      return { ok: true, state: st };
    };
  if (latticeId === 'triangular')
    return (k, st) => {
      const nm = name(k);
      if (st === 0) return { ok: nm === 'E' || nm === 'NE' || nm === 'NW', state: nm === 'E' ? 0 : 1 };
      return { ok: true, state: st };
    };
  return (_k, st) => ({ ok: true, state: st });
})();

// ---- search ----
let best = atLeast > 0 ? atLeast - 1 : -1;
let bestPath: number[] | null = null;
const path = new Int32Array(n); // path[k] = step index from residue k-1 to k
let nodes = 0;
let stopped = false;
const t0 = Date.now();
// free neighbour sites of placed H's, by parity class (an optimistic count of contacts left)
const placedCap = [0, 0];

function freeAround(p: number): number {
  let f = 0;
  for (let s = 0; s < z; s++) if (occ[p + off[s]] < 0) f++;
  return f;
}

function rec(k: number, pos: number, score: number, st: number) {
  if (stopped) return;
  if ((++nodes & 0xfffff) === 0 && Date.now() - t0 > timeLimit) {
    stopped = true;
    return;
  }
  if (k === n) {
    if (score > best) {
      best = score;
      bestPath = Array.from(path.slice(1));
    }
    return;
  }
  // every future contact has an unplaced end; on a bipartite lattice it joins the two classes
  const uE = suf[0][k];
  const uO = suf[1][k];
  let bound = uE + uO;
  if (bip) bound = Math.min(bound, uE + placedCap[0], uO + placedCap[1]);
  else bound = Math.min(bound, Math.floor((uE + uO + placedCap[0] + placedCap[1]) / 2));
  if (score + bound <= best) return;

  for (let s = 0; s < z; s++) {
    if (k === 1 && s !== 0) break; // the first step is fixed (every lattice here is symmetric enough)
    const sy = sym(s, st);
    if (!sy.ok) continue;
    const q = pos + off[s];
    if (occ[q] >= 0) continue;
    let gain = 0;
    // placing q removes one free site from each H around it
    for (let t = 0; t < z; t++) {
      const j = occ[q + off[t]];
      if (j >= 0 && isH[j]) {
        placedCap[j & 1]--;
        if (isH[k] && j !== k - 1) gain++;
      }
    }
    occ[q] = k;
    path[k] = s;
    const f = isH[k] ? freeAround(q) : 0;
    placedCap[k & 1] += f;
    rec(k + 1, q, score + gain, sy.state);
    placedCap[k & 1] -= f;
    occ[q] = -1;
    for (let t = 0; t < z; t++) {
      const j = occ[q + off[t]];
      if (j >= 0 && isH[j]) placedCap[j & 1]++;
    }
  }
}

const origin = encode(lattice.steps[0].map(() => 0));
occ[origin] = 0;
if (isH[0]) placedCap[0] += z;
rec(1, origin, 0, 0);

const secs = ((Date.now() - t0) / 1000).toFixed(1);
let moves = '';
if (bestPath) {
  const pts: number[][] = [lattice.steps[0].map(() => 0)];
  for (const s of bestPath as number[]) pts.push(pts[pts.length - 1].map((x, i) => x + lattice.steps[s][i]));
  moves = encodeMoves(lattice, pts);
}
const result = {
  lattice: latticeId,
  sequence: seq,
  length: n,
  score: bestPath ? best : null,
  moves: bestPath ? moves : null,
  exhaustive: !stopped,
  verdict: stopped
    ? `time limit reached: ${bestPath ? `best found ${best} (a lower bound only)` : 'nothing found'}`
    : bestPath
      ? `optimum = ${best} (exhaustive search)`
      : `no fold with ${atLeast} or more contacts (exhaustive search)`,
  nodes,
  seconds: Number(secs),
};
console.log(JSON.stringify(result, null, 2));
