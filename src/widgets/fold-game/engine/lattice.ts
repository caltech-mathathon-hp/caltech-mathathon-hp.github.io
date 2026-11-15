/**
 * Lattices. A lattice is a set of integer points with a list of unit steps; it knows how to
 * draw its points in Euclidean space. Adding a lattice = adding one object here and
 * registering it in LATTICES; the fold logic and the renderers work for all of them.
 *
 * Coordinates are integer vectors ("lattice coordinates"). `embed` maps them to drawing
 * coordinates in which neighbouring points are at distance 1. 2D lattices return z = 0.
 *
 * Square, cubic, triangular and FCC are Bravais lattices: every point has the same steps.
 * Hexagonal (honeycomb) and diamond are not. Their points come in two kinds, and the steps
 * of a point depend on its kind (`stepsAt`). Every step joins points of different kinds, so
 * residue i of a fold that starts at the origin sits on a point of kind i mod 2.
 * Always use `stepsAt(l, v)`, `neighbours` and `stepIndex` rather than `l.steps` directly.
 */

export type Vec = readonly number[];

export interface Lattice {
  /** stable id used in props, level files and URLs (lower-case letters only) */
  id: string;
  /** display name, e.g. "Square lattice (2D)" */
  name: string;
  /** dimension of the drawing: 2 → SVG renderer, 3 → three.js renderer */
  dim: 2 | 3;
  /**
   * The unit steps at the origin; the neighbours of v are v + steps[k]. For a Bravais lattice
   * these are the steps at every point. Every point has steps.length neighbours.
   */
  steps: Vec[];
  /** one short label per step (keyboard help, move encoding), same order as steps */
  stepNames: string[];
  /**
   * Optional, for lattices with two kinds of points (hexagonal, diamond): the steps at v and
   * their names, in a fixed order per kind (index k means steps[k] at a point of that kind).
   * Points of the origin's kind return `steps` / `stepNames`. Return the same arrays every
   * time: renderers cache per array.
   */
  stepsAt?(v: Vec): Vec[];
  stepNamesAt?(v: Vec): string[];
  /** lattice coordinates → drawing coordinates (unit nearest-neighbour distance) */
  embed(v: Vec): [number, number, number];
  /**
   * Bipartite lattices (square, cubic, hexagonal, diamond) split into two colour classes and
   * every step changes the class. Then residue i always sits on class (i + class of residue 0)
   * mod 2, and H–H contacts only join residues of opposite parity: this gives the parity bound.
   */
  bipartite: boolean;
  /**
   * Length of the shortest cycle: two residues can touch only if they are girth − 1 or more
   * apart along the string. Optional for backward compatibility; see girthOf.
   */
  girth?: number;
}

export const key = (v: Vec): string => v.join(',');
export const add = (a: Vec, b: Vec): number[] => a.map((x, i) => x + b[i]);
export const sub = (a: Vec, b: Vec): number[] => a.map((x, i) => x - b[i]);
export const eq = (a: Vec, b: Vec): boolean => a.length === b.length && a.every((x, i) => x === b[i]);

/** the steps at v (the same for every point of a Bravais lattice) */
export function stepsAt(l: Lattice, v: Vec): readonly Vec[] {
  return l.stepsAt ? l.stepsAt(v) : l.steps;
}

/** the names of the steps at v, in the order of stepsAt(l, v) */
export function stepNamesAt(l: Lattice, v: Vec): readonly string[] {
  return l.stepNamesAt ? l.stepNamesAt(v) : l.stepNames;
}

/** length of the shortest cycle (default: 4 if bipartite, else 3) */
export function girthOf(l: Lattice): number {
  return l.girth ?? (l.bipartite ? 4 : 3);
}

/** number of neighbours of every point */
export function degree(l: Lattice): number {
  return l.steps.length;
}

export function neighbours(l: Lattice, v: Vec): number[][] {
  return stepsAt(l, v).map((s) => add(v, s));
}

/** index of the step u → v among stepsAt(l, u), or -1 if u and v are not neighbours */
export function stepIndex(l: Lattice, u: Vec, v: Vec): number {
  const d = sub(v, u);
  return stepsAt(l, u).findIndex((s) => eq(s, d));
}

/** v + the k-th step at v, or null if there is no such step */
export function stepFrom(l: Lattice, v: Vec, k: number): number[] | null {
  const s = stepsAt(l, v)[k];
  return s ? add(v, s) : null;
}

export const square: Lattice = {
  id: 'square',
  name: 'Square lattice (2D)',
  dim: 2,
  steps: [
    [1, 0],
    [-1, 0],
    [0, 1],
    [0, -1],
  ],
  stepNames: ['R', 'L', 'U', 'D'],
  embed: (v) => [v[0], v[1], 0],
  bipartite: true,
  girth: 4,
};

export const cubic: Lattice = {
  id: 'cubic',
  name: 'Cubic lattice (3D)',
  dim: 3,
  steps: [
    [1, 0, 0],
    [-1, 0, 0],
    [0, 1, 0],
    [0, -1, 0],
    [0, 0, 1],
    [0, 0, -1],
  ],
  // x: right/left, y: up/down, z: forward (towards the viewer)/back
  stepNames: ['R', 'L', 'U', 'D', 'F', 'B'],
  embed: (v) => [v[0], v[1], v[2]],
  bipartite: true,
  girth: 4,
};

const S3 = Math.sqrt(3) / 2;
/** Triangular lattice (each point has 6 neighbours). Not bipartite: odd cycles exist. */
export const triangular: Lattice = {
  id: 'triangular',
  name: 'Triangular lattice (2D)',
  dim: 2,
  steps: [
    [1, 0],
    [-1, 0],
    [0, 1],
    [0, -1],
    [-1, 1],
    [1, -1],
  ],
  stepNames: ['E', 'W', 'NE', 'SW', 'NW', 'SE'],
  embed: (v) => [v[0] + v[1] / 2, v[1] * S3, 0],
  bipartite: false,
  girth: 3,
};

const R2 = Math.SQRT1_2;
/** Face-centred cubic lattice: points of Z³ with even coordinate sum, 12 neighbours. */
export const fcc: Lattice = {
  id: 'fcc',
  name: 'Face-centred cubic lattice (3D)',
  dim: 3,
  steps: (() => {
    const out: number[][] = [];
    for (const [i, j] of [
      [0, 1],
      [0, 2],
      [1, 2],
    ])
      for (const a of [1, -1])
        for (const b of [1, -1]) {
          const s = [0, 0, 0];
          s[i] = a;
          s[j] = b;
          out.push(s);
        }
    return out;
  })(),
  stepNames: Array.from({ length: 12 }, (_, i) => String(i + 1)),
  embed: (v) => [v[0] * R2, v[1] * R2, v[2] * R2],
  bipartite: false,
  girth: 3,
};

/** kind of a point of a two-kind lattice: 0 for the origin's kind, 1 for the other */
const odd = (x: number) => ((x % 2) + 2) % 2;

/**
 * Hexagonal (honeycomb) lattice, 3 neighbours. Coordinates: all of Z², as a "brick wall".
 * Every point has a left and a right neighbour, (x − 1, y) and (x + 1, y). Points with x + y
 * even (kind 0, the origin's) also have (x, y + 1) above; points with x + y odd have (x, y − 1)
 * below. The rows are drawn as zigzags: kind 0 is raised by 1/4 and kind 1 lowered by 1/4.
 */
const HEX_STEPS: Vec[][] = [
  [
    [1, 0],
    [-1, 0],
    [0, 1],
  ],
  [
    [1, 0],
    [-1, 0],
    [0, -1],
  ],
];
const HEX_NAMES = [
  ['R', 'L', 'U'],
  ['R', 'L', 'D'],
];
export const hexagonal: Lattice = {
  id: 'hexagonal',
  name: 'Hexagonal lattice (2D)',
  dim: 2,
  steps: HEX_STEPS[0],
  stepNames: HEX_NAMES[0],
  stepsAt: (v) => HEX_STEPS[odd(v[0] + v[1])],
  stepNamesAt: (v) => HEX_NAMES[odd(v[0] + v[1])],
  embed: (v) => [v[0] * S3, 1.5 * v[1] + (odd(v[0] + v[1]) ? -0.25 : 0.25), 0],
  bipartite: true,
  girth: 6,
};

/**
 * Diamond lattice, 4 neighbours. Coordinates: points of Z³ with all coordinates even and sum
 * ≡ 0 (mod 4) (kind 0, the origin's), and those points + (1, 1, 1) (kind 1, all coordinates
 * odd). Kind 0 steps to the corners of a tetrahedron, (1, 1, 1), (1, −1, −1), (−1, 1, −1),
 * (−1, −1, 1); kind 1 steps by the opposite vectors. Step k at either kind is the same bond
 * direction up to sign. Drawn at scale 1/√3, the usual diamond cubic cell.
 */
const TETRA: Vec[] = [
  [1, 1, 1],
  [1, -1, -1],
  [-1, 1, -1],
  [-1, -1, 1],
];
const DIA_STEPS: Vec[][] = [TETRA, TETRA.map((s) => s.map((x) => -x))];
const DIA_NAMES = ['+++', '+--', '-+-', '--+'];
const R3 = 1 / Math.sqrt(3);
export const diamond: Lattice = {
  id: 'diamond',
  name: 'Diamond lattice (3D)',
  dim: 3,
  steps: DIA_STEPS[0],
  stepNames: DIA_NAMES,
  stepsAt: (v) => DIA_STEPS[odd(v[0])],
  stepNamesAt: () => DIA_NAMES,
  embed: (v) => [v[0] * R3, v[1] * R3, v[2] * R3],
  bipartite: true,
  girth: 6,
};

export const LATTICES: Record<string, Lattice> = { square, cubic, triangular, fcc, hexagonal, diamond };

export function getLattice(id: string): Lattice {
  const l = LATTICES[id];
  if (!l) throw new Error(`unknown lattice "${id}" (known: ${Object.keys(LATTICES).join(', ')})`);
  return l;
}
