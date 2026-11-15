/**
 * Levels of the folding game: one JSON file per level in this folder, picked up automatically.
 * Add a level = add a file. The game lists the levels of the lattice the reader has chosen,
 * numbered by `order` (so keep the levels of one lattice in a block of `order` values).
 *
 * {
 *   "id": "first-contact",            stable id (URLs, the `level` prop); equals the file name
 *   "order": 10,                      position in the list of its lattice
 *   "group": "Square lattice (2D)",   the set the level belongs to (for people editing the files)
 *   "title": "A first contact",
 *   "lattice": "square",              square | cubic | triangular | fcc
 *   "sequence": "HPPH",
 *   "best": 1,                        best score known (contacts, the game's convention)
 *   "optimal": true,                  true if no fold can beat `best`
 *   "bestKind": "computed",           how we know: proved (argument in bestSource) |
 *                                     computed (scripts/hp-optimum.ts, exhaustive) | cited
 *   "bestSource": "…",                one line: the argument, the script run, or the reference
 *   "intro": "…",                     one or two sentences under the title: the goal
 *   "hint": "…",                      optional, shown on request
 *   "solution": "RUL"                 moves of a fold scoring `best` ("Show solution"); every
 *                                     level should have one (levels.test.ts checks it scores `best`)
 * }
 *
 * The game also uses `best` and `solution` whenever the reader plays the string of a level on
 * its lattice, e.g. the compact game of the intro page, which shows no level list.
 */
export interface Level {
  id: string;
  order: number;
  group: string;
  title: string;
  lattice: string;
  sequence: string;
  best: number;
  optimal: boolean;
  bestKind: 'proved' | 'computed' | 'cited';
  bestSource: string;
  intro: string;
  hint?: string;
  solution?: string;
}

const modules = import.meta.glob<Level>('./*.json', { eager: true, import: 'default' });

export const LEVELS: Level[] = Object.values(modules).sort((a, b) => a.order - b.order);

export function getLevel(id: string | undefined | null): Level | undefined {
  return id ? LEVELS.find((l) => l.id === id) : undefined;
}

/** the level with this lattice and string, if any (strings compared without spaces, upper case) */
export function findLevel(lattice: string, sequence: string): Level | undefined {
  const s = sequence.toUpperCase().replace(/[^HP]/g, '');
  return LEVELS.find((l) => l.lattice === lattice && l.sequence === s);
}
