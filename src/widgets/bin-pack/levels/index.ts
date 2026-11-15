/**
 * Levels of the bin-packing game: one JSON file per level in this folder, picked up
 * automatically and listed by `order`. Add a level = add a file.
 *
 * {
 *   "id": "three-sixes",         stable id; equals the file name
 *   "order": 40,                 position in the list
 *   "title": "Three sixes",
 *   "bins": 2,                   K
 *   "capacity": 10,              B
 *   "items": [6, 6, 6, 2],       sizes, even, adding up to K·B (Berger and Leighton's
 *                                modified bin packing, §2 p. 31); item u is drawn in colour u
 *   "answer": "no",              "yes" if a packing exists (levels.test.ts checks it)
 *   "intro": "…",                one or two sentences under the title: the goal
 *   "hint": "…",                 optional, shown on request
 *   "why": "…",                  "no" levels: why no packing exists (shown with the solution)
 *   "solution": [0, 1, 1, 0]     optional, "yes" levels: bin of each item, for "Show solution"
 *                                (default: the solver's packing)
 * }
 */
import type { Instance } from '../engine/pack.ts';

export interface Level {
  id: string;
  order: number;
  title: string;
  bins: number;
  capacity: number;
  items: number[];
  answer: 'yes' | 'no';
  intro: string;
  hint?: string;
  why?: string;
  solution?: number[];
}

const modules = import.meta.glob<Level>('./*.json', { eager: true, import: 'default' });

export const LEVELS: Level[] = Object.values(modules).sort((a, b) => a.order - b.order);

export function getLevel(id: string | undefined | null): Level | undefined {
  return id ? LEVELS.find((l) => l.id === id) : undefined;
}

export const instanceOf = (l: Level): Instance => ({ bins: l.bins, capacity: l.capacity, sizes: l.items });
