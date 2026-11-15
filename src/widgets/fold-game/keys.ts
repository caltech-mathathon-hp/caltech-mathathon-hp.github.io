/**
 * Keyboard mapping of the folding game: KeyboardEvent.key → lattice step index.
 * Used when the renderer does not register its own mapping (RendererProps.registerKeyMap).
 *
 *   square      arrows (or R L U D)
 *   hexagonal   ← → to the left and right neighbours; ↑ or ↓ to the third neighbour, which
 *               is above the node or below it (one of the two at each node)
 *   cubic       arrows for x and y, F / B for z (only without the 3D renderer's own map)
 *   triangular  the hexagon around S on a QWERTY keyboard: W E / A D / Z X (or arrows for E / W)
 *   others      none (click the ghosts); the 3D renderer maps keys relative to the camera
 *
 * stepGlyph gives the key to print on a legal next position, so the board teaches its own keys.
 * On the hexagonal lattice the steps depend on the node, so both take the node (`from`).
 */
import { type Lattice, type Vec, stepNamesAt } from './engine/lattice.ts';

const ARROWS: Record<string, string> = { ArrowRight: 'R', ArrowLeft: 'L', ArrowUp: 'U', ArrowDown: 'D' };
const HEX: Record<string, string> = { d: 'E', a: 'W', e: 'NE', w: 'NW', z: 'SW', x: 'SE', ArrowRight: 'E', ArrowLeft: 'W' };

/** step name → the key printed on the board */
const GLYPHS: Record<string, Record<string, string>> = {
  square: { R: '→', L: '←', U: '↑', D: '↓' },
  hexagonal: { R: '→', L: '←', U: '↑', D: '↓' },
  cubic: { R: '→', L: '←', U: '↑', D: '↓', F: 'F', B: 'B' },
  triangular: { E: 'D', W: 'A', NE: 'E', NW: 'W', SW: 'Z', SE: 'X' },
};

const names = (lattice: Lattice, from?: Vec) => (from ? stepNamesAt(lattice, from) : lattice.stepNames);

/** the step index that `key` places from the node `from` (default: the origin), or null */
export function absoluteStep(lattice: Lattice, key: string, from?: Vec): number | null {
  let name: string | undefined;
  if (lattice.id === 'square' || lattice.id === 'cubic') {
    name = ARROWS[key] ?? (key.length === 1 ? key.toUpperCase() : undefined);
  } else if (lattice.id === 'hexagonal') {
    name = ARROWS[key];
  } else if (lattice.id === 'triangular') {
    name = HEX[key.length === 1 ? key.toLowerCase() : key];
  }
  if (!name) return null;
  const k = names(lattice, from).indexOf(name);
  return k >= 0 ? k : null;
}

/** the key that places the next residue along the k-th step at `from` (absolute mapping), or null */
export function stepGlyph(lattice: Lattice, k: number, from?: Vec): string | null {
  return GLYPHS[lattice.id]?.[names(lattice, from)[k]] ?? null;
}

/** keyboard help, as [keys, meaning] pairs */
export function keyHint(lattice: Lattice, rendererKeys: boolean): [string, string][] {
  if (lattice.id === 'square') return [['← ↑ → ↓', 'place the next residue']];
  if (lattice.id === 'hexagonal')
    return [
      ['← →', 'place the next residue on the left or right neighbour'],
      ['↑ ↓', 'place it on the third neighbour, above or below'],
    ];
  // with the 3D renderer's camera-relative map (render/three3d-scene.ts, KEY_SLOTS)
  if (lattice.dim === 3 && rendererKeys)
    return lattice.steps.length < 6
      ? [
          ['← ↑ → ↓', 'place the next residue on the neighbour closest to that direction on the screen'],
          ['W S', 'the same, away from you or toward you'],
        ]
      : [
          ['← ↑ → ↓', 'place the next residue in the plane of the screen'],
          ['W S', 'place it away from you or toward you'],
        ];
  if (lattice.id === 'cubic') return [['← ↑ → ↓', 'x and y'], ['F B', 'z']];
  if (lattice.id === 'triangular') return [['W E A D Z X', 'place the next residue (the six keys around S)']];
  return [];
}

/** the modifier for "go back to this residue": ⌘ on Apple keyboards, Ctrl elsewhere */
export function isApple(): boolean {
  if (typeof navigator === 'undefined') return false;
  const p = (navigator as Navigator & { userAgentData?: { platform?: string } }).userAgentData?.platform ?? navigator.platform ?? '';
  return /mac|iphone|ipad|ipod/i.test(p);
}
