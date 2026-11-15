/**
 * The contract between the folding-game shell (FoldGame.tsx) and a renderer.
 * A renderer is a Preact component that draws controller.fold and turns pointer input into
 * controller actions. Two exist: Svg2D (dim 2 lattices) and Three3D (dim 3 lattices).
 * Any lattice with the right `dim` must work, not only square/cubic: use lattice.embed.
 */
import type { GameController } from '../engine/controller.ts';

export interface RendererProps {
  controller: GameController;
  /** controller.version at render time; changes on every fold/hover change */
  version: number;
  /** show legal next positions (ghosts) and accept clicks on them */
  interactive: boolean;
  /** draw the lattice points / grid around the fold */
  showLattice: boolean;
  /** draw H–H contacts */
  showContacts: boolean;
  /** draw letter indices next to the letters */
  showIndices: boolean;
  /** CSS height of the drawing area, e.g. 420 or '60vh' */
  height: number | string;
  /**
   * Optional: lattice points the view should keep in frame instead of fitting the current
   * fold (view mode passes the complete fold, so the camera stays still while scrubbing).
   */
  frame?: readonly (readonly number[])[];
  /**
   * Optional: a renderer may supply its own keyboard mapping (e.g. 3D arrows relative to the
   * camera). The function maps a KeyboardEvent.key to a lattice step index, or null.
   * Call with null on unmount. The shell falls back to an absolute mapping otherwise.
   */
  registerKeyMap?: (fn: ((key: string, e: KeyboardEvent) => number | null) | null) => void;
  /**
   * Optional: the reader is using the keyboard on the board; print on each legal next position
   * the key that places the letter there. (The 3D renderer decides this itself.)
   */
  showKeys?: boolean;
  /** label of the modifier for "go back to this letter" in tooltips: '⌘' or 'Ctrl' */
  modKey?: string;
}

/*
 * Pointer conventions shared by both renderers (interactive mode):
 *   click / tap a legal next position      place the next letter there
 *   ⌘-click or Ctrl-click a placed letter  controller.truncate: go back to that letter
 *   touch: tap a placed letter to select it (controller.hover), tap it again to go back to it
 *   hover with ⌘ / Ctrl held                controller.setCut: preview what the click removes
 * and they draw controller.cut: letters after it faded, their contacts hidden.
 */

/** "letter 5", "letters 5 and 6", "letters 5 to 9" (numbers from 1) */
export function residueRange(a: number, b: number): string {
  return a === b ? `letter ${a}` : b === a + 1 ? `letters ${a} and ${b}` : `letters ${a} to ${b}`;
}

/** Read a design token at runtime (canvas/WebGL renderers). Re-read on 'themechange'. */
export function token(name: string): string {
  return getComputedStyle(document.documentElement).getPropertyValue(name).trim();
}
