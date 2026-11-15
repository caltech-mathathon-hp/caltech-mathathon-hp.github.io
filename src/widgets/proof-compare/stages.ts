/**
 * The two proof boards compared step by step: which steps of the original proof (map `bl`) and of
 * the one-edge proof (map `ours`) do the same job. ProofCompare.astro draws the stages as a proof
 * board of its own, with the places of the original board: the idea on top, the setup row, the two
 * directions side by side, and the conclusion. Each stage is one comparison card, a stack that
 * opens in place to show the cards of both boards side by side.
 *
 * Every card of each board must appear in exactly one stage (ProofCompare checks this at build
 * time), so adding or renaming a card means updating this list. `note` is one line of card text:
 * $math$, `HP strings` in backticks, *em* and **strong** (see ../proof-map/inline.ts).
 */

export interface Side {
  /** Folder of the cards: src/content/proof-steps/<map>/. */
  map: string;
  /** Name of the proof. */
  name: string;
  /** Short name, for the lists on the comparison cards. */
  short: string;
  /** Page that holds the board (absolute site path; the base is added). */
  page: string;
}

export type Place = 'top' | 'setup' | 'left' | 'right' | 'end';

export interface Stage {
  /** Short title, at most four words. */
  title: string;
  /** Where the comparison card sits, as on a proof board. */
  place: Place;
  /** same: both steps prove the same thing the same way, up to our numbers. changed: it works differently. */
  kind: 'same' | 'changed';
  /** Card slugs of the original board, then of ours, in board order. */
  cards: [string[], string[]];
  /** What changes from the original to ours, in one or two sentences. */
  note: string;
}

export const SIDES: [Side, Side] = [
  { map: 'bl', name: 'The original proof', short: 'Original', page: '/original-proof/' },
  { map: 'ours', name: 'Bins on one edge', short: 'One edge', page: '/one-edge-proof/' },
];

export const STAGES: Stage[] = [
  {
    title: 'The plan',
    place: 'top',
    kind: 'changed',
    cards: [['idea'], ['idea']],
    note: 'Both build one string whose perfect folds match the packings. The original makes its bins from strips of one face of the cube; ours makes them from gaps on one edge.',
  },
  {
    title: 'Why bin packing',
    place: 'setup',
    kind: 'same',
    cards: [['problems'], ['problems']],
    note: 'The same puzzle. The original also needs at least $2B^{1/3}$ strips; ours needs no relation between $B$ and $K$.',
  },
  {
    title: 'Why a cube',
    place: 'setup',
    kind: 'same',
    cards: [['cube'], ['cube']],
    note: 'The same statement. Ours proves the inequality of Loomis and Whitney by Cauchy–Schwarz instead of slices.',
  },
  {
    title: 'Spelling the string',
    place: 'setup',
    kind: 'changed',
    cards: [['string'], ['string']],
    note: 'Items become rods `(PHP)^{s(u)}` instead of ribbons. Separators of one length replace the short and long rods, the spaced rod, the paddings and the plugs.',
  },
  {
    title: 'Local rules',
    place: 'left',
    kind: 'same',
    cards: [['local-rules'], ['local-rules']],
    note: 'The same rules. Ours shows that the H\'s of `HPPH` touch by one argument about shortest paths, for faces, edges and corners at once.',
  },
  {
    title: 'Edges and faces',
    place: 'left',
    kind: 'same',
    cards: [['skeleton'], ['skeleton', 'working-face']],
    note: 'The same two rods leave two edges free. Ours adds that every later rod is a run on one free edge, and that the walls and the filler fill the front face.',
  },
  {
    title: 'Making the bins',
    place: 'left',
    kind: 'changed',
    cards: [['free-edges', 'walls'], ['anchors', 'order', 'gaps']],
    note: 'The original pins $2q$ walls by rods of lengths $q$ and $2q+1$ and a step with six P\'s. Ours fixes the ends of the separators with two walls, and the rods in a gap block any way round it longer than $B$.',
  },
  {
    title: 'Reading off a packing',
    place: 'left',
    kind: 'changed',
    cards: [['packing'], ['packing']],
    note: 'The original first puts a padding in each strip and the plugs in the spare ones. Ours reads the bins straight off the gaps.',
  },
  {
    title: 'Folding the frame',
    place: 'right',
    kind: 'changed',
    cards: [['frame'], ['placements', 'frame']],
    note: 'The same pieces in nearly the same places. The original joins them by short detours of P\'s; ours by linkers, routed at the end.',
  },
  {
    title: 'Filling the front face',
    place: 'right',
    kind: 'changed',
    cards: [['build-walls', 'fill-strips'], ['front-face']],
    note: '$2q$ walls, $q$ paddings and the plugs, against two walls, the separators and one filler. The items go into gaps of an edge instead of strips.',
  },
  {
    title: 'Joining the pieces',
    place: 'right',
    kind: 'changed',
    cards: [['crossbar', 'linkers'], ['corner-routes', 'item-routes']],
    note: 'The original passes its linkers through a switchboard in front of the cube. Ours sends seven linkers round edges of the cube and gives each linker between items its own plane.',
  },
  {
    title: 'Folding is NP-complete',
    place: 'end',
    kind: 'same',
    cards: [['conclusion'], ['conclusion']],
    note: 'The same conclusion. The original string grows like $K^6+B^2$ and ours like $(KB)^3$, both polynomial in the size of the puzzle.',
  },
];
