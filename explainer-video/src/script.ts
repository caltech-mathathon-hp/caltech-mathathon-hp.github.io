/**
 * The script: every scene, its captions and what the picture does under each caption.
 * Timing comes from the captions (reading speed), so the scenes animate against cue times.
 * `node scripts/storyboard.ts` writes storyboard.md from this file.
 *
 * Caption markup: [[h:H]] colours a word like an H, [[p:P]] like a P, [[i0:6]]…[[i3:4]] like
 * items 1–4, [[pad:padding]], [[plug:plug]], [[bond:contact]].
 */
import { FPS } from './theme/consts.ts';

export interface Cue {
  text: string;
  /** what the picture does while this caption is up (for the storyboard) */
  visual: string;
  /** extra seconds on top of reading time (animation-heavy cues, key claims) */
  hold?: number;
}

export interface SceneDef {
  id: string;
  part: 0 | 1 | 2 | 3;
  /** shown top left */
  title: string;
  /** seconds of picture before the first caption */
  lead?: number;
  /** seconds after the last caption */
  tail?: number;
  cues: Cue[];
}

/** reading speed in characters per second (subtitle norms: 12–17; slower, as the eye also reads the picture) */
export const CPS = 15;
/** time to look at the picture after reading */
export const HOLD = 1.2;
export const MIN_CUE = 2.8;

export const SCENES: SceneDef[] = [
  {
    id: 'title',
    part: 0,
    title: '',
    lead: 4.5,
    tail: 0,
    cues: [],
  },
  // ------------------------------------------------------------------ Part 1: the idea
  {
    id: 'fold',
    part: 1,
    title: 'The folding problem',
    cues: [
      {
        text: "An HP string is a chain of [[h:H]]’s and [[p:P]]’s. A fold lays it on the grid, one letter per node, without crossing itself.",
        visual: 'A 12-letter string (H filled orange, P hollow blue, letters above) is laid bead by bead. The letters fade, and the string slides head first onto a floor grid, into a flat fold of three arms. An H/P key appears on the right.',
      },
      {
        text: "Two [[h:H]]’s that touch on the grid but are not joined in the chain make a [[bond:contact]]. A best fold has the most contacts.",
        visual: 'Gold dashed contacts appear one by one between the H’s of neighbouring arms. A counter, "contacts: 4", counts them, then adds "the most possible".',
      },
      {
        text: 'On the cubic grid, finding a best fold is NP-complete: as hard as a whole family of puzzles that nobody knows how to solve fast.',
        visual: 'The camera pulls back and the floor grows into a block of cubic cells, drawn on its three visible faces; the fold lies on top, with its key and counter.',
      },
    ],
  },
  {
    id: 'plan',
    part: 1,
    title: 'The plan',
    cues: [
      {
        text: 'Berger and Leighton proved it in 1998, starting from one of those puzzles, bin packing: can items of given sizes fill bins of one size exactly?',
        visual: 'The bin-packing game look: items 6, 2, 8, 4 as coloured bars of cells, two empty bins of 10. The items slide in: 6 + 4, 2 + 8. Both bins full.',
      },
      {
        text: 'For each such puzzle we write one HP string. Its best fold shows whether the items fit.',
        visual: 'The items lift back out of the bins into two rows above them, 6 + 4 over 2 + 8. The puzzle shrinks to the left ("bin packing puzzle", "a hard puzzle"). An arrow, "we write", leads to a long HP string (laid bead by bead, shortened by a break mark). An arrow, "fold", leads to a small cube of H’s ("best fold"). An arrow goes back from the cube to the puzzle: "fits / does not fit".',
      },
      {
        text: 'So a fast folding program would also solve bin packing, and folding is at least as hard.',
        visual: 'The same picture. "a fast program?" appears under the "fold" arrow, and "at least as hard" under "best fold".',
      },
    ],
  },
  {
    id: 'cube',
    part: 1,
    title: 'Why a cube',
    cues: [
      {
        text: "First, the shape of a best fold. Each [[h:H]] has six neighbours, and each neighbour that is not an [[h:H]] is a contact lost.",
        visual: 'One H and its six neighbours (empty nodes, small grey dots, joined to it by faint grid lines): "6 neighbours". Three fill with H’s: two joined to it ("chain"), and one by a gold dashed "contact". The other three stay empty, each with a dashed red ring and a red dashed link from the centre: "contact lost".',
      },
      {
        text: "So [[h:H]]’s make the most contacts when they show the least surface. For n × n × n of them, that means filling a cube of side n.",
        visual: 'A chain of 27 H’s is laid as a flat 9 × 3 slab, with a red stub on every side that touches no H: "9 × 3 slab, 27 H’s, 78 contacts lost". The slab slides left. Where it was, a copy of the chain fades in and folds like an accordion, one third and then the other, into a cube: "3 × 3 × 3 cube, so n = 3, 27 H’s, 54 contacts lost". Slab and cube end side by side.',
        hold: 1.5,
      },
      {
        text: "We call such a fold perfect, and spell the string so that it folds perfectly exactly when the items fit.",
        visual: 'Slab and cube fade out. The 12-cube full of H’s fades in, and the view turns slowly a few degrees. Label: "a perfect fold", "every node holds an H".',
      },
    ],
  },
  {
    id: 'local',
    part: 1,
    title: "P’s stay outside",
    cues: [
      {
        text: "In a perfect fold the cube is full of [[h:H]]’s, so every [[p:P]] lies outside. That decides where each [[h:H]] can go.",
        visual: 'The 12-cube full of H’s, turned so three faces show ("inside: only H’s"). Twelve H’s on the cube’s outline each grow a stem, and a P fades in at its end, one step out into the empty space ("every P sits one step outside").',
      },
      {
        text: "An [[h:H]] between two [[p:P]]’s needs two neighbours outside, so it sits on an edge. A run of PHP’s is a rod.",
        visual: 'The cube quiets and turns to its front-left edge. A rod is laid along it with one growing tip, each H with a P off each of the two faces. Labels "rod, on an edge: PHP PHP PHP …", and under the cube "a P outside one face", "a P outside the other face".',
      },
      {
        text: "An [[h:H]] next to one [[p:P]] needs one, so it sits on a face. A run of PHHP’s is a ribbon.",
        visual: 'The camera rises over the top face. A ribbon is laid across its middle with one growing tip, a P above each H. Label "ribbon, on a face: PHHP PHHP …".',
      },
      {
        text: "A long run of [[h:H]]’s, the core, has no [[p:P]] to put outside, so it can fill the inside.",
        visual: 'Back to the whole cube. The outer layer of its front-top-right corner goes in a wave and shows the core: H-red beads joined by chain sticks. Label "core, inside: HHHHHHHH …". In the tail the beads go and the empty wireframe comes back.',
      },
    ],
  },
  {
    id: 'frame',
    part: 1,
    title: 'A jigsaw with one solution',
    cues: [
      {
        text: 'The front face and two of its edges are kept for the puzzle. The rest gets pieces so long that each has one place.',
        visual: 'The empty wireframe cube. The front face is tinted and its two side edges are soft blue bands, corner to corner. A parts list on the left names rod 1, ribbon 1, rod 2, ribbons 2–5, the core, and "front face, and its 2 free edges: kept for the puzzle".',
      },
      {
        text: 'The first rod is as long as a walk along the edges can be: nine edges and all eight corners. A second rod takes a tenth.',
        visual: 'The inner edges go. Rod 1 is laid with one tip round nine edges and all eight corners (H’s only, no P’s; a note says so), then ribbon 1 on the top face, then rod 2 down the back-left edge, in full colour; it swells once and is named "rod 2". The list ticks each piece off.',
        hold: 1.5,
      },
      {
        text: 'Five ribbons cover five faces and the core fills the inside. Only the front face is left, with its two [[free:free edges]].',
        visual: 'Ribbons 2–5 fill the left, back, right and bottom faces, one after another, then the core is laid inside. The rods and faces quiet, the core goes, and the front face is left: its empty nodes and the two blue free edges. In the tail the list fades out.',
        hold: 1.5,
      },
    ],
  },
  {
    id: 'walls',
    part: 1,
    title: 'Walls cut out strips',
    cues: [
      {
        text: 'On the front face, ribbons as long as a row become walls, joined by short rods on the two [[free:free edges]].',
        visual: 'The camera turns to face the front; the frame is full orange and the free edges stay as blue bands ("free edge", "rod 1" top and bottom). The walls are laid in string order with one tip ("wall"); a bracket marks one "short rod". A note under the face: "The P’s are not drawn. Between the pairs of H’s, they stick out in front of the cube."',
        hold: 2,
      },
      {
        text: 'The rod lengths leave the walls no slack, so they run straight across and cut the face into strips.',
        visual: 'The labels go. A bracket with its length marks each short rod in string order (2, 5, 2, 2, 5, 2, 1, 1); the left ones go. The strips between the walls light up as boxes, named on the left "strip 1", "strip 2", "3 rows × 10 nodes". In the tail the brackets, bands and sub-lines go and the names move to the strips’ middle rows.',
      },
    ],
  },
  {
    id: 'padding',
    part: 1,
    title: 'Padding and plugs',
    cues: [
      {
        text: 'A strip has more room than a bin. So each strip gets a [[pad:padding]], a ribbon that fills more than half of it.',
        visual: 'The toy face of step 18 grows into a bigger sketch face (4 strips of 3 rows × 20; badge "Sketch: a bigger cube, 4 strips of 3 rows × 20, 2 bins of 10"). The camera closes on strip 1 ("strip 1, 3 rows × 20"; the rows above tagged "cube edge" and "wall"), with a bin of 10 right under its right end. A grey padding (50 H’s) is laid in with one tip and leaves a hole of 10, column for column above the bin ("hole 1: 10 nodes", "a bin: 10").',
      },
      {
        text: 'Two paddings never fit in one strip, so each strip takes one and keeps a hole the size of a bin.',
        visual: 'The camera pulls back to the whole face. A pale second padding tries strip 1: only its last 10 H’s find room, in the hole; its other 40 lie outside the face, boxed in red, "no room: 40 left over". It goes. Strips 2, 3 and 4 get their paddings, one after another; each hole gets its box and its label on the left ("hole 2", "10 nodes").',
        hold: 1,
      },
      {
        text: 'The size of the cube sets the number of strips, often more than bins. Ribbons the size of a hole, called [[plug:plugs]], close the spare holes.',
        visual: 'Holes 3 and 4 are marked "spare". Tan plugs (10 H’s) fill hole 3, then hole 4, and their labels become "plug". A line says "the plugs could go in any 2 holes". Holes 1 and 2 stay open.',
      },
    ],
  },
  {
    id: 'choice',
    part: 1,
    title: 'The only choice left',
    cues: [
      {
        text: 'Each item becomes a ribbon of its size. The other pieces have no real choice, so all that is left is which hole each item takes.',
        visual: 'The items 6, 2, 8, 4 appear one after another right of the face, as ribbons in their colours with their sizes. One at a time, in string order, each slides to the row of its hole and is laid into it: 6 and 4 in hole 1, 2 and 8 in hole 2. The holes’ sub-lines read "6 + 4" and "2 + 8".',
      },
      {
        text: 'So the string folds perfectly exactly when the items fit.',
        visual: 'Two full bins appear right of the holes, row for row (dotted guides): bin 1 "6 + 4 = 10", bin 2 "2 + 8 = 10", the same colours. Between face and bins: "exactly when" with ⟺.',
        hold: 2.5,
      },
      {
        text: 'Given a perfect fold, we read a packing off the face: the items in one hole form one bin.',
        visual: 'Arrow "fold ⇒ packing": the bins empty, then each hole’s items are read into the bin on its row, one bar after another.',
      },
      {
        text: 'Given a packing, we lay each item in the hole of its bin. Then we still have to join the ribbons up.',
        visual: 'Arrow "packing ⇒ fold": the face is cleared and each item is laid again into the hole on its bin’s row, one at a time in string order. The frame steps back. Discs right of each hole give each item’s place in the string (hole 1: 1, 4; hole 2: 2, 3). A panel "order in the string" (top left) shows the discs 1–4 with the three joins still missing, dashed.',
      },
    ],
  },
  {
    id: 'linkers',
    part: 1,
    title: 'Linkers',
    cues: [
      {
        text: "Linkers, long runs of [[p:P]]’s, join consecutive ribbons. We write them before knowing a packing, so all have one length.",
        visual: 'The face seen from the side: the front face is a row of beads (orange walls and rods, the two holes side by side), with fading rows of the cube under it. The items, numbered 1–4 in string order, come down onto the face row. From the end of items 1, 2 and 3, one after another, a linker of P’s goes straight up into the space in front of the cube. Each is tagged with the number of the item it has to reach, and all reach the same height ("all the same length").',
      },
      {
        text: "In front of the cube a switchboard brings the two ends of each linker side by side, and a loop uses up the [[p:P]]’s left over.",
        visual: 'The linkers shrink to stubs and a switchboard panel appears in front of the cube. One after another, each linker goes up its stub, along its own lane through the switchboard to a pair of gates on the far side, round a loop of the P’s left over, and back down into the start of the next item. Where two routes cross, the one behind has a gap. One linker is followed, darker: "two ends side by side", "loop: the P’s left over".',
        hold: 1.5,
      },
      {
        text: "Put the bins in the other holes and the same linkers are only rerouted. They stay in front of the cube and never meet, so the [[h:H]]’s fill it: a perfect fold.",
        visual: 'The wires and loops fade. The two rows of items lift, change holes carrying their stubs, and drop: "The bins swapped, the same linkers, only rerouted". The same linkers are routed again one after another, with new lanes and new loop sizes; "passes behind" points at one crossing. "every node holds an H".',
      },
    ],
  },
  // ------------------------------------------------------------------ Part 2: an example
  {
    id: 'instance',
    part: 2,
    title: 'The puzzle, built in full',
    lead: 1.2,
    cues: [
      {
        text: 'Now the same puzzle, built in full: items [[i0:6]], [[i1:2]], [[i2:8]] and [[i3:4]], and two bins of size 10.',
        visual: 'The puzzle in the bin-packing game’s style, empty bins.',
      },
      {
        text: 'The recipe would build a cube of side 80. So that we can see every node, we use 2 strips instead of 6, which gives side 12.',
        visual: 'A cube of side 80 (outline) with the toy cube of side 12 in its corner; a note under the puzzle reads "Recipe: 6 strips, side 80" and "Toy: 2 strips, side 12, one strip per bin, so no plugs are needed". The camera moves in to the small cube, labelled "side 12" under its front edge, which turns into the toy’s fold. The badge "Toy size" appears top right and stays for the rest of the video.',
      },
    ],
  },
  {
    id: 'string',
    part: 2,
    title: 'Its string',
    cues: [
      {
        text: "The string has one [[h:H]] for each of the 1,728 nodes of the cube. Most of them form the frame and the core.",
        visual: 'The string’s 1,728 H’s as one bar to scale: rod 1, ribbons 1–5 and rod 2 in orange, split by white rules ("frame · 606 H’s"); the core as one long lighter stretch ("core · 1,002 H’s"); the walls in orange; then the paddings and items. The end of the bar (walls, paddings and items, 120 H’s) is shown again five times wider.',
      },
      {
        text: "It ends with two paddings of 20 and one ribbon per item, each after a linker of 626 [[p:P]]’s.",
        visual: 'The end of the string enlarged, piece after piece in string order: the last of the walls, then linker – padding – linker – padding – linker – 6 – linker – 2 – linker – 8 – linker – 4, each linker "626 P’s". A bracket over the first three linkers: "routed in front of the cube, like the three between the items"; one under the items: "one ribbon per item".',
      },
    ],
  },
  {
    id: 'forward',
    part: 2,
    title: 'Packing ⇒ perfect fold',
    cues: [
      {
        text: 'Take the packing [[i0:6]] + [[i3:4]] and [[i1:2]] + [[i2:8]]. The frame and walls fold as before and leave two strips of 3 rows by 10.',
        visual: 'The packed bins of the puzzle wait on the right (6 + 4, 2 + 8). The 12-cube is laid fast in string order, each piece fading in whole. The camera turns to the front face: two strips of 3 rows × 10, boxed and labelled on the left.',
        hold: 1,
      },
      {
        text: 'Each padding snakes through two rows of its strip. The third row is a hole of 10 nodes, exactly a bin.',
        visual: 'Grey paddings snake in one after the other, 20 H’s each. A small chevron in each gap shows the way the string runs. The strip boxes give way to hole boxes (one row of 10 nodes), and the bins slide next to the holes: same length, row for row.',
      },
      {
        text: 'The item ribbons go into the holes as the items went into the bins. Now every node of the cube holds an [[h:H]].',
        visual: 'The items go into the holes in string order (6, 2, 8, 4). A copy lifts off its bin, which keeps it dimmed, flies left along its row, lands on its hole and shrinks cell by cell to uncover its ribbon. The face is full, and the bins with their sums stay beside it.',
      },
      {
        text: 'The linkers leave the face, pass through the switchboard and loop back, joining the ribbons in string order.',
        visual: 'The face becomes the side view of steps 26–28: the items, numbered 1–4 in string order, slide onto the face row, and a switchboard panel appears in front of the cube. Three linkers are laid one after another, each from the end of one item up through the switchboard, round its loop and down into the start of the next; crossings are drawn over and under. At the end all three are the same grey: "626 P’s each".',
        hold: 1.5,
      },
    ],
  },
  {
    id: 'backward',
    part: 2,
    title: 'Perfect fold ⇒ packing',
    cues: [
      {
        text: 'Backwards, any perfect fold gives a packing: read the holes. [[i0:6]] and [[i3:4]] share one, [[i1:2]] and [[i2:8]] the other.',
        visual: 'Face-on view of the full front face; the frame steps back. We read the holes one after the other. A bar of the game is laid over each ribbon in turn, from the ribbon’s first bead, and gets its size. Then the hole’s bars lift off and slide into an empty bin, which turns full: 6 + 4 = 10, 2 + 8 = 10.',
      },
    ],
  },
  {
    id: 'no',
    part: 2,
    title: 'When the items do not fit',
    cues: [
      {
        text: "Now try items [[i0:6]], [[i0:6]], [[i0:6]] and [[i1:2]]. Two 6’s never share a hole of 10, so one 6 has no place.",
        visual: 'Same face, frame stepped back, holes empty. The items 6, 6, 6, 2 wait on the right in a column, as the game’s bars. In string order, each goes along a lane beside the face to its hole’s row and into the hole, and the column closes up. The first 6 goes into hole 1, the second into hole 2. The third 6 tries hole 2, sticks out past the edge, turns red ("only 4 nodes free") and goes back. The 2 goes next to the first 6. The third 6 is marked "no place".',
        hold: 1.5,
      },
      {
        text: 'Some nodes of the cube stay empty. This string has no perfect fold, and its best fold has fewer contacts.',
        visual: 'The empty nodes get dashed red rings one by one (2 in hole 1, 4 in hole 2) and a counter: "6 nodes empty". The hole labels step aside, and short red dashes run from each empty node to its H neighbours: "contacts lost". Under "no place": "it folds in front of the cube".',
      },
    ],
  },
  {
    id: 'end',
    part: 3,
    title: 'Folding is as hard as packing',
    tail: 3,
    cues: [
      {
        text: "The string has n³ [[h:H]]’s plus the linkers, so it grows with the sizes. That is fine because bin packing stays hard with small sizes.",
        visual: 'Two cube outlines, side 80 in grey and the toy, side 12, in orange. They are labelled "side n = 80, 80³ = 512,000 H’s" and "side n = 12, 12³ = 1,728 H’s". One line beside them: "Bigger sizes make a bigger cube, but bin packing is hard even with small sizes."',
      },
      {
        text: 'So a program that finds best folds would also solve bin packing. HP folding on the cubic grid is NP-complete.',
        visual: 'The plan’s picture is built again: puzzle ("a hard puzzle") → HP string → best fold, and the arrow back, "fits / does not fit". Then "a fast program?" and "at least as hard" appear. Reference: Berger and Leighton, J. Comput. Biol. 5(1), 1998.',
        hold: 2,
      },
    ],
  },
];

// ---------------------------------------------------------------- timing
const plain = (t: string) => t.replace(/\[\[[a-z0-9]+:([^\]]*)\]\]/g, '$1');

export interface CueTime extends Cue {
  /** frames, relative to the scene start */
  from: number;
  to: number;
}
export interface SceneTime extends SceneDef {
  /** absolute start frame */
  start: number;
  duration: number;
  cueTimes: CueTime[];
}

export const cueSeconds = (c: Cue) => Math.max(MIN_CUE, plain(c.text).length / CPS + HOLD) + (c.hold ?? 0);

export function timeline(): SceneTime[] {
  let start = 0;
  return SCENES.map((s) => {
    const lead = s.lead ?? 0.6;
    const tail = s.tail ?? 0.7;
    let t = lead;
    const cueTimes = s.cues.map((c) => {
      const from = Math.round(t * FPS);
      t += cueSeconds(c);
      return { ...c, from, to: Math.round(t * FPS) };
    });
    const duration = Math.round((t + tail) * FPS);
    const out = { ...s, start, duration, cueTimes };
    start += duration;
    return out;
  });
}

export const TIMELINE = timeline();
export const TOTAL_FRAMES = TIMELINE.reduce((a, s) => a + s.duration, 0);
export const sceneTime = (id: string) => {
  const s = TIMELINE.find((x) => x.id === id);
  if (!s) throw new Error(`no scene ${id}`);
  return s;
};
