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
        text: 'Berger and Leighton proved it in 1998 using bin packing: can items of given sizes fill bins of one size exactly?',
        visual: 'Items 6, 2, 8, 4 fade in as a row above two empty bins side by side ("bin 1", "bin 2", each "size 10"). One by one, 6, 4, 2, 8 go down into a lane under the row, along it and down into their bins: 6 + 4, 2 + 8. Both bins turn green: full.',
        hold: 31 / 15, // the cue keeps the length of its old, longer caption
      },
      {
        text: 'For each such puzzle we write one HP string. Its best fold shows whether the items fit.',
        visual: 'The packed bins fade out, and the row 6, 2, 8, 4 fades back in above them. The puzzle shrinks to the left ("bin packing puzzle", "a hard puzzle"). An arrow, "we write", leads to a long HP string, written bead by bead and shortened by a break mark. An arrow, "fold", leads to a small cube of H’s laid bead by bead ("best fold"). An arrow goes back from the cube to the puzzle: "fits / does not fit".',
        hold: 1,
      },
      {
        text: 'So a fast folding program would also solve bin packing, and folding is at least as hard.',
        visual: 'The same picture. "a fast program?" appears under the "fold" arrow. A dot runs once round the loop: along "we write", along "fold", and back along "fits / does not fit" to the puzzle. Then "at least as hard" appears under "best fold".',
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
        visual: 'The 12-cube full of H’s turns a little so three faces show ("the cube, full of H’s"). Twelve H’s on the cube’s outline each get a stem and a P one step out into the empty space, fading in one pair after another ("every P, one step outside").',
      },
      {
        text: "An [[h:H]] between two [[p:P]]’s needs two neighbours outside, so it sits on an edge. A run of PHP’s is a rod.",
        visual: 'The pairs fade out. The camera turns to the cube’s front-right edge, and a rod is laid down it with one soft tip: each H on the edge has a P off each of the two faces. Labels "rod, on an edge: PHP PHP PHP …", and under the cube "a P outside one face", "a P outside the other face".',
      },
      {
        text: "An [[h:H]] next to one [[p:P]] needs one, so it sits on a face. A run of PHHP’s is a ribbon.",
        visual: 'The rod fades out and the camera turns back to three faces. A ribbon is laid near the back of the top face with one soft tip, a P above each H, the H’s in pairs. Label "ribbon, on a face: PHHP PHHP …".',
      },
      {
        text: "A long run of [[h:H]]’s, the core, has no [[p:P]] to put outside, so it can fill the inside.",
        visual: 'The ribbon fades out. The outer beads of the cube’s front-top-right corner go one by one, in a wave from the corner, leaving a hole into the cube; then the core fades in on the hole’s three walls, H’s joined by chain sticks. Label "core, inside: HHHHHHHH …". In the tail the cube fades out, the camera moves back, and the empty wireframe fades in.',
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
        visual: 'The empty wireframe cube. A list on the left, "the string, in order:", names rod 1, ribbon 1, rod 2, ribbons 2–5 and the core, each with a small chain (start, break, end), and last "front face, and two of its edges: kept for the puzzle". The front face is tinted and its two side edges are soft blue bars.',
      },
      {
        text: 'Rod 1 is the longest walk along the edges: nine edges, all eight corners. Ribbon 1 covers the top, and rod 2 takes a tenth edge.',
        visual: 'The tint and the inner edges go. Rod 1 is laid with one soft tip round nine edges and all eight corners (H’s only; a note under the list says the P’s sit outside and are not drawn), then ribbon 1 on the top face, then rod 2 down a tenth edge; rod 2 swells once and is named. Each list row gets its sub-line as its piece goes in and a tick when it is done.',
        hold: 1.5 - 8 / 15, // the cue keeps the length of its old caption
      },
      {
        text: 'Five ribbons cover five faces and the core fills the inside. Only the front face is left, with its two [[free:free edges]].',
        visual: 'The blue bars step aside. Ribbons 2–5 fill the left, back, right and bottom faces, each with one soft tip, then the core is laid inside, back to front. The core fades out, and the open front face is left: its empty nodes as grey dots and its two free edges as blue bars. In the tail the list fades out.',
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
        visual: 'The camera turns to face the front; the cube behind the face fades out early in the turn. Labels "free edge" (left and right) and "rod 1" (top and bottom row). The walls are laid in string order with one soft tip, each named "wall" on the left; the H’s between them on the free edges are short rods (one bracketed "short rod"). Where the string leaves the face, a dashed arc with an arrow joins the two H’s on the right edge. A note under the face: "the P’s are not drawn: they stick out in front of the cube, between pairs of H’s and along each dashed jump".',
        hold: 2,
      },
      {
        text: 'The rod lengths leave the walls no slack, so they run straight across and cut the face into strips.',
        visual: 'The labels go. Brackets mark each short rod with its length, in string order (2, 5, 2, 2, 5, 2, 1, 1); on the far right a bracket per period adds the right rods to 5, level with the 5 on the left. The strips between the walls light up as outlined boxes, named on the left "strip 1" and "strip 2" with "3 rows × 10 nodes". In the tail the brackets, bars and sub-lines go and the names move to the strips’ middle rows.',
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
        visual: 'The toy face of step 18 fades out; the cube’s thin outline grows to a bigger cube, and the sketch face fades in as one picture: 4 strips of 3 rows × 20, named "strip 1" to "strip 4" (badge "Sketch: a bigger cube / 4 strips of 3 rows × 20, 2 bins of 10"). The other strips fade and the camera closes on strip 1 ("strip 1, 3 rows × 20 nodes"; the rows above named "rod 1" and "wall"), with "bin 1, size 10" right under its right end. A grey padding (50 H’s) is laid in at one soft tip and leaves 10 nodes free, column for column above the bin. "rod 1" and "wall" give way to the padding’s outline and its name "padding, 50 H’s".',
      },
      {
        text: 'Two paddings never fit in one strip, so each strip takes one and keeps a hole the size of a bin.',
        visual: 'The camera pulls back to the whole face; strips 2–4 fade back in, hole 1 gets its box, and a legend appears (walls and rods, empty node, padding). A second padding in the same grey tries strip 1 ("a second padding"): only its last 10 H’s find room, in the hole; its other 40 lie right of the face, boxed in red: "no room, 40 H’s left over". It fades out. The strip names give way to "hole 1, 10 nodes"; strips 2, 3 and 4 get their paddings, each fading in whole, then each hole its box and its name left of the face ("hole 2, 10 nodes", and so on).',
        hold: 1,
      },
      {
        text: 'The size of the cube sets the number of strips, often more than bins. Ribbons the size of a hole, called [[plug:plugs]], close the spare holes.',
        visual: 'Holes 3 and 4 are marked "spare". Tan plugs (10 H’s) are laid into hole 3, then hole 4, each at one soft tip, and their names become "plug, 10 H’s"; the legend gains "plug (H’s)". A grey note between the two plug names says "the plugs could go in any 2 holes". Holes 1 and 2 stay open.',
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
        visual: 'The plug note goes. The items 6, 2, 8, 4 fade in right of the face one after another, as bars in their colours with white size chips; the legend gains "items (H’s)". One at a time, in string order, each bar moves along one smooth curve into the hole on its row, its chip fades, and the bar gives way to its beads: 6 and 4 in hole 1, 2 and 8 in hole 2. The holes’ sub-lines read "6 + 4" and "2 + 8".',
      },
      {
        text: 'So the string folds perfectly exactly when the items fit.',
        visual: 'Two full bins fade in right of the holes, row for row, with dotted guides between them: bin 1 "6 + 4 = 10" and bin 2 "2 + 8 = 10", in the same colours, with green outlines. Between the face and the bins: ⟺ with the words "exactly when".',
        hold: 2.5,
      },
      {
        text: 'Given a perfect fold, we read a packing off the face: the items in one hole form one bin.',
        visual: '"exactly when" goes and an arrow "fold ⇒ packing" fades in. The bins empty. Hole 1’s box lights up and bin 1 fills again from it, bar by bar (6, then 4), until its outline turns green and its sum shows; then hole 2 and bin 2 (2, then 8).',
      },
      {
        text: 'Given a packing, we lay each item in the hole of its bin. Then we still have to join the ribbons up.',
        visual: 'The arrow fades out and "packing ⇒ fold" fades in. The items fade off the face, leaving holes 1 and 2 empty. One at a time, in string order, each bar moves out of its bin straight along its row into the hole, its chip fades, and it gives way to its beads; the holes’ sub-lines are rebuilt. The frame stays full orange. Discs right of each hole, under the grey word "order", give each item’s place in the string (hole 1: 1, 4; hole 2: 2, 3). A panel "order in the string" (top left) shows the discs 1–4 with the three joins still missing, dashed; the legend gains "join still missing".',
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
        visual: 'The face as one row of beads, "front face / its two holes end to end" (orange walls and rods, the two holes end to end), with fainter rows under it, "inside the cube". The items, numbered 1–4 ("order in the string"), come down into the holes. From the end of items 1, 2 and 3, one after another, a linker is laid bead by bead straight up into the space "in front of the cube". Each is tagged with the item it has to reach ("to ②"), and all end at one height ("all the same length").',
      },
      {
        text: "In front of the cube a switchboard brings the two ends of each linker side by side, and a loop uses up the [[p:P]]’s left over.",
        visual: 'The linkers shrink to stubs and a switchboard panel appears: "switchboard / each line is a run of P’s". One after another, each linker goes up its stub, along its own lane to a pair of gates on the far side, round a loop of the P’s left over, and back down into the start of the next item. Where two routes cross, the one behind has a gap ("routes cross at / different depths"). One linker is followed, darker: "two ends side by side", "loop: the P’s left over".',
        hold: 1.5,
      },
      {
        text: "Put the bins in the other holes and the same linkers are only rerouted. They never meet, so the [[h:H]]’s fill the cube: a perfect fold.",
        visual: 'The routes and loops fade. The two rows of items lift, change holes in an arch carrying their stubs, and land: "the bins swapped / the same linkers, only rerouted". The same linkers are routed again one after another, with new lanes and new loop sizes; "passes behind" points at one crossing. "every node / holds an H".',
        hold: 24 / 15, // the cue keeps the length of its old, longer caption
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
        visual: 'The puzzle in the bin-packing game’s style: two empty bins, then the items 6, 2, 8 and 4 fade in one after the other. "the same puzzle as before: 6 + 4 and 2 + 8 fill the two bins".',
      },
      {
        text: 'The recipe would build a cube of side 80. So that we can see every node, we use 2 strips instead of 6, which gives side 12.',
        visual: 'The puzzle moves left and shrinks. A cube of side 80 comes in as a thin grey wireframe, "side 80"; note "the recipe: 6 strips, side 80". Our cube of side 12 fades in whole in its corner, as beads: frame and walls, its front face empty where the two strips go, "side 12" under its front edge; note "we use: 2 strips, side 12 / one strip per bin, so no plugs are needed". The wireframe fades, the camera moves in to the small cube, and its two strips get a thin outline.',
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
        visual: 'The string’s 1,728 H’s as one bar to scale, under "1,728 H’s, one for each node of the cube". It grows at one steady pace in string order: rod 1, ribbon 1, rod 2, ribbons 2–5 in orange, each named once it is laid ("frame · 606 H’s / two rods and five face ribbons"); the core as one long lighter stretch ("core · 1,002 H’s"); then the walls, paddings and items. Their 120 H’s are shown again five times wider: "walls · 60 H’s", "paddings and items · 60 H’s".',
      },
      {
        text: "It ends with two paddings of 20 and one ribbon per item, each after a linker of 626 [[p:P]]’s.",
        visual: 'The end of the string enlarged, piece after piece in string order: the last of the walls, then linker – padding – linker – padding – linker – 6 – linker – 2 – linker – 8 – linker – 4, each linker "626 P’s", the size 2 in a chip under its small item. A bracket over the first three linkers: "routed in front of the cube, like the three between the items"; one under the items: "one ribbon per item". Under the row: "the bar above counts only the H’s; the linkers’ P’s come in between".',
      },
    ],
  },
  {
    id: 'forward',
    part: 2,
    title: 'Packing ⇒ perfect fold',
    cues: [
      {
        text: 'Take the packing [[i0:6]] + [[i3:4]] and [[i1:2]] + [[i2:8]]. The frame and walls are built as before and leave two strips of 3 rows by 10.',
        visual: 'The packed bins of the puzzle wait on the right (6 + 4, 2 + 8). The 12-cube, already folded, fades in as a whole. Everything behind the front face fades out as one picture, then the camera turns to the face: two strips of 3 rows × 10, boxed and labelled on the left.',
        hold: 1 - 5 / 15, // the cue keeps the length of its old caption
      },
      {
        text: 'Each padding snakes through two rows of its strip. The third row is a hole of 10 nodes, exactly a bin.',
        visual: 'Grey paddings snake in one after the other, 20 H’s each. A small chevron in each gap shows the way the string runs. The strip boxes give way to hole boxes (one row of 10 nodes), and the bins slide next to the holes: same length, row for row.',
      },
      {
        text: 'The item ribbons go into the holes as the items went into the bins. Now every node of the cube holds an [[h:H]].',
        visual: 'The items go into the holes in string order (6, 2, 8, 4). Each bar leaves its bin, moves straight left along its row onto its hole, and gives way to its ribbon: the bar shrinks from the ribbon’s start while the beads fade in under it. The face is full; the empty bins with their sums stay beside it.',
      },
      {
        text: 'The linkers leave the face, pass through the switchboard and loop back, joining the ribbons in string order.',
        visual: 'The rest of the face fades and the item beads slide into the side view of steps 26–28: the front face as one row of beads (the two holes end to end), the cube’s rows under it, the order discs 1–4 above the items, and a switchboard panel in front of the cube. Three linkers are laid one after another, bead by bead, each from the end of one item up through the switchboard, round its loop and down into the start of the next; crossings are drawn over and under. At the end all three are the same grey: "626 P’s each".',
        hold: 3,
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
        visual: 'Face-on view of the full front face, frame in full orange. We read the holes one after the other: a bar of the game grows over each ribbon in turn, from the ribbon’s first bead, and gets its size. Then the hole’s bars lift and move together into the empty bin on its row, which turns full: 6 + 4 = 10, 2 + 8 = 10. The ribbons stay in the holes.',
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
        visual: 'Same face, frame in full orange, holes empty. The items 6, 6, 6, 2 wait on the right in a column, as the game’s bars. In string order, each goes along one smooth path, beside the face to its hole’s row and into the hole, and gives way to its beads; the column closes up. The first 6 goes into hole 1, the second into hole 2. The third 6 tries hole 2, sticks out past the edge, gets a red outline ("only 4 nodes free") and goes back. The 2 goes next to the first 6. The third 6 is marked "no place".',
        hold: 1.5,
      },
      {
        text: 'Some nodes of the cube stay empty. This string has no perfect fold, and its best fold has fewer contacts.',
        visual: 'The empty nodes get dashed red rings one by one (2 in hole 1, 4 in hole 2) and a counter, "6 nodes empty". The hole labels step aside, and short red dashes run from each empty node to its H neighbours: "contacts lost". Under "no place", in grey: "it folds in front of the cube".',
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
        visual: 'Two thin grey wire cubes to scale, side by side: the recipe’s cube for items 6, 2, 8, 4 ("side 80, 80³ = 512,000 H’s"), and for every size tripled, items 18, 6, 24, 12 ("side 138, 138³ = 2,628,072 H’s").',
      },
      {
        text: 'So a program that finds best folds would also solve bin packing. HP folding on the cubic grid is NP-complete.',
        visual: 'The cubes fade. The plan’s picture is built again: puzzle ("a hard puzzle") → HP string → best fold, and the arrow back, "fits / does not fit". Reference in small type: Berger and Leighton, J. Comput. Biol. 5(1), 1998. Then "a fast program?", one pass of the dot round the loop, and "at least as hard".',
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
