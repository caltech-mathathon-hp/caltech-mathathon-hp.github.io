# Storyboard

Generated from `src/script.ts` by `node scripts/storyboard.ts`. Length 6:27 at 30 fps.
Captions are the only text; each stays up for its reading time (15 characters a second) plus a pause to look.

### 0:00 · Title card (`title`, 4.5 s)

No caption.

## Part 1, the idea

### 0:05 · The folding problem (`fold`, 28.5 s)

- **0:05** “An HP string is a chain of H’s and P’s. A fold lays it on the grid, one letter per node, without crossing itself.”
  *Picture:* A 12-letter string (H filled orange, P hollow blue, letters above) is laid bead by bead. The letters fade, and the string slides head first onto a floor grid, into a flat fold of three arms. An H/P key appears on the right.
- **0:14** “Two H’s that touch on the grid but are not joined in the chain make a contact. A best fold has the most contacts.”
  *Picture:* Gold dashed contacts appear one by one between the H’s of neighbouring arms. A counter, "contacts: 4", counts them, then adds "the most possible".
- **0:23** “On the cubic grid, finding a best fold is NP-complete: as hard as a whole family of puzzles that nobody knows how to solve fast.”
  *Picture:* The camera pulls back and the floor grows into a block of cubic cells, drawn on its three visible faces; the fold lies on top, with its key and counter.

### 0:33 · The plan (`plan`, 27.1 s)

- **0:34** “Berger and Leighton proved it in 1998 using bin packing: can items of given sizes fill bins of one size exactly?”
  *Picture:* Items 6, 2, 8, 4 fade in as a row above two empty bins side by side ("bin 1", "bin 2", each "size 10"). One by one, 6, 4, 2, 8 go down into a lane under the row, along it and down into their bins: 6 + 4, 2 + 8. Both bins turn green: full.
- **0:44** “For each such puzzle we write one HP string. Its best fold shows whether the items fit.”
  *Picture:* The packed bins fade out, and the row 6, 2, 8, 4 fades back in above them. The puzzle shrinks to the left ("bin packing puzzle", "a hard puzzle"). An arrow, "we write", leads to a long HP string, written bead by bead and shortened by a break mark. An arrow, "fold", leads to a small cube of H’s laid bead by bead ("best fold"). An arrow goes back from the cube to the puzzle: "fits / does not fit".
- **0:52** “So a fast folding program would also solve bin packing, and folding is at least as hard.”
  *Picture:* The same picture. "a fast program?" appears under the "fold" arrow. A dot runs once round the loop: along "we write", along "fold", and back along "fits / does not fit" to the puzzle. Then "at least as hard" appears under "best fold".

### 1:00 · Why a cube (`cube`, 29.1 s)

- **1:01** “First, the shape of a best fold. Each H has six neighbours, and each neighbour that is not an H is a contact lost.”
  *Picture:* One H and its six neighbours (empty nodes, small grey dots, joined to it by faint grid lines): "6 neighbours". Three fill with H’s: two joined to it ("chain"), and one by a gold dashed "contact". The other three stay empty, each with a dashed red ring and a red dashed link from the centre: "contact lost".
- **1:10** “So H’s make the most contacts when they show the least surface. For n × n × n of them, that means filling a cube of side n.”
  *Picture:* A chain of 27 H’s is laid as a flat 9 × 3 slab, with a red stub on every side that touches no H: "9 × 3 slab, 27 H’s, 78 contacts lost". The slab slides left. Where it was, a copy of the chain fades in and folds like an accordion, one third and then the other, into a cube: "3 × 3 × 3 cube, so n = 3, 27 H’s, 54 contacts lost". Slab and cube end side by side.
- **1:20** “We call such a fold perfect, and spell the string so that it folds perfectly exactly when the items fit.”
  *Picture:* Slab and cube fade out. The 12-cube full of H’s fades in, and the view turns slowly a few degrees. Label: "a perfect fold", "every node holds an H".

### 1:29 · P’s stay outside (`local`, 30.0 s)

- **1:30** “In a perfect fold the cube is full of H’s, so every P lies outside. That decides where each H can go.”
  *Picture:* The 12-cube full of H’s turns a little so three faces show ("the cube, full of H’s"). Twelve H’s on the cube’s outline each get a stem and a P one step out into the empty space, fading in one pair after another ("every P, one step outside").
- **1:38** “An H between two P’s needs two neighbours outside, so it sits on an edge. A run of PHP’s is a rod.”
  *Picture:* The pairs fade out. The camera turns to the cube’s front-right edge, and a rod is laid down it with one soft tip: each H on the edge has a P off each of the two faces. Labels "rod, on an edge: PHP PHP PHP …", and under the cube "a P outside one face", "a P outside the other face".
- **1:46** “An H next to one P needs one, so it sits on a face. A run of PHHP’s is a ribbon.”
  *Picture:* The rod fades out and the camera turns back to three faces. A ribbon is laid near the back of the top face with one soft tip, a P above each H, the H’s in pairs. Label "ribbon, on a face: PHHP PHHP …".
- **1:52** “A long run of H’s, the core, has no P to put outside, so it can fill the inside.”
  *Picture:* The ribbon fades out. The outer beads of the cube’s front-top-right corner go one by one, in a wave from the corner, leaving a hole into the cube; then the core fades in on the hole’s three walls, H’s joined by chain sticks. Label "core, inside: HHHHHHHH …". In the tail the cube fades out, the camera moves back, and the empty wireframe fades in.

### 1:59 · A jigsaw with one solution (`frame`, 31.1 s)

- **2:00** “The front face and two of its edges are kept for the puzzle. The rest gets pieces so long that each has one place.”
  *Picture:* The empty wireframe cube. A list on the left, "the string, in order:", names rod 1, ribbon 1, rod 2, ribbons 2–5 and the core, each with a small chain (start, break, end), and last "front face, and two of its edges: kept for the puzzle". The front face is tinted and its two side edges are soft blue bars.
- **2:09** “Rod 1 is the longest walk along the edges: nine edges, all eight corners. Ribbon 1 covers the top, and rod 2 takes a tenth edge.”
  *Picture:* The tint and the inner edges go. Rod 1 is laid with one soft tip round nine edges and all eight corners (H’s only; a note under the list says the P’s sit outside and are not drawn), then ribbon 1 on the top face, then rod 2 down a tenth edge; rod 2 swells once and is named. Each list row gets its sub-line as its piece goes in and a tick when it is done.
- **2:19** “Five ribbons cover five faces and the core fills the inside. Only the front face is left, with its two free edges.”
  *Picture:* The blue bars step aside. Ribbons 2–5 fill the left, back, right and bottom faces, each with one soft tip, then the core is laid inside, back to front. The core fades out, and the open front face is left: its empty nodes as grey dots and its two free edges as blue bars. In the tail the list fades out.

### 2:30 · Walls cut out strips (`walls`, 19.0 s)

- **2:31** “On the front face, ribbons as long as a row become walls, joined by short rods on the two free edges.”
  *Picture:* The camera turns to face the front; the cube behind the face fades out early in the turn. Labels "free edge" (left and right) and "rod 1" (top and bottom row). The walls are laid in string order with one soft tip, each named "wall" on the left; the H’s between them on the free edges are short rods (one bracketed "short rod"). Where the string leaves the face, a dashed arc with an arrow joins the two H’s on the right edge. A note under the face: "the P’s are not drawn: they stick out in front of the cube, between pairs of H’s and along each dashed jump".
- **2:41** “The rod lengths leave the walls no slack, so they run straight across and cut the face into strips.”
  *Picture:* The labels go. Brackets mark each short rod with its length, in string order (2, 5, 2, 2, 5, 2, 1, 1); on the far right a bracket per period adds the right rods to 5, level with the 5 on the left. The strips between the walls light up as outlined boxes, named on the left "strip 1" and "strip 2" with "3 rows × 10 nodes". In the tail the brackets, bars and sub-lines go and the names move to the strips’ middle rows.

### 2:49 · Padding and plugs (`padding`, 28.2 s)

- **2:50** “A strip has more room than a bin. So each strip gets a padding, a ribbon that fills more than half of it.”
  *Picture:* The toy face of step 18 fades out; the cube’s thin outline grows to a bigger cube, and the sketch face fades in as one picture: 4 strips of 3 rows × 20, named "strip 1" to "strip 4" (badge "Sketch: a bigger cube / 4 strips of 3 rows × 20, 2 bins of 10"). The other strips fade and the camera closes on strip 1 ("strip 1, 3 rows × 20 nodes"; the rows above named "rod 1" and "wall"), with "bin 1, size 10" right under its right end. A grey padding (50 H’s) is laid in at one soft tip and leaves 10 nodes free, column for column above the bin. "rod 1" and "wall" give way to the padding’s outline and its name "padding, 50 H’s".
- **2:58** “Two paddings never fit in one strip, so each strip takes one and keeps a hole the size of a bin.”
  *Picture:* The camera pulls back to the whole face; strips 2–4 fade back in, hole 1 gets its box, and a legend appears (walls and rods, empty node, padding). A second padding in the same grey tries strip 1 ("a second padding"): only its last 10 H’s find room, in the hole; its other 40 lie right of the face, boxed in red: "no room, 40 H’s left over". It fades out. The strip names give way to "hole 1, 10 nodes"; strips 2, 3 and 4 get their paddings, each fading in whole, then each hole its box and its name left of the face ("hole 2, 10 nodes", and so on).
- **3:07** “The size of the cube sets the number of strips, often more than bins. Ribbons the size of a hole, called plugs, close the spare holes.”
  *Picture:* Holes 3 and 4 are marked "spare". Tan plugs (10 H’s) are laid into hole 3, then hole 4, each at one soft tip, and their names become "plug, 10 H’s"; the legend gains "plug (H’s)". A grey note between the two plug names says "the plugs could go in any 2 holes". Holes 1 and 2 stay open.

### 3:18 · The only choice left (`choice`, 33.5 s)

- **3:18** “Each item becomes a ribbon of its size. The other pieces have no real choice, so all that is left is which hole each item takes.”
  *Picture:* The plug note goes. The items 6, 2, 8, 4 fade in right of the face one after another, as bars in their colours with white size chips; the legend gains "items (H’s)". One at a time, in string order, each bar moves along one smooth curve into the hole on its row, its chip fades, and the bar gives way to its beads: 6 and 4 in hole 1, 2 and 8 in hole 2. The holes’ sub-lines read "6 + 4" and "2 + 8".
- **3:28** “So the string folds perfectly exactly when the items fit.”
  *Picture:* Two full bins fade in right of the holes, row for row, with dotted guides between them: bin 1 "6 + 4 = 10" and bin 2 "2 + 8 = 10", in the same colours, with green outlines. Between the face and the bins: ⟺ with the words "exactly when".
- **3:35** “Given a perfect fold, we read a packing off the face: the items in one hole form one bin.”
  *Picture:* "exactly when" goes and an arrow "fold ⇒ packing" fades in. The bins empty. Hole 1’s box lights up and bin 1 fills again from it, bar by bar (6, then 4), until its outline turns green and its sum shows; then hole 2 and bin 2 (2, then 8).
- **3:43** “Given a packing, we lay each item in the hole of its bin. Then we still have to join the ribbons up.”
  *Picture:* The arrow fades out and "packing ⇒ fold" fades in. The items fade off the face, leaving holes 1 and 2 empty. One at a time, in string order, each bar moves out of its bin straight along its row into the hole, its chip fades, and it gives way to its beads; the holes’ sub-lines are rebuilt. The frame stays full orange. Discs right of each hole, under the grey word "order", give each item’s place in the string (hole 1: 1, 4; hole 2: 2, 3). A panel "order in the string" (top left) shows the discs 1–4 with the three joins still missing, dashed; the legend gains "join still missing".

### 3:51 · Linkers (`linkers`, 32.5 s)

- **3:52** “Linkers, long runs of P’s, join consecutive ribbons. We write them before knowing a packing, so all have one length.”
  *Picture:* The face as one row of beads, "front face / its two holes end to end" (orange walls and rods, the two holes end to end), with fainter rows under it, "inside the cube". The items, numbered 1–4 ("order in the string"), come down into the holes. From the end of items 1, 2 and 3, one after another, a linker is laid bead by bead straight up into the space "in front of the cube". Each is tagged with the item it has to reach ("to ②"), and all end at one height ("all the same length").
- **4:01** “In front of the cube a switchboard brings the two ends of each linker side by side, and a loop uses up the P’s left over.”
  *Picture:* The linkers shrink to stubs and a switchboard panel appears: "switchboard / each line is a run of P’s". One after another, each linker goes up its stub, along its own lane to a pair of gates on the far side, round a loop of the P’s left over, and back down into the start of the next item. Where two routes cross, the one behind has a gap ("routes cross at / different depths"). One linker is followed, darker: "two ends side by side", "loop: the P’s left over".
- **4:11** “Put the bins in the other holes and the same linkers are only rerouted. They never meet, so the H’s fill the cube: a perfect fold.”
  *Picture:* The routes and loops fade. The two rows of items lift, change holes in an arch carrying their stubs, and land: "the bins swapped / the same linkers, only rerouted". The same linkers are routed again one after another, with new lanes and new loop sizes; "passes behind" points at one crossing. "every node / holds an H".

## Part 2, an example

### 4:24 · The puzzle, built in full (`instance`, 17.9 s)

- **4:25** “Now the same puzzle, built in full: items 6, 2, 8 and 4, and two bins of size 10.”
  *Picture:* The puzzle in the bin-packing game’s style: two empty bins, then the items 6, 2, 8 and 4 fade in one after the other. "the same puzzle as before: 6 + 4 and 2 + 8 fill the two bins".
- **4:31** “The recipe would build a cube of side 80. So that we can see every node, we use 2 strips instead of 6, which gives side 12.”
  *Picture:* The puzzle moves left and shrinks. A cube of side 80 comes in as a thin grey wireframe, "side 80"; note "the recipe: 6 strips, side 80". Our cube of side 12 fades in whole in its corner, as beads: frame and walls, its front face empty where the two strips go, "side 12" under its front edge; note "we use: 2 strips, side 12 / one strip per bin, so no plugs are needed". The wireframe fades, the camera moves in to the small cube, and its two strips get a thin outline.

### 4:42 · Its string (`string`, 16.4 s)

- **4:42** “The string has one H for each of the 1,728 nodes of the cube. Most of them form the frame and the core.”
  *Picture:* The string’s 1,728 H’s as one bar to scale, under "1,728 H’s, one for each node of the cube". It grows at one steady pace in string order: rod 1, ribbon 1, rod 2, ribbons 2–5 in orange, each named once it is laid ("frame · 606 H’s / two rods and five face ribbons"); the core as one long lighter stretch ("core · 1,002 H’s"); then the walls, paddings and items. Their 120 H’s are shown again five times wider: "walls · 60 H’s", "paddings and items · 60 H’s".
- **4:50** “It ends with two paddings of 20 and one ribbon per item, each after a linker of 626 P’s.”
  *Picture:* The end of the string enlarged, piece after piece in string order: the last of the walls, then linker – padding – linker – padding – linker – 6 – linker – 2 – linker – 8 – linker – 4, each linker "626 P’s", the size 2 in a chip under its small item. A bracket over the first three linkers: "routed in front of the cube, like the three between the items"; one under the items: "one ribbon per item". Under the row: "the bar above counts only the H’s; the linkers’ P’s come in between".

### 4:58 · Packing ⇒ perfect fold (`forward`, 38.2 s)

- **4:59** “Take the packing 6 + 4 and 2 + 8. The frame and walls are built as before and leave two strips of 3 rows by 10.”
  *Picture:* The packed bins of the puzzle wait on the right (6 + 4, 2 + 8). The 12-cube, already folded, fades in as a whole. Everything behind the front face fades out as one picture, then the camera turns to the face: two strips of 3 rows × 10, boxed and labelled on the left.
- **5:08** “Each padding snakes through two rows of its strip. The third row is a hole of 10 nodes, exactly a bin.”
  *Picture:* Grey paddings snake in one after the other, 20 H’s each. A small chevron in each gap shows the way the string runs. The strip boxes give way to hole boxes (one row of 10 nodes), and the bins slide next to the holes: same length, row for row.
- **5:16** “The item ribbons go into the holes as the items went into the bins. Now every node of the cube holds an H.”
  *Picture:* The items go into the holes in string order (6, 2, 8, 4). Each bar leaves its bin, moves straight left along its row onto its hole, and gives way to its ribbon: the bar shrinks from the ribbon’s start while the beads fade in under it. The face is full; the empty bins with their sums stay beside it.
- **5:24** “The linkers leave the face, pass through the switchboard and loop back, joining the ribbons in string order.”
  *Picture:* The rest of the face fades and the item beads slide into the side view of steps 26–28: the front face as one row of beads (the two holes end to end), the cube’s rows under it, the order discs 1–4 above the items, and a switchboard panel in front of the cube. Three linkers are laid one after another, bead by bead, each from the end of one item up through the switchboard, round its loop and down into the start of the next; crossings are drawn over and under. At the end all three are the same grey: "626 P’s each".

### 5:36 · Perfect fold ⇒ packing (`backward`, 9.0 s)

- **5:37** “Backwards, any perfect fold gives a packing: read the holes. 6 and 4 share one, 2 and 8 the other.”
  *Picture:* Face-on view of the full front face, frame in full orange. We read the holes one after the other: a bar of the game grows over each ribbon in turn, from the ribbon’s first bead, and gets its size. Then the hole’s bars lift and move together into the empty bin on its row, which turns full: 6 + 4 = 10, 2 + 8 = 10. The ribbons stay in the holes.

### 5:45 · When the items do not fit (`no`, 17.9 s)

- **5:46** “Now try items 6, 6, 6 and 2. Two 6’s never share a hole of 10, so one 6 has no place.”
  *Picture:* Same face, frame in full orange, holes empty. The items 6, 6, 6, 2 wait on the right in a column, as the game’s bars. In string order, each goes along one smooth path, beside the face to its hole’s row and into the hole, and gives way to its beads; the column closes up. The first 6 goes into hole 1, the second into hole 2. The third 6 tries hole 2, sticks out past the edge, gets a red outline ("only 4 nodes free") and goes back. The 2 goes next to the first 6. The third 6 is marked "no place".
- **5:54** “Some nodes of the cube stay empty. This string has no perfect fold, and its best fold has fewer contacts.”
  *Picture:* The empty nodes get dashed red rings one by one (2 in hole 1, 4 in hole 2) and a counter, "6 nodes empty". The hole labels step aside, and short red dashes run from each empty node to its H neighbours: "contacts lost". Under "no place", in grey: "it folds in front of the cube".

## Part 3, in general

### 6:03 · Folding is as hard as packing (`end`, 23.9 s)

- **6:04** “The string has n³ H’s plus the linkers, so it grows with the sizes. That is fine because bin packing stays hard with small sizes.”
  *Picture:* Two thin grey wire cubes to scale, side by side: the recipe’s cube for items 6, 2, 8, 4 ("side 80, 80³ = 512,000 H’s"), and for every size tripled, items 18, 6, 24, 12 ("side 138, 138³ = 2,628,072 H’s").
- **6:14** “So a program that finds best folds would also solve bin packing. HP folding on the cubic grid is NP-complete.”
  *Picture:* The cubes fade. The plan’s picture is built again: puzzle ("a hard puzzle") → HP string → best fold, and the arrow back, "fits / does not fit". Reference in small type: Berger and Leighton, J. Comput. Biol. 5(1), 1998. Then "a fast program?", one pass of the dot round the loop, and "at least as hard".
