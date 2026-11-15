# Storyboard

Generated from `src/script.ts` by `node scripts/storyboard.ts`. Length 6:09 at 30 fps.
Captions are the only text; each stays up for its reading time (15 characters a second) plus a pause to look.

### 0:00 · Title card (`title`, 4.5 s)

No caption.

## Part 1, the idea

### 0:05 · The folding problem (`fold`, 27.8 s)

- **0:05** “An HP string is a chain of H's and P's. A fold lays it on the grid, one letter per node, without crossing itself.”
  *Picture:* A 12-letter string (H filled orange, P hollow blue, letters above) lies straight; the letters give way to an H/P key and the string slides head first onto the grid, into a hairpin fold.
- **0:14** “Two H's that touch on the grid but are not joined in the chain make a contact. A best fold has the most contacts.”
  *Picture:* Gold dashed contacts appear one by one; a counter "contacts: 4" counts them.
- **0:23** “On the cubic grid, finding a best fold is NP-complete. Berger and Leighton proved it in 1998, and this is their proof.”
  *Picture:* The fold stays with its key and counter; the camera pulls back as the grid around it grows.

### 0:32 · The plan (`plan`, 22.2 s)

- **0:33** “They start from bin packing: can items of given sizes fill bins of one size exactly?”
  *Picture:* The bin-packing game look: items 6, 2, 8, 4 as coloured bars of cells, two empty bins of 10. The items slide in: 6 + 4, 2 + 8. Both bins full.
- **0:40** “For each such puzzle we write one HP string. Its best fold shows whether the items fit.”
  *Picture:* An arrow from the puzzle to a long HP string (beads, shortened by a break mark), then from the string to a small cube of H’s.
- **0:47** “So a fast folding program would also solve bin packing, and folding is at least as hard.”
  *Picture:* A second arrow back from the cube to the puzzle, labelled "fits / does not fit".

### 0:55 · Why a cube (`cube`, 26.9 s)

- **0:55** “First, the shape of a best fold. Each H has six neighbours, and each neighbour that is not an H is a contact lost.”
  *Picture:* One H and its six neighbours (grey rings). Three fill with H’s: two joined to it ("chain"), one by a gold dashed "contact". The other three turn red, each labelled "lost".
- **1:04** “So n³ H's make the most contacts when they show the least surface: when they fill a cube.”
  *Picture:* A chain of 27 H’s as a flat 9 × 3 slab, a red stub on every side that touches no H; a key counts them: "9 × 3 slab 78". The outer thirds fold like an accordion into a 3 × 3 × 3 cube: "3 × 3 × 3 cube 54".
- **1:13** “We call such a fold perfect, and spell the string so that it folds perfectly exactly when the items fit.”
  *Picture:* The 3-cube grows shell by shell into the 12-cube, full of H’s, while the camera pulls back. Label "a perfect fold: every node holds an H".

### 1:21 · P's stay outside (`local`, 30.0 s)

- **1:22** “In a perfect fold the cube is full of H's, so every P lies outside. That decides where each H can go.”
  *Picture:* The 12-cube full of H’s ("inside: only H’s"). P’s pop up one step outside the three faces we see, each on a stem to its H ("every P sits one step outside").
- **1:30** “An H between two P's needs two neighbours outside, so it sits on an edge. A run of PHP's is a rod.”
  *Picture:* The camera comes closer and the cube dims. A rod is laid along the top-front edge, each H with a P above and a P in front. Label "rod, on an edge: PHP PHP PHP …".
- **1:38** “An H next to one P needs one, so it sits on a face. A run of PHHP's is a ribbon.”
  *Picture:* Same view. A ribbon is laid in a row across the top face, one P above each H. Label "ribbon, on a face: PHHP PHHP …".
- **1:44** “A long run of H's, the core, has no P to put outside, so it can fill the inside.”
  *Picture:* Back to the whole cube. Its front-top-right corner is cut away and the H’s inside light up. Label "core, inside: HHHHHHHH …". In the tail the beads go, leaving the outline.

### 1:51 · A jigsaw with one solution (`frame`, 30.4 s)

- **1:52** “We spell exactly as many of each piece as the cube needs, and make them so long that each has one place.”
  *Picture:* The empty cube outline. Piece names fade in as a legend: rod, ribbon, core.
- **2:00** “The first rod is as long as a walk along the edges can be: nine edges and all eight corners. A second rod takes a tenth.”
  *Picture:* The corner rod’s H’s run along the edges in string order (top face, down an edge, bottom face). Then the tenth-edge rod fills the back-left edge. The two front vertical edges stay empty and are labelled "free edges".
- **2:11** “Five ribbons cover five faces and the core fills the inside. Only the front face is left, with its two free edges.”
  *Picture:* The core’s block of H’s appears inside, then the five faces fill (back, left, bottom, right, top) as snakes. The front face stays open: lattice points only.

### 2:22 · Walls cut out strips (`walls`, 19.0 s)

- **2:22** “On the front face, ribbons as long as a row become walls, joined by short rods on the two free edges.”
  *Picture:* The camera turns to face the front. One period is laid in string order: rod up the right edge, wall right to left, rod down the left edge, wall back, rod up. Then the second period.
- **2:32** “The rod lengths leave the walls no slack, so they run straight across and cut the face into strips.”
  *Picture:* The q strips between the walls light up as bands of empty nodes, labelled "strip 1", "strip 2".

### 2:41 · Padding and plugs (`padding`, 26.1 s)

- **2:41** “A strip has more room than a bin. So each strip gets a padding, a ribbon that fills more than half of it.”
  *Picture:* Schematic in the bin-packing game’s style: four strips as long bars of cells; a grey padding bar slides into strip 1.
- **2:50** “Two paddings never fit in one strip, so each strip takes one and keeps a hole of B nodes, the size of a bin.”
  *Picture:* A second padding tries strip 1 and runs into the first (red rings, "no room"), backs out and goes to strip 2. Strips 3 and 4 get theirs; every hole is marked "B".
- **2:59** “When there are more strips than bins, ribbons of B H’s called plugs close the spare holes.”
  *Picture:* Two light-grey plugs fill the holes of strips 3 and 4. Strips 1 and 2 keep their holes, labelled "bin 1", "bin 2".

### 3:07 · The only choice left (`choice`, 33.5 s)

- **3:08** “Each item becomes a ribbon of its size. Every other piece has one place, so the only choice left is which hole each item takes.”
  *Picture:* Item ribbons 6, 2, 8, 4 (item colours) wait beside the two holes; they slide in: 6 + 4, 2 + 8.
- **3:17** “So the string folds perfectly exactly when the items fit.”
  *Picture:* Still frame. The two full holes, and the bins of the puzzle beside them, same colours.
- **3:25** “Given a perfect fold, we read a packing off the face: the items in one hole form one bin.”
  *Picture:* Arrow "fold ⇒ packing": the ribbons lift out of the holes into the bins.
- **3:32** “Given a packing, we lay each item in the hole of its bin. Then we still have to join the ribbons up.”
  *Picture:* Arrow "packing ⇒ fold": the items go back into the holes; gaps between consecutive ribbons in the string are marked.

### 3:40 · Linkers (`linkers`, 28.6 s)

- **3:41** “Linkers, long runs of P's, join consecutive ribbons. We write them before knowing a packing, so all have one length.”
  *Picture:* Back to 3D, the cube from the front-left. From each ribbon end a chain of P’s goes straight out of the front face.
- **3:50** “In front of the cube a switchboard brings the two ends of each linker side by side, and a loop uses up the P's left over.”
  *Picture:* A translucent box labelled "switchboard" in front of the face; the P chains enter it; on its far side, loops stick out. One linker is highlighted end to end.
- **4:01** “The linkers stay outside the cube and never meet, so the H's still fill it. The fold is perfect.”
  *Picture:* Slow orbit of the whole fold.

## Part 2, an example

### 4:09 · An example (`instance`, 16.6 s)

- **4:10** “Now an example: items 6, 2, 8 and 4, and two bins of size 10.”
  *Picture:* The puzzle in the bin-packing game’s style, empty bins.
- **4:16** “The recipe would build a cube of side 80. So that we can see every node, we use 2 strips instead of 6, which gives side 12.”
  *Picture:* A cube of side 80 (outline, tiny lattice) shrinks to the cube of side 12. The badge "toy: 2 strips instead of 6" appears top right and stays for the rest of the video.

### 4:26 · Its string (`string`, 16.4 s)

- **4:26** “The string has one H for each of the 1,728 nodes of the cube. Most of them form the frame and the core.”
  *Picture:* The string as a bar, each piece to scale and coloured: rods, face ribbons, core, walls, then the item part. The core is the long middle stretch.
- **4:34** “It ends with two paddings of 20 and one ribbon per item, each after a linker of 626 P's.”
  *Picture:* The item part enlarged: linker – padding – linker – padding – linker – 6 – linker – 2 – linker – 8 – linker – 4.

### 4:42 · Packing ⇒ perfect fold (`forward`, 36.7 s)

- **4:43** “Take the packing 6 + 4 and 2 + 8. The frame and walls fold as before and leave two strips of 3 rows by 10.”
  *Picture:* The 12-cube builds fast (edges, core, faces, walls). The camera turns to the front face: two strips of 3 × 10 empty nodes.
- **4:52** “Each padding snakes through two rows of its strip. The third row is a hole of 10 nodes, exactly a bin.”
  *Picture:* Grey paddings snake in, 20 H’s each. The bins of the puzzle slide next to the holes: same length, row for row.
- **5:00** “The item ribbons go into the holes as the items went into the bins. Now every node of the cube holds an H.”
  *Picture:* Items fly from the bins into the rows: 6 + 4 in strip 1, 2 + 8 in strip 2. The face is full.
- **5:08** “The linkers leave the face, pass through the switchboard and loop back, joining the ribbons in string order.”
  *Picture:* 3D view from the front-left: six linkers, each a chain of P’s out of the face into the switchboard box, loops beyond it (drawn shortened, labelled "626 P’s each").

### 5:19 · Perfect fold ⇒ packing (`backward`, 9.0 s)

- **5:19** “Backwards, any perfect fold gives a packing: read the holes. 6 and 4 share one, 2 and 8 the other.”
  *Picture:* Face-on view of the full front face; the two hole rows lift off and become the two bins of the puzzle.

### 5:28 · When the items do not fit (`no`, 17.9 s)

- **5:28** “Now try items 6, 6, 6 and 2. Two 6's never share a hole of 10, so one 6 has no place.”
  *Picture:* Same face, holes empty; the items 6, 6, 6, 2 wait on the right as the game’s bars. 6 goes into hole 1, 6 into hole 2, 2 next to the first 6. The third 6 tries hole 2, sticks out past the edge, turns red and goes back: "no place".
- **5:37** “Some nodes of the cube stay empty. This string has no perfect fold, and its best fold has fewer contacts.”
  *Picture:* The empty nodes get red rings one by one (2 in hole 1, 4 in hole 2) and a counter: "6 nodes empty".

### 5:46 · Conclusion (`end`, 23.4 s)

- **5:46** “The string has about n³ letters, so it grows with the sizes. That is fine because bin packing stays hard with small sizes.”
  *Picture:* The real cube of side 80 next to the toy, with "512,000 H’s" and "1,728 H’s".
- **5:56** “So a program that finds best folds would also solve bin packing. HP folding on the cubic grid is NP-complete.”
  *Picture:* The two arrows of the plan again: puzzle → string → fold → answer. Reference: Berger and Leighton, J. Comput. Biol. 5(1), 1998.
