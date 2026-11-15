# Explainer video: Berger and Leighton's reduction

A captions-only video (about 6 minutes, 1920 × 1080, 30 fps) of how Berger and Leighton (1998)
turn any bin packing puzzle into an HP string whose best fold on the cubic grid answers the
puzzle, so that finding a best fold is NP-complete. Part 1 explains the idea; part 2 runs it on
the site's running example (items 6, 2, 8, 4 into two bins of 10) in a toy-sized cube.

The video is for understanding the proof. It does not present the team's own proof in `proof/`.

## Step through it (the main way to watch)

A page plays the video one caption at a time and waits on the finished picture after each, so you
can go through the construction at your own pace: 41 numbered steps in two parts.

```bash
cd explainer-video
npm install
npm run stepper         # → http://localhost:5199
```

A thin bar under the picture shows where you are inside the current step; drag it to look again at
part of a step. Keys: Space (or a click on the picture) plays and pauses, and at the end of a step
goes on to the next; → next step (a press while a step is still playing jumps to its end); ← the
step before; Shift+← and Shift+→ two seconds back and forward inside the step; End the step's
finished picture; R replays the step; F full screen; Home the first step.

The 3D is drawn live, so on any 3D picture you can drag to turn the camera round what it looks
at and scroll to zoom; labels pinned to the cube follow. "Reset view" (or V) eases back to the
scripted camera, and every new step starts from its own camera. Renders never turn the view, so
the MP4 stays as scripted. The numbered pills below jump to any step, `#12` in
the address opens step 12, and "Play through" runs on without stopping. `npm run stepper:build` writes a static copy to `out/stepper/` that opens from any web
server.

The page is `stepper/` (a Vite app around a Remotion Player that plays `src/Video.tsx`); the
steps come from the captions in `src/script.ts` (`stepper/steps.ts`), so editing a caption or its
timing updates the page.

## Render

Everything is installed locally in this folder.

```bash
cd explainer-video
npm install
npm run render          # → out/explainer.mp4 (the whole video)
```

Other commands:

| Command | What it does |
|---|---|
| `npm run studio` | Opens Remotion Studio to scrub through the video and each scene |
| `npx remotion render src/index.ts scene-frame out/frame.mp4` | Renders one scene (ids: see `src/script.ts`) |
| `npm run still -- out/x.png --frame=900` | Renders one frame of the whole video |
| `npm run steps` | Renders the picture each step stops on to `out/steps/step-NN.png` (about 20 s; `npm run steps -- 7 12-15` for some) |
| `node scripts/flicker-frames.ts <dir> <from> <to>` then `python3 -I scripts/flicker.py <dir> --show <dir>/hits.png` | Flicker check: renders every frame of a range at half size (about 100 frames a second), then lists frames where something pops or blinks for one frame while the picture around it is still, with close-ups |
| `npm run storyboard` | Rewrites `storyboard.md` (scenes, captions, timings) from `src/script.ts` |
| `npm run check` | Type-checks, then tests the toy model (`src/model/model.test.ts`) |

A full render takes several minutes (the 3D is drawn by headless Chrome through WebGL).

## Why Remotion and three.js

The video should look like the site, and the 3D should look like the site's folding game, because
that is what readers of the site will have seen. Remotion renders React components frame by frame
into an MP4, so the video can use the site's colour tokens and fonts (Source Serif 4, Inter)
directly. The 3D uses three.js with the folding game's own shaders (`src/three/shaders.ts`, ported
from `site/src/widgets/fold-game/render/three3d-scene.ts`): H's are the same lit orange beads, P's
the same hollow blue beads, the backbone and contacts the same sticks. Every frame is a pure
function of the frame number, so renders are repeatable. Labels and 2D figures are SVG on top of
the 3D. The bin packing figures copy the look of the site's bin packing game.

Manim was the other candidate; it would have meant redrawing the game's look in Python and kept
the video apart from the site's styles.

## The toy example and what it simplifies

The recipe sets q = 2·max(K, ⌈B^(1/3)⌉). For the example (K = 2 bins of B = 10) that is q = 6, a
cube of side n = q(2q + 1) + 2 = 80 and 512,000 H's, too many to see. The video takes q = 2
instead, the smallest q with q ≥ K, q even and strips longer than two bins. Every other number
follows the recipe: side n = 12 (1,728 H's), strips of T = (2q − 1)(n − 2) = 30 nodes, paddings of
T − B = 20, linkers of 52n + 2 = 626 P's. `src/model/toy.ts` builds this cube and string;
`npm run check` verifies that the fold fills the cube exactly and keeps the parity rules.

What the video draws in a simplified way (and says so on screen where it matters):

- With q = K there are no plugs in the toy, so the plugs appear only in the part 1 schematic.
- In face-on views the P's are hidden, since they sit in front of the H's; H's of a ribbon are drawn joined in pairs.
- Linkers are drawn shortened. The routes inside the switchboard are not drawn.

## Files

| Path | Contents |
|---|---|
| `src/script.ts` | Every scene, its captions and what the picture shows under each; timing comes from reading speed |
| `storyboard.md` | The script as a readable storyboard (generated) |
| `src/model/toy.ts` | The toy cube and string: frame, walls, strips, paddings, items, links (no drawing code) |
| `src/three/` | The 3D stage (`Scene3D.tsx`), the game's shaders, pieces of the cube with their P's (`cube.ts`) |
| `src/ui/` | Captions, scene titles, the toy badge, bin packing bars (`Bins.tsx`) |
| `src/scenes/` | One file per scene; helpers shared by several scenes in `src/scenes/lib/` |
| `src/Video.tsx` | The whole video: every scene in order (used by the render and by the step page) |
| `stepper/` | The step-through page |
| `src/theme/` | The site's colour tokens and fonts |
| `out/` | Renders (not in git) |

## Sources

Berger, B. and Leighton, T. (1998). Protein folding in the hydrophobic-hydrophilic (HP) model is
NP-complete. *Journal of Computational Biology* 5(1), 27–40. The video paraphrases the
construction; it quotes nothing and shows no figure from the paper.
