/**
 * Scene "forward": a packing gives a perfect fold. The packed bins of the puzzle wait on the right.
 * The frame and walls are known from steps 14–17, so they come in whole, as one picture (never
 * piece by piece, which would read as two parts of the string growing at once). Everything behind
 * the front face fades out, then the camera turns to the face: two strips of 3 × 10. The paddings
 * snake in one after the other, a chevron in each gap between their pairs showing the way the
 * string runs, and leave one row of 10 in each strip, a hole; the bins slide next to the holes,
 * row for row. Then the items go into the holes in string order: each bar leaves its bin and moves
 * straight left along its row onto the hole, then gives way to its beads, which fade in from the
 * ribbon's start. Then the picture becomes the flat side view of the linkers (lib/linkerBoard):
 * the item beads themselves move onto the face's edge while the rest of the face fades, and the
 * linkers grow one after the other through the switchboard, each from the end of one ribbon to the
 * start of the next.
 *
 * Every cue is also a step of the page, paused at cue.to − 10: each cue's motion ends before that.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, mixShot, projector, type Shot } from '../three/Scene3D';
import { FRAME_SHOT, CUBE_SHELL } from '../three/cube';
import { ItemBar, BinTrack, BinSum, trackWidth, trackHeight, slotX, TRACK_PAD } from '../ui/Bins';
import { ramp, sec, clamp01, lerp, easeOut, easeInOut } from '../lib/anim';
import { C, FONT, W, H, itemColor } from '../theme/theme';
import * as M from '../model/toy';
import type { V3 } from '../model/toy';
import type { SceneTime } from '../script';
import { newDraw, drawFrame, drawWalls, drawPaddings, drawRibbon, addHoles, faceOutline, stripBox, softFor } from './lib/face';
import { faceShot, faceGeom, holeCells, holeRow, giveWay, BoxLabel, FACE_SHIFT } from './lib/backwardFace';
import { LinkerBoard, placement, itemPts, routes, type Pt } from './lib/linkerBoard';

/** the face-on geometry the bins line up with (the shot of cues 1–3) */
const G = faceGeom(projector(faceShot(1)));
/** for each bin: its items in order, with their first cell in the hole */
const ROWS = M.PACKING.map((items, s) => {
  let a = 0;
  return items.map((u) => {
    const r = { s, u, size: M.SIZES[u], first: a, cells: holeCells(s, a, M.SIZES[u]) };
    a += M.SIZES[u];
    return r;
  });
});
/** the items in the order they go in: string order (6, 2, 8, 4), as the string is laid */
const FLY = ROWS.flat().sort((a, b) => a.u - b.u);
/** before they line up, the bins sit closer together, around the middle of the two holes */
const MID = (G.holeY(0) + G.holeY(1)) / 2;
const startHoleY = (s: number) => MID + (s === 0 ? -62 : 62);
/** cue 4: the items on the face-on view, and on the side view of the linkers */
const PROJ = projector(faceShot(1));
const RIBBONS = M.placeItems(M.SIZES, M.PACKING);
const PLACE = placement(M.PACKING);
const ROUTES = routes(M.PACKING);

/** a gentle ease for the camera turn: its top speed is half that of the cubic in-out */
const easeSine = (t: number) => (1 - Math.cos(Math.PI * clamp01(t))) / 2;
const lin = (t: number) => clamp01(t);
/** the frames each padding takes to snake in */
const PAD_FRAMES = sec(2.0);
/**
 * The gaps between the pairs of a padding, in string order: where the string leaves the face
 * between two pairs (its P's stand out towards the viewer). Each gets a chevron pointing the way
 * the string runs; `at` is the letter of the piece where the laying tip passes it.
 */
const PAD_GAPS = M.strips.map((st) => {
  const cells = st.padding;
  const out: { a: V3; b: V3; at: number }[] = [];
  // ribbonChain: pair k is the letters P H H P, 4k..4k+3, so the gap after it is at letter 4k+4
  for (let k = 0; 2 * k + 2 < cells.length; k++) out.push({ a: cells[2 * k + 1], b: cells[2 * k + 2], at: 4 * k + 4 });
  const letters = 2 * cells.length;
  return { gaps: out, letters, soft: softFor(letters, PAD_FRAMES) };
});

/** when the turn to the face starts (s after the cue): the cube behind the face has gone by then */
const TURN_AT = 5.2;

export default function ForwardScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1, c2, c3] = scene.cueTimes;

  // ---- cue 1: the packing; the frame and walls as one picture; the turn to the face; the strips
  const binsIn = ramp(f, c0.from, sec(0.6));
  const cubeIn = ramp(f, c0.from + sec(0.7), sec(0.7));
  // everything behind the front face fades out (see-through) before the camera starts to turn
  const backFade = ramp(f, c0.from + sec(4.2), sec(0.8));
  const turn = ramp(f, c0.from + sec(TURN_AT), sec(2.0), easeSine);
  const stripsIn = ramp(f, c0.from + sec(7.4), sec(0.5));

  // ---- cue 2: paddings one after the other; the strips give way to their holes; the bins line up
  const pads = [ramp(f, c1.from + sec(0.4), PAD_FRAMES, lin), ramp(f, c1.from + sec(2.6), PAD_FRAMES, lin)];
  const stripOut = ramp(f, c1.from + sec(4.8), sec(0.3));
  const holeIn = ramp(f, c1.from + sec(5.15), sec(0.35));
  // linear here: where it is used it is eased once (easing it twice made the middle of the move a jump)
  const align = ramp(f, c1.from + sec(5.7), sec(1.1), lin);
  const chevOut = ramp(f, c2.from, sec(0.3));

  // ---- cue 3: the items, one at a time in string order: each bar leaves its bin, moves straight
  // into its hole, and gives way to its beads
  const fly = FLY.map((it, i) => {
    const at = c2.from + sec(0.45 + i * 1.75);
    const go = ramp(f, at, sec(0.95));
    const revealAt = at + sec(1.2);
    return {
      go,
      lift: Math.sin(Math.PI * go),
      chip: 1 - ramp(f, at + sec(0.95), sec(0.25)),
      way: giveWay(it.cells, it.size, f - revealAt),
      revealing: f >= revealAt - sec(0.2),
      // its slots in the bin show their dots once the bar has moved off them
      freed: ramp(f, at + sec(0.3), sec(0.3)),
    };
  });
  /** a bin is full until its first item leaves */
  const binFull = [0, 1].map((s) => 1 - Math.max(...FLY.map((it, i) => (it.s === s ? fly[i].freed : 0))));

  // ---- cue 4: the side view. The flat items come in over the 3D ribbons, exactly where they lie
  // and looking the same; then the 3D ribbons go (unseen, under them), the rest of the face fades,
  // and only then do the items move: the beads themselves, never a copy over a fading original
  const binsOut = ramp(f, c3.from, sec(0.35));
  const xfade = ramp(f, c3.from + sec(0.05), sec(0.3));
  const swapped = f >= c3.from + sec(0.35);
  const fade3D = ramp(f, c3.from + sec(0.4), sec(0.6));
  const slide = ramp(f, c3.from + sec(0.9), sec(1.2));
  // the board's cube rows come in only once the 3D face has gone, never under it
  const band = ramp(f, c3.from + sec(1.2), sec(0.6));
  const boardLab = ramp(f, c3.from + sec(1.2), sec(0.5));
  const order = ramp(f, c3.from + sec(1.4), sec(0.5));
  const box = ramp(f, c3.from + sec(1.6), sec(0.5));
  const lay = ROUTES.map((_, k) => c3.from + sec(2.2 + 1.6 * k));
  const grow = lay.map((at) => ramp(f, at, sec(1.5), (t) => t));
  const glow = lay.map((at, k) => ramp(f, at - sec(0.1), sec(0.3)) * (k === lay.length - 1 ? 1 : 1 - ramp(f, at + sec(1.6), sec(0.4))));
  const each = ramp(f, c3.from + sec(7.2), sec(0.5));
  const inBoard = f >= c3.from;

  // camera: the cube turning slowly (moved left, to leave the bins room), then the face
  const spin = easeOut(clamp01((f - c0.from) / sec(TURN_AT)));
  const buildShot: Shot = { ...FRAME_SHOT(lerp(0.35, 1, spin)), offset: [FACE_SHIFT, 0] };
  const shot = mixShot(buildShot, faceShot(1), turn);
  const project = projector(shot);

  const d = newDraw();
  drawFrame(d, { backFade });
  drawWalls(d, 1);
  drawPaddings(d, pads, { frames: PAD_FRAMES });
  // each ribbon fades in bead by bead as its bar gives way; after the swap of cue 4 the board's
  // beads stand where they were
  if (!swapped) FLY.forEach((it, i) => fly[i].revealing && drawRibbon(d, it.cells, itemColor(it.u), 1, { beadOpacity: fly[i].way.bead }));
  addHoles(d, { opacity: 0.9, free: 0 });
  // the cube's outline as the camera sees it, all through the turn: the far edges of the top and
  // right faces fade with the cube behind the face, then the front square is the outline
  d.lines.push(...faceOutline(0.6, backFade, C.fgSubtle, true));

  const binsO = binsIn * (1 - binsOut);
  const faceO = 1 - fade3D;
  const faceLeft = project([-0.5, 0, 0])[0];

  return (
    <SceneFrame scene={scene}>
      {/* the cube: one picture, coming in and going as a whole */}
      <div style={{ position: 'absolute', inset: 0, opacity: cubeIn * faceO }}>
        <Scene3D shot={shot} beads={d.beads} sticks={d.sticks} lines={d.lines} panels={d.panels} solids={d.solids} shell={CUBE_SHELL} />
      </div>
      <svg width={W} height={H} viewBox={`0 0 ${W} ${H}`} textRendering="geometricPrecision" style={{ position: 'absolute', inset: 0, overflow: 'visible' }}>
        <g fontFamily={FONT.sans}>
          {/* the strips (cue 1), then their holes (cue 2): one label style for both */}
          {[0, 1].map((s) => (
            <g key={s}>
              <BoxLabel box={stripBox(project, s, 0.5)} faceLeft={faceLeft} title={`strip ${s + 1}`} sub={`${M.strips[s].rows.length} rows × ${M.n - 2} nodes`} opacity={stripsIn * (1 - stripOut)} />
              <BoxLabel box={stripBox(project, s, 0.5, [holeRow(s)])} faceLeft={faceLeft} title={`hole ${s + 1}`} sub={`${M.B} nodes`} opacity={holeIn * faceO} />
            </g>
          ))}
          {/* the way each padding runs: a chevron in each gap between its pairs, as the tip passes */}
          {chevOut < 1 &&
            PAD_GAPS.map(({ gaps, letters, soft }, s) => {
              const head = pads[s] * (letters + soft);
              return gaps.map((g, k) => {
                const o = clamp01((head - g.at) / soft) * (1 - chevOut);
                if (o <= 0) return null;
                return <Chevron key={`${s}-${k}`} a={project(g.a)} b={project(g.b)} opacity={o} />;
              });
            })}
          {/* the bins of the puzzle, packed; they line up with the holes; their sums stay */}
          {binsO > 0 &&
            [0, 1].map((s) => {
              const hy = lerp(startHoleY(s), G.holeY(s), easeInOut(align));
              const ty = hy - G.h / 2 - TRACK_PAD;
              const th = trackHeight(G.h);
              return (
                <g key={`b${s}`} opacity={binsO}>
                  <BinTrack x={G.trackX} y={ty} B={M.B} unit={G.u} h={G.h} label={`bin ${s + 1}`} full={binFull[s]} dots={false} />
                  {FLY.map((it, i) =>
                    it.s === s && fly[i].freed > 0
                      ? Array.from({ length: it.size }, (_, k) => <circle key={`${i}-${k}`} cx={slotX(G.trackX, it.first + k, G.u) + G.u / 2} cy={ty + th / 2} r={3} fill={C.lattice} opacity={fly[i].freed} />)
                      : null,
                  )}
                  <BinSum x={G.trackX + trackWidth(M.B, G.u) + 26} y={ty + th / 2 + 9} items={ROWS[s]} B={M.B} />
                </g>
              );
            })}
          {/* the items: in their bins, then each moves straight left along its row onto its hole and
              gives way to its beads */}
          {FLY.map((it, i) => {
            const { go, lift, chip, way } = fly[i];
            if (way.gone) return null;
            const hy = lerp(startHoleY(it.s), G.holeY(it.s), easeInOut(align));
            const x = lerp(slotX(G.trackX, it.first, G.u), G.barX(1 + it.first), go);
            const y = hy - G.h / 2 - 14 * lift;
            return (
              <ItemBar
                key={`it${i}`}
                x={x}
                y={y}
                size={it.size}
                color={itemColor(it.u)}
                unit={G.u}
                h={G.h}
                opacity={go > 0 ? 1 : binsO}
                lift={lift}
                chipOpacity={chip}
                span={way.span}
                sliverFade={false}
              />
            );
          })}
        </g>
      </svg>
      {inBoard && (
        <svg width={W} height={H} viewBox={`0 0 ${W} ${H}`} style={{ position: 'absolute', inset: 0 }}>
          <LinkerBoard
            items={PLACE.map((p) => {
              const to = itemPts(p);
              const from = RIBBONS[p.u]!.map((v) => PROJ(v));
              return { u: p.u, opacity: xfade, pts: to.map((q, i) => [lerp(from[i][0], q[0], slide), lerp(from[i][1], q[1], slide)] as Pt) };
            })}
            band={band}
            routes={ROUTES.map((r, k) => ({ r, grow: grow[k], glow: glow[k] }))}
            box={box}
            lab={{ face: boardLab, cube: boardLab, holes: boardLab, out: boardLab, order, switchboard: box, depths: each, each, eachText: `${M.TOY.linker} P’s each` }}
          />
        </svg>
      )}
    </SceneFrame>
  );
}

/** a small chevron in the gap between two beads a → b (screen points), pointing from a to b */
function Chevron({ a, b, opacity }: { a: [number, number]; b: [number, number]; opacity: number }) {
  const l = Math.hypot(b[0] - a[0], b[1] - a[1]) || 1;
  const dx = (b[0] - a[0]) / l;
  const dy = (b[1] - a[1]) / l;
  const mx = (a[0] + b[0]) / 2;
  const my = (a[1] + b[1]) / 2;
  const back = 2.6;
  const half = 6.5;
  const p = (s: number) => `${mx - back * dx + s * half * -dy} ${my - back * dy + s * half * dx}`;
  return <path d={`M ${p(1)} L ${mx + back * dx} ${my + back * dy} L ${p(-1)}`} fill="none" stroke={C.fgMuted} strokeWidth={2.5} strokeLinecap="round" strokeLinejoin="round" opacity={opacity} />;
}
