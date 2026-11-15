/**
 * Scene "padding": the front face of a bigger cube, four strips, for a puzzle with two bins.
 * Cue 1: it opens on the toy face exactly as "walls" leaves it. The toy face fades out, the cube's
 *        outline grows to a bigger cube while the camera pulls back, and the sketch (four strips of
 *        3 × 20) fades in as one picture, its strips named. The camera closes in on strip 1, with
 *        "rod 1" and "wall" above it and a bin of 10 right under its right end, column for column.
 *        A padding (50 H's) is laid in at one soft tip and leaves a hole as long as the bin.
 * Cue 2: the camera pulls back and the other strips return; hole 1 gets its box. A second padding
 *        (the same grey) tries strip 1: only its last 10 H's find room, in the hole; its other 40
 *        lie outside the face ("no room"). It goes. The strips' names give way to hole 1's label;
 *        strips 2, 3 and 4 get their paddings, one after another, and every hole its box and label.
 * Cue 3: holes 3 and 4 are marked "spare"; plugs are laid into them, one after the other, and their
 *        labels become "plug". A note between the two plugs says they could go in any 2 holes.
 * The last frame is the first frame of the scene "choice".
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, projector, mixShot, type Bead, type Stick, type Shot } from '../three/Scene3D';
import { FRAME_SHOT, FACE_SHOT } from '../three/cube';
import { BinTrack, trackHeight, TRACK_PAD } from '../ui/Bins';
import { C, FONT, W, H } from '../theme/theme';
import { ramp } from '../lib/anim';
import * as M from '../model/toy';
import type { V3 } from '../model/toy';
import type { SceneTime, CueTime } from '../script';
import * as F from './lib/face';
import * as S from './lib/padding-sketch';

/** the height of an item bar (and a bin's slot) at the sketch's scale, shared with "choice" */
export const BIN_H = 37;

// ------------------------------------------------------------------ the toy face of "walls"

/** the toy face (12 × 12, its nodes at x, y = 0..11) sits on the sketch's top-left corner, moved up by LIFT */
const LIFT: V3 = [0, S.ROWS - M.n, 0];
/** where "walls" ends: its camera, face-on */
const WALLS_SHOT = mixShot(FRAME_SHOT(1), FACE_SHOT, 1);
const wallsProject = projector(WALLS_SHOT);
/** the same view in the sketch's coordinates (lighting is in view space, so it renders the same) */
const TOY_SHOT: Shot = { ...WALLS_SHOT, target: S.add(WALLS_SHOT.target, LIFT) };

/** the toy face as "walls" leaves it, in its own place, with opacity k (it fades out as one picture) */
function toyFace(k: number): { beads: Bead[]; sticks: Stick[] } {
  if (k <= 0) return { beads: [], sticks: [] };
  const d = F.newDraw();
  F.drawFrame(d, { backFade: 1, context: 0 });
  d.solids.length = 0;
  F.drawWalls(d, 1);
  F.addHoles(d, { opacity: 1, free: 0 });
  if (k >= 1) return d;
  return {
    beads: d.beads.map((b) => ({ ...b, opacity: (b.opacity ?? 1) * k })),
    sticks: d.sticks.map((s) => ({ ...s, fade: 1 - (1 - (s.fade ?? 0)) * k })),
  };
}
/** the toy's strip boxes, as "walls" leaves them (under the beads) */
function ToyBoxes({ k }: { k: number }) {
  if (k <= 0) return null;
  return (
    <g>
      {[0, 1].map((s) => {
        const [x0, y0, x1, y1] = F.stripBox(wallsProject, s, 0.5);
        return <rect key={s} x={x0} y={y0} width={x1 - x0} height={y1 - y0} rx={12} fill="none" stroke={C.fgMuted} strokeWidth={2.5} opacity={k} />;
      })}
    </g>
  );
}
/** the toy's strip names on their middle rows, as "walls" leaves them */
function ToyNames({ k }: { k: number }) {
  if (k <= 0) return null;
  const p = wallsProject;
  const u = F.unitPx(p);
  const left = p([0, 0, 0])[0];
  const tx = p([-0.5, 0, 0])[0] - 30;
  const bx = left - 0.5 * u - 16;
  return (
    <g fontFamily={FONT.sans} opacity={k}>
      {[0, 1].map((s) => {
        const y = p([0, M.n - 1 - M.strips[s].rows[1], 0])[1];
        return (
          <g key={s}>
            {/* the gap "walls" cuts in its bracket for the leader (the bracket is gone; kept so the cut is exact) */}
            {tx + 8 < bx - 4 && <line x1={bx} x2={bx} y1={y - 8} y2={y + 8} stroke={C.bg} strokeWidth={6} />}
            <line x1={tx + 8} x2={left - 0.3 * u - 8} y1={y} y2={y} stroke={C.fgMuted} strokeWidth={2} strokeLinecap="round" />
            <text x={tx} y={y + 9} textAnchor="end" {...S.NAME}>
              {`strip ${s + 1}`}
            </text>
          </g>
        );
      })}
    </g>
  );
}

// ------------------------------------------------------------------ timing

/** cue 1 (frames from the scene start; the cut is at 0, the caption comes at 18) */
const T1 = {
  toyOut: 4,
  grow: 14,
  growDur: 24,
  badge: 20,
  sketchIn: 38,
  names: 46,
  /** rows below strip 1, the outline and the other strips' names go before the camera closes in */
  closeOut: 78,
  push: 84,
  pushDur: 26,
  closeIn: 110,
  bin: 112,
  pad: { from: 120, every: 2.0, fade: 6 } as S.Lay,
  /** "rod 1" and "wall" go, then the padding's outline and label come */
  named: 0,
};
T1.named = Math.ceil(S.layEnd(S.PAD, T1.pad)) + 1;

/** cue 2 (frames from its start) */
const T2 = { closeOut: 0, pull: 6, pullDur: 30, rows: 20, back: 36, legend: 40, tryIn: 50, noRoom: 66, tryOut: 118, stripsOut: 132, hole1: 140, pad: [0, 152, 178, 204], holeAfter: 16 };
/** cue 3 (frames from its start) */
const T3 = { spareOut: 8, spareIn: 18, legend: 30, plug: [0, 0, 36, 94], every: 2.5, labelOut: 2, labelIn: 12, note: 156 };

/** cue 1: the close-up of strip 1, with its bin under the hole */
const ZOOM_PITCH = 52;
const ZOOM_BIN_ROW = 7.5;
const SHOT_ZOOM = S.faceShot([(S.COLS - 1) / 2, S.ROWS - 1 - 3.7, 0], 1030, 475, ZOOM_PITCH);

/** the period (0..3) a row belongs to */
const periodOf = (r: number) => Math.max(0, Math.min(S.NSTRIPS - 1, Math.floor((r - 1) / 5)));

export default function PaddingScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [, c1, c2] = scene.cueTimes;
  const at = (c: CueTime, k: number) => c.from + k;
  const fd = S.fade;

  // ---- the camera: the toy's place in "walls", back to the sketch as the outline grows, close on
  // strip 1, and (cue 2) back to the whole face
  const grow = ramp(f, T1.grow, T1.growDur);
  const push = ramp(f, T1.push, T1.pushDur);
  const pull = ramp(f, at(c1, T2.pull), T2.pullDur);
  // while the toy is on screen (before the outline grows) the camera is exactly that of "walls",
  // and the toy is drawn where "walls" has it: only the outline is moved, by −LIFT
  const toyPhase = grow <= 0;
  const mix = (a: Shot, b: Shot, k: number) => (k <= 0 ? a : k >= 1 ? b : mixShot(a, b, k));
  const shot = toyPhase ? WALLS_SHOT : f >= c1.from ? mix(SHOT_ZOOM, S.SHOT, pull) : push > 0 ? mix(S.SHOT, SHOT_ZOOM, push) : mix(TOY_SHOT, S.SHOT, grow);
  const p = projector(shot);

  // ---- what is shown: the toy (it fades out), the sketch (it fades in as one picture); the rows
  // below strip 1 go before the close-up and come back in cue 2
  const toy = 1 - fd(f, T1.toyOut, 10);
  const sketch = fd(f, T1.sketchIn, 14);
  const lower = f < c1.from ? 1 - fd(f, T1.closeOut, 10) : fd(f, at(c1, T2.rows), 16);
  const show = (r: number) => sketch * (r <= 5 ? 1 : lower);
  // the cube's outline: grows with the camera; goes before the close-up, back once the strips are
  const outlineO = f < c1.from ? 1 - fd(f, T1.closeOut, 10) : fd(f, at(c1, T2.back), 10);

  const d = S.newDraw();
  if (toyPhase) {
    const t = toyFace(toy);
    d.beads.push(...t.beads);
    d.sticks.push(...t.sticks);
  }
  S.drawFrame(d, { show });
  S.drawHoles(d, { show });

  // cue 1: the first padding, at one soft tip
  S.drawRibbon(d, S.STRIPS[0].padding, C.pad, (i) => S.laid(f, T1.pad, i));
  // cue 2: a second padding tries strip 1 and goes; then strips 2, 3 and 4 get theirs, one after
  // another (a padding is known by now: each comes in as one picture)
  const tryO = fd(f, at(c1, T2.tryIn), 14) * (1 - fd(f, at(c1, T2.tryOut), 12));
  S.drawRibbon(d, S.ATTEMPT, C.pad, tryO);
  for (const s of [1, 2, 3]) S.drawRibbon(d, S.STRIPS[s].padding, C.pad, fd(f, at(c1, T2.pad[s]), 14));
  // cue 3: a plug in each spare hole, one after the other, at one soft tip
  for (const s of [2, 3]) {
    const lay = { from: at(c2, T3.plug[s]), every: T3.every };
    S.drawRibbon(d, S.STRIPS[s].hole, S.PLUG, (i) => S.laid(f, lay, i));
  }
  // legend: once the whole face is back in view; the plug's entry when the plugs come
  const legendIn = fd(f, at(c1, T2.legend), 10);
  const legend = { wall: legendIn, empty: legendIn, pad: legendIn, plug: fd(f, at(c2, T3.legend), 10) };
  S.drawLegend(d, legend);
  const back = (v: V3): V3 => [v[0] - LIFT[0], v[1] - LIFT[1], v[2] - LIFT[2]];
  d.lines.push(...S.outline(outlineO, grow).map((l) => (toyPhase ? { ...l, a: back(l.a), b: back(l.b) } : l)));

  // ---- labels
  // the strips' names: over the sketch, strip 1's through the close-up; they give way to hole 1's label
  const stripsOut = 1 - fd(f, at(c1, T2.stripsOut), 8);
  const names = S.STRIPS.map((st) => {
    if (st.s === 0) return fd(f, T1.names, 10) * stripsOut;
    if (f < c1.from) return fd(f, T1.names, 10) * (1 - fd(f, T1.closeOut, 8));
    return fd(f, at(c1, T2.rows), 16) * stripsOut;
  });
  // the close-up's labels; they go before the camera pulls back
  const closeOut = 1 - fd(f, at(c1, T2.closeOut), 8);
  const stripSub = fd(f, T1.closeIn, 10) * closeOut;
  const rows01 = fd(f, T1.closeIn, 10) * (1 - fd(f, T1.named, 8));
  const named = fd(f, T1.named + 8, 10) * closeOut;
  const binO = fd(f, T1.bin, 12) * closeOut;
  // cue 2: the second padding and the 40 H's it has no room for
  const second = fd(f, at(c1, T2.tryIn), 14) * (1 - fd(f, at(c1, T2.tryOut), 12));
  const noRoom = fd(f, at(c1, T2.noRoom), 10) * (1 - fd(f, at(c1, T2.tryOut), 12));
  // the holes' boxes and labels
  const holeBox = (s: number) => fd(f, s === 0 ? at(c1, T2.back) : at(c1, T2.pad[s] + T2.holeAfter), 10);
  const holeLab = (s: number) => {
    const inO = fd(f, s === 0 ? at(c1, T2.hole1) : at(c1, T2.pad[s] + T2.holeAfter), 10);
    if (s < 2) return { hole: inO, plug: 0 };
    const done = at(c2, T3.plug[s]) + Math.ceil(S.layEnd(S.BIN, { from: 0, every: T3.every }));
    return { hole: inO * (1 - fd(f, done + T3.labelOut, 8)), plug: fd(f, done + T3.labelIn, 8) };
  };
  // cue 3: holes 3 and 4 are the spare ones (their sub-line says so before the plugs come)
  const spare = f >= at(c2, T3.spareIn);
  const spareSub = spare ? fd(f, at(c2, T3.spareIn), 8) : 1 - fd(f, at(c2, T3.spareOut), 8);
  const note = fd(f, at(c2, T3.note), 12);

  // the bin of cue 1, under strip 1, slot k under column 11 + k
  const unit = S.pitchOf(p);
  const binH = 0.8 * unit;
  const trackX = S.X(S.HOLE_COL0 - 0.5, p) - TRACK_PAD;
  const trackY = S.Y(ZOOM_BIN_ROW, p) - trackHeight(binH) / 2;

  return (
    <SceneFrame scene={scene}>
      {/* behind the beads: the toy's strip boxes as "walls" leaves them, the holes' boxes, the bin */}
      <svg width={W} height={H} style={{ position: 'absolute', inset: 0 }}>
        <ToyBoxes k={toy} />
        {S.STRIPS.map((st) => (
          <S.HoleBox key={st.s} s={st.s} opacity={holeBox(st.s)} p={p} />
        ))}
        <S.PaddingOutline opacity={named} p={p} />
        <BinTrack x={trackX} y={trackY} B={S.BIN} unit={unit} h={binH} opacity={binO} label="bin 1" sub="size 10" />
      </svg>
      <Scene3D shot={shot} beads={d.beads} sticks={d.sticks} lines={d.lines}>
        {() => (
          <g fontFamily={FONT.sans}>
            <ToyNames k={toy} />
            {S.STRIPS.map((st) => (
              <S.StripLabel key={st.s} s={st.s} sub={st.s === 0 ? '3 rows × 20 nodes' : undefined} subOpacity={st.s === 0 ? stripSub : 0} opacity={names[st.s]} p={p} />
            ))}
            {/* strip 1, close up: what lies above it, then its padding */}
            <S.RowLabel r={0} title="rod 1" opacity={rows01} p={p} />
            <S.RowLabel r={1} title="wall" opacity={rows01} p={p} />
            <S.PaddingLabel opacity={named} p={p} />
            {/* cue 2: the second padding, and the 40 H's it has no room for (a red box; the words grey and dark) */}
            {second > 0 && (
              <text x={S.X(S.TAIL_COL0 - 0.5)} y={S.Y(S.STRIPS[0].rows[1] - 0.5) - 18} {...S.NAME} opacity={second}>
                a second padding
              </text>
            )}
            {noRoom > 0 &&
              (() => {
                const [x0, y0, x1, y1] = S.cellBox(S.TAIL_COL0, S.TAIL_COL0 + 19, S.STRIPS[0].rows[1], S.STRIPS[0].holeRow);
                return (
                  <g opacity={noRoom}>
                    <rect x={x0 - 4} y={y0 - 4} width={x1 - x0 + 8} height={y1 - y0 + 8} rx={0.45 * S.PITCH} fill="none" stroke={C.invalid} strokeWidth={3} />
                    <text x={x0} y={y1 + 36} {...S.NAME}>
                      no room
                    </text>
                    <text x={x0} y={y1 + 64} {...S.SUB}>
                      40 H’s left over
                    </text>
                  </g>
                );
              })()}
            {S.STRIPS.map((st) => {
              const l = holeLab(st.s);
              const sub = st.s < 2 ? '10 nodes' : spare ? 'spare' : '10 nodes';
              return (
                <g key={st.s}>
                  <S.HoleLabel s={st.s} title={`hole ${st.s + 1}`} sub={sub} subOpacity={st.s < 2 ? 1 : spareSub} opacity={l.hole} p={p} />
                  <S.HoleLabel s={st.s} title="plug" sub="10 H’s" opacity={l.plug} p={p} />
                </g>
              );
            })}
            <S.LegendLabels show={legend} p={p} />
            <S.SpareNote opacity={note} p={p} />
          </g>
        )}
      </Scene3D>
      {/* "walls" has no badge: it comes in as the cube grows */}
      <S.SketchBadge opacity={S.fade(f, T1.badge, 12)} />
    </SceneFrame>
  );
}
