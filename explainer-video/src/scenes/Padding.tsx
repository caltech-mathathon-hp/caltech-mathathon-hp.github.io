/**
 * Scene "padding": the front face of a bigger cube, four strips, for a puzzle with two bins.
 * Cue 1: it opens on the toy face of "walls" (two strips of 3 × 10), which grows into the sketch
 *        (four strips of 3 × 20) while the camera pulls back; then the camera closes in on strip 1
 *        (3 rows × 20 = 60 nodes) with a bin (10) right under its right end, column for column.
 *        A padding (50 H's) is laid in and leaves a hole as long as the bin.
 * Cue 2: the camera pulls back and the other strips return. A second padding tries strip 1: only
 *        its last 10 H's find room (in the hole), its other 40 lie outside the face ("no room").
 *        It goes; strips 2, 3 and 4 get their paddings, one after another in string order. Every
 *        hole gets its box and its label ("hole 2", "10 nodes") left of the face.
 * Cue 3: holes 3 and 4 are marked "spare"; plugs close them, one after the other, and their labels
 *        become "plug". A line says that the plugs could go in any 2 holes (these are an example).
 * The last frame is the first frame of the scene "choice".
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, projector, mixShot, type Project } from '../three/Scene3D';
import { BinTrack, trackHeight, TRACK_PAD } from '../ui/Bins';
import { C, FONT, W, H } from '../theme/theme';
import { ramp, sec, clamp01, easeOut } from '../lib/anim';
import type { SceneTime, CueTime } from '../script';
import * as S from './lib/padding-sketch';

const lin = (t: number) => clamp01(t);
const BIN_H = 37;

/** cue 1: close on strip 1 (rows 0..5) with the bin under it, row 6.8 */
const ZOOM_PITCH = 52;
const ZOOM_BIN_ROW = 6.8;
const SHOT_ZOOM = S.faceShot([(S.COLS - 1) / 2, S.ROWS - 1 - 3.7, 0], 1030, 475, ZOOM_PITCH);

/** cue 1, in seconds from the scene start: the toy face grows, then the camera closes in */
const GROW_AT = 0.4;
const GROW_DUR = 1.2;
const PUSH_AT = 2.2;
const PUSH_DUR = 0.9;
const BIN_AT = 3.2;
const PAD1_AT = 3.9;
const PAD1_DUR = 1.8;
const NAMED_AT = 5.9;

/** cue 2, from its start: the second padding, then the paddings of strips 2, 3 and 4 */
const TRY_AT = 1.5;
const TRY_DUR = 1.5;
const NOROOM_AT = 3.05;
const TRY_OUT = 3.9;
/** how pale the second padding is drawn */
const TRY_GHOST = 0.45;
const PAD_AT = [0, 4.3, 5.3, 6.3];
const PAD_DUR = 0.9;
/** cue 3: a plug in each spare hole, one after the other */
const PLUG_AT = [0, 0, 1.6, 3.0];
const PLUG_DUR = 0.9;
/** cue 3, once both plugs are in and named: which holes they take is only an example */
const SPARE_NOTE_AT = 4.8;

/** the period (0..3) a row belongs to */
const periodOf = (r: number) => Math.max(0, Math.min(S.NSTRIPS - 1, Math.floor((r - 1) / 5)));

/**
 * The holes' labels at frame f (shared with the scene "choice"): a hole gets its box and its label
 * ("hole 1", "10 nodes") once its strip has a padding (hole 1's label once the camera has pulled back); a plugged hole's label becomes "plug"
 * ("10 H’s"): the old label fades out completely before the new one fades in. With c1 = c2 =
 * null: the last state.
 */
export function holeLabels(f: number, c1: CueTime | null, c2: CueTime | null) {
  const at = (c: CueTime, s: number) => c.from + sec(s);
  return S.STRIPS.map((st) => {
    if (!c1 || !c2) return { s: st.s, hole: st.s < 2 ? 1 : 0, plug: st.s < 2 ? 0 : 1, box: 1 };
    const inAt = st.s === 0 ? sec(NAMED_AT) : at(c1, PAD_AT[st.s] + PAD_DUR);
    const box = ramp(f, inAt, sec(0.4));
    // hole 1 is tagged on the right in the close-up; its label on the left comes once the face is back
    if (st.s === 0) return { s: 0, hole: f < c1.from ? 0 : ramp(f, at(c1, 1.2), sec(0.4)), plug: 0, box };
    if (st.s < 2) return { s: st.s, hole: box, plug: 0, box };
    const outAt = at(c2, PLUG_AT[st.s] + PLUG_DUR);
    const hole = box * (1 - ramp(f, outAt, sec(0.25)));
    const plug = ramp(f, outAt + sec(0.3), sec(0.3));
    return { s: st.s, hole, plug, box };
  });
}

/** the labels left of the holes; `sub` replaces a hole's sub-line ("10 nodes") */
export function HoleLabels({ labels, sub, subOpacity, p }: { labels: ReturnType<typeof holeLabels>; sub?: (s: number) => React.ReactNode; subOpacity?: (s: number) => number; p?: Project }) {
  return (
    <>
      {labels.map((l) => (
        <g key={l.s}>
          <S.HoleLabel s={l.s} title={`hole ${l.s + 1}`} sub={sub?.(l.s) ?? '10 nodes'} subOpacity={subOpacity?.(l.s) ?? 1} opacity={l.hole} p={p} />
          <S.HoleLabel s={l.s} title="plug" sub="10 H’s" opacity={l.plug} p={p} />
        </g>
      ))}
    </>
  );
}

export default function PaddingScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [, c1, c2] = scene.cueTimes;
  const at = (c: CueTime, s: number) => c.from + sec(s);

  // the camera: the toy face's place in "walls", back to the whole sketch as it grows, close on
  // strip 1, and (cue 2) back to the whole face
  const grow = ramp(f, sec(GROW_AT), sec(GROW_DUR));
  const push = ramp(f, sec(PUSH_AT), sec(PUSH_DUR));
  const pull = ramp(f, at(c1, 0.2), sec(1.0));
  const shot = pull > 0 ? mixShot(SHOT_ZOOM, S.SHOT, pull) : push > 0 ? mixShot(S.SHOT, SHOT_ZOOM, push) : mixShot(S.TOY_SHOT, S.SHOT, grow);
  const p = pull >= 1 ? S.proj : projector(shot);
  const gr = S.growth(grow);

  // rows below strip 1: shown while the face grows, gone in the close-up, back in cue 2
  const hide = ramp(f, sec(PUSH_AT), sec(0.4));
  const reveal = [1, ...[1, 2, 3].map((k) => ramp(f, at(c1, 0.6 + 0.15 * (k - 1)), sec(0.4)))];
  const other = (k: number) => (f < c1.from ? 1 - hide : reveal[k]);
  const show = (r: number) => (r <= 5 ? 1 : other(periodOf(r)));

  const d = S.newDraw();
  S.drawFrame(d, { show, gr });
  S.drawHoles(d, { show, gr });

  // cue 1: the first padding
  const pad1 = S.STRIPS[0].padding;
  S.drawRibbon(d, pad1, C.pad, ramp(f, sec(PAD1_AT), sec(PAD1_DUR), lin), { lead: S.layLead(pad1, sec(PAD1_DUR)) });

  // cue 2: a second padding tries strip 1 and goes; then strips 2, 3 and 4, one after another
  const tryIn = ramp(f, at(c1, TRY_AT), sec(TRY_DUR), lin);
  const tryGone = ramp(f, at(c1, TRY_OUT), sec(0.3));
  // lighter than a real padding, so the part in the hole never reads as the first padding grown
  S.drawRibbon(d, S.ATTEMPT, C.pad, tryIn, { lead: S.layLead(S.ATTEMPT, sec(TRY_DUR)), fade: TRY_GHOST + (1 - TRY_GHOST) * tryGone });
  for (const s of [1, 2, 3]) {
    const cells = S.STRIPS[s].padding;
    S.drawRibbon(d, cells, C.pad, ramp(f, at(c1, PAD_AT[s]), sec(PAD_DUR), lin), { lead: S.layLead(cells, sec(PAD_DUR)) });
  }

  // cue 3: plugs in strips 3 and 4, one after another
  for (const s of [2, 3]) {
    const cells = S.STRIPS[s].hole;
    S.drawRibbon(d, cells, S.PLUG, ramp(f, at(c2, PLUG_AT[s]), sec(PLUG_DUR), lin), { lead: S.layLead(cells, sec(PLUG_DUR)) });
  }

  // legend: once the whole face is back in view, each entry when its kind is on the face
  const legendIn = ramp(f, at(c1, 1.2), sec(0.4));
  const legend = { wall: legendIn, empty: legendIn, pad: legendIn, plug: ramp(f, at(c2, PLUG_AT[2] - 0.1), sec(0.4)) };
  S.drawLegend(d, legend);

  // cue 1, the toy face growing: the strips' boxes and the cube's outline (as in "walls"), the names
  const overview = 1 - ramp(f, sec(PUSH_AT), sec(0.4));
  const outline = f < c1.from ? overview : ramp(f, at(c1, 0.6), sec(0.4));
  const stripIn = (s: number) => (s < 2 ? 1 : gr.row(S.STRIPS[s].top + 4));
  const names = S.STRIPS.map((st) => (st.s === 0 ? 1 : f < c1.from ? stripIn(st.s) * overview : reveal[st.s]));
  // the close-up's labels; they go before the camera pulls back
  const closeOut = 1 - ramp(f, at(c1, 0), sec(0.3));
  const closeIn = ramp(f, sec(PUSH_AT + PUSH_DUR - 0.1), sec(0.4)) * closeOut;
  const named = ramp(f, sec(NAMED_AT), sec(0.4)) * closeOut;
  const binIn = ramp(f, sec(BIN_AT), sec(0.6), easeOut);
  const binOp = binIn * closeOut;
  const noRoom = ramp(f, at(c1, NOROOM_AT), sec(0.3)) * (1 - ramp(f, at(c1, TRY_OUT), sec(0.3)));
  const second = ramp(f, at(c1, TRY_AT), sec(0.3)) * (1 - ramp(f, at(c1, TRY_OUT), sec(0.3)));
  const labels = holeLabels(f, c1, c2);
  // cue 3: holes 3 and 4 are the spare ones (their sub-line says so before the plugs come)
  const spareAt = at(c2, 0.4);
  const spareText = f < spareAt + sec(0.3) ? '10 nodes' : 'spare';
  const spareOp = f < spareAt + sec(0.3) ? 1 - ramp(f, spareAt, sec(0.25)) : ramp(f, spareAt + sec(0.3), sec(0.3));

  // the bin of cue 1, under strip 1, slot k under column k + 1
  const unit = S.pitchOf(p);
  const binH = 0.8 * unit;
  const trackX = S.X(S.HOLE_COL0, p) - unit / 2 - TRACK_PAD;
  const binY = S.Y(ZOOM_BIN_ROW, p) + 24 * (1 - binIn);
  const trackY = binY - trackHeight(binH) / 2;

  return (
    <SceneFrame scene={scene}>
      {/* behind the beads: the cube's outline, the strips' boxes while the face grows, the holes' boxes, the bin */}
      <svg width={W} height={H} style={{ position: 'absolute', inset: 0 }}>
        <S.FaceOutline opacity={outline} gr={gr} p={p} />
        {overview > 0 && (
          <g opacity={overview}>
            {S.STRIPS.map((st) => {
              const o = stripIn(st.s);
              if (o <= 0) return null;
              const [x0, y0] = [S.X(0.5, p), S.Y(st.rows[0] - 0.5, p)];
              const [x1, y1] = [S.X(gr.xr - 0.5, p), S.Y(st.rows[2] + 0.5, p)];
              return <rect key={st.s} x={x0} y={y0} width={x1 - x0} height={y1 - y0} rx={12} fill={C.fgSubtle} fillOpacity={0.13} stroke={C.fgMuted} strokeWidth={2.5} opacity={o} />;
            })}
          </g>
        )}
        {labels.map((l) => (
          <S.HoleBox key={l.s} s={l.s} opacity={l.box} p={p} />
        ))}
        <BinTrack x={trackX} y={trackY} B={S.BIN} unit={unit} h={binH} opacity={binOp} />
      </svg>
      <Scene3D shot={shot} beads={d.beads} sticks={d.sticks} panels={d.panels}>
        {(project) => (
          <g>
            {S.STRIPS.map((st) => (
              <S.StripLabel key={st.s} s={st.s} sub={st.s === 0 && closeIn > 0 ? '3 rows × 20 nodes' : undefined} opacity={names[st.s]} p={project} />
            ))}
            {/* strip 1, close up: what lies above and around it, the padding, the bin */}
            <S.RowTag r={0} label="cube edge" opacity={closeIn} p={project} />
            <S.RowTag r={1} label="wall" opacity={closeIn} p={project} />
            <S.PaddingOutline opacity={named} p={project} />
            <S.RowTag r={S.STRIPS[0].holeRow} label="hole 1: 10 nodes" opacity={named} p={project} />
            <S.RowTag atY={binY} label="a bin: 10" opacity={binOp} p={project} />
            {/* cue 2: the second padding, and the 40 H's it has no room for */}
            {second > 0 && (
              <text x={S.X(S.TAIL_COL0 - 0.5)} y={S.Y(S.STRIPS[0].rows[1] - 0.5) - 16} fontFamily={FONT.sans} {...S.NAME} opacity={second}>
                a second padding
              </text>
            )}
            {noRoom > 0 &&
              (() => {
                const [x0, y0, x1, y1] = S.cellBox(S.TAIL_COL0, S.TAIL_COL0 + 19, S.STRIPS[0].rows[1], S.STRIPS[0].holeRow);
                return (
                  <g opacity={noRoom} fontFamily={FONT.sans}>
                    <rect x={x0} y={y0} width={x1 - x0} height={y1 - y0} rx={0.45 * S.PITCH} fill="none" stroke={C.invalid} strokeWidth={3} />
                    <text x={x0} y={y1 + 30} fontSize={22} fontWeight={600} fill={C.invalid}>
                      no room: 40 left over
                    </text>
                  </g>
                );
              })()}
            <HoleLabels labels={labels.map((l) => ({ ...l }))} sub={(s) => (s >= 2 ? spareText : '10 nodes')} subOpacity={(s) => (s >= 2 ? spareOp : 1)} p={project} />
            <S.LegendLabels show={legend} />
            <S.SpareNote opacity={ramp(f, at(c2, SPARE_NOTE_AT), sec(0.4))} p={project} />
          </g>
        )}
      </Scene3D>
      {/* "walls" has no badge: it comes in after the cut, which continues the picture exactly */}
      <S.SketchBadge opacity={ramp(f, 2, 12)} />
    </SceneFrame>
  );
}

export { BIN_H };
