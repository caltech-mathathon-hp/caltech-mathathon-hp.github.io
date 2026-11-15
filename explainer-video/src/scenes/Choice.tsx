/**
 * Scene "choice": the sketch face of "padding", with two open holes and two plugged.
 * Cue 1: the item ribbons 6, 2, 8, 4 fade in right of the face, one after another in string
 *        order. Then, one at a time and in string order, each slides (through free space only) to
 *        the row of the hole it takes, just right of the face, fades there and is laid into the
 *        hole with one growing tip: 6 + 4 in hole 1, 2 + 8 in hole 2. The holes' sub-lines add up
 *        their items.
 * Cue 2: the puzzle's two full bins appear beside the holes, row for row (the key claim), each with
 *        its sum ("6 + 4 = 10", as in part 2).
 * Cue 3: fold ⇒ packing: the bins empty, and each bin is filled again, bar by bar, from the hole
 *        on its row: the items in one hole form one bin.
 * Cue 4: packing ⇒ fold: the face is cleared; the items are laid again into the hole on the row of
 *        their bin, one at a time in string order. The frame steps back; right of each hole, discs
 *        give the order in the string of its items, and a panel "order in the string" draws the
 *        three joins still missing between consecutive items.
 *
 * Nothing moves over a bead: an item only slides where the face has no beads, and enters a hole
 * by being laid in it (one tip, new beads at full size), like the paddings and plugs.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, R_RES, FADE } from '../three/Scene3D';
import { BinTrack, BinSum, ItemBar, Arrow, trackHeight, trackWidth, slotX, slotY, TRACK_PAD } from '../ui/Bins';
import { C, FONT, W, H, itemColor } from '../theme/theme';
import { ramp, sec, clamp01, easeOut, easeInOut, lerp } from '../lib/anim';
import type { SceneTime, CueTime } from '../script';
import type { V3 } from '../model/toy';
import * as S from './lib/padding-sketch';
import { holeLabels, HoleLabels, BIN_H } from './Padding';

const lin = (t: number) => clamp01(t);
const unit = S.PITCH;
const rb = R_RES * unit;
/** cue 1: where the items wait, right of the face (the column of their left ends, and their rows) */
const STACK_COL = 32;
const WAIT_ROW = [1.5, 4, 6.5, 9];
/** where an item stops, on the row of its hole, just right of the face (its left end) */
const DOCK_COL = 22.6;
/** the joins still missing: a neutral colour (linkers get their own later) */
const JOIN = C.fgMuted;

const trackX = S.X(S.BIN_COL) - unit / 2 - TRACK_PAD;
const trackY = (b: number) => S.Y(S.STRIPS[b].holeRow) - trackHeight(BIN_H) / 2;
const GAP_L = S.X(S.COLS - 1) + 30;
const GAP_R = trackX - 22;
const GAP_Y = (S.Y(S.STRIPS[0].holeRow) + S.Y(S.STRIPS[1].holeRow)) / 2;

/**
 * cue 1: the items fade in one after another; then one at a time, in string order, each slides to
 * its hole's row, fades there and is laid into the hole (the next starts once it is in)
 */
const APPEAR_AT = 0.5;
const APPEAR_GAP = 0.35;
const TAKE_AT = 2.0;
const TAKE_GAP = 1.7;
const SLIDE_DUR = 0.8;
const DOCK_FADE = 0.25;
const LAY_DUR = 0.6;
/** cue 3: the bars wiped in, bin by bin, left to right */
const WIPE_ORDER = [0, 3, 1, 2];
const WIPE_AT = 1.0;
const WIPE_GAP = 0.6;
const WIPE_DUR = 0.5;
/** cue 4: the items laid back into the holes, in string order; then the frame steps back */
const BACK_AT = 1.0;
const BACK_GAP = 0.85;
const QUIET_AT = 4.4;

type P2 = [number, number];
/** a route through points (world x, y) with rounded corners: s (0..1, by length) → point */
function route(pts: P2[], rad: number) {
  const q = pts.filter((p, i) => i === 0 || Math.hypot(p[0] - pts[i - 1][0], p[1] - pts[i - 1][1]) > 1e-6);
  const out: P2[] = [q[0]];
  for (let i = 1; i < q.length - 1; i++) {
    const [a, b, c] = [q[i - 1], q[i], q[i + 1]];
    const la = Math.hypot(b[0] - a[0], b[1] - a[1]);
    const lc = Math.hypot(c[0] - b[0], c[1] - b[1]);
    const k = Math.min(rad, la / 2, lc / 2);
    const p0: P2 = [b[0] + ((a[0] - b[0]) * k) / la, b[1] + ((a[1] - b[1]) * k) / la];
    const p1: P2 = [b[0] + ((c[0] - b[0]) * k) / lc, b[1] + ((c[1] - b[1]) * k) / lc];
    for (let j = 0; j <= 12; j++) {
      const t = j / 12;
      out.push([(1 - t) * (1 - t) * p0[0] + 2 * t * (1 - t) * b[0] + t * t * p1[0], (1 - t) * (1 - t) * p0[1] + 2 * t * (1 - t) * b[1] + t * t * p1[1]]);
    }
  }
  out.push(q[q.length - 1]);
  const L = [0];
  for (let i = 1; i < out.length; i++) L.push(L[i - 1] + Math.hypot(out[i][0] - out[i - 1][0], out[i][1] - out[i - 1][1]));
  const total = L[L.length - 1];
  return (s: number): P2 => {
    const d = clamp01(s) * total;
    let i = 1;
    while (i < out.length - 1 && L[i] < d) i++;
    const t = L[i] > L[i - 1] ? (d - L[i - 1]) / (L[i] - L[i - 1]) : 0;
    return [lerp(out[i - 1][0], out[i][0], t), lerp(out[i - 1][1], out[i][1], t)];
  };
}

/**
 * item u's way from where it waits to its hole's row, right of the face (left along its own row,
 * then up or down the free column there), as offsets of its left cell from its place in the hole
 */
const DOCK = S.PLACED.map((it) => {
  const [hx, hy] = [it.lr[0][0], it.lr[0][1]];
  const wy = S.ROWS - 1 - WAIT_ROW[it.u];
  const r = route(
    [
      [STACK_COL, wy],
      [DOCK_COL, wy],
      [DOCK_COL, hy],
    ],
    1.2,
  );
  return (s: number): V3 => {
    const [x, y] = r(s);
    return [x - hx, y - hy, 0];
  };
});
/** an item laid into its hole from the end next to the bins (all sizes are even, so the pairs of H's are the same) */
const LAY_CELLS = S.PLACED.map((it) => [...it.lr].reverse());

/** ⟺, drawn (fonts differ in whether they have the glyph) */
function Iff({ x, y, opacity }: { x: number; y: number; opacity: number }) {
  if (opacity <= 0) return null;
  const w = 64;
  const h = 7;
  const head = 14;
  return (
    <g opacity={opacity} stroke={C.accent} strokeWidth={3} fill="none" strokeLinecap="round" strokeLinejoin="round">
      <line x1={x - w / 2 + 6} y1={y - h} x2={x + w / 2 - 6} y2={y - h} />
      <line x1={x - w / 2 + 6} y1={y + h} x2={x + w / 2 - 6} y2={y + h} />
      <path d={`M${x - w / 2 + head},${y - h - head * 0.8} L${x - w / 2},${y} L${x - w / 2 + head},${y + h + head * 0.8}`} />
      <path d={`M${x + w / 2 - head},${y - h - head * 0.8} L${x + w / 2},${y} L${x + w / 2 - head},${y + h + head * 0.8}`} />
      <text x={x} y={y - 30} textAnchor="middle" fontFamily={FONT.sans} fontSize={22} fontWeight={500} fill={C.fgMuted} stroke="none">
        exactly when
      </text>
    </g>
  );
}

/**
 * An item's order in the string: a disc in its colour with a white number (the same in every step;
 * sizes are the white chips on the bars). It fades in at full size.
 */
export function OrderBadge({ x, y, n, color, opacity, r = 18 }: { x: number; y: number; n: number; color: string; opacity: number; r?: number }) {
  if (opacity <= 0) return null;
  return (
    <g transform={`translate(${x} ${y})`} opacity={opacity}>
      <circle r={r + 2.5} fill={C.bgElev} />
      <circle r={r} fill={color} />
      <text y={r * 0.42} textAnchor="middle" fontFamily={FONT.sans} fontWeight={700} fontSize={Math.max(20, r * 1.25)} fill="#fff">
        {n}
      </text>
    </g>
  );
}

export default function ChoiceScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1, c2, c3] = scene.cueTimes;
  const at = (c: CueTime, s: number) => c.from + sec(s);

  // cue 4: once the items are back, the frame steps back (the whole frame, by the shared amount)
  const quiet = FADE.context * ramp(f, at(c3, QUIET_AT), sec(0.5));
  const d = S.newDraw();
  S.drawFrame(d, { quiet });
  S.drawHoles(d);
  for (const st of S.STRIPS) S.drawRibbon(d, st.padding, C.pad, 1);
  S.drawRibbon(d, S.STRIPS[2].hole, S.PLUG, 1);
  S.drawRibbon(d, S.STRIPS[3].hole, S.PLUG, 1);
  const legend = { wall: 1, empty: 1, pad: 1, plug: 1 };
  S.drawLegend(d, legend);

  // cue 1: items fade in right of the face, then go into the holes one at a time
  const appear = (u: number) => ramp(f, at(c0, APPEAR_AT + APPEAR_GAP * u), sec(0.27), lin);
  const takeAt = (u: number) => at(c0, TAKE_AT + TAKE_GAP * u);
  const slide = (u: number) => ramp(f, takeAt(u), sec(SLIDE_DUR));
  const docked = (u: number) => ramp(f, takeAt(u) + sec(SLIDE_DUR), sec(DOCK_FADE), lin);
  const layAt = (u: number) => takeAt(u) + sec(SLIDE_DUR + DOCK_FADE);
  const landed = (u: number) => ramp(f, layAt(u) + sec(LAY_DUR), sec(0.3));
  S.drawItemsLegend(d, appear(0));
  // cue 4: the face is cleared (completely) before the items are laid again
  const clear = ramp(f, at(c3, 0.3), sec(0.3));
  const backAt = (u: number) => at(c3, BACK_AT + BACK_GAP * u);

  for (const it of S.PLACED) {
    const u = it.u;
    const col = itemColor(u);
    const lead = S.layLead(LAY_CELLS[u], sec(LAY_DUR));
    if (f < c3.from) {
      // waiting, sliding to its hole's row, fading there
      S.drawRibbon(d, it.cells, col, 1, { offset: DOCK[u](slide(u)), fade: 1 - appear(u) * (1 - docked(u)) });
      // laid into the hole
      S.drawRibbon(d, LAY_CELLS[u], col, ramp(f, layAt(u), sec(LAY_DUR), lin), { lead });
    } else {
      S.drawRibbon(d, it.cells, col, 1, { fade: clear });
      S.drawRibbon(d, LAY_CELLS[u], col, ramp(f, backAt(u), sec(LAY_DUR), lin), { lead });
    }
  }

  // the bars in the bins: in with the bins (cue 2); out, then wiped in one by one (cue 3)
  const binsIn = ramp(f, at(c1, 0.3), sec(1.0), easeOut);
  const barsOut = ramp(f, at(c2, 0.3), sec(0.4));
  const wipeStart = (u: number) => at(c2, WIPE_AT + WIPE_GAP * WIPE_ORDER.indexOf(u));
  const bar = (u: number) => {
    if (f < c2.from) return { op: binsIn, wipe: 1, chip: 1 };
    if (f >= c3.from) return { op: 1, wipe: 1, chip: 1 };
    const w = ramp(f, wipeStart(u), sec(WIPE_DUR), lin);
    if (w > 0) return { op: 1, wipe: w, chip: ramp(f, wipeStart(u) + sec(WIPE_DUR), sec(0.25)) };
    return { op: 1 - barsOut, wipe: 1, chip: 1 };
  };
  // a bin's green border and its sum: off while its bars are out (cue 3), back once its last bar is in
  const binDone = (b: number) => Math.max(...S.BINS[b].map(wipeStart)) + sec(WIPE_DUR);
  const binFull = (b: number) => (f < c2.from || f >= c3.from ? 1 : Math.max(1 - barsOut, ramp(f, binDone(b), sec(0.4))));
  const binSum = (b: number) => (f < c2.from ? binsIn : binFull(b));

  // labels
  const names = 1 - ramp(f, at(c0, 0), sec(0.4));
  const guides = ramp(f, at(c1, 1.0), sec(0.6)) * (1 - ramp(f, at(c3, 0), sec(0.3)));
  const iff = ramp(f, at(c1, 1.4), sec(0.6)) * (1 - ramp(f, at(c2, 0), sec(0.3)));
  const arrowR = ramp(f, at(c2, 0.4), sec(0.6), easeOut) * (1 - ramp(f, at(c3, 0), sec(0.3)));
  const arrowL = ramp(f, at(c3, 0.4), sec(0.6), easeOut);
  // cue 4: the order in the string, right of the holes, then the panel and the joins
  const badge = (u: number) => ramp(f, at(c3, QUIET_AT + 0.3 + 0.15 * u), sec(0.3), lin);
  const panelIn = ramp(f, at(c3, QUIET_AT + 0.8), sec(0.4));
  const chainBadge = (u: number) => ramp(f, at(c3, QUIET_AT + 0.9 + 0.1 * u), sec(0.25), lin);
  const join = (i: number) => ramp(f, at(c3, QUIET_AT + 1.4 + 0.3 * i), sec(0.3), easeInOut);

  // a hole's sub-line: "10 nodes", then (once its first item is in) the sizes of its items; in
  // cue 4 the sizes go with the cleared items and come back as they are laid again
  const firstIn = (b: number) => layAt(S.BINS[b][0]) + sec(LAY_DUR);
  const backIn = (u: number) => backAt(u) + sec(LAY_DUR);
  const second = (b: number) => {
    const u = S.BINS[b][1];
    return f < c3.from || f < backIn(S.BINS[b][0]) ? landed(u) : ramp(f, backIn(u), sec(0.3));
  };
  const holeSub = (b: number) =>
    b >= 2 || f < firstIn(b) + sec(0.3) ? (
      '10 nodes'
    ) : (
      <>
        <tspan fill={itemColor(S.BINS[b][0])} fontWeight={650}>
          {S.SIZES[S.BINS[b][0]]}
        </tspan>
        <tspan opacity={second(b)}>{' + '}</tspan>
        <tspan fill={itemColor(S.BINS[b][1])} fontWeight={650} opacity={second(b)}>
          {S.SIZES[S.BINS[b][1]]}
        </tspan>
      </>
    );
  const holeSubOp = (b: number) => {
    if (b >= 2) return 1;
    if (f >= c3.from) {
      const t = backIn(S.BINS[b][0]);
      return f < t ? 1 - clear : ramp(f, t, sec(0.3));
    }
    return f < firstIn(b) + sec(0.3) ? 1 - ramp(f, firstIn(b), sec(0.25)) : ramp(f, firstIn(b) + sec(0.3), sec(0.3));
  };

  // the panel "order in the string", top left, above the hole labels
  // its left edge on the header's
  const PX0 = 64;
  const PY0 = 106;
  const CH_X = (u: number) => PX0 + 38 + 74 * u;
  const CH_Y = PY0 + 116;
  // the order discs right of the holes: in each hole, its items left to right
  const BADGE_X = (k: number) => S.X(S.COLS - 1) + rb + 40 + 46 * k;

  return (
    <SceneFrame scene={scene}>
      {/* behind the beads: the cube's outline, the holes' boxes, the bins */}
      <svg width={W} height={H} style={{ position: 'absolute', inset: 0 }}>
        <S.FaceOutline opacity={1} />
        {S.STRIPS.map((st) => (
          <S.HoleBox key={st.s} s={st.s} opacity={1} />
        ))}
        {[0, 1].map((b) => (
          <BinTrack key={b} x={trackX + 40 * (1 - binsIn)} y={trackY(b)} B={S.BIN} unit={unit} h={BIN_H} label={`bin ${b + 1}`} full={binFull(b)} opacity={binsIn} />
        ))}
        {[0, 1].map((b) => (
          <BinSum key={`sum${b}`} x={trackX + 40 * (1 - binsIn) + trackWidth(S.BIN, unit) + 26} y={trackY(b) + trackHeight(BIN_H) / 2 + 9} items={S.BINS[b].map((u) => ({ u, size: S.SIZES[u] }))} B={S.BIN} opacity={binSum(b)} />
        ))}
        {/* the bins' contents: each bar wiped in from the left */}
        {S.PLACED.map((it) => {
          const { op, wipe, chip } = bar(it.u);
          if (op <= 0 || wipe <= 0) return null;
          const x = slotX(trackX + 40 * (1 - binsIn), it.slot, unit);
          const y = slotY(trackY(it.bin));
          const size = S.SIZES[it.u];
          return <ItemBar key={it.u} x={x} y={y} size={size} color={itemColor(it.u)} unit={unit} h={BIN_H} opacity={op} span={wipe < 1 ? [0, Math.max(0.001, size * wipe)] : undefined} chipOpacity={chip} />;
        })}
      </svg>
      <Scene3D shot={S.SHOT} beads={d.beads} sticks={d.sticks} panels={d.panels}>
        {(project) => (
          <g>
            {S.STRIPS.map((st) => (
              <S.StripLabel key={st.s} s={st.s} opacity={names} p={project} />
            ))}
            <HoleLabels labels={holeLabels(f, null, null)} sub={holeSub} subOpacity={holeSubOp} />
            <S.LegendLabels show={legend} />
            {/* from "padding": the plugs' holes are an example; it goes before the items come */}
            <S.SpareNote opacity={1 - ramp(f, at(c0, 0), sec(0.3))} p={project} />
            {/* the items, in the legend */}
            {(() => {
              const o = appear(0);
              if (o <= 0) return null;
              const [lx, ly] = S.legendText(S.LEG_ROW_ITEMS, project);
              return (
                <text x={lx} y={ly + 7.5} fontFamily={FONT.sans} {...S.SUB} opacity={o}>
                  {'items: '}
                  {S.SIZES.map((sz, u) => (
                    <tspan key={u} fill={itemColor(u)} fontWeight={650}>
                      {sz}
                      {u < S.SIZES.length - 1 && <tspan fill={C.fgMuted} fontWeight={500}>{', '}</tspan>}
                    </tspan>
                  ))}
                </text>
              );
            })()}
            {/* the joins, in the legend */}
            {(() => {
              const o = join(0);
              if (o <= 0) return null;
              const [lx, ly] = S.legendText(S.LEG_ROW_JOIN, project);
              const [x0] = project([S.LEG_COL - 0.1, 0, 0]);
              const [x1] = project([S.LEG_COL + 1.1, 0, 0]);
              return (
                <g opacity={o}>
                  <path d={`M${x0},${ly + 6} Q${(x0 + x1) / 2},${ly - 16} ${x1},${ly + 6}`} fill="none" stroke={JOIN} strokeWidth={3} strokeLinecap="round" strokeDasharray="6 6" />
                  <text x={lx} y={ly + 7.5} fontFamily={FONT.sans} {...S.SUB}>
                    join still missing
                  </text>
                </g>
              );
            })()}
            {/* sizes of the waiting items, right of them */}
            {S.PLACED.map((it) => {
              const o = appear(it.u) * (1 - ramp(f, takeAt(it.u), sec(0.25)));
              if (o <= 0) return null;
              const [x, y] = project([STACK_COL + S.SIZES[it.u] - 1, S.ROWS - 1 - WAIT_ROW[it.u], 0]);
              return (
                <text key={it.u} x={x + rb + 16} y={y + 9} fontFamily={FONT.sans} fontWeight={600} fontSize={26} fill={itemColor(it.u)} opacity={o}>
                  {S.SIZES[it.u]}
                </text>
              );
            })}
            {/* row for row: hole b and bin b */}
            {guides > 0 &&
              [0, 1].map((b) => {
                const y = S.Y(S.STRIPS[b].holeRow);
                return <line key={b} x1={GAP_L} x2={GAP_R + 10} y1={y} y2={y} stroke={C.fgSubtle} strokeWidth={2} strokeDasharray="2 7" strokeLinecap="round" opacity={guides} />;
              })}
            <Iff x={(GAP_L + GAP_R) / 2} y={GAP_Y} opacity={iff} />
            <Arrow from={[GAP_L, GAP_Y]} to={[GAP_R, GAP_Y]} label="fold ⇒ packing" color={C.accent} progress={arrowR} opacity={arrowR > 0 ? 1 : 0} />
            <Arrow from={[GAP_R, GAP_Y]} to={[GAP_L, GAP_Y]} label="packing ⇒ fold" color={C.accent} progress={arrowL} opacity={arrowL > 0 ? 1 : 0} />
            {/* cue 4: right of each hole, the order in the string of its items, left to right */}
            {S.PLACED.map((it) => {
              const k = S.BINS[it.bin].indexOf(it.u);
              return <OrderBadge key={it.u} x={BADGE_X(k)} y={S.Y(S.STRIPS[it.bin].holeRow)} n={it.u + 1} color={itemColor(it.u)} opacity={badge(it.u)} />;
            })}
            {/* cue 4: the order in the string and the joins still missing, in a panel */}
            {panelIn > 0 && (
              <g fontFamily={FONT.sans}>
                <rect x={PX0} y={PY0} width={CH_X(3) + 38 - PX0} height={CH_Y + 38 - PY0} rx={10} fill={C.bgElev} stroke={C.ruleStrong} strokeWidth={1.5} opacity={panelIn} />
                <text x={PX0 + 18} y={PY0 + 34} {...S.SUB} opacity={panelIn}>
                  order in the string
                </text>
                {[0, 1, 2].map((i) => {
                  const k = join(i);
                  if (k <= 0) return null;
                  const x0 = CH_X(i) + 14;
                  const x1 = CH_X(i + 1) - 14;
                  const y0 = CH_Y - 16;
                  const cx = (x0 + x1) / 2;
                  const top = CH_Y - 54;
                  // drawn left to right as it grows (the first part of the curve, exactly)
                  const qx = (1 - k) * x0 + k * cx;
                  const qy = (1 - k) * y0 + k * top;
                  const ex = (1 - k) * (1 - k) * x0 + 2 * k * (1 - k) * cx + k * k * x1;
                  const ey = (1 - k) * (1 - k) * y0 + 2 * k * (1 - k) * top + k * k * y0;
                  return <path key={i} d={`M${x0},${y0} Q${qx},${qy} ${ex},${ey}`} fill="none" stroke={JOIN} strokeWidth={3} strokeLinecap="round" strokeDasharray="6 6" />;
                })}
                {S.SIZES.map((_, u) => (
                  <OrderBadge key={u} x={CH_X(u)} y={CH_Y} n={u + 1} color={itemColor(u)} opacity={chainBadge(u)} r={20} />
                ))}
              </g>
            )}
          </g>
        )}
      </Scene3D>
      <S.SketchBadge />
    </SceneFrame>
  );
}
