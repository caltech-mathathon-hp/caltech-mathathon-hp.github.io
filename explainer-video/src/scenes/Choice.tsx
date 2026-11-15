/**
 * Scene "choice": the sketch face of "padding", with two open holes and two plugged.
 * Cue 1: the items 6, 2, 8, 4 come in right of the face as bars with their sizes, one after
 *        another in string order. Then, one at a time and in string order, each bar moves along one
 *        smooth path to the row of its hole and straight into it, and gives way to its beads (as in
 *        step 35): 6 + 4 in hole 1, 2 + 8 in hole 2. The holes' sub-lines add up their items.
 * Cue 2: the puzzle's two full bins appear beside the holes, row for row (the key claim), each with
 *        its sum ("6 + 4 = 10", as in part 2).
 * Cue 3: fold ⇒ packing: the bins empty; hole 1's box lights up and bin 1 is filled again from it,
 *        bar by bar; then hole 2 and bin 2: the items in one hole form one bin.
 * Cue 4: packing ⇒ fold: the face is cleared; each bar moves out of its bin straight along its row
 *        into the hole on that row and gives way to its beads, one at a time in string order. Discs
 *        right of each hole give its items' order in the string, and a panel "order in the string"
 *        draws the three joins still missing between consecutive items.
 *
 * The frame stays full orange throughout (face-on). Coming and going is by opacity; a bar moving
 * over the face is opaque and on top.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D, R_RES } from '../three/Scene3D';
import { BinTrack, BinSum, ItemBar, Arrow, trackHeight, trackWidth, slotX, slotY, TRACK_PAD } from '../ui/Bins';
import { C, FONT, W, H, itemColor } from '../theme/theme';
import { lerp, ramp } from '../lib/anim';
import type { SceneTime, CueTime } from '../script';
import * as S from './lib/padding-sketch';
import { BIN_H } from './Padding';

const unit = S.PITCH;
const rb = R_RES * unit;
const COLORS = S.SIZES.map((_, u) => itemColor(u));
/** cue 1: where the items wait, right of the face (the column of their left ends, and their rows) */
const STACK_COL = 32;
const WAIT_ROW = [1.5, 4, 6.5, 9];
/** the joins still missing: a neutral colour (linkers get their own later) */
const JOIN = C.fgMuted;

const trackX = S.X(S.BIN_COL - 0.5) - TRACK_PAD;
const trackY = (b: number) => S.Y(S.STRIPS[b].holeRow) - trackHeight(BIN_H) / 2;
const GAP_L = S.X(S.COLS - 1) + 30;
const GAP_R = trackX - 22;
const GAP_Y = (S.Y(S.STRIPS[0].holeRow) + S.Y(S.STRIPS[1].holeRow)) / 2;

type P2 = [number, number];
/** an item bar's top-left corner: waiting right of the face, on its hole, in its bin */
const waitXY = (u: number): P2 => [S.X(STACK_COL - 0.5), S.Y(WAIT_ROW[u]) - BIN_H / 2];
const holeXY = (it: S.PlacedItem): P2 => [S.X(S.HOLE_COL0 + it.slot - 0.5), S.Y(S.STRIPS[it.bin].holeRow) - BIN_H / 2];
const binXY = (it: S.PlacedItem): P2 => [slotX(trackX, it.slot, unit), slotY(trackY(it.bin))];

/**
 * One smooth way from a to b (a bar's top-left corner): an S-bend that ends level with b at x = xe,
 * right of the face, then straight along the row into the hole. s (0..1, by length) → point.
 */
function smoothPath(a: P2, b: P2, xe: number) {
  const pts: P2[] = [];
  const N = 48;
  for (let i = 0; i <= N; i++) {
    const s = i / N;
    pts.push([lerp(a[0], xe, s), lerp(a[1], b[1], (1 - Math.cos(Math.PI * s)) / 2)]);
  }
  if (Math.abs(xe - b[0]) > 0.5) pts.push(b);
  const L = [0];
  for (let i = 1; i < pts.length; i++) L.push(L[i - 1] + Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]));
  const total = L[L.length - 1];
  return (s: number): P2 => {
    const d = Math.min(1, Math.max(0, s)) * total;
    let i = 1;
    while (i < pts.length - 1 && L[i] < d) i++;
    const t = L[i] > L[i - 1] ? (d - L[i - 1]) / (L[i] - L[i - 1]) : 0;
    return [lerp(pts[i - 1][0], pts[i][0], t), lerp(pts[i - 1][1], pts[i][1], t)];
  };
}
/** cue 1: each item's way from where it waits into its hole */
const INTO = S.PLACED.map((it) => smoothPath(waitXY(it.u), holeXY(it), S.X(S.COLS + 0.5)));

// ------------------------------------------------------------------ timing (frames from each cue's start)

/** cue 1: the items come in, then go into their holes one at a time (the next leaves once the last has landed) */
const T1 = { noteOut: 0, appear: 14, appearGap: 8, legend: 50, fly: 64, flyGap: 40, flyDur: 36, chip: 8 };
/** cue 2: the bins with their bars and sums, the guides, ⟺ */
const T2 = { bins: 10, guides: 34, iff: 46 };
/** cue 3: fold ⇒ packing; hole by hole, its box lights up and its bin is filled from it */
const T3 = { iffOut: 0, arrow: 12, barsOut: 26, hole: [44, 108], chip: 8 };
/** cue 4: packing ⇒ fold; the bars go back one at a time; then the order in the string */
const T4 = { arrowOut: 0, arrow: 12, clear: 8, move: 28, moveDur: 28, chip: 8, discs: 168, panel: 176, chain: 180, joins: 194 };

/** ⟺, drawn (fonts differ in whether they have the glyph); its words are a grey sub-line */
function Iff({ x, y, opacity }: { x: number; y: number; opacity: number }) {
  if (opacity <= 0) return null;
  const w = 64;
  const h = 7;
  const head = 14;
  return (
    <g opacity={opacity}>
      <g stroke={C.accent} strokeWidth={3} fill="none" strokeLinecap="round" strokeLinejoin="round">
        <line x1={x - w / 2 + 6} y1={y - h} x2={x + w / 2 - 6} y2={y - h} />
        <line x1={x - w / 2 + 6} y1={y + h} x2={x + w / 2 - 6} y2={y + h} />
        <path d={`M${x - w / 2 + head},${y - h - head * 0.8} L${x - w / 2},${y} L${x - w / 2 + head},${y + h + head * 0.8}`} />
        <path d={`M${x + w / 2 - head},${y - h - head * 0.8} L${x + w / 2},${y} L${x + w / 2 - head},${y + h + head * 0.8}`} />
      </g>
      <text x={x} y={y - 30} textAnchor="middle" fontFamily={FONT.sans} {...S.SUB}>
        exactly when
      </text>
    </g>
  );
}

/** an arrow between the face and the bins (a mark, in the accent colour), its words a grey sub-line above it */
function GapArrow({ from, to, label, opacity }: { from: P2; to: P2; label: string; opacity: number }) {
  if (opacity <= 0) return null;
  return (
    <g opacity={opacity}>
      <Arrow from={from} to={to} color={C.accent} />
      <text x={(from[0] + to[0]) / 2} y={(from[1] + to[1]) / 2 - 16} textAnchor="middle" fontFamily={FONT.sans} {...S.SUB}>
        {label}
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
  const at = (c: CueTime, k: number) => c.from + k;
  const fd = S.fade;

  // ---- the face as "padding" leaves it
  const d = S.newDraw();
  S.drawFrame(d);
  S.drawHoles(d);
  for (const st of S.STRIPS) S.drawRibbon(d, st.padding, C.pad, 1);
  S.drawRibbon(d, S.STRIPS[2].hole, S.PLUG, 1);
  S.drawRibbon(d, S.STRIPS[3].hole, S.PLUG, 1);
  const legend = { wall: 1, empty: 1, pad: 1, plug: 1 };
  S.drawLegend(d, legend);

  // ---- cue 1: the items come in, then each goes into its hole and gives way to its beads
  const appear = (u: number) => fd(f, at(c0, T1.appear + T1.appearGap * u), 10);
  const flyAt = (u: number) => at(c0, T1.fly + T1.flyGap * u);
  const landAt = (u: number) => flyAt(u) + T1.flyDur;
  const revealAt = (u: number) => landAt(u) + T1.chip;
  const itemsLegend = fd(f, at(c0, T1.legend), 10);
  S.drawItemsLegend(d, itemsLegend, COLORS);

  // ---- cue 4: the face is cleared, then each bar goes back from its bin into its hole
  const clear = fd(f, at(c3, T4.clear), 12);
  const moveAt = (u: number) => at(c3, T4.move + T4.moveDur * u);
  const backLand = (u: number) => moveAt(u) + T4.moveDur;
  const backReveal = (u: number) => backLand(u) + T4.chip;

  for (const it of S.PLACED) {
    const u = it.u;
    if (f < c3.from + T4.clear) {
      const w = S.giveWay(it.cells, f - revealAt(u));
      S.drawRibbon(d, it.cells, COLORS[u], (k) => w.bead(k) * (1 - clear));
    } else if (clear < 1) S.drawRibbon(d, it.cells, COLORS[u], 1 - clear);
    else {
      const w = S.giveWay(it.cells, f - backReveal(u));
      S.drawRibbon(d, it.cells, COLORS[u], (k) => w.bead(k));
    }
  }
  d.lines.push(...S.outline(1));

  // ---- cue 2: the bins with their bars and sums; cue 3: the bars go, and come back hole by hole
  const binsIn = fd(f, at(c1, T2.bins), 18);
  const barsOut = fd(f, at(c2, T3.barsOut), 10);
  const holeAt = (b: number) => at(c2, T3.hole[b]);
  /** cue 3: when bar u is wiped into its bin (left to right in the bin, after its hole lights up) */
  const wipeAt = (u: number) => {
    const it = S.PLACED[u];
    const first = S.BINS[it.bin][0];
    return holeAt(it.bin) + 10 + (u === first ? 0 : S.wipeFrames(S.SIZES[first]) + 2);
  };
  const binDone = (b: number) => Math.max(...S.BINS[b].map((u) => wipeAt(u) + S.wipeFrames(S.SIZES[u]))) + 4;
  const ring = (b: number) => fd(f, holeAt(b), 8) * (1 - fd(f, binDone(b) + 6, 10));
  // a bin's green border and its sum: in with the bins; off while its bars are out (cue 3), back once
  // its last bar is in; off again when its first bar leaves (cue 4)
  const binFull = (b: number) => {
    if (f < c2.from) return binsIn;
    if (f < c3.from) return Math.max(1 - barsOut, fd(f, binDone(b), 10));
    return 1 - fd(f, moveAt(S.BINS[b][0]), 8);
  };

  // ---- labels and marks
  const note = 1 - fd(f, at(c0, T1.noteOut), 8);
  const guides = fd(f, at(c1, T2.guides), 12) * (1 - fd(f, at(c3, T4.arrowOut), 10));
  const iff = fd(f, at(c1, T2.iff), 14) * (1 - fd(f, at(c2, T3.iffOut), 10));
  const arrowR = fd(f, at(c2, T3.arrow), 12) * (1 - fd(f, at(c3, T4.arrowOut), 10));
  const arrowL = fd(f, at(c3, T4.arrow), 10);
  // cue 4: the order in the string, right of the holes, then the panel and the joins
  const badge = (u: number) => fd(f, at(c3, T4.discs + 4 * u), 10);
  const orderLab = fd(f, at(c3, T4.discs), 10);
  const panelIn = fd(f, at(c3, T4.panel), 10);
  const chainBadge = (u: number) => fd(f, at(c3, T4.chain + 4 * u), 8);
  const join = (i: number) => ramp(f, at(c3, T4.joins + 8 * i), 10);

  // a hole's sub-line: "10 nodes", then (once its first item's beads are in) the sizes of its items
  // as they come; in cue 4 the sizes go with the cleared items and come back as they are laid again
  const holeSub = (b: number) => {
    const [u0, u1] = S.BINS[b];
    // cue 4, once the face is cleared: the sizes come back as the items are laid again
    const again = f >= c3.from + T4.clear + 12;
    const first = S.giveWayEnd(S.SIZES[u0], again ? backReveal(u0) : revealAt(u0));
    const second = fd(f, S.giveWayEnd(S.SIZES[u1], again ? backReveal(u1) : revealAt(u1)), 8);
    if (!again && f < first + 8) return { text: '10 nodes' as React.ReactNode, o: 1 - fd(f, first, 8) };
    const text = (
      <>
        {S.SIZES[u0]}
        <tspan fillOpacity={second}>{` + ${S.SIZES[u1]}`}</tspan>
      </>
    );
    if (again) return { text, o: fd(f, first, 8) };
    return { text, o: f < c3.from ? fd(f, first + 8, 8) : 1 - clear };
  };

  // the panel "order in the string", top left, above the hole labels; its left edge on the header's
  const PX0 = 64;
  const PY0 = 106;
  const CH_X = (u: number) => PX0 + 38 + 74 * u;
  const CH_Y = PY0 + 106;
  // the order discs right of the holes: in each hole, its items left to right
  const BADGE_X = (k: number) => S.X(S.COLS - 1) + rb + 40 + 46 * k;

  /** an item's bar: where it is and how much of it shows, or null */
  const barOf = (it: S.PlacedItem) => {
    const u = it.u;
    const size = S.SIZES[u];
    if (f < c1.from) {
      // cue 1: waiting, moving into its hole, giving way to its beads
      const go = easeSine01(f - flyAt(u), T1.flyDur);
      const w = S.giveWay(it.cells, f - revealAt(u));
      if (w.gone) return null;
      const [x, y] = go > 0 ? INTO[u](go) : waitXY(u);
      const lift = Math.sin(Math.PI * go);
      return { x, y: y - 8 * lift, lift, op: appear(u), chip: 1 - fd(f, landAt(u), T1.chip), span: f >= revealAt(u) ? w.span : undefined, sliver: false };
    }
    const [bx, by] = binXY(it);
    if (f < c2.from) return { x: bx, y: by, lift: 0, op: binsIn, chip: 1 };
    if (f < c3.from) {
      // cue 3: out with the others, then wiped in from the left, its chip after
      const t = f - wipeAt(u);
      if (t < 0) return barsOut < 1 ? { x: bx, y: by, lift: 0, op: 1 - barsOut, chip: 1 } : null;
      const R = S.wipeFrames(size);
      const k = Math.min(1, t / R);
      return { x: bx, y: by, lift: 0, op: 1, chip: fd(f, wipeAt(u) + R, 8), span: k < 1 ? ([0, Math.max(0.001, size * k)] as [number, number]) : undefined };
    }
    // cue 4: out of its bin, straight along its row into its hole, giving way to its beads
    const go = easeSine01(f - moveAt(u), T4.moveDur);
    const w = S.giveWay(it.cells, f - backReveal(u));
    if (w.gone) return null;
    const [hx, hy] = holeXY(it);
    const lift = Math.sin(Math.PI * go);
    return { x: lerp(bx, hx, go), y: lerp(by, hy, go) - 8 * lift, lift, op: 1, chip: 1 - fd(f, backLand(u), T4.chip), span: f >= backReveal(u) ? w.span : undefined, sliver: false };
  };
  /** an empty bin shows a dot in every slot (under its bars, which cover them): from when its bars first go (cue 3) */
  const binDots = f < c2.from ? 0 : barsOut;

  return (
    <SceneFrame scene={scene}>
      {/* behind the beads: the holes' boxes (one lights up in cue 3), the bins */}
      <svg width={W} height={H} style={{ position: 'absolute', inset: 0 }}>
        {S.STRIPS.map((st) => (
          <S.HoleBox key={st.s} s={st.s} opacity={1} />
        ))}
        {[0, 1].map((b) => (
          <S.HoleBox key={`r${b}`} s={b} opacity={ring(b)} stroke={C.accent} width={3.5} />
        ))}
        {[0, 1].map((b) => (
          <g key={`bin${b}`} opacity={binsIn}>
            <BinTrack x={trackX} y={trackY(b)} B={S.BIN} unit={unit} h={BIN_H} label={`bin ${b + 1}`} full={binFull(b)} dots={false} />
            {binDots > 0 && Array.from({ length: S.BIN }, (_, k) => <circle key={k} cx={slotX(trackX, k, unit) + unit / 2} cy={trackY(b) + trackHeight(BIN_H) / 2} r={3} fill={C.lattice} opacity={binDots} />)}
            <BinSum x={trackX + trackWidth(S.BIN, unit) + 26} y={trackY(b) + trackHeight(BIN_H) / 2 + 9} items={S.BINS[b].map((u) => ({ u, size: S.SIZES[u] }))} B={S.BIN} opacity={binFull(b)} />
          </g>
        ))}
      </svg>
      <Scene3D shot={S.SHOT} beads={d.beads} sticks={d.sticks} lines={d.lines}>
        {() => (
          <g fontFamily={FONT.sans}>
            {S.STRIPS.map((st) => {
              if (st.s >= 2) return <S.HoleLabel key={st.s} s={st.s} title="plug" sub="10 H’s" opacity={1} />;
              const sub = holeSub(st.s);
              return <S.HoleLabel key={st.s} s={st.s} title={`hole ${st.s + 1}`} sub={sub.text} subOpacity={sub.o} opacity={1} />;
            })}
            <S.LegendLabels show={legend} />
            {/* from "padding": the plugs' holes are an example; it goes before the items come */}
            <S.SpareNote opacity={note} />
            {/* the items, in the legend */}
            {itemsLegend > 0 &&
              (() => {
                const [lx, ly] = S.legendText(S.LEG_ROW_ITEMS);
                return (
                  <text x={lx} y={ly + 7.5} {...S.SUB} opacity={itemsLegend}>
                    items (H’s)
                  </text>
                );
              })()}
            {/* the joins, in the legend */}
            {(() => {
              const o = fd(f, at(c3, T4.joins), 10);
              if (o <= 0) return null;
              const [lx, ly] = S.legendText(S.LEG_ROW_JOIN);
              const x0 = S.X(S.LEG_COL - 0.1);
              const x1 = S.X(S.LEG_COL + 1.1);
              return (
                <g opacity={o}>
                  <path d={`M${x0},${ly + 6} Q${(x0 + x1) / 2},${ly - 16} ${x1},${ly + 6}`} fill="none" stroke={JOIN} strokeWidth={3} strokeLinecap="round" strokeDasharray="6 6" />
                  <text x={lx} y={ly + 7.5} {...S.SUB}>
                    join still missing
                  </text>
                </g>
              );
            })()}
            {/* row for row: hole b and bin b */}
            {guides > 0 &&
              [0, 1].map((b) => {
                const y = S.Y(S.STRIPS[b].holeRow);
                return <line key={b} x1={GAP_L} x2={GAP_R + 10} y1={y} y2={y} stroke={C.fgSubtle} strokeWidth={2} strokeDasharray="2 7" strokeLinecap="round" opacity={guides} />;
              })}
            <Iff x={(GAP_L + GAP_R) / 2} y={GAP_Y} opacity={iff} />
            <GapArrow from={[GAP_L, GAP_Y]} to={[GAP_R, GAP_Y]} label="fold ⇒ packing" opacity={arrowR} />
            <GapArrow from={[GAP_R, GAP_Y]} to={[GAP_L, GAP_Y]} label="packing ⇒ fold" opacity={arrowL} />
            {/* cue 4: right of each hole, the order in the string of its items, left to right */}
            {orderLab > 0 && (
              <text x={(BADGE_X(0) + BADGE_X(1)) / 2} y={S.Y(S.STRIPS[0].holeRow) - 32} textAnchor="middle" {...S.SUB} opacity={orderLab}>
                order
              </text>
            )}
            {S.PLACED.map((it) => {
              const k = S.BINS[it.bin].indexOf(it.u);
              return <OrderBadge key={it.u} x={BADGE_X(k)} y={S.Y(S.STRIPS[it.bin].holeRow)} n={it.u + 1} color={COLORS[it.u]} opacity={badge(it.u)} />;
            })}
            {/* cue 4: the order in the string and the joins still missing, in a panel */}
            {panelIn > 0 && (
              <g>
                <rect x={PX0} y={PY0} width={CH_X(3) + 38 - PX0} height={CH_Y + 34 - PY0} rx={10} fill={C.bgElev} stroke={C.ruleStrong} strokeWidth={1.5} opacity={panelIn} />
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
                  <OrderBadge key={u} x={CH_X(u)} y={CH_Y} n={u + 1} color={COLORS[u]} opacity={chainBadge(u)} r={20} />
                ))}
              </g>
            )}
            {/* the item bars, on top of everything: waiting, moving, in the bins */}
            {S.PLACED.map((it) => {
              const bar = barOf(it);
              if (!bar || bar.op <= 0) return null;
              return (
                <ItemBar
                  key={it.u}
                  x={bar.x}
                  y={bar.y}
                  size={S.SIZES[it.u]}
                  color={COLORS[it.u]}
                  unit={unit}
                  h={BIN_H}
                  opacity={bar.op}
                  lift={bar.lift}
                  chipOpacity={bar.chip}
                  span={bar.span}
                  sliverFade={bar.sliver ?? true}
                />
              );
            })}
          </g>
        )}
      </Scene3D>
      <S.SketchBadge />
    </SceneFrame>
  );
}

/** progress of a move of `dur` frames, `t` frames in: eased gently at both ends only */
function easeSine01(t: number, dur: number) {
  return S.easeSine(t / dur);
}
