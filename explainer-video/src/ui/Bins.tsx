/**
 * Bin packing in the look of the site's bin-packing game (site/src/widgets/bin-pack/styles.css),
 * as SVG: an item is a rounded bar of `size` units in its colour, with thin lines between the
 * units and a white chip with its size; a bin is a track of B units with a dot in every free unit.
 * Put these inside an <svg> (Scene3D's overlay, or a full-frame <svg>).
 *
 *   <BinTrack x={…} y={…} B={10} label="bin 1" />
 *   <ItemBar x={slotX(trackX, 0)} y={slotY(trackY)} size={6} color={itemColor(0)} />
 */
import React from 'react';
import { C, FONT, itemColor } from '../theme/theme';

export const BAR = { unit: 48, h: 46 };
/** border + padding of a track: an item at slot k sits at x + TRACK_PAD + k·unit */
export const TRACK_PAD = 4.5;
export const trackWidth = (B: number, unit = BAR.unit) => B * unit + 2 * TRACK_PAD;
export const trackHeight = (h = BAR.h) => h + 2 * TRACK_PAD;
export const slotX = (trackX: number, k: number, unit = BAR.unit) => trackX + TRACK_PAD + k * unit;
export const slotY = (trackY: number) => trackY + TRACK_PAD;

export interface ItemBarProps {
  x: number;
  y: number;
  size: number;
  color: string;
  unit?: number;
  h?: number;
  opacity?: number;
  /** the size chip; a string replaces the number */
  chip?: boolean | string;
  /** an outline (red for "does not fit", say) */
  stroke?: string;
  /** 0..1, for an outline that fades in */
  strokeOpacity?: number;
  /** rotate about the bar's centre, degrees (a lifted item) */
  tilt?: number;
  /** lift: a soft shadow under the bar, 0..1 */
  lift?: number;
  /** 0..1, the size chip's opacity (a chip that fades out before the bar turns into beads) */
  chipOpacity?: number;
  /**
   * Only the units [a, b] of the bar (0 ≤ a < b ≤ size), the rest left out: a bar that shrinks
   * cell by cell to uncover the beads under it, or grows over them. The unit lines stay on the
   * cell borders.
   */
  span?: [number, number];
  /**
   * With a `span`: the bar also fades over its last unit (default). `false` keeps it at full colour
   * to the end, for a bar that gives way to beads coming in under it (a fading bar over them would
   * show as a pale sliver).
   */
  sliverFade?: boolean;
}

export function ItemBar({ x, y, size, color, unit = BAR.unit, h = BAR.h, opacity = 1, chip = true, stroke, strokeOpacity = 1, tilt = 0, lift = 0, chipOpacity = 1, span, sliverFade = true }: ItemBarProps) {
  if (opacity <= 0 || size <= 0) return null;
  const w = size * unit;
  const [a, b] = span ?? [0, size];
  if (b - a <= 0.01) return null;
  // the drawn part: [x0, x1], inset 2 px at the bar's own ends only
  const x0 = x + a * unit + (a <= 0 ? 2 : 0);
  const x1 = x + b * unit - (b >= size ? 2 : 0);
  const lines = [];
  for (let k = 1; k < size; k++) if (k > a + 0.05 && k < b - 0.05) lines.push(<line key={k} x1={x + k * unit} x2={x + k * unit} y1={y + 2} y2={y + h - 2} stroke={C.bgElev} strokeOpacity={0.5} strokeWidth={1.2} />);
  const label = typeof chip === 'string' ? chip : String(size);
  const chipW = Math.max(30, 14 + label.length * 12);
  const whole = a <= 0 && b >= size;
  const rx = Math.min(7, (x1 - x0) / 2);
  // over its last unit a shrinking bar also fades (and a growing one fades in over its first), so
  // no thin pill is left standing on the bead under it
  const sliver = span && sliverFade ? Math.min(1, b - a) : 1;
  return (
    <g opacity={opacity * sliver} transform={tilt ? `rotate(${tilt} ${x + w / 2} ${y + h / 2})` : undefined}>
      {lift > 0 && <rect x={x0 + 4 * lift} y={y + 2 + 8 * lift} width={x1 - x0} height={h - 4} rx={rx} fill="#000" opacity={0.12 * lift} />}
      <rect x={x0} y={y + 2} width={x1 - x0} height={h - 4} rx={rx} fill={color} />
      {lines}
      {chip !== false && whole && chipOpacity > 0 && (
        <g opacity={chipOpacity}>
          <rect x={x + w / 2 - chipW / 2} y={y + h / 2 - 15} width={chipW} height={30} rx={5} fill={C.bgElev} />
          <text x={x + w / 2} y={y + h / 2 + 7} textAnchor="middle" fontFamily={FONT.sans} fontWeight={650} fontSize={20} fill={C.fg} style={{ fontVariantNumeric: 'tabular-nums' }}>
            {label}
          </text>
        </g>
      )}
      {stroke && strokeOpacity > 0 && <rect x={x + 1} y={y + 1} width={w - 2} height={h - 2} rx={8} fill="none" stroke={stroke} strokeWidth={3} strokeOpacity={strokeOpacity} />}
    </g>
  );
}

export interface BinTrackProps {
  x: number;
  y: number;
  /** capacity in units */
  B: number;
  unit?: number;
  h?: number;
  opacity?: number;
  /** 'full': green border (the game's "full" state); 'refuse': red (an item does not fit) */
  state?: 'normal' | 'full' | 'refuse';
  /**
   * How far the green "full" border is in, 0..1, instead of `state`: pass a value that ramps over
   * several frames, so the border fades in and out rather than switching in one frame
   */
  full?: number;
  /** above the track, left: the bin's name ("bin 1"), in the name style of the picture */
  label?: string;
  /** a grey sub-line under the name ("size 10") */
  sub?: string;
  /** dots in the free units; pass the units already covered to hide their dots */
  covered?: number;
  /** draw the dots at all */
  dots?: boolean;
}

export function BinTrack({ x, y, B, unit = BAR.unit, h = BAR.h, opacity = 1, state = 'normal', full, label, sub, covered = 0, dots = true }: BinTrackProps) {
  if (opacity <= 0) return null;
  const w = trackWidth(B, unit);
  const th = trackHeight(h);
  const green = Math.min(1, Math.max(0, full ?? (state === 'full' ? 1 : 0)));
  const border = state === 'refuse' ? C.invalid : C.ruleStrong;
  const ds = [];
  if (dots) for (let k = Math.ceil(covered); k < B; k++) ds.push(<circle key={k} cx={slotX(x, k, unit) + unit / 2} cy={y + th / 2} r={3} fill={C.lattice} />);
  return (
    <g opacity={opacity}>
      {label && (
        <text x={x + 2} y={y - (sub ? 42 : 13)} fontFamily={FONT.sans} fontSize={26} fontWeight={600} fill={C.fg}>
          {label}
        </text>
      )}
      {label && sub && (
        <text x={x + 2} y={y - 12} fontFamily={FONT.sans} fontSize={22} fontWeight={500} fill={C.fgMuted}>
          {sub}
        </text>
      )}
      {state === 'refuse' && <rect x={x - 3} y={y - 3} width={w + 6} height={th + 6} rx={13} fill="none" stroke={C.invalid} strokeOpacity={0.35} strokeWidth={3} />}
      <rect x={x + 0.75} y={y + 0.75} width={w - 1.5} height={th - 1.5} rx={10} fill={C.bgElev} stroke={border} strokeWidth={state === 'refuse' ? 2.5 : 1.5} />
      {green > 0 && <rect x={x + 0.75} y={y + 0.75} width={w - 1.5} height={th - 1.5} rx={10} fill="none" stroke={C.ok} strokeWidth={2.5} opacity={green} />}
      {ds}
    </g>
  );
}

/** a thin arrow between two points, with an optional label above its middle */
export function Arrow({ from, to, label, opacity = 1, color = C.fgMuted, progress = 1 }: { from: [number, number]; to: [number, number]; label?: string; opacity?: number; color?: string; progress?: number }) {
  if (opacity <= 0 || progress <= 0) return null;
  const [x1, y1] = from;
  const x2 = x1 + (to[0] - x1) * progress;
  const y2 = y1 + (to[1] - y1) * progress;
  const a = Math.atan2(y2 - y1, x2 - x1);
  const hl = 14;
  const p1 = [x2 - hl * Math.cos(a - 0.45), y2 - hl * Math.sin(a - 0.45)];
  const p2 = [x2 - hl * Math.cos(a + 0.45), y2 - hl * Math.sin(a + 0.45)];
  return (
    <g opacity={opacity}>
      <line x1={x1} y1={y1} x2={x2} y2={y2} stroke={color} strokeWidth={2.5} strokeLinecap="round" />
      <path d={`M${p1[0]},${p1[1]} L${x2},${y2} L${p2[0]},${p2[1]}`} fill="none" stroke={color} strokeWidth={2.5} strokeLinecap="round" strokeLinejoin="round" />
      {label && (
        <text x={(x1 + to[0]) / 2} y={(y1 + to[1]) / 2 - 16} textAnchor="middle" fontFamily={FONT.sans} fontSize={22} fill={color} opacity={clampLabel(progress)}>
          {label}
        </text>
      )}
    </g>
  );
}
const clampLabel = (p: number) => Math.max(0, Math.min(1, (p - 0.6) / 0.4));

/**
 * What a full bin holds, right of its track: "6 + 4 = 10" in the name style of the picture, the
 * sizes in their items' colours as in the captions
 */
export function BinSum({ x, y, items, B = 10, opacity = 1 }: { x: number; y: number; items: { u: number; size: number }[]; B?: number; opacity?: number }) {
  if (opacity <= 0) return null;
  return (
    <text x={x} y={y} fontFamily={FONT.sans} fontSize={26} fontWeight={600} fill={C.fg} opacity={opacity} style={{ fontVariantNumeric: 'tabular-nums' }}>
      {items.map((it, k) => (
        <React.Fragment key={k}>
          {k > 0 && ' + '}
          <tspan fill={itemColor(it.u)} fontWeight={700}>
            {it.size}
          </tspan>
        </React.Fragment>
      ))}
      {` = ${B}`}
    </text>
  );
}
