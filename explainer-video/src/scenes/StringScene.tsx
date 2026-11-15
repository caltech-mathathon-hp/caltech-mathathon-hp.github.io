/**
 * Scene "string": the toy string's 1,728 H's as one bar, in string order and to scale, coloured
 * by what they build (frame, core, walls, then the paddings and items). The frame's pieces are
 * named (rod 1, ribbons 1 to 5, rod 2); the end of the bar (walls, paddings, items: 120 H's) is
 * shown again five times wider. Rods, ribbons and walls are all orange, split by white rules; only
 * the core is a lighter tint. Then a zoom into the end of the string, piece after piece in string
 * order: the end of the walls, then each padding and item ribbon after a linker of 626 P's. A
 * bracket says that the three linkers before the items are routed in front of the cube too.
 *
 * The bar counts H's, not letters: most letters of the toy string are the P's of its six linkers
 * (6 × 624 of 6,386), but the caption is about the H's, one per node of the cube.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { ItemBar } from '../ui/Bins';
import { ramp, sec, clamp01, lerp, easeOut } from '../lib/anim';
import { C, FONT, itemColor } from '../theme/theme';
import * as M from '../model/toy';
import type { SceneTime } from '../script';
import { FlatString, Label } from './lib/planPipeline';

// ------------------------------------------------------------------ the bar of H's

type Group = 'frame' | 'core' | 'walls' | 'items';
interface Run {
  group: Group;
  origin: M.Origin;
  /** first H (0-based) and number of H's */
  from: number;
  h: number;
  color: string;
}

const GROUP_OF: Partial<Record<M.Origin, Group>> = {
  corner: 'frame',
  tenth: 'frame',
  face: 'frame',
  core: 'core',
  'wall-rod': 'walls',
  wall: 'walls',
  spaced: 'walls',
  padding: 'items',
  plug: 'items',
  item: 'items',
};
/** rods, ribbons and walls are orange as on every face; only the core, one block inside, is a lighter tint */
const SHADE: Record<Group, string> = { frame: C.h, core: '#e39d80', walls: C.h, items: C.pad };

const SEGS = M.toyString();
const RUNS: Run[] = (() => {
  const out: Run[] = [];
  let at = 0;
  for (const s of SEGS) {
    if (!s.h) continue;
    const group = GROUP_OF[s.origin]!;
    const color = s.origin === 'item' ? itemColor(s.index ?? 0) : s.origin === 'padding' ? C.pad : SHADE[group];
    out.push({ group, origin: s.origin, from: at, h: s.h, color });
    at += s.h;
  }
  return out;
})();
const TOTAL_H = RUNS.reduce((a, r) => a + r.h, 0); // 1728
const groupSpan = (g: Group) => {
  const rs = RUNS.filter((r) => r.group === g);
  return { from: rs[0].from, to: rs[rs.length - 1].from + rs[rs.length - 1].h };
};
const SPANS = { frame: groupSpan('frame'), core: groupSpan('core'), walls: groupSpan('walls'), items: groupSpan('items') };

const BAR_X = 90;
const BAR_W = 1740;
const BAR_Y = 300;
const BAR_H = 52;
const px = (h: number) => BAR_X + (h / TOTAL_H) * BAR_W;
const fmt = (k: number) => k.toLocaleString('en-US');
/** the group names under the bar (a row above them is kept for the short rod 2) */
const NAME_Y = BAR_Y + BAR_H + 92;

/** the frame's pieces, named: rod 1, ribbon 1, rod 2 (10 H's, too thin for a name inside), ribbons 2 to 5 */
const FRAME_RUNS = (() => {
  let ribbon = 0;
  return RUNS.filter((r) => r.group === 'frame').map((r) => ({ ...r, name: r.origin === 'corner' ? 'rod 1' : r.origin === 'tenth' ? 'rod 2' : `ribbon ${++ribbon}` }));
})();

// ------------------------------------------------------------------ the end of the bar, magnified (cue 1)

/** walls, paddings and items are 120 H's, a sliver of the bar: drawn again 5 times wider underneath */
const INSET_K = 5;
const INSET_FROM = SPANS.walls.from;
const INSET_W = (TOTAL_H - INSET_FROM) * INSET_K;
const INSET_X = BAR_X + BAR_W - INSET_W;
const INSET_Y = 560;
const ix = (h: number) => INSET_X + (h - INSET_FROM) * INSET_K;

// ------------------------------------------------------------------ the end of the string, enlarged

const ROW_Y = 616;
const UNIT = 17;
const LINK_STEP = 14;
const LINK_SEQ = 'PPPPPP';
const LINK_W = 5 * LINK_STEP + 0.54 * LINK_STEP + 0.9 * LINK_STEP + 6;
const GAP = 7;
/** the row starts with the last 2 H's of the walls, after a "…" */
const WALL_STUB = 2;
const DOTS_W = 34;
interface RowEl {
  kind: 'walls' | 'linker' | 'padding' | 'item';
  index: number;
  x: number;
  w: number;
}
const ROW: RowEl[] = (() => {
  const els: { kind: RowEl['kind']; index: number; w: number }[] = [{ kind: 'walls', index: 0, w: WALL_STUB * UNIT }];
  for (const s of SEGS) {
    if (s.origin === 'linker') els.push({ kind: 'linker', index: els.length, w: LINK_W });
    else if (s.origin === 'padding') els.push({ kind: 'padding', index: s.index ?? 0, w: s.h * UNIT });
    else if (s.origin === 'item') els.push({ kind: 'item', index: s.index ?? 0, w: s.h * UNIT });
  }
  const total = DOTS_W + els.reduce((a, e) => a + e.w, 0) + GAP * (els.length - 1);
  let x = (1920 - total) / 2 + DOTS_W;
  return els.map((e) => {
    const out = { ...e, x };
    x += e.w + GAP;
    return out;
  });
})();
const ROW_L = ROW[0].x - DOTS_W;
const ROW_R = ROW[ROW.length - 1].x + ROW[ROW.length - 1].w;
/** the part of the bar the row shows again: from the last wall on */
const LAST_WALL = (() => {
  const ws = RUNS.filter((r) => r.origin === 'wall');
  return ws[ws.length - 1].from;
})();
/** P's between two ribbons: the linker's own run plus the P at each ribbon end (PHHP…PHHP) */
const LINKER_PS = (SEGS.find((s) => s.origin === 'linker')?.len ?? 0) + 2;

export default function StringScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1] = scene.cueTimes;

  // cue 1
  const head = ramp(f, c0.from, sec(0.6));
  const grow = ramp(f, c0.from + sec(0.7), sec(2.8));
  const growH = grow * TOTAL_H;
  /** a group's label fades in over the last 40 H's of the group, so it is full once the group is drawn */
  const labelIn = (g: Group) => clamp01((growH - SPANS[g].to) / 40 + 1);
  /** a frame piece's name, once the bar has passed it */
  const pieceIn = (to: number) => clamp01((growH - to) / 30 + 1);
  const insetIn = ramp(f, c0.from + sec(3.6), sec(0.7));

  // cue 2
  const zoomOut = ramp(f, c1.from, sec(0.5));
  const lines = ramp(f, c1.from + sec(0.3), sec(0.9));
  /** the row, piece after piece in string order: each fades in whole before the next starts */
  const ROW_FADE = sec(0.38);
  const rowT = (i: number) => ramp(f, c1.from + sec(0.9 + i * 0.4), ROW_FADE);
  const routedNote = ramp(f, c1.from + sec(0.9 + ROW.length * 0.4 + 0.1), sec(0.4));

  const segClip = 'string-bar-clip';
  return (
    <SceneFrame scene={scene}>
      <svg width={1920} height={1080} style={{ position: 'absolute', inset: 0 }}>
        <defs>
          <clipPath id={segClip}>
            <rect x={BAR_X} y={BAR_Y} width={BAR_W * grow} height={BAR_H} rx={0} />
          </clipPath>
        </defs>

        {/* header: one H per node */}
        <g opacity={head}>
          <line x1={BAR_X} x2={BAR_X + BAR_W} y1={BAR_Y - 26} y2={BAR_Y - 26} stroke={C.fgSubtle} strokeWidth={1.5} />
          <line x1={BAR_X} x2={BAR_X} y1={BAR_Y - 34} y2={BAR_Y - 18} stroke={C.fgSubtle} strokeWidth={1.5} />
          <line x1={BAR_X + BAR_W} x2={BAR_X + BAR_W} y1={BAR_Y - 34} y2={BAR_Y - 18} stroke={C.fgSubtle} strokeWidth={1.5} />
          <rect x={960 - 250} y={BAR_Y - 46} width={500} height={40} fill={C.bg} />
          <text x={960} y={BAR_Y - 18} textAnchor="middle" fontFamily={FONT.sans} fontSize={26} fontWeight={600} fill={C.fg}>
            1,728 <tspan fill={C.h}>H</tspan>’s, one for each node of the cube
          </text>
        </g>

        {/* the bar */}
        <rect x={BAR_X} y={BAR_Y} width={BAR_W} height={BAR_H} rx={8} fill={C.bgElev} stroke={C.rule} strokeWidth={1.5} opacity={head} />
        <g clipPath={`url(#${segClip})`}>
          <g>
            {RUNS.map((r, i) => (
              <rect key={i} x={px(r.from)} y={BAR_Y} width={Math.max(0.6, px(r.from + r.h) - px(r.from))} height={BAR_H} fill={r.color} />
            ))}
            {/* thin gaps between the pieces of the frame and of the walls */}
            {RUNS.filter((r) => (r.group === 'frame' || r.group === 'walls') && r.from > 0).map((r, i) => (
              <line key={`s${i}`} x1={px(r.from)} x2={px(r.from)} y1={BAR_Y} y2={BAR_Y + BAR_H} stroke={C.bgElev} strokeWidth={1.5} />
            ))}
          </g>
        </g>
        {/* the part shown in the row (the last wall, the paddings and the items), outlined while it is enlarged */}
        <rect x={px(LAST_WALL) - 3} y={BAR_Y - 5} width={px(SPANS.items.to) - px(LAST_WALL) + 6} height={BAR_H + 10} rx={4} fill="none" stroke={C.fg} strokeWidth={2} opacity={lines} />

        {/* the frame's pieces, named inside the bar; rod 2 is 10 H's thin, so its name sits under it */}
        {FRAME_RUNS.map((r, i) => {
          const o = pieceIn(r.from + r.h);
          if (o <= 0) return null;
          const cx = (px(r.from) + px(r.from + r.h)) / 2;
          return r.origin === 'tenth' ? (
            <g key={i} opacity={o} fontFamily={FONT.sans}>
              <line x1={cx} x2={cx} y1={BAR_Y + BAR_H + 4} y2={BAR_Y + BAR_H + 16} stroke={C.fgSubtle} strokeWidth={1.5} />
              <text x={cx} y={BAR_Y + BAR_H + 40} textAnchor="middle" fontSize={22} fontWeight={600} fill={C.fg}>
                {r.name}
              </text>
            </g>
          ) : (
            <text key={i} x={cx} y={BAR_Y + BAR_H / 2 + 8} textAnchor="middle" fontFamily={FONT.sans} fontSize={22} fontWeight={600} fill="#fff" opacity={o}>
              {r.name}
            </text>
          );
        })}

        {/* labels under the bar */}
        <GroupLabel x={(px(SPANS.frame.from) + px(SPANS.frame.to)) / 2} name="frame" count={SPANS.frame.to - SPANS.frame.from} note="two rods and five face ribbons" opacity={labelIn('frame')} />
        {/* the core is wide enough to carry its label inside; below it, the zoom lines of cue 2 pass */}
        <text x={(px(SPANS.core.from) + px(SPANS.core.to)) / 2} y={BAR_Y + BAR_H / 2 + 9} textAnchor="middle" fontFamily={FONT.sans} fontSize={26} fontWeight={600} fill={C.fg} opacity={labelIn('core')}>
          core
          <tspan fontWeight={500}>{` · ${fmt(SPANS.core.to - SPANS.core.from)} H’s`}</tspan>
        </text>

        {/* the end of the bar, magnified */}
        {insetIn > 0 && (
          <g opacity={insetIn * (1 - zoomOut)} fontFamily={FONT.sans}>
            <rect x={px(INSET_FROM) - 3} y={BAR_Y - 5} width={px(TOTAL_H) - px(INSET_FROM) + 6} height={BAR_H + 10} rx={4} fill="none" stroke={C.fg} strokeWidth={2} />
            <g opacity={0.55}>
              <line x1={px(INSET_FROM) - 3} y1={BAR_Y + BAR_H + 5} x2={INSET_X - 3} y2={INSET_Y - 5} stroke={C.fgSubtle} strokeWidth={1.5} strokeDasharray="5 5" />
              <line x1={px(TOTAL_H) + 3} y1={BAR_Y + BAR_H + 5} x2={INSET_X + INSET_W + 3} y2={INSET_Y - 5} stroke={C.fgSubtle} strokeWidth={1.5} strokeDasharray="5 5" />
            </g>
            <rect x={INSET_X} y={INSET_Y} width={INSET_W} height={BAR_H} fill={C.bgElev} stroke={C.rule} strokeWidth={1.5} />
            {RUNS.filter((r) => r.from >= INSET_FROM).map((r, i) => (
              <rect key={i} x={ix(r.from)} y={INSET_Y} width={r.h * INSET_K} height={BAR_H} fill={r.color} />
            ))}
            {RUNS.filter((r) => r.from > INSET_FROM).map((r, i) => (
              <line key={`s${i}`} x1={ix(r.from)} x2={ix(r.from)} y1={INSET_Y} y2={INSET_Y + BAR_H} stroke={C.bgElev} strokeWidth={1.5} />
            ))}
            {(['walls', 'items'] as const).map((g) => {
              const cx = (ix(SPANS[g].from) + ix(SPANS[g].to)) / 2;
              return (
                <g key={g}>
                  <text x={cx} y={INSET_Y + BAR_H + 36} textAnchor="middle" fontSize={26} fontWeight={600} fill={C.fg}>
                    {g === 'walls' ? 'walls' : 'paddings and items'}
                  </text>
                  <text x={cx} y={INSET_Y + BAR_H + 66} textAnchor="middle" fontSize={22} fill={C.fgMuted}>
                    {`${fmt(SPANS[g].to - SPANS[g].from)} H’s`}
                  </text>
                </g>
              );
            })}
          </g>
        )}

        {/* zoom lines from the item part to the enlarged row */}
        {lines > 0 && (
          <g opacity={0.55}>
            <line x1={px(SPANS.items.from) - 3} y1={BAR_Y + BAR_H + 5} x2={lerp(px(SPANS.items.from) - 3, ROW_L - 6, easeOut(lines))} y2={lerp(BAR_Y + BAR_H + 5, ROW_Y - 62, easeOut(lines))} stroke={C.fgSubtle} strokeWidth={1.5} strokeDasharray="5 5" />
            <line x1={px(SPANS.items.to) + 3} y1={BAR_Y + BAR_H + 5} x2={lerp(px(SPANS.items.to) + 3, ROW_R + 6, easeOut(lines))} y2={lerp(BAR_Y + BAR_H + 5, ROW_Y - 62, easeOut(lines))} stroke={C.fgSubtle} strokeWidth={1.5} strokeDasharray="5 5" />
          </g>
        )}

        {/* the enlarged end of the string */}
        {ROW.map((e, i) => {
          const t = rowT(i);
          if (t <= 0) return null;
          const prev = ROW[i - 1];
          const join = prev && <line x1={prev.x + prev.w - 2} x2={e.x + 2} y1={ROW_Y + 23} y2={ROW_Y + 23} stroke={C.backbone} strokeWidth={1.2} opacity={t} />;
          if (e.kind === 'walls') {
            // the end of the walls: "…" and their last 2 H's
            return (
              <g key={i} opacity={t}>
                {[0, 1, 2].map((k) => (
                  <circle key={k} cx={e.x - DOTS_W + 6 + k * 10} cy={ROW_Y + 23} r={2.6} fill={C.fgSubtle} />
                ))}
                <ItemBar x={e.x} y={ROW_Y} size={WALL_STUB} unit={UNIT} color={C.h} chip={false} />
                <Label x={e.x + e.w / 2 - DOTS_W / 2} y={ROW_Y + 84} size={22}>
                  walls
                </Label>
              </g>
            );
          }
          if (e.kind === 'linker') {
            return (
              <g key={i}>
                {join}
                <g opacity={t}>
                  <FlatString x={e.x} y={ROW_Y + 23} seq={LINK_SEQ} step={LINK_STEP} breakAfter={[2]} tail={false} progress={t} />
                </g>
                <Label x={e.x + e.w / 2} y={ROW_Y - 12} size={22} opacity={clamp01(t * 2 - 1)}>
                  {`${LINKER_PS} P’s`}
                </Label>
              </g>
            );
          }
          const color = e.kind === 'padding' ? C.pad : itemColor(e.index);
          const h = e.w / UNIT;
          // a ribbon too narrow for its size chip carries it above, in the row of the P counts
          const narrow = e.w < 30 + 16;
          return (
            <g key={i}>
              {join}
              <g transform={`translate(0 ${(1 - t) * 14})`}>
                <ItemBar x={e.x} y={ROW_Y} size={h} unit={UNIT} color={color} opacity={t} chip={!narrow} />
              </g>
              {narrow && (
                <g opacity={t} fontFamily={FONT.sans}>
                  <rect x={e.x + e.w / 2 - 15} y={ROW_Y - 37} width={30} height={30} rx={5} fill={C.bgElev} stroke={C.ruleStrong} strokeWidth={1.5} />
                  <text x={e.x + e.w / 2} y={ROW_Y - 15} textAnchor="middle" fontWeight={650} fontSize={20} fill={C.fg}>
                    {h}
                  </text>
                </g>
              )}
              {e.kind === 'padding' && (
                <Label x={e.x + e.w / 2} y={ROW_Y + 84} size={22} opacity={clamp01(t * 2 - 1)}>
                  padding
                </Label>
              )}
            </g>
          );
        })}
        {/* the three linkers before the items: never drawn in the fold, but routed the same way */}
        {routedNote > 0 &&
          (() => {
            const ls = ROW.filter((e) => e.kind === 'linker').slice(0, 3);
            const l = ls[0].x;
            const r = ls[2].x + ls[2].w;
            const y = ROW_Y - 44;
            return (
              <g opacity={routedNote}>
                <path d={`M${l},${y + 8} L${l},${y} L${r},${y} L${r},${y + 8}`} fill="none" stroke={C.fgSubtle} strokeWidth={1.5} />
                <Label x={(l + r) / 2} y={y - 12} size={22}>
                  routed in front of the cube, like the three between the items
                </Label>
              </g>
            );
          })()}
        {/* the items, bracketed */}
        {(() => {
          const items = ROW.filter((e) => e.kind === 'item');
          const t = clamp01(rowT(ROW.length - 1) * 2 - 1);
          const l = items[0].x;
          const r = items[items.length - 1].x + items[items.length - 1].w;
          return (
            <g opacity={t}>
              <path d={`M${l},${ROW_Y + 62} L${l},${ROW_Y + 70} L${r},${ROW_Y + 70} L${r},${ROW_Y + 62}`} fill="none" stroke={C.fgSubtle} strokeWidth={1.5} />
              <Label x={(l + r) / 2} y={ROW_Y + 98} size={22}>
                one ribbon per item
              </Label>
            </g>
          );
        })()}
      </svg>
    </SceneFrame>
  );
}

function GroupLabel({ x, name, count, note, opacity }: { x: number; name: string; count: number; note?: string; opacity: number }) {
  if (opacity <= 0) return null;
  return (
    <g opacity={opacity} fontFamily={FONT.sans}>
      <text x={x} y={NAME_Y} textAnchor="middle" fontSize={26} fontWeight={600} fill={C.fg}>
        {name}
        <tspan fontWeight={500} fill={C.fgMuted}>{` · ${fmt(count)} H’s`}</tspan>
      </text>
      {note && (
        <text x={x} y={NAME_Y + 32} textAnchor="middle" fontSize={22} fill={C.fgMuted}>
          {note}
        </text>
      )}
    </g>
  );
}
