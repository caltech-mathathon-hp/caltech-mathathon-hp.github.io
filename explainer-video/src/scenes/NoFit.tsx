/**
 * Scene "no": items 6, 6, 6, 2 and bins of 10 have no packing, so the string has no perfect fold.
 * The face of the example with its paddings and two empty holes; the items wait on the right as
 * the bin-packing game's bars, in a column in string order, and go into the holes one at a time:
 * along a free lane beside the face to their hole's row, then along the row. Each lands on its
 * hole and shrinks cell by cell to uncover its ribbon, and the items still waiting close up.
 * The third 6 finds only 4 free nodes, sticks out past the edge, turns red and goes back: no
 * place. The 2 goes in after it. Then the nodes left empty get dashed red rings and are counted;
 * the hole labels step aside, red dashes from their H neighbours show the contacts lost (the look
 * of the first part), and the 6 with no place is said to fold in front of the cube.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D } from '../three/Scene3D';
import { R_RES } from '../three/cube';
import { ItemBar } from '../ui/Bins';
import { ramp, sec, clamp01, lerp, easeBack, easeOut, easeInOut } from '../lib/anim';
import { C, FONT, itemColor } from '../theme/theme';
import * as M from '../model/toy';
import type { V3 } from '../model/toy';
import type { SceneTime } from '../script';
import { drawRibbon, addHoles, stripBox } from './lib/face';
import { faceShot, faceWithPaddings, faceGeom, holeCells, holeRow, barSpan, BoxLabel, type FaceGeom } from './lib/backwardFace';

const SIZES = M.NO_SIZES; // 6, 6, 6, 2
/** all three 6's in the first item colour, the 2 in the second, as the caption colours them */
const colorOf = (u: number) => itemColor(SIZES[u] === 6 ? 0 : 1);
const N1 = M.n - 1;

/** the flight from the tray to a hole, and the bar shrinking off its ribbon once it has landed */
const FLY = 1.1;
const CHIP = 0.2;
const REVEAL = 0.45;
/** the items that find a place, in string order: hole (strip), first free cell, start (s after the cue) */
const PLACED: { u: number; s: number; a: number; at: number }[] = [
  { u: 0, s: 0, a: 0, at: 0.8 },
  { u: 1, s: 1, a: 0, at: 2.0 },
  { u: 3, s: 0, a: 6, at: 6.1 },
];
/** the third 6, between them in string order: to hole 2, where only 4 nodes are free, and back */
const FAIL = { u: 2, s: 1, a: 6, at: 3.2 };
const FAIL_WAIT = 0.75;
const FAIL_BACK = 1.0;
/** the column closing up: once an item has left it, the ones under it move up a place */
const CLOSE = [1.25, 2.45];

/**
 * The items waiting, right of the face: one column, in string order from the top (6, 6, 6, 2), as
 * the caption lists them. Between it and the face runs a free lane, where the items go up or down
 * to their hole's row. As items leave, the rest close up: slot k before and after each close-up.
 */
const SLOTS: Record<number, number[]> = { 0: [0], 1: [1, 0], 2: [2, 1, 0], 3: [3, 2, 1] };
const PITCH = 52;
const colX = (g: FaceGeom) => g.trackX + 6 * g.u + 40;
const slotPos = (g: FaceGeom, k: number): [number, number] => {
  const midY = (g.holeY(0) + g.holeY(1)) / 2;
  return [colX(g), midY + (k - 1.5) * PITCH - g.h / 2];
};
/** where item u waits, given how far each close-up is */
const trayPos = (g: FaceGeom, u: number, close: number[]): [number, number] => {
  const s = SLOTS[u];
  let [x, y] = slotPos(g, s[0]);
  for (let i = 1; i < s.length; i++) {
    const [x1, y1] = slotPos(g, s[i]);
    x = lerp(x, x1, close[i - 1]);
    y = lerp(y, y1, close[i - 1]);
  }
  return [x, y];
};
/**
 * A flight, t from 0 to 1 (linear): left out of the column into the lane, up or down the lane to
 * the hole's row, then left along the row into the hole, as the items go into the holes in step
 * 35. The three legs overlap a little, so the corners are round; the bar never passes over a bead
 * of the face or over a waiting item. Returns the bar's top-left corner and how lifted it is.
 */
const LEGS: [number, number][] = [
  [0, 0.38],
  [0.3, 0.68],
  [0.6, 1],
];
const leg = (t: number, [a, b]: [number, number]) => easeInOut(clamp01((t - a) / (b - a)));
const flight = (g: FaceGeom, [x0, y0]: [number, number], [x1, y1]: [number, number], t: number): [number, number, number] => {
  const lane = g.trackX;
  const lift = Math.sin(Math.PI * clamp01(t));
  return [x0 + (lane - x0) * leg(t, LEGS[0]) + (x1 - lane) * leg(t, LEGS[2]), lerp(y0, y1, leg(t, LEGS[1])) - 14 * lift, lift];
};
const holePos = (g: FaceGeom, s: number, a: number): [number, number] => [g.barX(1 + a), g.holeY(s) - g.h / 2];

/** the empty nodes once the three items are in: hole 1 from cell 8, hole 2 from cell 6 */
const EMPTY: V3[] = [...M.strips[0].hole.slice(8), ...M.strips[1].hole.slice(6)];
const isEmpty = (p: V3) => EMPTY.some((q) => q[0] === p[0] && q[1] === p[1] && q[2] === p[2]);
/**
 * The contacts the empty nodes cost: from each empty node to each of its H neighbours on the face
 * (every other node of the face holds an H). Their neighbours behind the face are hidden face-on.
 */
const LOST: { h: V3; e: V3 }[] = EMPTY.flatMap((e) =>
  (
    [
      [1, 0],
      [-1, 0],
      [0, 1],
      [0, -1],
    ] as const
  )
    .map(([dx, dy]): V3 => [e[0] + dx, e[1] + dy, 0])
    .filter((h) => h[0] >= 0 && h[0] <= N1 && h[1] >= 0 && h[1] <= N1 && !isEmpty(h))
    .map((h) => ({ h, e })),
);

export default function NoFitScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1] = scene.cueTimes;
  const t0 = c0.from;
  const at = (s: number) => t0 + sec(s);

  // each placed item: flies, lands, its chip fades, then the bar shrinks off the ribbon
  const placed = PLACED.map((p) => ({
    ...p,
    go: ramp(f, at(p.at), sec(FLY), clamp01),
    landed: f >= at(p.at + FLY),
    chip: 1 - ramp(f, at(p.at + FLY), sec(CHIP)),
    reveal: ramp(f, at(p.at + FLY + CHIP), sec(REVEAL)),
    cells: holeCells(p.s, p.a, SIZES[p.u]),
  }));
  const close = CLOSE.map((s) => ramp(f, at(s), sec(0.6)));

  const shot = faceShot(1);
  const d = faceWithPaddings(1);
  // a ribbon is there, whole, from the moment its bar lands: the bar hides it, then uncovers it
  for (const p of placed) if (p.landed) drawRibbon(d, p.cells, colorOf(p.u), 1);
  addHoles(d, { opacity: 0.9, free: 0 });

  // the failed attempt
  const failGo = ramp(f, at(FAIL.at), sec(FLY), clamp01);
  const failRed = ramp(f, at(FAIL.at + FLY), sec(0.35));
  const failBack = ramp(f, at(FAIL.at + FLY + FAIL_WAIT), sec(FAIL_BACK), clamp01);
  // "only 4 nodes free" stays under the hole until the 6 is back in the column
  const freeOut = ramp(f, at(FAIL.at + FLY + FAIL_WAIT + FAIL_BACK - 0.2), sec(0.3));
  // once the 2 has left the tray, the 6 still in it is named: "no place"
  const itemsOut = ramp(f, at(PLACED[2].at + 0.15), sec(0.3));
  const leftIn = ramp(f, at(PLACED[2].at + 0.5), sec(0.35));
  // cue 2: the rings and the counter, then the contacts lost, then where the left-over 6 goes
  const ringP = (i: number) => clamp01((f - (c1.from + sec(0.5) + i * sec(0.3))) / sec(0.35));
  const rings = EMPTY.map((_, i) => ringP(i));
  const count = rings.filter((r) => r > 0.5).length;
  const counterIn = ramp(f, c1.from + sec(0.6), sec(0.3));
  // the hole labels step aside first: the dashes cross where the hole boxes run
  const holesOut = ramp(f, c1.from + sec(2.1), sec(0.35));
  const stubs = ramp(f, c1.from + sec(2.6), sec(0.6));
  const lostIn = ramp(f, c1.from + sec(3.0), sec(0.4));
  const outside = ramp(f, c1.from + sec(4.0), sec(0.4));

  return (
    <SceneFrame scene={scene}>
      <Scene3D shot={shot} beads={d.beads} sticks={d.sticks} lines={d.lines}>
        {(project) => {
          const g = faceGeom(project);
          const faceLeft = project([-0.5, 0, 0])[0];
          // the two label styles of the picture: a name, and a sub-line under it
          const lab = { fontSize: 26, fontWeight: 600 } as const;
          const sub = { fontSize: 22, fontWeight: 500, fill: C.fgMuted } as const;
          const bead = R_RES * g.u;
          const bars: React.ReactNode[] = [];
          // the items still waiting (in the tray, closing up), then flying, landing, uncovering
          for (const p of placed) {
            const show = ramp(f, t0 + sec(0.1 + p.u * 0.18), sec(0.35), easeOut);
            if (p.reveal >= 1) continue;
            const [x, y, arc] = flight(g, trayPos(g, p.u, close), holePos(g, p.s, p.a), p.go);
            bars.push(
              <ItemBar
                key={p.u}
                x={x}
                y={y}
                size={SIZES[p.u]}
                color={colorOf(p.u)}
                unit={g.u}
                h={g.h}
                opacity={show}
                lift={arc}
                chipOpacity={p.chip}
                span={barSpan(p.cells, SIZES[p.u], p.reveal)}
              />,
            );
          }
          const [tx, ty] = trayPos(g, FAIL.u, close);
          {
            const show = ramp(f, t0 + sec(0.1 + FAIL.u * 0.18), sec(0.35), easeOut);
            const [x1, y1] = holePos(g, FAIL.s, FAIL.a);
            // back the same way it came
            const [x, y, arc] = flight(g, [tx, ty], [x1, y1], failBack > 0 ? 1 - failBack : failGo);
            const since = f - at(FAIL.at + FLY);
            const shake = since > 0 && since < sec(0.6) ? 7 * Math.sin(since * 1.1) * (1 - since / sec(0.6)) : 0;
            bars.push(
              <ItemBar key="fail" x={x + shake} y={y} size={6} color={colorOf(FAIL.u)} unit={g.u} h={g.h} opacity={show} lift={Math.max(arc, failRed * (1 - failBack))} stroke={C.invalid} strokeOpacity={failRed} />,
            );
            bars.push(
              <text key="free" x={g.right + 40} y={y1 + g.h + 36} {...lab} fill={C.invalid} opacity={failRed * (1 - freeOut)}>
                only 4 nodes free
              </text>,
            );
            bars.push(
              <text key="np" x={tx + 2} y={ty + g.h + 34} {...lab} fill={C.invalid} opacity={leftIn}>
                no place
              </text>,
              <text key="out" x={tx + 2} y={ty + g.h + 62} {...sub} opacity={outside}>
                it folds in front of the cube
              </text>,
            );
          }
          const [ix, iy] = slotPos(g, 0);
          const itemsIn = ramp(f, t0, sec(0.4));
          // the empty nodes: a dashed red ring the size of a bead round each (as in the first part)
          const ringEls = EMPTY.map((p, i) => {
            const r = rings[i];
            if (r <= 0) return null;
            const [x, y] = project(p);
            return <circle key={i} cx={x} cy={y} r={bead * (0.6 + 0.4 * easeBack(r))} fill="none" stroke={C.invalid} strokeWidth={3.5} strokeDasharray="7 5" opacity={r} />;
          });
          // the contacts lost: a short red dash from each H neighbour's edge to the empty node's ring
          const stubEls =
            stubs > 0
              ? LOST.map(({ h, e }, i) => {
                  const [hx, hy] = project(h);
                  const [ex, ey] = project(e);
                  const a = 0.37;
                  const b = a + (0.63 - a) * stubs;
                  return <line key={`l${i}`} x1={lerp(hx, ex, a)} y1={lerp(hy, ey, a)} x2={lerp(hx, ex, b)} y2={lerp(hy, ey, b)} stroke={C.invalid} strokeWidth={3.5} strokeDasharray="5 4" />;
                })
              : null;
          const cy = g.holeY(1) + 72;
          return (
            <g fontFamily={FONT.sans}>
              <text x={ix + 2} y={iy - 18} {...sub} opacity={itemsIn * (1 - itemsOut)}>
                items
              </text>
              {[0, 1].map((s) => (
                <BoxLabel key={`h${s}`} box={stripBox(project, s, 0.5, [holeRow(s)])} faceLeft={faceLeft} title={`hole ${s + 1}`} sub={`${M.B} nodes`} opacity={1 - holesOut} />
              ))}
              {bars}
              {stubEls}
              {ringEls}
              <g opacity={counterIn}>
                <circle cx={g.trackX + 16} cy={cy - 8} r={bead} fill="none" stroke={C.invalid} strokeWidth={3.5} strokeDasharray="7 5" />
                <text x={g.trackX + 44} y={cy} {...lab} fill={C.invalid} style={{ fontVariantNumeric: 'tabular-nums' }}>
                  {count} {count === 1 ? 'node' : 'nodes'} empty
                </text>
              </g>
              <g opacity={lostIn}>
                <line x1={g.trackX + 2} x2={g.trackX + 30} y1={cy + 34} y2={cy + 34} stroke={C.invalid} strokeWidth={3.5} strokeDasharray="5 4" />
                <text x={g.trackX + 44} y={cy + 42} {...lab} fill={C.invalid}>
                  contacts lost
                </text>
              </g>
            </g>
          );
        }}
      </Scene3D>
    </SceneFrame>
  );
}
