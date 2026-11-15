/**
 * Shared by the "backward" and "no" scenes: the front face seen straight on (FACE_SHOT), moved
 * left so the puzzle's bars fit beside it, and the screen geometry that lines a ribbon on the face
 * up with an item bar of the bin-packing game. On the face one lattice step is `u` px; the bars
 * use the same unit, so a ribbon of 6 H's and a bar of 6 units have the same length, cell by cell.
 */
import React from 'react';
import * as M from '../../model/toy';
import type { V3 } from '../../model/toy';
import { C, FONT } from '../../theme/theme';
import { FADE, type Project, type Shot } from '../../three/Scene3D';
import { FACE_SHOT } from '../../three/cube';
import { newDraw, drawFrame, drawWalls, drawPaddings, faceOutline, drawMark, quietFrom, type Draw } from './face';
import { BAR, TRACK_PAD } from '../../ui/Bins';

/** how far the face moves left (px) to make room for the bars on its right */
export const FACE_SHIFT = -297;
export const faceShot = (k = 1): Shot => ({ ...FACE_SHOT, offset: [FACE_SHIFT * k, 0] });

const N1 = M.n - 1;

/**
 * The front face with frame, walls and paddings in place, the rest of the cube hidden. Face-on the
 * frame is full orange (the hole outlines draw the eye to the holes). `quietFrame` (0..1) would
 * step the whole frame back by the shared FADE.context; no face-on step uses it.
 */
export function faceWithPaddings(quietFrame = 0): Draw {
  const d = newDraw();
  drawFrame(d, { backFade: 1, context: FADE.context * quietFrame });
  const walls = drawMark(d);
  drawWalls(d, 1);
  quietFrom(d, walls, FADE.context * quietFrame);
  drawPaddings(d, [1, 1]);
  d.lines.push(...faceOutline(0.6, 1));
  return d;
}

/** screen geometry of the face for one shot */
export function faceGeom(project: Project) {
  const o = project([0, 0, 0]);
  const u = project([1, 0, 0])[0] - o[0];
  const X = (c: number) => o[0] + c * u;
  /** screen y of the hole row of strip s */
  const holeY = (s: number) => project(M.strips[s].hole[0])[1];
  /** left x of a bar whose first cell is column c */
  const barX = (c: number) => X(c) - u / 2;
  /** the bins: same rows as the holes, to the right of the face */
  const trackX = X(N1) + u * 0.3 + 70;
  const h = BAR.h;
  const trackY = (s: number) => holeY(s) - h / 2 - TRACK_PAD;
  return { u, X, holeY, barX, trackX, trackY, h, left: X(0) - u * 0.3, right: X(N1) + u * 0.3 };
}
export type FaceGeom = ReturnType<typeof faceGeom>;

/** the hole cells of strip s, left to right; a ribbon on cells [a, a+k) starts on its even end */
export const holeCells = (s: number, a: number, k: number): V3[] => {
  const cells = M.strips[s].hole.slice(a, a + k);
  return M.isEven(cells[0]) ? cells : [...cells].reverse();
};

/** the face row (0 = top) of the hole of strip s */
export const holeRow = (s: number) => N1 - M.strips[s].hole[0][1];

/**
 * The part [a, b] (in units) of an item bar still showing while it turns into its ribbon: the bar
 * shrinks from the end where the ribbon starts (its first cell in string order), uncovering the
 * beads under it one by one, `w` (0..1) of the way. Reversed (`grow`), it grows over them instead.
 */
export function barSpan(cells: V3[], size: number, w: number, grow = false): [number, number] {
  const leftFirst = cells[0][0] <= cells[cells.length - 1][0];
  const done = size * Math.min(1, Math.max(0, w));
  if (grow) return leftFirst ? [0, done] : [size - done, size];
  return leftFirst ? [done, size] : [0, size - done];
}

/** frames an item bar of `size` cells takes to give way to its beads, or to grow over them: at least 12, 2.5 a cell */
export const wipeFrames = (size: number) => Math.max(12, Math.round(2.5 * size));
/** frames a bead takes to fade in as the bar uncovers it */
const BEAD_IN = 7;

/**
 * An item bar that has landed on its hole gives way to its beads, `t` frames after it starts: the
 * bar shrinks from the end where the ribbon starts, at a steady pace, and each bead fades in at
 * full size as the bar's edge reaches it (k = its place in the string). The bar stays at full
 * colour to the end (draw it with `sliverFade={false}`), so nothing pale sits over the beads.
 */
export function giveWay(cells: V3[], size: number, t: number) {
  const R = wipeFrames(size);
  const w = Math.min(1, Math.max(0, t / R));
  return {
    span: barSpan(cells, size, w),
    /** the bar has gone */
    gone: w >= 1,
    bead: (k: number) => Math.min(1, Math.max(0, (t - (R * (k - 0.5)) / size) / BEAD_IN)),
  };
}

/**
 * The label of a strip or a hole, the same in every face-on step: a grey box round its rows, and
 * left of the face a title with a grey line under it. The line leaves the title, runs through the
 * gap between two edge beads along the box's top edge and joins the box at its corner, so it ends
 * on the box and never on a bead.
 */
export function BoxLabel({ box, faceLeft, title, sub, opacity, boxOpacity = opacity }: { box: [number, number, number, number]; faceLeft: number; title: string; sub?: string; opacity: number; boxOpacity?: number }) {
  if (opacity <= 0 && boxOpacity <= 0) return null;
  // a little wider than the cells, so an item bar on the hole sits inside the box, clear of it
  const [x0, y0, x1, y1] = [box[0] - PADX, box[1], box[2] + PADX, box[3]];
  const tx = faceLeft - 30;
  return (
    <g fontFamily={FONT.sans}>
      {boxOpacity > 0 && <rect x={x0} y={y0} width={x1 - x0} height={y1 - y0} rx={RX} fill="none" stroke={C.fgMuted} strokeWidth={2.5} opacity={boxOpacity} />}
      {opacity > 0 && (
        <g opacity={opacity}>
          <line x1={tx + 8} x2={x0 + RX} y1={y0} y2={y0} stroke={C.fgMuted} strokeWidth={2} strokeLinecap="round" />
          <text x={tx} y={y0 + 10} textAnchor="end" fontSize={26} fontWeight={600} fill={C.fg}>
            {title}
          </text>
          {sub && (
            <text x={tx} y={y0 + 37} textAnchor="end" fontSize={22} fontWeight={500} fill={C.fgMuted}>
              {sub}
            </text>
          )}
        </g>
      )}
    </g>
  );
}
const RX = 10;
const PADX = 3;
