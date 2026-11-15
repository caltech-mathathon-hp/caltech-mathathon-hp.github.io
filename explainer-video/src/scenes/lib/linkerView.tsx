/**
 * The 3D view of the finished fold with its linkers, shared by "linkers" and "forward":
 * the camera shot, the full fold, and the labels (linker, switchboard, loop, 626 P's each).
 */
import React from 'react';
import { yaw, type Shot, type Project } from '../../three/Scene3D';
import { itemPieces } from '../../three/cube';
import { C, FONT } from '../../theme/theme';
import * as M from '../../model/toy';
import type { V3 } from '../../model/toy';
import { drawFrame, drawWalls, drawPaddings, drawRibbon, quietFrom, drawMark, type Draw } from './face';
import { LINKERS, BOX, BOX_FRONT } from './linkers';

/** from the front-left and above, so the face and the space in front of it both show */
export const LINK_DIR: V3 = [-0.74, 0.4, 0.54];
export const linkerShot = (yawDeg = 0): Shot => ({ target: [5.5, 5.6, 0.5], dir: yaw(LINK_DIR, yawDeg), dist: 70 });

const ITEMS = itemPieces().filter((p) => p.kind === 'item');

/** where the linkers meet the face: the first and last H of every ribbon they join */
export const LINKER_ENDS = new Set(LINKERS.flatMap((L) => [M.key(L.from), M.key(L.end)]));

/**
 * The finished fold: frame (core as a block), walls, paddings and the items of the packing, face
 * as dominoes. `context` quiets all of it (FADE.context when the linkers are the subject); the
 * ribbon ends the linkers attach to stay at `endFade` (default: as loud as the linkers).
 */
export function drawFullFold(d: Draw, opts: { itemFade?: number; backFade?: number; context?: number; endFade?: number } = {}) {
  const m = drawMark(d);
  drawFrame(d, { backFade: opts.backFade });
  drawWalls(d, 1);
  drawPaddings(d, [1, 1]);
  for (const it of ITEMS) {
    const cells = it.letters.filter((l) => l.h).map((l) => l.pos);
    drawRibbon(d, cells, it.color, 1, { fade: opts.itemFade });
  }
  const ctx = opts.context ?? 0;
  if (ctx > 0) {
    const ends = d.beads.slice(m.b).map((b, i) => (Math.abs(b.pos[2]) < 0.01 && LINKER_ENDS.has(M.key(b.pos)) ? i : -1)).filter((i) => i >= 0);
    const keep = ends.map((i) => d.beads[m.b + i]);
    quietFrom(d, m, ctx);
    const endFade = opts.endFade ?? 0;
    ends.forEach((i, k) => (d.beads[m.b + i] = { ...keep[k], fade: Math.max(keep[k].fade ?? 0, endFade) }));
  }
}

export interface LinkerLabelOpacity {
  /** "linker" on the first linker */
  linker?: number;
  /** "626 P's each" by the loops */
  each?: number;
  /** "switchboard" above the box */
  box?: number;
  /** "loop: the P's left over" at the highlighted linker's loop */
  loop?: number;
}

function Label({ at, dx, dy, text, opacity, color = C.fgMuted, weight = 400, size = 25, anchor = 'start' }: { at: [number, number]; dx: number; dy: number; text: string; opacity: number; color?: string; weight?: number; size?: number; anchor?: 'start' | 'end' | 'middle' }) {
  if (opacity <= 0) return null;
  const tx = at[0] + dx;
  const ty = at[1] + dy;
  const lx = anchor === 'end' ? tx + 8 : anchor === 'start' ? tx - 8 : tx;
  return (
    <g opacity={opacity}>
      <line x1={at[0]} y1={at[1]} x2={lx} y2={ty - 8} stroke={C.fgSubtle} strokeWidth={1.5} />
      <circle cx={at[0]} cy={at[1]} r={3} fill={C.fgSubtle} />
      <text x={tx} y={ty} textAnchor={anchor} fontFamily={FONT.sans} fontSize={size} fontWeight={weight} fill={color}>
        {text}
      </text>
    </g>
  );
}

export function LinkerLabels({ project, lab, highlight }: { project: Project; lab: LinkerLabelOpacity; highlight?: number }) {
  const first = LINKERS[0];
  const last = LINKERS[LINKERS.length - 1];
  const hiL = highlight !== undefined ? LINKERS[highlight] : undefined;
  const boxCorner = project(BOX_FRONT);
  return (
    <g>
      {(() => {
        // "linker" to the right of the first linker's last P before the switchboard, clear of the loops
        const at = project([first.from[0], first.from[1], 4]);
        const boxRight = project([BOX.x1, BOX.y1, BOX.z1])[0];
        return <Label at={at} dx={Math.max(110, boxRight - at[0] + 50)} dy={18} text="linker" opacity={lab.linker ?? 0} color={C.p} weight={600} size={27} />;
      })()}
      <Label at={project([last.tip[0] + 0.5, last.tip[1], last.tip[2]])} dx={70} dy={-40} text={`${M.TOY.linker} P’s each`} opacity={lab.each ?? 0} color={C.p} weight={600} size={26} />
      {(lab.box ?? 0) > 0 && (
        <g opacity={lab.box}>
          <text x={boxCorner[0] + 26} y={boxCorner[1] + 40} fontFamily={FONT.sans} fontSize={28} fontWeight={600} fill={C.p}>
            switchboard
          </text>
        </g>
      )}
      {hiL &&
        (() => {
          // above everything: the top of the picture is free
          const at = project(hiL.tip);
          return <Label at={at} dx={-30} dy={Math.min(-60, 215 - at[1])} text="loop: the P’s left over" opacity={lab.loop ?? 0} color={C.accent} anchor="end" />;
        })()}
    </g>
  );
}
