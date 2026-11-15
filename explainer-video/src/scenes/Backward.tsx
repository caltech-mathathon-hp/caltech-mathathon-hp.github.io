/**
 * Scene "backward": a perfect fold gives a packing. The full front face, seen straight on, its
 * frame full orange; we read the holes one after the other. In a hole, a bar of the bin-packing
 * game grows over each ribbon in turn, at a steady pace from the ribbon's first bead, and gets its
 * size; then the hole's bars, as a row, lift off and move in one smooth arc into a bin of the puzzle
 * (6 + 4 in bin 1, 2 + 8 in bin 2). The ribbons stay in the holes: the fold is still perfect, we
 * only read it.
 *
 * The cue is a step of the page, paused at cue.to − 10: everything ends before that.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D } from '../three/Scene3D';
import { ItemBar, BinTrack, BinSum, trackWidth, TRACK_PAD } from '../ui/Bins';
import { ramp, sec, clamp01 } from '../lib/anim';
import { FONT, itemColor } from '../theme/theme';
import * as M from '../model/toy';
import type { SceneTime } from '../script';
import { drawRibbon, stripBox } from './lib/face';
import { faceShot, faceWithPaddings, faceGeom, holeCells, holeRow, barSpan, wipeFrames, BoxLabel } from './lib/backwardFace';

/** for each bin: its items in order, with their first cell in the hole */
const ROWS = M.PACKING.map((items, s) => {
  let a = 0;
  return items.map((u) => {
    const r = { u, size: M.SIZES[u], first: a, cells: holeCells(s, a, M.SIZES[u]) };
    a += M.SIZES[u];
    return r;
  });
});

/** when the first hole is read (s after the cue); the second starts once the first hole's bars are in their bin */
const HOLE_AT = 1.2;
const HOLE_GAP = 0.2;
/** the size chip fades in after its bar is whole; the next bar starts after a short wait */
const CHIP = 0.25;
const NEXT = 0.15;
/** the row's move into its bin: one eased move, lifted in an arc on the way */
const MOVE = 1.1;
const lin = (t: number) => clamp01(t);

export default function BackwardScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0] = scene.cueTimes;
  const t0 = c0.from;
  // the face moves left; the empty bins and the hole labels fade in
  const pan = ramp(f, 2, sec(1.2));
  const binsIn = ramp(f, sec(0.9), sec(0.6));
  // per hole: a bar grows over each ribbon in turn (then its size), then the row moves into its bin
  let at = t0 + sec(HOLE_AT);
  const steps = [0, 1].map((s) => {
    let w0 = at;
    let read = at;
    const items = ROWS[s].map((it) => {
      const R = wipeFrames(it.size);
      const r = { wipe: ramp(f, w0, R, lin), chip: ramp(f, w0 + R, sec(CHIP)) };
      read = w0 + R + sec(CHIP);
      w0 = read + sec(NEXT);
      return r;
    });
    const move = ramp(f, read, sec(MOVE));
    at = read + sec(MOVE + HOLE_GAP);
    return { items, move, lift: Math.sin(Math.PI * move), full: ramp(f, read + sec(MOVE), sec(0.3)) };
  });

  const shot = faceShot(pan);
  // face-on, the frame is full orange; the hole outlines draw the eye to the holes
  const d = faceWithPaddings(0);
  // the fold stays perfect: the ribbons never leave their holes (only the bars go to the bins)
  for (const row of ROWS) for (const it of row) drawRibbon(d, it.cells, itemColor(it.u), 1);

  return (
    <SceneFrame scene={scene}>
      <Scene3D shot={shot} beads={d.beads} sticks={d.sticks} lines={d.lines}>
        {(project) => {
          const g = faceGeom(project);
          const faceLeft = project([-0.5, 0, 0])[0];
          return (
            <g fontFamily={FONT.sans}>
              {[0, 1].map((s) => (
                <BoxLabel key={`h${s}`} box={stripBox(project, s, 0.5, [holeRow(s)])} faceLeft={faceLeft} title={`hole ${s + 1}`} sub={`${M.B} nodes`} opacity={binsIn} />
              ))}
              {[0, 1].map((s) => (
                <BinTrack key={`t${s}`} x={g.trackX} y={g.trackY(s)} B={M.B} unit={g.u} h={g.h} opacity={binsIn} label={`bin ${s + 1}`} full={steps[s].full} />
              ))}
              {ROWS.map((row, s) => (
                <BinSum key={`sum${s}`} x={g.trackX + trackWidth(M.B, g.u) + 26} y={g.holeY(s) + 9} items={row} B={M.B} opacity={steps[s].full} />
              ))}
              {ROWS.map((row, s) => {
                const st = steps[s];
                const dx = (g.trackX + TRACK_PAD - g.barX(1)) * st.move;
                return row.map((it, k) => {
                  const { wipe, chip } = st.items[k];
                  if (wipe <= 0) return null;
                  return (
                    <ItemBar
                      key={`${s}-${it.u}`}
                      x={g.barX(1 + it.first) + dx}
                      y={g.holeY(s) - g.h / 2 - 14 * st.lift}
                      size={it.size}
                      color={itemColor(it.u)}
                      unit={g.u}
                      h={g.h}
                      lift={st.lift}
                      chipOpacity={chip}
                      span={barSpan(it.cells, it.size, wipe, true)}
                      sliverFade={false}
                    />
                  );
                });
              })}
            </g>
          );
        }}
      </Scene3D>
    </SceneFrame>
  );
}
