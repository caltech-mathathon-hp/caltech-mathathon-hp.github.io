/**
 * Scene "backward": a perfect fold gives a packing. The full front face, seen straight on; we read
 * the holes one after the other. In a hole, a bar of the bin-packing game is laid over each ribbon
 * in turn, cell by cell from the ribbon's first bead, and gets its size; then the hole's bars lift
 * off as a row and slide, as they are, into a bin of the puzzle (6 + 4 in bin 1, 2 + 8 in bin 2).
 * The ribbons stay in the holes: the fold is still perfect, we only read it.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { Scene3D } from '../three/Scene3D';
import { ItemBar, BinTrack, BinSum, trackWidth, TRACK_PAD } from '../ui/Bins';
import { ramp, sec } from '../lib/anim';
import { FONT, itemColor } from '../theme/theme';
import * as M from '../model/toy';
import type { SceneTime } from '../script';
import { drawRibbon, stripBox } from './lib/face';
import { faceShot, faceWithPaddings, faceGeom, holeCells, holeRow, barSpan, BoxLabel } from './lib/backwardFace';

/** for each bin: its items in order, with their first cell in the hole */
const ROWS = M.PACKING.map((items, s) => {
  let a = 0;
  return items.map((u) => {
    const r = { u, size: M.SIZES[u], first: a, cells: holeCells(s, a, M.SIZES[u]) };
    a += M.SIZES[u];
    return r;
  });
});

/** one hole after the other: when each starts (s after the cue), and its items' bars, one at a time */
const HOLE_AT = [1.2, 3.8];
const WIPE = 0.45;
const ITEM_GAP = 0.55;

export default function BackwardScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0] = scene.cueTimes;
  const t0 = c0.from;
  // the face moves left; the empty bins and the hole labels fade in
  const pan = ramp(f, 2, sec(1.2));
  const binsIn = ramp(f, sec(0.9), sec(0.6));
  // the frame steps back (by the shared context fade) so the two hole rows stand out
  const quietFrame = ramp(f, t0 + sec(0.5), sec(0.8));
  // per hole: a bar laid over each ribbon in turn (and its size), then the row lifts and slides into its bin
  const steps = [0, 1].map((s) => {
    const at = t0 + sec(HOLE_AT[s]);
    const items = ROWS[s].map((_, k) => {
      const w0 = at + sec(k * ITEM_GAP);
      return { wipe: ramp(f, w0, sec(WIPE)), chip: ramp(f, w0 + sec(WIPE), sec(0.25)) };
    });
    const read = at + sec((ROWS[s].length - 1) * ITEM_GAP + WIPE + 0.25);
    return {
      items,
      lift: ramp(f, read, sec(0.3)),
      slide: ramp(f, read + sec(0.15), sec(1.1)),
      full: ramp(f, read + sec(1.25), sec(0.3)),
    };
  });

  const shot = faceShot(pan);
  const d = faceWithPaddings(quietFrame);
  // the fold stays perfect: the ribbons never leave their holes (only copies go to the bins)
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
                const dx = (g.trackX + TRACK_PAD - g.barX(1)) * st.slide;
                const lift = st.lift * (1 - st.full);
                // the copy lifts off the ribbon (which stays on the face), then slides to the bin
                const rise = 14 * st.lift * (1 - st.slide) + 6 * lift;
                return row.map((it, k) => {
                  const { wipe, chip } = st.items[k];
                  if (wipe <= 0) return null;
                  return (
                    <ItemBar
                      key={`${s}-${it.u}`}
                      x={g.barX(1 + it.first) + dx}
                      y={g.holeY(s) - g.h / 2 - rise}
                      size={it.size}
                      color={itemColor(it.u)}
                      unit={g.u}
                      h={g.h}
                      lift={lift}
                      chipOpacity={chip}
                      span={barSpan(it.cells, it.size, wipe, true)}
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
