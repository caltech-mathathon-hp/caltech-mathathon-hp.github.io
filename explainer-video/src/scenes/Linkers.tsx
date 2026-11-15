/**
 * Scene "linkers", the cube seen from the side (lib/linkerBoard): its front face edge on, with the
 * two holes side by side on it, a few rows of the cube under it, the space in front of the cube
 * above. The four items come down from the face-on sketch of the step before, with their numbers
 * in the string.
 *
 * Cue 1: from the end of each ribbon, in string order, a linker of P's goes straight out of the
 * face, one after the other, all of one length; each is tagged with the number of the ribbon it
 * has to reach. Cue 2: the switchboard; the linkers, one after the other, go through it, out of its
 * far side at their own pair of gates, round a loop and back into the start of the next ribbon.
 * Where two routes cross, the one behind has a gap. One linker is followed. Cue 3: the bins
 * swapped: the wires and loops go, the two rows of items lift and change holes carrying their
 * stubs, and the same linkers are routed again (only the routes inside and the loops change). The
 * cube is still full of H's.
 *
 * Every cue is also a step of the page, paused at cue.to − 10: each cue's motion ends before that.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { SceneFrame } from '../ui/SceneFrame';
import { ramp, sec, lerp, clamp01 } from '../lib/anim';
import { W, H } from '../theme/theme';
import * as M from '../model/toy';
import type { SceneTime } from '../script';
import * as S from './lib/padding-sketch';
import { LinkerBoard, placement, swapHoles, itemPts, routesOf, routeFrames, badgeAt, HOLE_X, type Pt, type RouteDraw, type StraightLinker, type BoardItem } from './lib/linkerBoard';

const lin = (t: number) => clamp01(t);

/** the packing of the steps before, then the same bins in the other holes */
const PLACE_A = placement(M.PACKING);
const PLACE_B = swapHoles(PLACE_A);
const ROUTES_A = routesOf(PLACE_A);
const ROUTES_B = routesOf(PLACE_B);
/** the linker followed end to end: from the end of item 1 to the start of item 2 */
const HI = 0;
/**
 * cue 3: how far each hole's row moves, and the height of its arch: each row goes along one smooth
 * arch into the other hole (up, across, down, never stopping), hole 2's row high enough to pass over
 * hole 1's row and its stubs (at least 39 px clear at every moment)
 */
const SHIFT = HOLE_X[1] - HOLE_X[0];
const ARCH = [40, 330];
/** the arch: a cubic Bézier from (0, 0) via (0, −h) and (S, −h) to (S, 0) */
const arch = (s: number, S: number, h: number): Pt => [S * s * s * (3 - 2 * s), -3 * h * s * (1 - s)];
/** a gentle ease, for moves along a curve: its top speed is half that of the cubic in-out */
const sine = (t: number) => (1 - Math.cos(Math.PI * clamp01(t))) / 2;
/** routes laid one after the other at their natural pace, `gap` frames apart */
const schedule = (from: number, durs: number[], gap: number) => durs.map((_, k) => from + durs.slice(0, k).reduce((a, d) => a + d + gap, 0));
const DUR_A = ROUTES_A.map((r) => routeFrames(r, { fromStub: true }));
const DUR_B = ROUTES_B.map((r) => routeFrames(r, { fromStub: true, toStub: true }));

/** an item's cells as the face-on sketch of the step before draws them, in string order */
const sketchPts = (u: number): Pt[] => {
  const it = S.PLACED.find((p) => p.u === u)!;
  const lr = it.lr.map((c) => S.proj(c));
  const cells = PLACE_A[u].cells;
  const lo = Math.min(...cells);
  return cells.map((c) => [lr[c - lo][0], lr[c - lo][1]] as Pt);
};
/** an item's number as the step before draws it: over the middle of the item */
const sketchBadge = (u: number) => {
  const pts = sketchPts(u);
  const xs = pts.map((p) => p[0]);
  return { at: [(Math.min(...xs) + Math.max(...xs)) / 2, pts[0][1] - 0.66 * S.PITCH] as Pt, r: 14 };
};

export default function LinkersScene({ scene }: { scene: SceneTime }) {
  const f = useCurrentFrame();
  const [c0, c1, c2] = scene.cueTimes;
  const at = (c: { from: number }, s: number) => c.from + sec(s);

  // ---- cue 1: the items come down onto the face (once the scene has faded in); linkers straight
  // out, one after the other
  const morph = ramp(f, 10, sec(1.5));
  const outLab = ramp(f, at(c0, 1.4), sec(0.5));
  const STRAIGHT = sec(1.1);
  const straightAt = [0, 1, 2].map((k) => at(c0, 2.0 + 1.25 * k));
  const straightGrow = straightAt.map((t0) => ramp(f, t0, STRAIGHT, lin));
  const tagIn = straightAt.map((t0) => ramp(f, t0 + STRAIGHT, sec(0.3)));
  const linkerLab = ramp(f, straightAt[0] + STRAIGHT + sec(0.1), sec(0.4));
  const same = ramp(f, at(c0, 6.0), sec(0.5));

  // ---- cue 2: the switchboard; the linkers routed one after the other; one followed
  const cue1Out = 1 - ramp(f, c1.from, sec(0.3));
  const topOut = ramp(f, at(c1, 0.15), sec(0.35));
  const stubsOnly = f >= at(c1, 0.5);
  /** the switchboard steps back while the rows change holes through it (cue 3) */
  const box = ramp(f, at(c1, 0.6), sec(0.5)) * (1 - 0.7 * (ramp(f, at(c2, 0.8), sec(0.4)) - ramp(f, at(c2, 3.2), sec(0.4))));
  const boxLab = ramp(f, at(c1, 0.9), sec(0.5));
  const routeAt = schedule(at(c1, 1.5), DUR_A, 6);
  const routeGrow = routeAt.map((t0, k) => ramp(f, t0, DUR_A[k], lin));
  const routesDone = routeAt[2] + DUR_A[2];
  const cue2Out = 1 - ramp(f, c2.from, sec(0.3));
  const depthsA = ramp(f, routesDone + sec(0.2), sec(0.5)) * cue2Out;
  const hiOn = ramp(f, routesDone + sec(0.8), sec(0.6)) * (1 - ramp(f, c2.from, sec(0.4)));
  const sides = ramp(f, routesDone + sec(1.3), sec(0.5)) * cue2Out;
  const loop = ramp(f, routesDone + sec(1.9), sec(0.5)) * cue2Out;

  // ---- cue 3: the bins swapped; the rows change holes with their stubs; the same linkers rerouted
  const another = ramp(f, at(c2, 0.5), sec(0.5));
  const bodyOut = ramp(f, at(c2, 0.6), sec(0.4));
  const swap = ramp(f, at(c2, 1.2), sec(2.0), sine);
  const swapped = f >= at(c2, 3.3);
  const rerouteAt = schedule(at(c2, 3.5), DUR_B, 6);
  const reroute = rerouteAt.map((t0, k) => ramp(f, t0, DUR_B[k], lin));
  const reroutesDone = rerouteAt[2] + DUR_B[2];
  const depthsB = ramp(f, reroutesDone + sec(0.2), sec(0.5));
  const full = ramp(f, reroutesDone + sec(0.8), sec(0.5));

  /** where item u's row is carried in cue 3 (px) */
  const carry = (u: number): Pt => {
    if (f < c2.from) return [0, 0];
    const h = PLACE_A[u].hole;
    return arch(swap, (h === 0 ? 1 : -1) * SHIFT, ARCH[h]);
  };

  const items: BoardItem[] = PLACE_A.map((p) => {
    const to = itemPts(p);
    const d = carry(p.u);
    if (morph < 1) {
      // one smooth path, sideways first, then straight down onto its cells: an item never slides
      // sideways through the row, and the rows never meet (hole 1's stays above hole 2's)
      const from = sketchPts(p.u);
      const o0 = from[0];
      const o1 = to[0];
      const ref: Pt = [o0[0] + (o1[0] - o0[0]) * (1 - (1 - morph) ** 2), o0[1] + (o1[1] - o0[1]) * morph * morph];
      const rel = (a: Pt, oa: Pt, b: Pt, ob: Pt): Pt => [ref[0] + lerp(a[0] - oa[0], b[0] - ob[0], morph), ref[1] + lerp(a[1] - oa[1], b[1] - ob[1], morph)];
      const pts = to.map((q, i) => rel(from[i], o0, q, o1));
      const b0 = sketchBadge(p.u);
      const b1 = badgeAt(p.u, to);
      return { u: p.u, pts, badge: { at: rel(b0.at, o0, b1.at, o1), r: lerp(b0.r, b1.r, morph) } };
    }
    return { u: p.u, pts: to.map((q) => [q[0] + d[0], q[1] + d[1]] as Pt) };
  });

  const straight: StraightLinker[] = stubsOnly
    ? []
    : ROUTES_A.map((r, k) => ({ a: r.a, grow: straightGrow[k], frames: STRAIGHT, topOut, to: k + 1, tag: tagIn[k] * cue1Out }));

  let rs: RouteDraw[] = [];
  if (stubsOnly && !swapped)
    rs = ROUTES_A.map((r, k) => ({ r, grow: routeGrow[k], frames: DUR_A[k], fromStub: true, glow: k === HI ? hiOn : 0, bodyOut, da: carry(k), db: carry(k + 1) }));
  else if (swapped) rs = ROUTES_B.map((r, k) => ({ r, grow: reroute[k], frames: DUR_B[k], fromStub: true, toStub: true }));

  return (
    <SceneFrame scene={scene}>
      <svg width={W} height={H} viewBox={`0 0 ${W} ${H}`} style={{ position: 'absolute', inset: 0 }}>
        <LinkerBoard
          items={items}
          band={1}
          straight={straight}
          routes={rs}
          hi={ROUTES_A[HI]}
          box={box}
          lab={{
            face: 1,
            cube: 1,
            holes: 1,
            order: 1,
            out: outLab,
            full,
            linker: linkerLab * cue1Out,
            same: same * cue1Out,
            switchboard: boxLab,
            depths: swapped ? depthsB : depthsA,
            sides,
            loop,
            another,
          }}
        />
      </svg>
    </SceneFrame>
  );
}
