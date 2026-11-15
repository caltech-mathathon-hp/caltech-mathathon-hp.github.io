/** @jsxImportSource preact */
/**
 * Svg2D: the renderer for 2D lattices (square, triangular, hexagonal, any lattice with dim 2).
 * Draws the lattice points around the fold (and, on the hexagonal lattice, its edges), the
 * backbone, the letters (H filled, P hollow), the H–H contacts (dashed), the last letter, and
 * the legal next positions (ghosts).
 *
 * Input: click or tap a ghost to place the next letter; press on a ghost or on the last
 * letter and drag to draw several steps; drag back onto the previous letter to undo.
 * ⌘-click / Ctrl-click a placed letter to go back to it (touch: tap it twice); holding the
 * modifier over a letter previews what goes (controller.cut). With `showKeys`, the legal next
 * positions carry the key that places a letter there.
 * The view fits the fold and glides when the fold leaves it (or becomes much smaller).
 * Styles: .fg-svg… in ../styles.css (colours from tokens.css, so dark mode is automatic).
 */
import { useEffect, useLayoutEffect, useMemo, useRef, useState } from 'preact/hooks';
import { residueRange, type RendererProps } from './types.ts';
import { type Lattice, neighbours, stepIndex } from '../engine/lattice.ts';
import { stepGlyph } from '../keys.ts';

type Pt = [number, number];
interface View {
  x: number;
  y: number;
  w: number;
  h: number;
}

/** letter radius, in lattice units (neighbours are 1 apart) */
const R = 0.27;
/** largest zoom, in pixels per lattice unit (short chains would otherwise look bloated) */
const MAX_PX = 58;
/** empty margin around the content, in lattice units */
const PAD = 1.05;
/** pointer distance (lattice units) within which a lattice point counts as hit */
const HIT = 0.44;

/** lattice → drawing coordinates (SVG y grows downwards, the lattice's y upwards) */
function drawer(l: Lattice) {
  return (v: readonly number[]): Pt => {
    const [x, y] = l.embed(v);
    return [x, -y];
  };
}

/**
 * The linear part of a 2D embedding and its inverse, for hit tests and dot grids. The hexagonal
 * lattice's embedding is linear up to an offset that repeats every two steps, so the basis is
 * taken over two steps; the inverse is then within a node of the truth, and callers search
 * around it.
 */
function basis(l: Lattice) {
  const e00 = l.embed([0, 0]);
  const e10 = l.embed([1, 0]);
  const a = [(l.embed([2, 0])[0] - e00[0]) / 2, (l.embed([2, 0])[1] - e00[1]) / 2];
  const b = [(l.embed([0, 2])[0] - e00[0]) / 2, (l.embed([0, 2])[1] - e00[1]) / 2];
  const o = [(e00[0] + e10[0] - a[0]) / 2, (e00[1] + e10[1] - a[1]) / 2];
  const m = [a[0], b[0], a[1], b[1]]; // [[m0 m1],[m2 m3]]
  const det = m[0] * m[3] - m[1] * m[2];
  /** drawing point → fractional lattice coordinates */
  const toLattice = (p: Pt): Pt => {
    const ex = p[0] - o[0];
    const ey = -p[1] - o[1];
    return [(m[3] * ex - m[1] * ey) / det, (-m[2] * ex + m[0] * ey) / det];
  };
  return { toLattice };
}

function contentBox(pts: Pt[]) {
  let x0 = Infinity,
    y0 = Infinity,
    x1 = -Infinity,
    y1 = -Infinity;
  for (const [x, y] of pts) {
    if (x < x0) x0 = x;
    if (x > x1) x1 = x;
    if (y < y0) y0 = y;
    if (y > y1) y1 = y;
  }
  if (!pts.length) return { x0: -1, y0: -1, x1: 1, y1: 1 };
  return { x0, y0, x1, y1 };
}

function fit(pts: Pt[], W: number, H: number, minSpan: number): View {
  const b = contentBox(pts);
  const bw = Math.max(b.x1 - b.x0 + 2 * PAD, minSpan);
  const bh = Math.max(b.y1 - b.y0 + 2 * PAD, minSpan);
  const scale = Math.min(W / bw, H / bh, MAX_PX);
  const w = W / scale;
  const h = H / scale;
  return { x: (b.x0 + b.x1) / 2 - w / 2, y: (b.y0 + b.y1) / 2 - h / 2, w, h };
}

/** is the content (with a small margin) inside v, and v not far too zoomed out for it? */
function stillGood(v: View, pts: Pt[], target: View): boolean {
  const b = contentBox(pts);
  const m = 0.6;
  const inside = b.x0 - m >= v.x && b.x1 + m <= v.x + v.w && b.y0 - m >= v.y && b.y1 + m <= v.y + v.h;
  return inside && v.w <= target.w * 1.45 + 1e-9;
}

const sameView = (a: View, b: View) =>
  Math.abs(a.x - b.x) < 1e-6 && Math.abs(a.y - b.y) < 1e-6 && Math.abs(a.w - b.w) < 1e-6 && Math.abs(a.h - b.h) < 1e-6;

const vb = (v: View) => `${v.x.toFixed(4)} ${v.y.toFixed(4)} ${v.w.toFixed(4)} ${v.h.toFixed(4)}`;

const reducedMotion = () =>
  typeof matchMedia !== 'undefined' && matchMedia('(prefers-reduced-motion: reduce)').matches;

export default function Svg2D(props: RendererProps) {
  const { controller: c, interactive, showLattice, showContacts, showIndices, height, frame, showKeys } = props;
  const mod = props.modKey ?? 'Ctrl';
  const lattice = c.lattice;
  const fold = c.fold;
  const seq = c.seq;
  const draw = useMemo(() => drawer(lattice), [lattice]);
  const { toLattice } = useMemo(() => basis(lattice), [lattice]);

  const wrapRef = useRef<HTMLDivElement>(null);
  const svgRef = useRef<SVGSVGElement>(null);
  const [size, setSize] = useState<{ W: number; H: number }>({ W: 640, H: 420 });
  const [ghost, setGhost] = useState<string | null>(null);
  /** the view on screen (changes every animation frame) and the view it is heading to */
  const viewRef = useRef<View | null>(null);
  const goalRef = useRef<View | null>(null);
  const sizeRef = useRef(size);
  const anim = useRef(0);
  const drag = useRef<number | null>(null);
  /** placed letter under the mouse (for the modifier preview), and whether the last input was touch */
  const overRes = useRef<number | null>(null);
  const [touchSel, setTouchSel] = useState(false);

  // ---------- size ----------
  useLayoutEffect(() => {
    const el = wrapRef.current;
    if (!el) return;
    const measure = () => {
      const r = el.getBoundingClientRect();
      if (r.width > 0 && r.height > 0) setSize({ W: r.width, H: r.height });
    };
    measure();
    const ro = new ResizeObserver(measure);
    ro.observe(el);
    return () => ro.disconnect();
  }, []);

  // ---------- geometry of this frame ----------
  const pts = fold.path.map(draw);
  const options = interactive && !fold.complete ? c.options() : [];
  const optPts = options.map(draw);
  const n = seq.length;
  const minSpan = Math.min(14, Math.max(4.6, Math.sqrt(n) + 2.6));

  const focusPts = frame && frame.length ? frame.map(draw) : [...pts, ...optPts];
  const fresh = fit(focusPts, size.W, size.H, minSpan);
  // keep the current goal while the content still fits it well (no needless camera moves)
  const goal = goalRef.current;
  const resized = sizeRef.current.W !== size.W || sizeRef.current.H !== size.H;
  // keep the camera still while folding; centre the finished fold
  const settled = fold.complete || (interactive && options.length === 0);
  const target = goal && !resized && !frame && !settled && stillGood(goal, focusPts, fresh) ? goal : fresh;
  if (!viewRef.current) viewRef.current = goalRef.current = target;
  const shown = viewRef.current;

  // glide to the target view
  useLayoutEffect(() => {
    sizeRef.current = size;
    const svg = svgRef.current;
    const from = viewRef.current;
    if (!svg || !from || (goalRef.current && sameView(goalRef.current, target))) return;
    goalRef.current = target;
    cancelAnimationFrame(anim.current);
    if (resized || reducedMotion()) {
      viewRef.current = target;
      svg.setAttribute('viewBox', vb(target));
      return;
    }
    const t0 = performance.now();
    const dur = 320;
    const step = (now: number) => {
      const t = Math.min(1, (now - t0) / dur);
      const e = 1 - Math.pow(1 - t, 3);
      const v: View = {
        x: from.x + (target.x - from.x) * e,
        y: from.y + (target.y - from.y) * e,
        w: from.w + (target.w - from.w) * e,
        h: from.h + (target.h - from.h) * e,
      };
      viewRef.current = v;
      svg.setAttribute('viewBox', vb(v));
      if (t < 1) anim.current = requestAnimationFrame(step);
    };
    anim.current = requestAnimationFrame(step);
  });
  useEffect(() => () => cancelAnimationFrame(anim.current), []);

  // ---------- lattice dots covering the shown and the target view ----------
  const dotView: View = {
    x: Math.min(shown.x, target.x) - 0.5,
    y: Math.min(shown.y, target.y) - 0.5,
    w: Math.max(shown.x + shown.w, target.x + target.w) - Math.min(shown.x, target.x) + 1,
    h: Math.max(shown.y + shown.h, target.y + target.h) - Math.min(shown.y, target.y) + 1,
  };
  const dots = useMemo(() => {
    if (!showLattice || dotView.w * dotView.h > 6000) return { dots: [], edges: [] };
    const corners: Pt[] = [
      [dotView.x, dotView.y],
      [dotView.x + dotView.w, dotView.y],
      [dotView.x, dotView.y + dotView.h],
      [dotView.x + dotView.w, dotView.y + dotView.h],
    ].map((p) => toLattice(p as Pt));
    const a0 = Math.floor(Math.min(...corners.map((p) => p[0]))) - 1;
    const a1 = Math.ceil(Math.max(...corners.map((p) => p[0]))) + 1;
    const b0 = Math.floor(Math.min(...corners.map((p) => p[1]))) - 1;
    const b1 = Math.ceil(Math.max(...corners.map((p) => p[1]))) + 1;
    const inView = (p: Pt) => p[0] >= dotView.x && p[0] <= dotView.x + dotView.w && p[1] >= dotView.y && p[1] <= dotView.y + dotView.h;
    const out: Pt[] = [];
    // the hexagonal lattice's dots alone do not show which nodes are neighbours: draw its edges
    const edges: [Pt, Pt][] = [];
    for (let a = a0; a <= a1; a++)
      for (let b = b0; b <= b1; b++) {
        const p = draw([a, b]);
        if (inView(p)) out.push(p);
        if (lattice.stepsAt && (a + b) % 2 === 0)
          for (const w of neighbours(lattice, [a, b])) {
            const q = draw(w);
            if (inView(p) || inView(q)) edges.push([p, q]);
          }
      }
    return { dots: out, edges };
  }, [showLattice, lattice, vb(dotView)]);

  // ---------- pointer input ----------
  const pointerPt = (e: PointerEvent): Pt | null => {
    const svg = svgRef.current;
    const v = viewRef.current;
    if (!svg || !v) return null;
    const r = svg.getBoundingClientRect();
    return [v.x + ((e.clientX - r.left) / r.width) * v.w, v.y + ((e.clientY - r.top) / r.height) * v.h];
  };
  /** nearest lattice point to a drawing point, and its distance */
  const nearest = (p: Pt): { v: number[]; d: number } => {
    const [fa, fb] = toLattice(p);
    let best: { v: number[]; d: number } = { v: [Math.round(fa), Math.round(fb)], d: Infinity };
    const near = (f: number) => [Math.floor(f) - 1, Math.floor(f), Math.ceil(f), Math.ceil(f) + 1];
    for (const a of near(fa))
      for (const b of near(fb)) {
        const q = draw([a, b]);
        const d = Math.hypot(q[0] - p[0], q[1] - p[1]);
        if (d < best.d) best = { v: [a, b], d };
      }
    return best;
  };
  const isOption = (v: number[]) => c.options().some((o) => o[0] === v[0] && o[1] === v[1]);
  const isAt = (v: number[], w: readonly number[] | undefined) => !!w && v[0] === w[0] && v[1] === w[1];

  const onPointerDown = (e: PointerEvent) => {
    const p = pointerPt(e);
    if (!p) return;
    const { v, d } = nearest(p);
    const touch = e.pointerType !== 'mouse';
    setTouchSel(touch);
    const i = d <= HIT ? c.fold.at(v) : undefined;
    if (!interactive) {
      c.setHover(i === undefined || c.hover === i ? null : i);
      return;
    }
    if (d > HIT) {
      if (touch) c.setHover(null);
      return;
    }
    const placed = c.fold.placed;
    if (i !== undefined && i < placed - 1) {
      // go back to letter i: modifier-click, or a second tap on a selected letter
      if (e.ctrlKey || e.metaKey || (touch && c.hover === i)) {
        e.preventDefault();
        c.truncate(i + 1);
        if (touch) c.setHover(null);
        return;
      }
      // a tap on a placed letter selects it (touch has no hover)
      if (touch) c.setHover(i);
      return;
    }
    if (isOption(v)) {
      c.extendTo(v);
      setGhost(null);
    } else if (!isAt(v, c.fold.last)) return;
    drag.current = e.pointerId;
    (e.currentTarget as Element).setPointerCapture?.(e.pointerId);
    e.preventDefault();
  };

  /** the modifier preview follows the key as well as the pointer */
  const setPreview = (i: number | null, modDown: boolean) => {
    overRes.current = i;
    c.setCut(interactive && modDown && i !== null ? i : null);
  };
  useEffect(() => {
    if (!interactive) return;
    const onKey = (e: KeyboardEvent) => {
      if (e.key !== 'Meta' && e.key !== 'Control') return;
      if (overRes.current !== null) c.setCut(e.type === 'keydown' ? overRes.current : null);
    };
    const onBlur = () => c.setCut(null);
    window.addEventListener('keydown', onKey);
    window.addEventListener('keyup', onKey);
    window.addEventListener('blur', onBlur);
    return () => {
      window.removeEventListener('keydown', onKey);
      window.removeEventListener('keyup', onKey);
      window.removeEventListener('blur', onBlur);
    };
  }, [c, interactive]);

  const onPointerMove = (e: PointerEvent) => {
    const p = pointerPt(e);
    if (!p) return;
    const { v, d } = nearest(p);
    if (drag.current !== null) {
      if (d > HIT - 0.08) return;
      const path = c.fold.path;
      if (isOption(v)) c.extendTo(v);
      else if (path.length >= 2 && isAt(v, path[path.length - 2])) c.undo();
      return;
    }
    if (e.pointerType !== 'mouse') return;
    if (touchSel) setTouchSel(false);
    if (d <= HIT) {
      const i = c.fold.at(v);
      c.setHover(i ?? null);
      setPreview(i ?? null, e.ctrlKey || e.metaKey);
      setGhost(i === undefined && interactive && isOption(v) ? v.join(',') : null);
    } else {
      c.setHover(null);
      setPreview(null, false);
      setGhost(null);
    }
  };

  const endDrag = (e: PointerEvent) => {
    if (drag.current === e.pointerId) drag.current = null;
  };
  const onPointerLeave = (e: PointerEvent) => {
    if (drag.current !== null) return;
    if (e.pointerType === 'mouse') {
      c.setHover(null);
      setPreview(null, false);
    }
    setGhost(null);
  };
  // Ctrl-click opens the context menu on a Mac; on the board it means "go back here"
  const onContextMenu = (e: MouseEvent) => {
    if (interactive && e.ctrlKey) e.preventDefault();
  };

  // ---------- what to draw ----------
  const placed = fold.placed;
  // "go back to letter cut": the letters after it are drawn faded, their contacts hidden
  const cut = interactive && c.cut !== null && c.cut < placed - 1 ? c.cut : null;
  const kept = cut === null ? placed : cut + 1;
  const contacts = showContacts ? fold.contacts().filter(({ j }) => j < kept) : [];
  const last = pts[pts.length - 1];
  const hoverIdx = c.hover !== null && c.hover < pts.length ? c.hover : null;
  const ghostIdx = ghost && cut === null ? options.findIndex((o) => o.join(',') === ghost) : -1;
  const ghostPt = ghostIdx >= 0 ? optPts[ghostIdx] : null;
  // contacts the next letter would make at the hovered ghost
  const gain: Pt[] = [];
  if (ghostPt && seq[placed] === 'H' && showContacts) {
    for (const w of neighbours(lattice, options[ghostIdx])) {
      const j = fold.at(w);
      if (j !== undefined && j < placed - 1 && seq[j] === 'H') gain.push(pts[j]);
    }
  }
  const glyphs =
    showKeys && interactive && last && cut === null
      ? options.map((o) => stepGlyph(lattice, stepIndex(lattice, fold.last!, o), fold.last!))
      : [];

  const seg = (a: Pt, b: Pt, r = R) => {
    const dx = b[0] - a[0];
    const dy = b[1] - a[1];
    const L = Math.hypot(dx, dy) || 1;
    return { x1: a[0] + (dx / L) * r, y1: a[1] + (dy / L) * r, x2: b[0] - (dx / L) * r, y2: b[1] - (dy / L) * r };
  };
  const line = (from: number, to: number) => pts.slice(from, to).map((p) => p.join(',')).join(' ');

  // tooltip over the letter under the pointer (or selected by a tap)
  let tip: { x: number; y: number; below: boolean; title: string; kind: string; action: string } | null = null;
  if (hoverIdx !== null && drag.current === null) {
    const [x, y] = pts[hoverIdx];
    const v = shown;
    const action = !interactive
      ? ''
      : hoverIdx === placed - 1
        ? 'Last placed'
        : cut === hoverIdx
          ? `Click to remove ${residueRange(hoverIdx + 2, placed)}`
          : touchSel
            ? 'Tap again to go back here'
            : `${mod}-click to go back here`;
    const top = ((y - R - v.y) / v.h) * size.H;
    const below = top < 52;
    tip = {
      x: Math.min(Math.max(((x - v.x) / v.w) * size.W, 80), size.W - 80),
      y: below ? ((y + R - v.y) / v.h) * size.H : top,
      below,
      title: `Letter ${hoverIdx + 1}`,
      kind: seq[hoverIdx],
      action,
    };
  }

  const label = `${lattice.name}: ${placed} of ${n} letters placed, ${fold.score()} contact${fold.score() === 1 ? '' : 's'}`;

  return (
    <div ref={wrapRef} class="fg-svg-wrap" style={{ height: typeof height === 'number' ? `${height}px` : height }}>
      <svg
        ref={svgRef}
        class={`fg-svg${interactive ? ' is-interactive' : ''}${ghost || cut !== null ? ' is-over-target' : ''}`}
        viewBox={vb(shown)}
        role="img"
        aria-label={label}
        onPointerDown={onPointerDown}
        onPointerMove={onPointerMove}
        onPointerUp={endDrag}
        onPointerCancel={endDrag}
        onPointerLeave={onPointerLeave}
        onContextMenu={onContextMenu}
      >
        {dots.edges.length > 0 && (
          <g class="fg-svg-edges">
            {dots.edges.map(([p, q]) => (
              <line x1={p[0]} y1={p[1]} x2={q[0]} y2={q[1]} />
            ))}
          </g>
        )}
        <g class="fg-svg-dots">
          {dots.dots.map(([x, y]) => (
            <circle cx={x} cy={y} r={0.045} />
          ))}
        </g>

        {showContacts && (
          <g class="fg-svg-contacts">
            {contacts.map(({ i, j }) => (
              <line key={`${i}-${j}`} {...seg(pts[i], pts[j], R + 0.04)} />
            ))}
          </g>
        )}

        {kept > 1 && <polyline class="fg-svg-backbone" points={line(0, kept)} />}
        {kept < placed && <polyline class="fg-svg-backbone is-cut" points={line(kept - 1, placed)} />}

        {ghostPt && last && (
          <g class="fg-svg-preview">
            <line class="fg-svg-preview-bb" x1={last[0]} y1={last[1]} x2={ghostPt[0]} y2={ghostPt[1]} />
            {gain.map((p) => (
              <line class="fg-svg-preview-bond" {...seg(ghostPt, p, R + 0.04)} />
            ))}
          </g>
        )}

        {cut === null &&
          optPts.map((p, k) => (
            <g key={options[k].join(',')} class={`fg-svg-ghost${k === ghostIdx ? ' is-hot' : ''}`} transform={`translate(${p[0]} ${p[1]})`}>
              {k === ghostIdx ? (
                <circle class={`fg-svg-ghost-res is-${seq[placed]}`} r={R} />
              ) : (
                <circle class="fg-svg-ghost-dot" r={R * 0.78} />
              )}
              {glyphs[k] && k !== ghostIdx && (
                <text class="fg-svg-key" y={0.005}>
                  {glyphs[k]}
                </text>
              )}
            </g>
          ))}

        <g class="fg-svg-letters">
          {pts.map((p, i) => (
            <g key={i} class={`fg-svg-res is-${seq[i]}${i >= kept ? ' is-cut' : ''}`} transform={`translate(${p[0]} ${p[1]})`}>
              <circle r={R} />
            </g>
          ))}
        </g>

        {cut !== null ? (
          <circle class="fg-svg-last is-new" cx={pts[cut][0]} cy={pts[cut][1]} r={R + 0.11} />
        ) : (
          last && <circle class={`fg-svg-last${interactive && fold.stuck ? ' is-stuck' : ''}`} cx={last[0]} cy={last[1]} r={R + 0.11} />
        )}
        {hoverIdx !== null && cut === null && (
          <circle class="fg-svg-hover" cx={pts[hoverIdx][0]} cy={pts[hoverIdx][1]} r={R + 0.15} />
        )}

        {showIndices && (
          <g class="fg-svg-idx">
            {pts.map((p, i) => (
              <text key={i} x={p[0] + R * 0.95} y={p[1] - R * 0.95} class={i === hoverIdx ? 'is-hot' : ''}>
                {i + 1}
              </text>
            ))}
          </g>
        )}

        {gain.length > 0 && ghostPt && (
          <text class="fg-svg-gain" x={ghostPt[0]} y={ghostPt[1] + R + 0.36}>
            +{gain.length}
          </text>
        )}
      </svg>
      {tip && (
        <div class={`fg-svg-tip${tip.below ? ' is-below' : ''}`} style={{ transform: `translate(${tip.x.toFixed(1)}px, ${tip.y.toFixed(1)}px)` }} aria-hidden="true">
          <span>
            {tip.title} <b class={`fg-k${tip.kind}`}>{tip.kind}</b>
          </span>
          {tip.action && <span class="fg-svg-tip-act">{tip.action}</span>}
        </div>
      )}
    </div>
  );
}
