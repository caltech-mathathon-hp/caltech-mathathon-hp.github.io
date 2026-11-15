/**
 * Dev-only test bench for Three3D (page: src/pages/dev/fold3d.astro). It plays the part of the
 * shell: owns a GameController, re-renders on its changes, forwards keys through the renderer's
 * keyboard map, and exposes every RendererProps toggle. Not used by the site itself.
 */
import { useEffect, useRef, useState } from 'preact/hooks';
import { GameController } from '../engine/controller.ts';
import Three3D from './Three3D.tsx';

/** Hamiltonian snake through an nx × ny × nz box (consecutive points are lattice neighbours) */
function snake(nx: number, ny: number, nz: number): number[][] {
  const S: number[][] = [];
  for (let y = 0; y < ny; y++) for (let i = 0; i < nx; i++) S.push([y % 2 === 0 ? i : nx - 1 - i, y]);
  const out: number[][] = [];
  for (let z = 0; z < nz; z++) {
    const layer = z % 2 === 0 ? S : [...S].reverse();
    for (const [x, y] of layer) out.push([x - (nx >> 1), y - (ny >> 1), z - (nz >> 1)]);
  }
  return out;
}

const GAME = 'HPHPPHHPHPPHPHHPPHPHHPPHHPHPHH';

interface Preset {
  label: string;
  lattice: string;
  sequence: string;
  positions?: () => number[][];
}

const PRESETS: Record<string, Preset> = {
  cubic: { label: 'Cubic · 30 residues (play)', lattice: 'cubic', sequence: GAME },
  fcc: { label: 'FCC · 30 residues (play)', lattice: 'fcc', sequence: GAME },
  cube4: {
    label: 'Cubic · 4³ H core + P layer (80)',
    lattice: 'cubic',
    sequence: 'H'.repeat(64) + 'P'.repeat(16),
    positions: () => snake(4, 4, 5),
  },
  cube16: {
    label: 'Cubic · 16³ H cube (4 096)',
    lattice: 'cubic',
    sequence: 'H'.repeat(4096),
    positions: () => snake(16, 16, 16),
  },
  stress: {
    label: 'Cubic · 16³ H + 4 P layers (5 120)',
    lattice: 'cubic',
    sequence: 'H'.repeat(4096) + 'P'.repeat(1024),
    positions: () => snake(16, 16, 20),
  },
  fccWalk: { label: 'FCC · random walk (600)', lattice: 'fcc', sequence: 'HPPHHPHP'.repeat(75) },
  cubicWalk: { label: 'Cubic · random walk (1 500)', lattice: 'cubic', sequence: 'HHPPHPHHPP'.repeat(150) },
};

function make(id: string): GameController {
  const p = PRESETS[id];
  const c = new GameController({ lattice: p.lattice, sequence: p.sequence });
  if (p.positions) c.loadPositions(p.positions());
  else if (id.endsWith('Walk')) randomWalk(c, Infinity);
  return c;
}

/** extend with random legal moves (prefers moves with more free neighbours, to avoid traps) */
function randomWalk(c: GameController, steps: number) {
  for (let s = 0; s < steps && !c.complete; s++) {
    const opts = c.options();
    if (!opts.length) break;
    const f = c.fold;
    const free = (v: number[]) => c.lattice.steps.filter((st) => f.isFree(v.map((x, i) => x + st[i]))).length;
    const scored = opts.map((v) => ({ v, w: free(v) + Math.random() * 2 }));
    scored.sort((a, b) => b.w - a.w);
    c.extendTo(scored[0].v);
  }
}

export default function Three3DHarness() {
  const [preset, setPreset] = useState('cubic');
  const [controller, setController] = useState(() => make('cubic'));
  const [version, setVersion] = useState(0);
  const [interactive, setInteractive] = useState(true);
  const [showLattice, setShowLattice] = useState(true);
  const [showContacts, setShowContacts] = useState(true);
  const [showIndices, setShowIndices] = useState(false);
  const [tall, setTall] = useState(false);
  const [playing, setPlaying] = useState(false);
  /** view mode, as in the shell: the complete fold is the frame and a slider shows its first k residues */
  const [full, setFull] = useState<number[][] | null>(null);
  const keyMap = useRef<((key: string, e: KeyboardEvent) => number | null) | null>(null);
  const playRef = useRef(0);

  useEffect(() => controller.subscribe((c) => setVersion(c.version)), [controller]);

  const choose = (id: string) => {
    stop();
    setFull(null);
    setPreset(id);
    setController(make(id));
  };

  const stop = () => {
    cancelAnimationFrame(playRef.current);
    playRef.current = 0;
    setPlaying(false);
  };

  /** replay the fold from residue 1, k residues per frame (exercises incremental updates) */
  const play = () => {
    if (playing) return stop();
    const c = controller;
    if (!c.canRedo) c.truncate(1);
    const per = Math.max(1, Math.round(c.seq.length / 150));
    setPlaying(true);
    const tick = () => {
      for (let i = 0; i < per && c.canRedo; i++) c.redo();
      if (c.canRedo) playRef.current = requestAnimationFrame(tick);
      else stop();
    };
    playRef.current = requestAnimationFrame(tick);
  };

  useEffect(() => () => cancelAnimationFrame(playRef.current), []);

  const onKey = (e: KeyboardEvent) => {
    if (e.key === 'Backspace' || (e.key === 'z' && !e.metaKey && !e.ctrlKey)) {
      controller.undo();
      e.preventDefault();
      return;
    }
    const k = keyMap.current?.(e.key, e) ?? null;
    if (k !== null) {
      controller.extendStep(k);
      e.preventDefault();
    }
  };

  const c = controller;
  const toggleView = () => {
    stop();
    if (full) {
      c.loadPositions(full);
      setFull(null);
    } else setFull(c.fold.path.map((v) => [...v]));
  };
  return (
    <div class="fg3h ui">
      <div class="fg3h-bar">
        <select value={preset} onChange={(e) => choose((e.target as HTMLSelectElement).value)} aria-label="Preset">
          {Object.entries(PRESETS).map(([id, p]) => (
            <option value={id}>{p.label}</option>
          ))}
        </select>
        <button class="btn" type="button" onClick={() => c.undo()} disabled={!c.canUndo}>
          Undo
        </button>
        <button class="btn" type="button" onClick={() => c.redo()} disabled={!c.canRedo}>
          Redo
        </button>
        <button class="btn" type="button" onClick={() => c.reset()}>
          Reset
        </button>
        <button class="btn" type="button" onClick={() => randomWalk(c, 25)} disabled={c.complete || c.stuck}>
          Add 25 random steps
        </button>
        <button class="btn" type="button" onClick={play}>
          {playing ? 'Stop' : 'Replay'}
        </button>
      </div>
      <div class="fg3h-bar">
        <label>
          <input type="checkbox" checked={interactive} onChange={() => setInteractive(!interactive)} /> interactive
        </label>
        <label>
          <input type="checkbox" checked={showLattice} onChange={() => setShowLattice(!showLattice)} /> lattice
        </label>
        <label>
          <input type="checkbox" checked={showContacts} onChange={() => setShowContacts(!showContacts)} /> contacts
        </label>
        <label>
          <input type="checkbox" checked={showIndices} onChange={() => setShowIndices(!showIndices)} /> indices
        </label>
        <label>
          <input type="checkbox" checked={tall} onChange={() => setTall(!tall)} /> tall (70vh)
        </label>
        <label>
          <input type="checkbox" checked={!!full} onChange={toggleView} /> view mode
        </label>
        {full && (
          <input
            type="range"
            min={1}
            max={full.length}
            value={c.fold.placed}
            aria-label="Residues shown"
            onInput={(e) => c.loadPositions(full.slice(0, +(e.target as HTMLInputElement).value))}
          />
        )}
      </div>
      <p class="fg3h-status">
        {c.lattice.name} · placed {c.fold.placed} / {c.fold.length} · contacts {c.score} (bound {c.bound})
        {c.complete ? ' · complete' : c.stuck ? ' · stuck' : ''} · hover {c.hover ?? '–'} · v{version}
      </p>
      <div class="fg3h-stage" tabIndex={0} onKeyDown={onKey} aria-label="Folding game (3D). Arrow keys and W/S place the next residue.">
        <Three3D
          controller={c}
          version={version}
          interactive={interactive && !full}
          showLattice={showLattice}
          showContacts={showContacts}
          showIndices={showIndices}
          height={tall ? '70vh' : 440}
          frame={full ?? undefined}
          registerKeyMap={(fn) => {
            keyMap.current = fn;
          }}
        />
      </div>
      <style>{`
        .fg3h { display: grid; gap: var(--s-2); }
        .fg3h-bar { display: flex; flex-wrap: wrap; gap: var(--s-2); align-items: center; }
        .fg3h-bar label { display: inline-flex; gap: 4px; align-items: center; color: var(--fg-muted); }
        .fg3h-bar select { font: inherit; padding: 0.4em; border-radius: var(--radius-sm); border: 1px solid var(--rule-strong); background: var(--bg-elev); color: var(--fg); max-width: 100%; }
        .fg3h-status { margin: 0; color: var(--fg-muted); font-variant-numeric: tabular-nums; }
        .fg3h-stage { border-radius: var(--radius-md); }
      `}</style>
    </div>
  );
}
