/** @jsxImportSource preact */
/**
 * FoldGame: the embeddable folding game (an Astro island).
 *
 *   <FoldGame client:visible compact lattice="square" sequence="HPHPPHHPHPPHPHHPPHPH" />
 *   <FoldGame client:load levels latticePicker lattice="cubic" />          the full playground
 *   <FoldGame client:visible mode="view" lattice="cubic" sequence="…" moves="RULF…" />
 *
 * It owns a GameController (engine/controller.ts) and picks a renderer by lattice.dim:
 * Svg2D for 2D lattices; the three.js renderer (render/Three3D.tsx) for 3D lattices, loaded
 * lazily so that 2D pages never download three.js.
 *
 * Layout of the full game, top to bottom:
 *   header   3D or 2D, then the lattice of that dimension, then its levels and "Own string"
 *   brief    the level's title and goal (or the form for an own string)
 *   body     [string strip, board, context line] | [score panel: contacts, bounds, actions]
 * The context line under the board says what to do next and how (it changes with the state);
 * "Controls" there opens the full list. Compact: strip, board, one bar with the same parts;
 * the score sits over the board on the right (on narrow screens it is in the bar instead).
 *
 * "Show solution" replays a best fold letter by letter (levels store one; for other strings
 * the browser runs an exhaustive search, engine/solve.ts, when the string is short enough).
 * Once the replay ends, the solution is a fold like any other: going back to a letter, undo or
 * placing letters changes it, and it becomes the reader's fold. Until then "Back to my fold"
 * restores the fold the reader had before.
 * Styles: styles.css (class prefix fg-). Levels: levels/*.json (schema in levels/index.ts).
 */
import { useCallback, useEffect, useId, useMemo, useRef, useState } from 'preact/hooks';
import type { ComponentChildren, ComponentType } from 'preact';
import { GameController } from './engine/controller.ts';
import { LATTICES, degree, girthOf, type Lattice } from './engine/lattice.ts';
import { chainBonds, decodeMoves, maxPairs, parseSequence, shapeBound } from './engine/fold.ts';
import { solveAsync, type SolveResult } from './engine/solve.ts';
import Svg2D from './render/Svg2D.tsx';
import { residueRange, type RendererProps } from './render/types.ts';
import { LEVELS, findLevel, getLevel, type Level } from './levels/index.ts';
import { absoluteStep, isApple, keyHint } from './keys.ts';
import './styles.css';

export interface FoldGameProps {
  /** the HP string; required unless a level provides it */
  sequence?: string;
  /** lattice id: 'cubic' | 'fcc' | 'diamond' | 'square' | 'triangular' | 'hexagonal'
   * (default: the level's, else 'square') */
  lattice?: string;
  /** initial fold as a move string (square/cubic/hexagonal: letters R L U D F B; see engine/fold.ts) */
  moves?: string;
  /** initial fold as explicit lattice points (alternative to moves, e.g. a construction) */
  positions?: number[][];
  /** 'play' (default): fold it yourself. 'view': read-only, with a scrubber over the letters */
  mode?: 'play' | 'view';
  /** minimal chrome, for figures inside prose */
  compact?: boolean;
  /** CSS height of the board (number = px) */
  height?: number | string;
  /** letter numbers next to the letters */
  showIndices?: boolean;
  /** show the levels: true = all levels, or a list of level ids (listed per lattice) */
  levels?: boolean | string[];
  /** level to start with (id); default: the first level of `lattice`, when `levels` is set and no sequence */
  level?: string;
  /** let the reader switch dimension and lattice: true = all lattices, or a list of ids */
  latticePicker?: boolean | string[];
  /** "Own string": a field to type your own string (default: on when levels or latticePicker are on) */
  custom?: boolean;
  /** "Copy link" button, and read a fold from the URL (#fold=…) (default: on with levels) */
  share?: boolean;
  /** best known score of `sequence` on `lattice`, shown in the score panel (levels have their own) */
  best?: number;
  /** accessible name of the board */
  label?: string;
}

type Renderer = ComponentType<RendererProps>;
type KeyMap = (key: string, e: KeyboardEvent) => number | null;

// ---- the three.js renderer, loaded on first use ----
// import.meta.glob compiles to () => import('./render/Three3D.tsx') when the file exists and
// to nothing when it does not, so the widget builds and degrades gracefully without it.
const threeModules = import.meta.glob<{ default?: Renderer; Three3D?: Renderer }>('./render/Three3D.tsx');
let threePromise: Promise<Renderer> | null = null;
function loadThree(): Promise<Renderer> {
  if (!threePromise) {
    const load = threeModules['./render/Three3D.tsx'];
    threePromise = load
      ? load().then((m) => {
          const R = m.default ?? m.Three3D;
          if (!R) throw new Error('render/Three3D.tsx has no default export');
          return R;
        })
      : Promise.reject(new Error('missing'));
    threePromise.catch(() => (threePromise = null)); // allow a retry
  }
  return threePromise;
}

/** the lattices in the order of the picker: 3D first (the theorem's case), then 2D */
const LATTICE_ORDER = ['cubic', 'fcc', 'diamond', 'square', 'triangular', 'hexagonal'];
const LATTICE_LABEL: Record<string, string> = {
  cubic: 'Cubic',
  fcc: 'FCC',
  diamond: 'Diamond',
  square: 'Square',
  triangular: 'Triangular',
  hexagonal: 'Hexagonal',
};
const DIMS: { dim: 2 | 3; label: string }[] = [
  { dim: 3, label: '3D' },
  { dim: 2, label: '2D' },
];
/** longest strings solved in the browser on request (exhaustive search; a few seconds at worst) */
const SOLVE_MAX: Record<string, number> = { square: 22, triangular: 14, hexagonal: 28, cubic: 14, fcc: 9, diamond: 18 };
const SOLVE_TIME_MS = 5000;
const STORE_KEY = 'hp-fold-game.solved';

const seqString = (s: string) => parseSequence(s).join('');
const contacts = (k: number) => `${k} contact${k === 1 ? '' : 's'}`;
const reducedMotion = () => typeof matchMedia === 'function' && matchMedia('(prefers-reduced-motion: reduce)').matches;

function readHash(): { lattice: string; seq: string; moves: string } | null {
  if (typeof location === 'undefined') return null;
  const m = location.hash.match(/[#&]fold=([a-z]+)\.([HPhp]+)(?:\.([A-Za-z0-9]*))?/);
  if (!m || !LATTICES[m[1]]) return null;
  return { lattice: m[1], seq: m[2].toUpperCase(), moves: m[3] ?? '' };
}

function loadSolved(): Set<string> {
  try {
    const v = JSON.parse(localStorage.getItem(STORE_KEY) ?? '[]');
    return new Set(Array.isArray(v) ? v.filter((x) => typeof x === 'string') : []);
  } catch {
    return new Set();
  }
}
function saveSolved(s: Set<string>) {
  try {
    localStorage.setItem(STORE_KEY, JSON.stringify([...s]));
  } catch {
    /* private mode or storage blocked: progress lasts for this visit only */
  }
}

/** where the best score shown for the current string comes from */
interface BestInfo {
  value: number;
  optimal: boolean;
  source?: string;
}
/** what "Show solution" can do for the current string */
type SolInfo =
  | { kind: 'ready'; moves: string; score: number; optimal: boolean }
  | { kind: 'compute' }
  | { kind: 'none'; why: string };

// ---------------------------------------------------------------------------------------

export default function FoldGame(props: FoldGameProps) {
  const mode = props.mode ?? 'play';
  const play = mode === 'play';
  const compact = !!props.compact;

  const levelList = useMemo<Level[]>(() => {
    if (!props.levels || !play) return [];
    if (Array.isArray(props.levels)) return props.levels.map((id) => getLevel(id)).filter((l): l is Level => !!l);
    return LEVELS;
  }, []);
  const lattices = useMemo<string[]>(() => {
    if (!props.latticePicker || !play) return [];
    const ids = Array.isArray(props.latticePicker) ? props.latticePicker : LATTICE_ORDER;
    return LATTICE_ORDER.filter((id) => ids.includes(id) && LATTICES[id]);
  }, []);
  const custom = play && !compact && (props.custom ?? (levelList.length > 0 || lattices.length > 0));
  const share = play && !compact && (props.share ?? levelList.length > 0);

  // ---- the controller (created once) ----
  const init = useMemo(() => {
    const startLevel =
      getLevel(props.level) ??
      (props.sequence ? undefined : levelList.find((l) => !props.lattice || l.lattice === props.lattice) ?? levelList[0]);
    const latticeId = props.lattice ?? startLevel?.lattice ?? 'square';
    const sequence = props.sequence ?? startLevel?.sequence ?? '';
    let error: string | null = null;
    let ctrl: GameController;
    try {
      if (!seqString(sequence)) throw new Error('no sequence given');
      ctrl = new GameController({ lattice: latticeId, sequence, moves: props.moves });
      if (props.positions) ctrl.loadPositions(props.positions);
    } catch (e) {
      error = e instanceof Error ? e.message : String(e);
      ctrl = new GameController({ lattice: 'square', sequence: 'HPPH' });
    }
    return { ctrl, error, levelId: startLevel?.id ?? null, latticeId, sequence: seqString(sequence) };
  }, []);
  const ctrl = init.ctrl;

  const [, setTick] = useState(0);
  useEffect(() => ctrl.subscribe((c) => setTick(c.version)), [ctrl]);

  /** the level being played; null = the reader's own string */
  const [levelId, setLevelId] = useState<string | null>(init.levelId);
  const [own, setOwn] = useState(init.sequence);
  const [ownError, setOwnError] = useState<string | null>(null);
  const [bump, setBump] = useState(0);
  const [copied, setCopied] = useState<null | 'ok' | 'fail'>(null);
  const [playing, setPlaying] = useState(false);
  const [solved, setSolved] = useState<Set<string>>(() => new Set());
  /**
   * solution mode: the reader's own fold is kept in `saved` and restored on leaving.
   * `shown` is null while the replay runs, then the moves of the solution as placed.
   */
  const [sol, setSol] = useState<null | { saved: string; score: number; optimal: boolean; total: number; shown: string | null }>(null);
  const [solving, setSolving] = useState(false);
  const [, setSolveTick] = useState(0);
  const [controlsOpen, setControlsOpen] = useState(false);
  const [undoStreak, setUndoStreak] = useState(0);
  /** the keyboard is in use on the focused board (2D: print the keys on the legal positions) */
  const [kbd, setKbd] = useState(false);
  const [stageFocus, setStageFocus] = useState(false);
  // set after hydration, so that the server HTML and the first client render agree
  const [env, setEnv] = useState({ coarse: false, apple: false });
  useEffect(() => {
    const mq = typeof matchMedia === 'function' ? matchMedia('(pointer: coarse)') : null;
    const update = () => setEnv({ coarse: !!mq?.matches, apple: isApple() });
    update();
    mq?.addEventListener?.('change', update);
    if (levelList.length) setSolved(loadSolved());
    return () => mq?.removeEventListener?.('change', update);
  }, []);

  const uid = useId();
  const stageRef = useRef<HTMLDivElement>(null);
  const controlsBtn = useRef<HTMLButtonElement>(null);
  const keyMapRef = useRef<KeyMap | null>(null);
  const pointerFocus = useRef(false);
  const solveRef = useRef<HTMLButtonElement>(null);
  const animRef = useRef<ReturnType<typeof setInterval> | null>(null);
  const jobRef = useRef<{ cancel: () => void } | null>(null);
  const computed = useRef(new Map<string, SolveResult>());
  const lastLevelOf = useRef<Record<string, string | null>>({});
  const lastLatticeOf = useRef<Record<number, string>>({ 2: 'square', 3: 'cubic' });
  const [rendererKeys, setRendererKeys] = useState(false);
  const registerKeyMap = useCallback((fn: KeyMap | null) => {
    keyMapRef.current = fn;
    setRendererKeys(!!fn);
  }, []);

  // the complete fold, for view mode (the scrubber shows its first k letters)
  const full = useMemo(() => ctrl.fold.path.map((v) => [...v]), []);

  const lattice: Lattice = ctrl.lattice;
  const seq = ctrl.seq;
  const seqStr = seq.join('');
  const n = seq.length;
  const fold = ctrl.fold;
  const placed = fold.placed;
  const score = fold.score();
  const key = `${lattice.id}.${seqStr}`;
  // three upper bounds; the game shows the smallest and explains that one (boundText):
  // the cube bound (square and cubic lattices), the number of pairs of H's that could touch,
  // and the engine's free-side (parity) bound
  const pairs = useMemo(() => touchablePairs(seq, lattice), [seqStr, lattice.id]);
  const shape = useMemo(() => shapeBound(lattice, seq), [seqStr, lattice.id]);
  const bound = Math.min(ctrl.bound, pairs, shape ?? Infinity);
  const boundKind: BoundKind = shape !== null && shape === bound ? 'shape' : pairs === bound && pairs < ctrl.bound ? 'pairs' : 'parity';

  // ---- levels of this lattice, the active one, and what is known about this string ----
  const latLevels = levelList.filter((l) => l.lattice === lattice.id);
  const chosen = getLevel(levelId);
  const active = chosen && chosen.lattice === lattice.id && chosen.sequence === seqStr ? chosen : undefined;
  const known = active ?? findLevel(lattice.id, seqStr);
  const result = computed.current.get(key);
  const bestInfo: BestInfo | undefined = known
    ? { value: known.best, optimal: known.optimal, source: known.bestSource }
    : result?.exhaustive
      ? { value: result.score, optimal: true, source: 'Found by an exhaustive search in your browser.' }
      : props.best !== undefined && lattice.id === init.latticeId && seqStr === init.sequence
        ? { value: props.best, optimal: false }
        : undefined;
  const best = bestInfo?.value;
  const levelIndex = active ? latLevels.indexOf(active) : -1;
  const nextLevel = levelIndex >= 0 ? latLevels[levelIndex + 1] : undefined;

  const solInfo: SolInfo = known?.solution
    ? { kind: 'ready', moves: known.solution, score: known.best, optimal: known.optimal }
    : result?.exhaustive
      ? { kind: 'ready', moves: result.moves, score: result.score, optimal: true }
      : result
        ? { kind: 'none', why: `The search for the best fold did not finish within ${SOLVE_TIME_MS / 1000} seconds.` }
        : n <= (SOLVE_MAX[lattice.id] ?? 0)
          ? { kind: 'compute' }
          : {
              kind: 'none',
              why: `No solution is stored for this string. Strings of up to ${SOLVE_MAX[lattice.id] ?? 0} letters are solved here; longer ones take too long.`,
            };

  // ---- the 3D renderer ----
  const [three, setThree] = useState<{ R: Renderer | null; state: 'idle' | 'loading' | 'ready' | 'missing' }>({
    R: null,
    state: 'idle',
  });
  useEffect(() => {
    if (lattice.dim !== 3 || three.R) return;
    let alive = true;
    setThree({ R: null, state: 'loading' });
    loadThree()
      .then((R) => alive && setThree({ R, state: 'ready' }))
      .catch(() => alive && setThree({ R: null, state: 'missing' }));
    return () => {
      alive = false;
    };
  }, [lattice.dim]);

  // ---- a fold from the URL (#fold=lattice.SEQUENCE.moves) ----
  useEffect(() => {
    if (!share) return;
    const h = readHash();
    if (!h) return;
    ctrl.setHover(null);
    ctrl.setLattice(h.lattice);
    ctrl.setSequence(h.seq);
    if (h.moves) ctrl.applyMoves(h.moves);
    const lv = levelList.find((l) => l.lattice === h.lattice && l.sequence === h.seq);
    setLevelId(lv ? lv.id : null);
    setOwn(h.seq);
  }, []);

  // ---- solution mode ----
  const stopAnim = () => {
    if (animRef.current) clearInterval(animRef.current);
    animRef.current = null;
  };
  /** leave solution mode: back to the reader's fold, to an empty fold, or as is (a new string follows) */
  const leaveSolution = (to: 'mine' | 'reset' | 'keep') => {
    stopAnim();
    if (!sol) return;
    if (to === 'mine') ctrl.applyMoves(sol.saved);
    else if (to === 'reset') ctrl.reset();
    setSol(null);
    // the buttons of solution mode disappear: keep the keyboard focus nearby
    if (to !== 'keep' && stageRef.current?.closest('.fg')?.contains(document.activeElement))
      requestAnimationFrame(() => solveRef.current?.focus({ preventScroll: true }));
  };
  const playSolution = (moves: string, s: number, optimal: boolean) => {
    const steps = decodeMoves(ctrl.lattice, moves);
    const base = { saved: sol?.saved ?? ctrl.fold.moves(), score: s, optimal, total: steps.length + 1 };
    stopAnim();
    ctrl.setHover(null);
    // the whole solution is placed: from now on the reader may change it like their own fold
    const placedAll = () => setSol({ ...base, shown: ctrl.fold.moves() });
    if (reducedMotion()) {
      ctrl.applyMoves(moves);
      placedAll();
      return;
    }
    setSol({ ...base, shown: null });
    ctrl.reset();
    let i = 0;
    const dt = Math.max(45, Math.min(170, 2600 / Math.max(1, steps.length)));
    animRef.current = setInterval(() => {
      if (i < steps.length && ctrl.extendStep(steps[i++])) return;
      stopAnim();
      placedAll();
    }, dt);
  };
  // the reader changed the solution: it is now their fold, and the one they had before is dropped
  useEffect(() => {
    if (typeof sol?.shown === 'string' && ctrl.fold.moves() !== sol.shown) setSol(null);
  }, [ctrl.version]);
  /** the replay of the solution is running: the board, the string and the keys wait */
  const replaying = !!sol && sol.shown === null;
  const showSolution = async () => {
    if (solInfo.kind === 'ready') return playSolution(solInfo.moves, solInfo.score, solInfo.optimal);
    if (solInfo.kind !== 'compute' || solving) return;
    setSolving(true);
    const job = solveAsync(ctrl.lattice, ctrl.seq, { timeMs: SOLVE_TIME_MS });
    jobRef.current = job;
    const r = await job.promise;
    if (jobRef.current !== job) return; // cancelled: the string or the lattice changed
    jobRef.current = null;
    computed.current.set(key, r);
    setSolving(false);
    setSolveTick((t) => t + 1);
    if (r.exhaustive) playSolution(r.moves, r.score, true);
  };
  // a new string or lattice cancels a running search
  useEffect(
    () => () => {
      jobRef.current?.cancel();
      jobRef.current = null;
      setSolving(false);
    },
    [key],
  );
  useEffect(() => () => stopAnim(), []);

  // ---- actions ----
  const flash = () => setBump((b) => b + 1);
  useEffect(() => {
    if (!bump) return;
    const t = setTimeout(() => setBump(0), 260);
    return () => clearTimeout(t);
  }, [bump]);

  const undo = () => {
    if (ctrl.undo()) setUndoStreak((s) => s + 1);
    else flash();
  };
  const reset = () => {
    ctrl.reset();
    setUndoStreak(0);
  };
  const prevPlaced = useRef(placed);
  useEffect(() => {
    if (placed > prevPlaced.current) setUndoStreak(0);
    prevPlaced.current = placed;
  }, [placed]);

  const chooseLevel = (id: string) => {
    const lv = getLevel(id);
    if (!lv) return;
    leaveSolution('keep');
    setLevelId(id);
    lastLevelOf.current[lv.lattice] = id;
    ctrl.setHover(null);
    if (ctrl.lattice.id !== lv.lattice) ctrl.setLattice(lv.lattice);
    ctrl.setSequence(lv.sequence);
    setOwn(lv.sequence);
    setOwnError(null);
  };
  const chooseOwn = () => {
    if (levelId === null) return;
    leaveSolution('mine');
    setLevelId(null);
    setOwn(seqStr);
  };
  const chooseLattice = (id: string) => {
    if (id === ctrl.lattice.id) return;
    leaveSolution('keep');
    lastLatticeOf.current[LATTICES[id].dim] = id;
    ctrl.setHover(null);
    // an own string stays the reader's string on the new lattice; a level goes to that lattice's level
    const lvId = levelId === null ? null : lastLevelOf.current[id] ?? levelList.find((l) => l.lattice === id)?.id ?? null;
    if (lvId) return chooseLevel(lvId);
    setLevelId(null);
    ctrl.setLattice(id);
  };
  const chooseDim = (d: number) => {
    if (d === ctrl.lattice.dim) return;
    const remembered = lastLatticeOf.current[d];
    const target = lattices.includes(remembered) ? remembered : lattices.find((id) => LATTICES[id].dim === d);
    if (target) chooseLattice(target);
  };
  const submitOwn = (e: Event) => {
    e.preventDefault();
    // read the field itself: the state may lag behind fast typing
    const field = (e.currentTarget as HTMLFormElement).querySelector('input');
    const raw = (field?.value ?? own).replace(/\s+/g, '').toUpperCase();
    if (!raw) return setOwnError('Type a string of H’s and P’s.');
    if (!/^[HP]+$/.test(raw)) return setOwnError('Use only the letters H and P.');
    if (raw.length < 2 || raw.length > 200) return setOwnError('Use 2 to 200 letters.');
    setOwnError(null);
    setOwn(raw);
    leaveSolution('keep');
    ctrl.setHover(null);
    ctrl.setSequence(raw);
  };
  const scrubTo = (k: number) => {
    k = Math.max(1, Math.min(full.length, k));
    if (k !== ctrl.fold.placed) ctrl.loadPositions(full.slice(0, k));
  };
  /** a click on letter i of the strip */
  const pickResidue = (i: number) => {
    if (!play) return scrubTo(i + 1);
    if (replaying || i >= ctrl.fold.placed - 1) return;
    ctrl.truncate(i + 1);
    ctrl.setHover(null);
  };
  const copyLink = async () => {
    const url = `${location.origin}${location.pathname}${location.search}#fold=${ctrl.lattice.id}.${seqStr}.${ctrl.fold.moves()}`;
    try {
      history.replaceState(null, '', url);
      await navigator.clipboard.writeText(url);
      setCopied('ok');
    } catch {
      setCopied('fail');
    }
    setTimeout(() => setCopied(null), 2400);
  };
  const closeControls = (refocus: boolean) => {
    setControlsOpen(false);
    if (refocus) controlsBtn.current?.focus();
  };

  // view mode: autoplay
  useEffect(() => {
    if (!playing) return;
    if (ctrl.fold.placed >= full.length) scrubTo(1);
    const dt = Math.max(30, Math.min(320, 4000 / full.length));
    const id = setInterval(() => {
      if (ctrl.fold.placed >= full.length) setPlaying(false);
      else scrubTo(ctrl.fold.placed + 1);
    }, dt);
    return () => clearInterval(id);
  }, [playing]);

  // ---- progress: a level counts as solved when the reader's own fold reaches its best ----
  const complete = fold.complete;
  useEffect(() => {
    if (sol || !active || !complete || score < active.best || solved.has(active.id)) return;
    const next = new Set(solved);
    next.add(active.id);
    setSolved(next);
    saveSolved(next);
  }, [ctrl.version, !!sol]);

  // ---- keyboard ----
  const onKeyDown = (e: KeyboardEvent) => {
    const t = e.target as HTMLElement;
    if (/^(INPUT|SELECT|TEXTAREA)$/.test(t.tagName)) return;
    const k = e.key;
    if (k === 'Escape') {
      if (controlsOpen) closeControls(true);
      else if (sol) leaveSolution('mine');
      else if (ctrl.cut !== null || ctrl.hover !== null) {
        ctrl.setCut(null);
        ctrl.setHover(null);
      } else return;
      e.preventDefault();
      return;
    }
    if (k === '?' && !e.metaKey && !e.ctrlKey) {
      e.preventDefault();
      setControlsOpen((o) => !o);
      return;
    }
    if (!play) {
      const steps: Record<string, number> = { ArrowLeft: -1, ArrowDown: -1, ArrowRight: 1, ArrowUp: 1 };
      if (t !== stageRef.current) return;
      if (k in steps) scrubTo(ctrl.fold.placed + steps[k]);
      else if (k === 'Home') scrubTo(1);
      else if (k === 'End') scrubTo(full.length);
      else if (k === ' ') setPlaying((p) => !p);
      else return;
      e.preventDefault();
      return;
    }
    if (replaying) return;
    const mod = e.metaKey || e.ctrlKey;
    if (mod && (k === 'z' || k === 'Z') && !e.shiftKey) {
      e.preventDefault();
      undo();
      return;
    }
    if (mod || e.altKey) return;
    if (k === 'Backspace') {
      e.preventDefault();
      undo();
      return;
    }
    // placing letters: only on the board (elsewhere the arrows move between controls)
    if (t !== stageRef.current) return;
    // the renderer's own mapping (3D: relative to the camera) replaces the absolute one
    const step = keyMapRef.current ? keyMapRef.current(k, e) : absoluteStep(ctrl.lattice, k, ctrl.fold.last);
    if (step === null || step === undefined) return;
    e.preventDefault();
    setKbd(true);
    if (!ctrl.extendStep(step)) flash();
  };

  // ---- words that depend on the device ----
  const coarse = env.coarse;
  const modKey = env.apple ? '⌘' : 'Ctrl';
  const goBack = coarse ? 'Tap a placed letter twice to go back to it' : `${modKey}-click a placed letter to go back to it`;
  const dim3 = lattice.dim === 3;
  const threeReady = !dim3 || three.state === 'ready';
  const stuck = play && fold.stuck;
  const cut = ctrl.cut;

  // ---- status (score panel) and context line (under the board) ----
  let tone: 'info' | 'good' | 'warn' | 'sol' = 'info';
  let status: ComponentChildren;
  let hint: ComponentChildren = null;
  if (!play) {
    status = placed < full.length ? `Letters 1 to ${placed} of ${full.length}.` : 'The complete fold.';
    if (full.length < n && placed === full.length) status = `The fold places ${full.length} of ${n} letters.`;
  } else if (sol) {
    tone = 'sol';
    status =
      placed < sol.total
        ? `Placing letter ${placed} of ${sol.total}.`
        : 'Your own fold is kept until you change this one. “Back to my fold” returns to it.';
  } else if (complete) {
    tone = 'good';
    if (best !== undefined && score > best)
      status = 'Complete, with more contacts than the best known fold. Copy the link to keep it.';
    else if (best !== undefined && score === best)
      status = bestInfo?.optimal ? 'Complete. No fold has more contacts.' : 'Complete. This matches the best known fold.';
    else if (best !== undefined) {
      tone = 'info';
      const more = best - score;
      status = `Complete. ${bestInfo?.optimal ? 'The best fold' : 'The best known fold'} has ${more} more contact${more === 1 ? '' : 's'}.`;
    } else if (score === bound) status = 'Complete. This meets the upper bound, so no fold has more contacts.';
    else status = 'Complete.';
  } else if (stuck) {
    tone = 'warn';
    status = `Stuck. Letter ${placed} has no free neighbour.`;
  } else
    status = (
      <>
        Next: letter {placed + 1} of {n}, <Res r={seq[placed]} />.
      </>
    );

  if (play && !replaying && threeReady) {
    // the keys are listed in the controls (the keyboard button), not in this line
    const hov = ctrl.hover;
    if (cut !== null && cut < placed - 1)
      hint = `Click to go back to letter ${cut + 1}. This removes ${residueRange(cut + 2, placed)}.`;
    else if (hov !== null && hov < placed - 1)
      hint = coarse
        ? `Tap letter ${hov + 1} again to go back to it.`
        : `${modKey}-click letter ${hov + 1} to go back to it, or click it in the string above.`;
    else if (stuck)
      hint = (
        <>
          Undo{!coarse && <> (<Keys k="⌫" />)</>}, or {goBack.charAt(0).toLowerCase() + goBack.slice(1)}.
        </>
      );
    else if (complete) hint = `${goBack} and refold from there.`;
    else if (placed === 1)
      hint = (
        <>
          {coarse ? 'Tap' : 'Click'} a highlighted node to place letter 2.{dim3 && ' Drag to turn the view.'}
        </>
      );
    else if (undoStreak >= 2) hint = `${goBack} in one step.`;
    else if (placed <= 4 && !dim3 && !coarse) hint = 'Drag through highlighted nodes to place several letters at once.';
    else if (placed <= 4 && dim3) hint = coarse ? 'Drag to turn the view. Pinch to zoom.' : 'Drag to turn the view. Scroll to zoom.';
    else hint = `${goBack}.`;
  }

  // polite announcements, after a pause, so that fast key presses give one message
  const message = !play
    ? `Letter ${placed} of ${full.length}. ${contacts(score)}.`
    : sol
      ? placed >= sol.total
        ? `Solution shown: ${contacts(sol.score)}. Escape returns to your fold.`
        : ''
      : complete || stuck
        ? `${typeof status === 'string' ? status : ''} ${contacts(score)}.`
        : placed === 1
          ? `${active ? `${active.title}. ` : ''}A string of ${n} letters; letter 1 is placed.`
          : `Letter ${placed} placed. ${contacts(score)}.`;
  const [announce, setAnnounce] = useState('');
  const quietUntil = useRef(ctrl.version); // nothing to announce before the first move
  useEffect(() => {
    if (!message || ctrl.version <= quietUntil.current) return;
    const t = setTimeout(() => setAnnounce(message), 450);
    return () => clearTimeout(t);
  }, [message]);

  // ---- renderer ----
  const height = props.height ?? (compact ? 'clamp(260px, 52vw, 320px)' : 'clamp(300px, 56vw, 460px)');
  const cssHeight = typeof height === 'number' ? `${height}px` : height;
  const rprops: RendererProps = {
    controller: ctrl,
    version: ctrl.version,
    interactive: play && !replaying,
    showLattice: true,
    showContacts: true,
    showIndices: !!props.showIndices,
    height,
    registerKeyMap,
    showKeys: kbd && stageFocus,
    modKey,
    ...(play ? {} : { frame: full }),
  };
  let board;
  if (lattice.dim === 2) board = <Svg2D {...rprops} />;
  else if (three.R) {
    const R3 = three.R;
    board = <R3 {...rprops} />;
  } else
    board = (
      <div class="fg-placeholder" style={{ height: cssHeight }}>
        <p>
          {three.state === 'missing' ? 'The 3D view could not be loaded.' : 'Loading the 3D view…'}
        </p>
        {three.state === 'missing' && lattices.includes('square') && (
          <button type="button" class="btn" onClick={() => chooseLattice('square')}>
            Play on the square lattice
          </button>
        )}
      </div>
    );

  const keyHelp = keyHint(lattice, rendererKeys || (dim3 && three.state !== 'missing'));
  const boardLabel =
    props.label ??
    (play
      ? `Folding board, ${lattice.name}. ${keyHelp.map(([k, w]) => `${k}: ${w}`).join('; ')}${keyHelp.length ? '; ' : ''}Backspace: undo.`
      : `Fold on the ${lattice.name}. Left and right arrows step through the letters; space plays.`);

  // ---- header: dimension, lattice, levels ----
  const dims = DIMS.filter((d) => lattices.some((id) => LATTICES[id].dim === d.dim));
  const latsHere = lattices.filter((id) => LATTICES[id].dim === lattice.dim);
  const showLevels = !compact && play && (levelList.length > 0 || custom);
  const head = !compact && play && (lattices.length > 1 || showLevels) && (
    <div class="fg-head">
      {(dims.length > 1 || latsHere.length > 1) && (
        <div class="fg-where">
          {dims.length > 1 && (
            <Choice
              class="fg-dims"
              label="Dimension"
              value={lattice.dim}
              options={dims.map((d) => ({
                value: d.dim,
                content: <span class="fg-dim-label">{d.label}</span>,
              }))}
              onChange={chooseDim}
            />
          )}
          {latsHere.length > 1 && (
            <Choice
              class="fg-lats"
              label={`Lattice (${lattice.dim}D)`}
              value={lattice.id}
              options={latsHere.map((id) => ({ value: id, content: LATTICE_LABEL[id] ?? id, title: LATTICES[id].name }))}
              onChange={chooseLattice}
            />
          )}
        </div>
      )}
      {showLevels && (
        <div class="fg-levels">
          <span class="fg-levels-label" id={`${uid}-levels`}>
            {LATTICE_LABEL[lattice.id]} levels
          </span>
          <Choice
            class="fg-chips"
            labelledby={`${uid}-levels`}
            value={levelId ?? '__own'}
            followFocus={false}
            options={[
              ...latLevels.map((l, i) => ({
                value: l.id,
                content: (
                  <>
                    {i + 1}
                    {solved.has(l.id) && <span class="fg-chip-done" aria-hidden="true" />}
                  </>
                ),
                title: `${l.title}${solved.has(l.id) ? ' (solved)' : ''}`,
                aria: `Level ${i + 1}: ${l.title}${solved.has(l.id) ? ', solved' : ''}`,
                cls: custom && i === latLevels.length - 1 ? 'fg-chip-last' : undefined,
              })),
              ...(custom
                ? [
                    {
                      value: '__own',
                      content: (
                        <>
                          <Icon d="M4 20h4L19 9l-4-4L4 16v4zM13.5 6.5l4 4" />
                          <span>Own string</span>
                        </>
                      ),
                      title: 'Fold a string you type',
                      cls: 'fg-chip-own',
                    },
                  ]
                : []),
            ]}
            onChange={(v) => (v === '__own' ? chooseOwn() : chooseLevel(String(v)))}
          />
        </div>
      )}
    </div>
  );

  // ---- brief: the level's goal, or the own-string form ----
  const brief =
    !compact &&
    play &&
    (active ? (
      <div class="fg-brief" key={active.id}>
        <p class="fg-kicker">
          Level {levelIndex + 1} of {latLevels.length}
          {solved.has(active.id) && <span class="fg-solved"> · solved</span>}
        </p>
        <p class="fg-title">{active.title}</p>
        <p class="fg-goal">{active.intro}</p>
        {active.hint && (
          <details class="fg-hint">
            <summary>Hint</summary>
            <p>{active.hint}</p>
          </details>
        )}
      </div>
    ) : custom && levelId === null ? (
      <div class="fg-brief">
        <p class="fg-kicker">Own string · {lattice.name.replace(/ \(.*\)$/, '').toLowerCase()}</p>
        <form class="fg-own" onSubmit={submitOwn}>
          <label class="visually-hidden" for={`${uid}-own`}>
            HP string
          </label>
          <input
            id={`${uid}-own`}
            type="text"
            inputMode="text"
            autocomplete="off"
            autocapitalize="characters"
            spellcheck={false}
            placeholder="e.g. HPHHPPHH"
            value={own}
            aria-invalid={!!ownError}
            aria-describedby={`${uid}-own-note`}
            onInput={(e) => {
              setOwn((e.currentTarget as HTMLInputElement).value);
              setOwnError(null);
            }}
          />
          <button type="submit" class="btn">
            Fold this string
          </button>
        </form>
        <p class={`fg-own-note${ownError ? ' is-error' : ''}`} id={`${uid}-own-note`} role={ownError ? 'alert' : undefined}>
          {ownError ??
            (known
              ? `This is the string of the level “${known.title}”: ${bestInfo?.optimal ? 'its best fold has' : 'the best known fold has'} ${contacts(known.best)}.`
              : `H and P only, 2 to 200 letters. Solutions are computed here for strings of up to ${SOLVE_MAX[lattice.id]} letters on this lattice.`)}
        </p>
      </div>
    ) : null);

  // ---- the string, the board and the line under it ----
  const strip = (!compact || n <= 64) && (
    <Strip ctrl={ctrl} play={play} locked={replaying} onPick={pickResidue} />
  );

  // the state on the board; on narrow screens (score panel below the board) also the score
  const pill = !play ? null : sol || complete || stuck ? (
    <div class={`fg-pill is-${sol ? 'sol' : stuck ? 'warn' : 'good'}`} aria-hidden="true">
      {sol ? `Solution · ${contacts(score)}` : stuck ? `Stuck · ${contacts(score)}` : `Complete · ${contacts(score)}`}
    </div>
  ) : !compact ? (
    <div class="fg-pill is-score" aria-hidden="true">
      {contacts(score)}
      {best !== undefined && <span class="fg-pill-best"> · best {best}</span>}
    </div>
  ) : null;

  // compact: the score over the board, on the right (narrow screens: in the bar instead)
  const reached = best !== undefined && score >= best;
  const tally = compact && play && (
    <div class={`fg-tally${reached ? ' is-good' : ''}`} aria-hidden="true">
      <div class="fg-tally-row">
        <span class="fg-tally-num">{score}</span>
        {best !== undefined && <span class="fg-tally-of">/ {best}</span>}
      </div>
      <div class="fg-tally-label">{best === undefined && score === 1 ? 'contact' : 'contacts'}</div>
      {best !== undefined && best > 0 && <Meter score={score} best={best} />}
      {reached && <span class="fg-chip-done" />}
    </div>
  );

  const scrubber = !play && (
    <div class="fg-scrub">
      <button type="button" class="btn ghost fg-icon" aria-label="Previous letter" onClick={() => scrubTo(placed - 1)} disabled={placed <= 1}>
        <Icon d="M15 5 8 12l7 7" />
      </button>
      <button type="button" class="btn fg-icon" aria-label={playing ? 'Pause' : 'Play'} onClick={() => setPlaying((p) => !p)}>
        {playing ? <Icon d="M8 5v14M16 5v14" /> : <Icon d="M7 4.5v15l12-7.5z" fill />}
      </button>
      <button
        type="button"
        class="btn ghost fg-icon"
        aria-label="Next letter"
        onClick={() => scrubTo(placed + 1)}
        disabled={placed >= full.length}
      >
        <Icon d="m9 5 7 7-7 7" />
      </button>
      <input
        type="range"
        class="fg-range"
        min={1}
        max={full.length}
        value={placed}
        aria-label="Letters shown"
        onInput={(e) => {
          setPlaying(false);
          scrubTo(Number((e.currentTarget as HTMLInputElement).value));
        }}
      />
      <span class="fg-scrub-count">
        {placed}/{full.length}
      </span>
    </div>
  );

  const solveTitle =
    solInfo.kind === 'none'
      ? solInfo.why
      : solving
        ? 'Searching all folds for the best one'
        : 'Replay a best fold, letter by letter. Your fold is kept.';
  const solveBtn = (cls: string) =>
    play &&
    !sol && (
      <button
        type="button"
        ref={solveRef}
        class={`btn ${cls}`}
        onClick={showSolution}
        disabled={solInfo.kind === 'none' || solving}
        aria-disabled={solInfo.kind === 'none' || solving}
        title={solveTitle}
        aria-describedby={solInfo.kind === 'none' ? `${uid}-nosol` : undefined}
      >
        {solving ? <span class="fg-spin" aria-hidden="true" /> : <Icon d="M4 12h3l3-7 4 14 3-7h3" />}
        <span>{solving ? 'Searching…' : 'Show solution'}</span>
      </button>
    );

  const controlsButton = (
    <button
      type="button"
      ref={controlsBtn}
      class={`btn ghost fg-ctl-btn${controlsOpen ? ' is-on' : ''}`}
      aria-expanded={controlsOpen}
      aria-controls={`${uid}-controls`}
      onClick={() => setControlsOpen((o) => !o)}
      title="All controls (?)"
    >
      <Icon d="M3 7.5A1.5 1.5 0 0 1 4.5 6h15A1.5 1.5 0 0 1 21 7.5v9a1.5 1.5 0 0 1-1.5 1.5h-15A1.5 1.5 0 0 1 3 16.5zM7 10h.01M11 10h.01M15 10h.01M8 14h8" />
      <span class={compact ? 'visually-hidden' : ''}>Controls</span>
    </button>
  );

  const context = play && (
    <div class={`fg-context${sol ? ' is-sol' : ''}`}>
      {sol ? (
        <>
          <p class="fg-context-text">
            <strong>Solution.</strong> {placed < sol.total ? `Letter ${placed} of ${sol.total}.` : `${contacts(sol.score)}, ${sol.optimal ? 'the most possible' : 'the best known'}.`}
            {hint && <> {hint}</>}
          </p>
          <div class="fg-context-actions">
            <button type="button" class="btn primary" onClick={() => leaveSolution('mine')} title="Back to your fold (Esc)">
              <Icon d="M9 14 4 9l5-5M4 9h10.5a5.5 5.5 0 0 1 0 11H11" />
              <span>Back to my fold</span>
            </button>
            <button type="button" class="btn" onClick={() => leaveSolution('reset')}>
              Start over
            </button>
          </div>
        </>
      ) : (
        <>
          <p class="fg-context-text" aria-live="off">
            {hint}
          </p>
          {compact && (
            <div class="fg-context-actions">
              <span class={`fg-bar-score fg-bar-tally${reached ? ' is-good' : ''}`}>
                <strong>{score}</strong> {score === 1 ? 'contact' : 'contacts'}
                {best !== undefined && <span class="fg-bar-best"> · best {best}</span>}
                {reached && <span class="fg-chip-done" aria-hidden="true" />}
              </span>
              <button type="button" class="btn ghost fg-icon fg-undo" aria-label="Undo" title="Undo (Backspace)" onClick={undo} disabled={!ctrl.canUndo}>
                <Icon d="M9 14 4 9l5-5M4 9h10.5a5.5 5.5 0 0 1 0 11H11" />
              </button>
              <button type="button" class="btn ghost fg-icon fg-reset" aria-label="Reset" title="Reset" onClick={reset} disabled={placed <= 1}>
                <Icon d="M3 12a9 9 0 1 0 3-6.7L3 8M3 3v5h5" />
              </button>
              {solveBtn('ghost fg-solve-compact')}
              {controlsButton}
            </div>
          )}
          {!compact && controlsButton}
        </>
      )}
      <ControlsPanel
        id={`${uid}-controls`}
        open={controlsOpen}
        onClose={closeControls}
        anchor={controlsBtn}
        lattice={lattice}
        keys={keyHelp}
        modKey={modKey}
        hasSolution={solInfo.kind !== 'none'}
      />
    </div>
  );

  // ---- the score panel ----
  const side = !compact && (
    <aside class="fg-side" aria-label="Score">
      <div class="fg-score">
        <p class="fg-score-head">
          <span>{sol ? 'Solution' : 'Contacts'}</span>
          <Tip label="What a contact is">
            A contact is a pair of H’s on neighbouring nodes that are not consecutive in the string. Berger and
            Leighton also count the H–H pairs joined by the chain itself ({ctrl.chainBonds} in this string). That
            adds a constant.
          </Tip>
        </p>
        <p class="fg-score-row">
          <span class="fg-score-num">{score}</span>
          {best !== undefined && <span class="fg-score-of">of {best}</span>}
        </p>
        {best !== undefined && best > 0 && <Meter score={score} best={best} />}
      </div>
      <dl class="fg-facts">
        {bestInfo && (
          <div>
            <dt>{bestInfo.optimal ? 'Best possible' : 'Best known'}</dt>
            <dd>
              {bestInfo.value}
              {bestInfo.source && (
                <Tip label="Where this number comes from">
                  {bestInfo.optimal ? 'No fold has more contacts. ' : 'The best score known so far. '}
                  {bestInfo.source}
                </Tip>
              )}
            </dd>
          </div>
        )}
        <div>
          <dt>Upper bound</dt>
          <dd>
            {bound}
            <Tip label="What the upper bound is">{boundText(lattice, seq, boundKind, pairs)}</Tip>
          </dd>
        </div>
      </dl>
      <p class={`fg-status is-${tone}`}>{status}</p>
      {play && !sol && (
        <div class="fg-actions">
          <div class="fg-actions-row">
            <button type="button" class="btn" onClick={undo} disabled={!ctrl.canUndo} title="Undo the last letter (Backspace)">
              <Icon d="M9 14 4 9l5-5M4 9h10.5a5.5 5.5 0 0 1 0 11H11" />
              <span>Undo</span>
            </button>
            <button type="button" class="btn" onClick={reset} disabled={placed <= 1} title="Remove every letter but the first">
              <Icon d="M3 12a9 9 0 1 0 3-6.7L3 8M3 3v5h5" />
              <span>Reset</span>
            </button>
          </div>
          {complete && nextLevel && best !== undefined && score >= best ? (
            <button type="button" class="btn primary fg-wide" onClick={() => chooseLevel(nextLevel.id)}>
              <span>Next level</span>
              <Icon d="m9 5 7 7-7 7" />
            </button>
          ) : null}
          {solveBtn('fg-wide')}
          {solInfo.kind === 'none' && (
            <p class="fg-nosol" id={`${uid}-nosol`}>
              {solInfo.why}
            </p>
          )}
        </div>
      )}
      {share && !sol && (
        <button type="button" class="btn ghost fg-share" onClick={copyLink}>
          <Icon d="M10 14a5 5 0 0 0 7 0l3-3a5 5 0 0 0-7-7l-1 1M14 10a5 5 0 0 0-7 0l-3 3a5 5 0 0 0 7 7l1-1" />
          <span>{copied === 'ok' ? 'Link copied' : copied === 'fail' ? 'The link is in the address bar' : 'Copy a link to this fold'}</span>
        </button>
      )}
    </aside>
  );

  return (
    <div
      class={`fg${compact ? ' fg-compact' : ''}${play ? ' fg-play' : ' fg-view'}${sol ? ' is-solution' : ''}`}
      onKeyDown={onKeyDown}
      data-lattice={lattice.id}
    >
      {init.error && <p class="fg-error">Folding game: {init.error}</p>}
      {head}
      {brief}
      <div class="fg-body">
        <div class="fg-main">
          {strip}
          <div
            ref={stageRef}
            class={`fg-stage${bump ? ' is-bump' : ''}${kbd && stageFocus ? ' is-kbd' : ''}`}
            data-dim={lattice.dim}
            tabIndex={0}
            role="application"
            aria-label={boardLabel}
            aria-roledescription="folding board"
            onPointerDown={() => {
              // the renderers prevent the default (no text selection, no scrolling), so focus here
              setKbd(false);
              pointerFocus.current = true;
              stageRef.current?.focus({ preventScroll: true });
              pointerFocus.current = false;
            }}
            onFocus={(e) => {
              if (e.target !== stageRef.current) return;
              setStageFocus(true);
              try {
                if (!pointerFocus.current && stageRef.current?.matches(':focus-visible')) setKbd(true);
              } catch {
                /* old browsers */
              }
            }}
            onBlur={(e) => e.target === stageRef.current && setStageFocus(false)}
          >
            {board}
            {pill}
            {tally}
          </div>
          {context}
          {!play && (
            <div class="fg-context">
              {scrubber}
              {compact && (
                <span class="fg-bar-score">
                  <strong>{score}</strong> {score === 1 ? 'contact' : 'contacts'}
                </span>
              )}
            </div>
          )}
        </div>
        {side}
      </div>
      <p class="visually-hidden" aria-live="polite">
        {announce}
      </p>
    </div>
  );
}

// ---------------------------------------------------------------------------------------

/** pairs of H's that a contact could join: at least g − 1 apart along the string, where g is
 * the length of the shortest cycle of the lattice, and an odd distance apart on a bipartite
 * lattice (consecutive letters alternate colours) */
function touchablePairs(seq: readonly string[], l: Lattice): number {
  const gap = girthOf(l) - 1;
  let count = 0;
  for (let i = 0; i < seq.length; i++) {
    if (seq[i] !== 'H') continue;
    for (let j = i + gap; j < seq.length; j++) if (seq[j] === 'H' && (!l.bipartite || (j - i) % 2 === 1)) count++;
  }
  return count;
}

type BoundKind = 'shape' | 'pairs' | 'parity';

function boundText(l: Lattice, seq: readonly string[], kind: BoundKind, pairs: number): string {
  const z = degree(l);
  const g = girthOf(l);
  const sides = (k: number) => `${k} free side${k === 1 ? '' : 's'}`;
  const colour = 'Colour the nodes black and white so that neighbours differ, as on a chessboard.';
  if (kind === 'shape') {
    const k = seq.filter((r) => r === 'H').length;
    const most = maxPairs(l, k) ?? 0;
    const chain = chainBonds(seq as ('H' | 'P')[]);
    const H = `${k} H${k === 1 ? '' : '’s'}`;
    const cube = l.id === 'cubic';
    const side = cube ? Math.round(Math.cbrt(k)) : Math.round(Math.sqrt(k));
    const perfect = cube ? side ** 3 === k : side * side === k;
    const shapeName = cube ? `a ${side}×${side}×${side} cube` : `a ${side}×${side} square`;
    const lines = cube ? 'line of the grid' : 'row or column';
    const met = (cube ? 3 : 2) * k - most;
    return (
      `Along each ${lines}, m H’s make at most m − 1 pairs of neighbours, so the fewer ${cube ? 'lines' : 'rows and columns'} the H’s meet, the more pairs they make. ` +
      `${H} meet at least ${met} ${cube ? 'lines' : 'rows and columns'}, so they make at most ${most} pairs` +
      `${perfect && k > 1 ? `, and only ${shapeName} has that many` : ''}. ` +
      (chain > 0
        ? `${chain} of the pairs are neighbours in the string, so at most ${most - chain} are contacts.`
        : 'None of them are neighbours in the string, so all of them can be contacts.')
    );
  }
  if (kind === 'pairs') {
    const such = `This string has ${pairs} such pair${pairs === 1 ? '' : 's'} of H’s.`;
    return l.bipartite
      ? `${colour} Consecutive letters alternate colours, so two H’s can touch only if they are an odd distance apart along the string. The shortest cycle has ${g} nodes, so they must also be at least ${g - 1} apart. ${such}`
      : `The shortest cycle has ${g} nodes, so two H’s can touch only if they are at least ${g - 1} apart along the string. ${such}`;
  }
  return l.bipartite
    ? `Parity bound. ${colour} Consecutive letters alternate colours, so a contact joins an H at an even position to an H at an odd position. Each node has ${z} neighbours, so each H has at most ${sides(z - 2)} (${z - 1} at the ends of the string). The score is at most the smaller of the two totals.`
    : `Each node has ${z} neighbours, so each H has at most ${sides(z - 2)} (${z - 1} at the ends of the string), and each contact uses two. The score is at most half the total.`;
}

/** H or P, coloured */
function Res({ r }: { r: string }) {
  return <b class={`fg-k${r}`}>{r}</b>;
}

/** a key sequence as <kbd> elements ("← ↑ → ↓" → four keys) */
function Keys({ k }: { k: string }) {
  const parts = k.split(' ');
  return (
    <span class="fg-keys">
      {parts.map((p) => (
        <kbd>{p}</kbd>
      ))}
    </span>
  );
}

interface ChoiceOption<T> {
  value: T;
  content: ComponentChildren;
  title?: string;
  aria?: string;
  cls?: string;
}

/**
 * One choice among a few, as a group of buttons with one tab stop (roving tabindex): Tab enters
 * at the chosen one, the arrow keys move between them. followFocus (default): the arrows also
 * choose (a radio group); otherwise Enter or Space chooses (a toolbar, for choices that reset
 * the fold, like levels).
 */
function Choice<T extends string | number>(props: {
  class: string;
  label?: string;
  labelledby?: string;
  value: T;
  options: ChoiceOption<T>[];
  onChange: (v: T) => void;
  followFocus?: boolean;
}) {
  const { options, value, onChange } = props;
  const follow = props.followFocus ?? true;
  const refs = useRef<(HTMLButtonElement | null)[]>([]);
  const chosen = Math.max(
    0,
    options.findIndex((o) => o.value === value),
  );
  const [focusIdx, setFocusIdx] = useState(chosen);
  useEffect(() => setFocusIdx(chosen), [chosen, options.length]);
  const onKey = (e: KeyboardEvent, i: number) => {
    const last = options.length - 1;
    const to =
      e.key === 'ArrowRight' || e.key === 'ArrowDown'
        ? i === last ? 0 : i + 1
        : e.key === 'ArrowLeft' || e.key === 'ArrowUp'
          ? i === 0 ? last : i - 1
          : e.key === 'Home'
            ? 0
            : e.key === 'End'
              ? last
              : -1;
    if (to < 0) return;
    e.preventDefault();
    e.stopPropagation();
    setFocusIdx(to);
    refs.current[to]?.focus();
    if (follow) onChange(options[to].value);
  };
  return (
    <div
      class={props.class}
      role={follow ? 'radiogroup' : 'toolbar'}
      aria-label={props.label}
      aria-labelledby={props.labelledby}
    >
      {options.map((o, i) => {
        const on = o.value === value;
        return (
          <button
            type="button"
            ref={(el) => {
              refs.current[i] = el;
            }}
            class={`fg-opt${on ? ' is-on' : ''}${o.cls ? ` ${o.cls}` : ''}`}
            role={follow ? 'radio' : undefined}
            aria-checked={follow ? on : undefined}
            aria-pressed={follow ? undefined : on}
            aria-label={o.aria}
            title={o.title}
            tabIndex={i === focusIdx ? 0 : -1}
            onClick={() => {
              setFocusIdx(i);
              onChange(o.value);
            }}
            onKeyDown={(e) => onKey(e, i)}
          >
            {o.content}
          </button>
        );
      })}
    </div>
  );
}

/**
 * The string as a row of letters. One tab stop; the arrow keys move between letters.
 * Placed letters before the last are buttons that go back to them (truncate); pointing at one
 * previews what goes (controller.cut).
 */
function Strip({ ctrl, play, locked, onPick }: { ctrl: GameController; play: boolean; locked: boolean; onPick: (i: number) => void }) {
  const seq = ctrl.seq;
  const placed = ctrl.fold.placed;
  const n = seq.length;
  const refs = useRef<(HTMLButtonElement | null)[]>([]);
  // the tab stop: the letter last focused while the strip has focus, else the last placed one
  const [focusIdx, setFocusIdx] = useState<number | null>(null);
  const idx = Math.min(focusIdx ?? Math.max(0, placed - 1), n - 1);
  if (n > 400) return <p class="fg-strip fg-strip-summary">{n} letters</p>;
  const cut = ctrl.cut;
  const active = (i: number) => (play ? !locked && i < placed - 1 : true);
  const point = (i: number | null) => {
    if (!play) return ctrl.setHover(i !== null && i < placed ? i : null);
    ctrl.setHover(i !== null && i < placed ? i : null);
    ctrl.setCut(i !== null && active(i) ? i : null);
  };
  const onKey = (e: KeyboardEvent, i: number) => {
    const to =
      e.key === 'ArrowRight' ? Math.min(n - 1, i + 1) : e.key === 'ArrowLeft' ? Math.max(0, i - 1) : e.key === 'Home' ? 0 : e.key === 'End' ? n - 1 : -1;
    if (to < 0) return;
    e.preventDefault();
    e.stopPropagation();
    setFocusIdx(to);
    refs.current[to]?.focus();
  };
  return (
    <div class={`fg-strip${n > 48 ? ' is-dense' : ''}`} role="toolbar" aria-label="The string, letter by letter">
      {seq.map((r, i) => {
        const state =
          i < placed ? (i === placed - 1 ? ' is-last' : cut !== null && i > cut ? ' is-cut' : '') : i === placed && play && !locked ? ' is-next' : ' is-future';
        const what = !play
          ? 'show the fold up to here'
          : i < placed - 1
            ? locked
              ? 'placed'
              : 'go back to it'
            : i === placed - 1
              ? 'last placed'
              : 'not placed yet';
        return (
          <button
            type="button"
            ref={(el) => {
              refs.current[i] = el;
            }}
            tabIndex={i === idx ? 0 : -1}
            class={`fg-cell is-${r}${state}${ctrl.hover === i ? ' is-hover' : ''}${active(i) ? ' is-active' : ''}`}
            title={`Letter ${i + 1} (${r}): ${what}`}
            aria-label={`Letter ${i + 1}, ${r}, ${what}`}
            aria-disabled={!active(i)}
            onClick={() => active(i) && onPick(i)}
            onKeyDown={(e) => onKey(e, i)}
            onFocus={() => {
              setFocusIdx(i);
              point(i);
            }}
            onBlur={(e) => {
              point(null);
              const to = e.relatedTarget as Node | null;
              if (!to || !refs.current.some((r) => r === to)) setFocusIdx(null);
            }}
            onPointerEnter={(e) => e.pointerType === 'mouse' && point(i)}
            onPointerLeave={(e) => e.pointerType === 'mouse' && point(null)}
          >
            {r}
          </button>
        );
      })}
    </div>
  );
}

/** contacts so far against the best: one segment per contact (a plain bar beyond 40) */
function Meter({ score, best }: { score: number; best: number }) {
  const k = Math.min(score, best);
  if (best > 40)
    return (
      <div class="fg-meter is-bar" aria-hidden="true">
        <span style={{ width: `${(100 * k) / best}%` }} />
      </div>
    );
  return (
    <div class="fg-meter" aria-hidden="true">
      {Array.from({ length: best }, (_, i) => (
        <span class={i < k ? 'is-on' : ''} />
      ))}
    </div>
  );
}

/** the list of every control, in a panel under the board ("Controls" or the ? key) */
function ControlsPanel(props: {
  id: string;
  open: boolean;
  onClose: (refocus: boolean) => void;
  anchor: { current: HTMLElement | null };
  lattice: Lattice;
  keys: [string, string][];
  modKey: string;
  hasSolution: boolean;
}) {
  const { open, onClose, lattice, keys, modKey } = props;
  const ref = useRef<HTMLDivElement>(null);
  useEffect(() => {
    if (!open) return;
    ref.current?.focus({ preventScroll: true });
    const away = (e: PointerEvent) => {
      const t = e.target as Node;
      if (!ref.current?.contains(t) && !props.anchor.current?.contains(t)) onClose(false);
    };
    document.addEventListener('pointerdown', away);
    return () => document.removeEventListener('pointerdown', away);
  }, [open]);
  if (!open) return null;
  const d3 = lattice.dim === 3;
  return (
    <div
      ref={ref}
      id={props.id}
      class="fg-pop"
      role="dialog"
      aria-label="Controls"
      tabIndex={-1}
      onKeyDown={(e) => {
        if (e.key === 'Escape') {
          e.preventDefault();
          e.stopPropagation();
          onClose(true);
        }
      }}
    >
      <div class="fg-pop-head">
        <p>Controls</p>
        <button type="button" class="btn ghost fg-icon" aria-label="Close" onClick={() => onClose(true)}>
          <Icon d="M6 6l12 12M18 6 6 18" />
        </button>
      </div>
      <dl class="fg-ctl">
        <dt>Place the next letter</dt>
        <dd>
          Click or tap a highlighted node.{!d3 && ' Drag through several nodes to place them in a row.'}
          {keys.map(([k, w]) => (
            <span class="fg-ctl-keys">
              <Keys k={k} /> {w}
            </span>
          ))}
          {d3 && lattice.steps.length > 6 && (
            <span class="fg-ctl-keys">
              <Keys k="⇧" /> with the same keys: the other six directions
            </span>
          )}
          {d3 && <span class="fg-ctl-note">While you use the keys, each highlighted node shows its key.</span>}
        </dd>
        <dt>Undo</dt>
        <dd>
          The Undo button, <Keys k="⌫" /> or <Keys k={`${modKey} Z`} />.{!d3 && ' Or drag back onto the previous letter.'}
        </dd>
        <dt>Go back to a letter</dt>
        <dd>
          {modKey}-click it on the board, or click it in the string above the board. On a touch screen, tap it
          twice.
        </dd>
        {d3 && (
          <>
            <dt>Turn the view</dt>
            <dd>
              Drag. Scroll or pinch to zoom; drag with the right button or two fingers to move. The button in the
              corner of the view resets it.
            </dd>
          </>
        )}
        {props.hasSolution && (
          <>
            <dt>Solution</dt>
            <dd>
              Show solution replays a best fold. You can then change it like your own fold, or press <Keys k="Esc" /> to return to your fold.
            </dd>
          </>
        )}
        <dt>This list</dt>
        <dd>
          <Keys k="?" /> opens and closes it.
        </dd>
      </dl>
    </div>
  );
}

/** an (i) with a short explanation on hover or focus */
function Tip({ label, children }: { label: string; children: ComponentChildren }) {
  return (
    <span class="fg-tip" tabIndex={0} aria-label={label} role="button">
      <span class="fg-tip-i" aria-hidden="true">
        i
      </span>
      <span class="fg-tip-body" role="tooltip">
        {children}
      </span>
    </span>
  );
}

function Icon({ d, fill }: { d: string; fill?: boolean }) {
  return (
    <svg class="fg-ico" viewBox="0 0 24 24" width="16" height="16" aria-hidden="true">
      <path
        d={d}
        fill={fill ? 'currentColor' : 'none'}
        stroke="currentColor"
        stroke-width="1.8"
        stroke-linecap="round"
        stroke-linejoin="round"
      />
    </svg>
  );
}
