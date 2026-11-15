/** @jsxImportSource preact */
/**
 * BinPack: the bin-packing game (an Astro island), the problem Berger and Leighton reduce from.
 *
 *   <BinPack client:load />                       all levels
 *   <BinPack client:visible level="three-sixes" levels={['three-sixes']} />
 *
 * It looks and works like the folding game (fold-game/FoldGame.tsx) and reuses its styles
 * (fold-game/styles.css, classes fg-), so a reader learns one interface:
 *   header   level chips
 *   brief    the level's title, goal and hint
 *   body     [board: the loose items, then the bins; the line under it] | [panel: packed, facts, actions]
 * The board's own styles are in styles.css (classes bp-). The state lives in a PackController
 * (engine/controller.ts); "Show solution" uses the level's stored packing or the exact solver
 * (engine/solve.ts), which for a "no" instance shows the most that fits.
 *
 * Moving items: click an item, then a bin; or drag it there. ⌘/Ctrl-click (touch: a second tap)
 * takes an item back out, as does dragging it back to the items. Keys: Tab to the items, ← → between
 * them, 1 to K puts the focused item into that bin, 0 takes it out, ⌫ or ⌘Z undoes.
 */
import { useEffect, useId, useLayoutEffect, useMemo, useRef, useState } from 'preact/hooks';
import type { ComponentChildren } from 'preact';
import { PackController } from './engine/controller.ts';
import type { Assignment, Instance, PackState } from './engine/pack.ts';
import { solve, type SolveResult } from './engine/solve.ts';
import { LEVELS, getLevel, instanceOf, type Level } from './levels/index.ts';
import { itemColor, itemPattern } from './colors.ts';
import { isApple } from '../fold-game/keys.ts';
import { Choice, ICON, Icon, Keys, Tip } from './ui.tsx';
import '../fold-game/styles.css';
import './styles.css';

export interface BinPackProps {
  /** show the levels: true (default) = all levels, or a list of level ids */
  levels?: boolean | string[];
  /** level to start with (id); default: the first */
  level?: string;
}

const STORE_KEY = 'hp-bin-pack.solved';
const reducedMotion = () => typeof matchMedia === 'function' && matchMedia('(prefers-reduced-motion: reduce)').matches;

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

/** bin contents from an assignment, each bin in item order */
const contentsOf = (inst: Instance, a: Assignment): number[][] => {
  const c: number[][] = Array.from({ length: inst.bins }, () => []);
  a.forEach((b, u) => b !== null && b !== undefined && c[b].push(u));
  return c;
};
/** "1", "1 and 2", "1, 2 and 3" */
const andList = (xs: (string | number)[]) =>
  xs.length <= 1 ? `${xs[0] ?? ''}` : `${xs.slice(0, -1).join(', ')} and ${xs[xs.length - 1]}`;
const items = (k: number) => `${k} item${k === 1 ? '' : 's'}`;

/** the best packing of a level: its stored one, else the solver's */
function solutionOf(level: Level | undefined, inst: Instance): SolveResult {
  if (level?.solution) {
    const total = inst.bins * inst.capacity;
    return { assignment: level.solution, packed: total, complete: true, exhaustive: true, nodes: 0 };
  }
  return solve(inst);
}

interface Drag {
  u: number;
  x: number;
  y: number;
  w: number;
  h: number;
  /** what is under the pointer: a bin, the loose items, or nothing */
  over: number | 'tray' | null;
}

// ---------------------------------------------------------------------------------------

export default function BinPack(props: BinPackProps) {
  const levelList = useMemo<Level[]>(() => {
    if (Array.isArray(props.levels)) return props.levels.map((id) => getLevel(id)).filter((l): l is Level => !!l);
    return LEVELS;
  }, []);
  // state, not a memo: a hot reload re-runs memos but keeps state, and the controller must stay
  // in step with levelId
  const [init] = useState(() => {
    const start = getLevel(props.level) ?? levelList[0];
    return { ctrl: new PackController(instanceOf(start)), levelId: start.id };
  });
  const ctrl = init.ctrl;
  const [, setTick] = useState(0);
  useEffect(() => ctrl.subscribe((c) => setTick(c.version)), [ctrl]);

  const [levelId, setLevelId] = useState(init.levelId);
  const [solved, setSolved] = useState<Set<string>>(() => new Set());
  const [revealed, setRevealed] = useState<Set<string>>(() => new Set());
  /** solution mode: the reader's own packing is kept in `saved` and restored on leaving */
  const [sol, setSol] = useState<null | { saved: number[][]; result: SolveResult; total: number }>(null);
  /** the reader's "Answer no", valid until the next change of the bins */
  const [claim, setClaim] = useState<null | { right: boolean; version: number }>(null);
  /** why the last move was refused, valid until the next change */
  const [notice, setNotice] = useState<null | { text: string; version: number }>(null);
  const [drag, setDrag] = useState<Drag | null>(null);
  const [bump, setBump] = useState(0);
  const [controlsOpen, setControlsOpen] = useState(false);
  const [undoStreak, setUndoStreak] = useState(0);
  /** the item that has the keyboard focus (after Tab or the arrows, not after a click) */
  const [kbdItem, setKbdItem] = useState<number | null>(null);
  /** roving tab stops: the item last focused in the loose items and in each bin */
  const [stops, setStops] = useState<Record<string, number>>({});
  const [env, setEnv] = useState({ coarse: false, apple: false });
  useEffect(() => {
    const mq = typeof matchMedia === 'function' ? matchMedia('(pointer: coarse)') : null;
    const update = () => setEnv({ coarse: !!mq?.matches, apple: isApple() });
    update();
    mq?.addEventListener?.('change', update);
    setSolved(loadSolved());
    return () => mq?.removeEventListener?.('change', update);
  }, []);

  const uid = useId();
  const rootRef = useRef<HTMLDivElement>(null);
  const controlsBtn = useRef<HTMLButtonElement>(null);
  const solveRef = useRef<HTMLButtonElement>(null);
  const animRef = useRef<ReturnType<typeof setInterval> | null>(null);
  const dragRef = useRef<null | { u: number; x0: number; y0: number; dx: number; dy: number; w: number; h: number; id: number; active: boolean }>(null);
  const suppressClick = useRef(false);
  /** after a key moves an item, the item to focus once the board is redrawn */
  const pendingFocus = useRef<number | null>(null);

  const inst = ctrl.inst;
  const st: PackState = ctrl.state;
  const { bins: K, capacity: B, sizes } = inst;
  const m = sizes.length;
  const goal = K * B;
  const packed = st.packed();
  const loose = st.loose();
  const complete = st.complete;
  const stuck = st.stuck;
  const selected = ctrl.selected;
  const level = getLevel(levelId);
  const levelIndex = level ? levelList.indexOf(level) : -1;
  const nextLevel = levelIndex >= 0 ? levelList[levelIndex + 1] : undefined;
  const solution = useMemo(() => solutionOf(level, inst), [levelId]);
  const claimNow = claim && claim.version === ctrl.version ? claim : null;
  const noticeNow = notice && notice.version === ctrl.version ? notice.text : null;
  /** the item being moved: dragged, or picked up by a click */
  const moving = drag?.u ?? selected;

  // ---- actions ----
  const flash = () => setBump((b) => b + 1);
  useEffect(() => {
    if (!bump) return;
    const t = setTimeout(() => setBump(0), 260);
    return () => clearTimeout(t);
  }, [bump]);

  /** put item u into bin b, or say why it does not fit */
  const tryPlace = (u: number, b: number): boolean => {
    if (st.binOf(u) === b) {
      ctrl.select(null);
      return true;
    }
    if (ctrl.place(u, b)) return true;
    flash();
    const free = st.free(b);
    setNotice({
      text: `The ${sizes[u]} does not fit in bin ${b + 1}: ${free === 0 ? 'it is full' : `it has ${free} free`}.`,
      version: ctrl.version,
    });
    return false;
  };
  const takeOut = (u: number) => ctrl.remove(u);
  const undo = () => {
    if (ctrl.undo()) setUndoStreak((s) => s + 1);
    else flash();
  };
  const reset = () => {
    ctrl.reset();
    setUndoStreak(0);
  };
  const prevPacked = useRef(packed);
  useEffect(() => {
    if (packed > prevPacked.current) setUndoStreak(0);
    prevPacked.current = packed;
  }, [packed]);

  const reveal = (id: string) => setRevealed((r) => (r.has(id) ? r : new Set(r).add(id)));
  const markSolved = (id: string) => {
    if (solved.has(id)) return;
    const next = new Set(solved).add(id);
    setSolved(next);
    saveSolved(next);
  };

  // ---- solution mode ----
  const stopAnim = () => {
    if (animRef.current) clearInterval(animRef.current);
    animRef.current = null;
  };
  useEffect(() => () => stopAnim(), []);
  const leaveSolution = (to: 'mine' | 'reset' | 'keep') => {
    stopAnim();
    if (!sol) return;
    if (to !== 'keep') ctrl.load(sol.saved);
    if (to === 'reset') ctrl.reset();
    setSol(null);
    if (to !== 'keep' && rootRef.current?.contains(document.activeElement))
      requestAnimationFrame(() => solveRef.current?.focus({ preventScroll: true }));
  };
  const showSolution = () => {
    const r = solution;
    const target = contentsOf(inst, r.assignment);
    const steps: [number, number][] = [];
    r.assignment.forEach((b, u) => b !== null && steps.push([u, b]));
    setSol({ saved: sol?.saved ?? ctrl.snapshot(), result: r, total: steps.length });
    setDrag(null);
    if (level) reveal(level.id);
    stopAnim();
    if (reducedMotion()) return ctrl.load(target);
    ctrl.load(Array.from({ length: K }, () => []));
    let i = 0;
    const dt = Math.max(220, Math.min(420, 2400 / Math.max(1, steps.length)));
    animRef.current = setInterval(() => {
      if (i >= steps.length) return stopAnim();
      const c = ctrl.snapshot();
      c[steps[i][1]].push(steps[i][0]);
      i++;
      ctrl.load(c);
    }, dt);
  };
  const answerNo = () => {
    if (!level) return;
    const right = solution.exhaustive && !solution.complete;
    setClaim({ right, version: ctrl.version });
    reveal(level.id);
    if (right) markSolved(level.id);
  };

  const chooseLevel = (id: string) => {
    const lv = getLevel(id);
    if (!lv) return;
    leaveSolution('keep');
    setLevelId(id);
    setDrag(null);
    setClaim(null);
    setNotice(null);
    setUndoStreak(0);
    setStops({});
    ctrl.setInstance(instanceOf(lv));
  };

  // ---- progress: a "yes" level counts as solved when the reader packs every item ----
  useEffect(() => {
    if (sol || !level || !complete) return;
    reveal(level.id);
    markSolved(level.id);
  }, [ctrl.version, !!sol]);

  // ---- focus after a key moved an item (before the next key press, hence a layout effect) ----
  useLayoutEffect(() => {
    const u = pendingFocus.current;
    if (u === null) return;
    pendingFocus.current = null;
    const el = rootRef.current?.querySelector<HTMLElement>(`[data-item="${u}"]`);
    el?.focus({ preventScroll: false });
  }, [ctrl.version]);

  // ---- dragging (pointer events; a short move is a click) ----
  const hitTest = (x: number, y: number): Drag['over'] => {
    const el = document.elementFromPoint(x, y);
    if (!el || !rootRef.current?.contains(el)) return null;
    const bin = el.closest<HTMLElement>('[data-bin]');
    if (bin) return Number(bin.dataset.bin);
    return el.closest('[data-tray]') ? 'tray' : null;
  };
  const onPointerDown = (e: PointerEvent, u: number) => {
    suppressClick.current = false;
    if (sol || e.button !== 0) return;
    const el = e.currentTarget as HTMLElement;
    const r = el.getBoundingClientRect();
    dragRef.current = { u, x0: e.clientX, y0: e.clientY, dx: e.clientX - r.left, dy: e.clientY - r.top, w: r.width, h: r.height, id: e.pointerId, active: false };
    try {
      el.setPointerCapture(e.pointerId);
    } catch {
      /* not capturable (synthetic event) */
    }
  };
  const onPointerMove = (e: PointerEvent) => {
    const d = dragRef.current;
    if (!d || e.pointerId !== d.id) return;
    if (!d.active) {
      if (Math.hypot(e.clientX - d.x0, e.clientY - d.y0) < 6) return;
      d.active = true;
      setKbdItem(null);
    }
    e.preventDefault();
    setDrag({ u: d.u, x: e.clientX - d.dx, y: e.clientY - d.dy, w: d.w, h: d.h, over: hitTest(e.clientX, e.clientY) });
  };
  const onPointerUp = (e: PointerEvent) => {
    const d = dragRef.current;
    if (!d || e.pointerId !== d.id) return;
    dragRef.current = null;
    if (!d.active) return; // a click: onClick handles it
    suppressClick.current = true;
    setDrag(null);
    const over = hitTest(e.clientX, e.clientY);
    if (typeof over === 'number') tryPlace(d.u, over);
    else if (over === 'tray' && st.binOf(d.u) !== null) takeOut(d.u);
  };
  const onPointerCancel = () => {
    dragRef.current = null;
    setDrag(null);
  };

  // ---- clicks ----
  const onItemClick = (e: MouseEvent, u: number) => {
    e.stopPropagation();
    if (suppressClick.current) {
      suppressClick.current = false;
      return;
    }
    if (sol) return;
    if (st.binOf(u) !== null) {
      // in a bin: ⌘/Ctrl-click or a second click takes it out; a first click picks it up
      if (e.metaKey || e.ctrlKey || selected === u) takeOut(u);
      else ctrl.select(u);
      return;
    }
    ctrl.select(selected === u ? null : u);
  };
  const onBinClick = (b: number) => {
    if (sol || selected === null) return;
    tryPlace(selected, b);
  };
  const onTrayClick = () => {
    if (sol || selected === null) return;
    if (st.binOf(selected) !== null) takeOut(selected);
    else ctrl.select(null);
  };

  // ---- keyboard ----
  const closeControls = (refocus: boolean) => {
    setControlsOpen(false);
    if (refocus) controlsBtn.current?.focus();
  };
  const onKeyDown = (e: KeyboardEvent) => {
    const t = e.target as HTMLElement;
    if (/^(INPUT|SELECT|TEXTAREA)$/.test(t.tagName)) return;
    const k = e.key;
    if (k === 'Escape') {
      if (controlsOpen) closeControls(true);
      else if (sol) leaveSolution('mine');
      else if (selected !== null) ctrl.select(null);
      else return;
      e.preventDefault();
      return;
    }
    if (k === '?' && !e.metaKey && !e.ctrlKey) {
      e.preventDefault();
      setControlsOpen((o) => !o);
      return;
    }
    if (sol) return;
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
    const itemEl = t.closest?.<HTMLElement>('[data-item]');
    const u = itemEl ? Number(itemEl.dataset.item) : selected;
    if (u === null || !(/^[0-9]$/.test(k) || k === 'Delete')) return;
    e.preventDefault();
    if (k === '0' || k === 'Delete') {
      if (st.binOf(u) === null) return flash();
      if (itemEl) pendingFocus.current = u;
      takeOut(u);
      return;
    }
    const b = Number(k) - 1;
    if (b >= K) return flash();
    const wasLoose = st.binOf(u) === null;
    // from the loose items, the focus moves on to the next loose item; otherwise it follows the item
    const after = wasLoose ? (loose.find((v) => v > u) ?? [...loose].reverse().find((v) => v < u) ?? u) : u;
    if (tryPlace(u, b) && itemEl) pendingFocus.current = after;
  };
  /** the arrows move between the items of one group (the loose items, or one bin) */
  const onItemKey = (e: KeyboardEvent) => {
    if (!['ArrowLeft', 'ArrowRight', 'ArrowUp', 'ArrowDown', 'Home', 'End'].includes(e.key)) return;
    const el = e.currentTarget as HTMLElement;
    const group = el.closest('[data-rove]');
    if (!group) return;
    const list = [...group.querySelectorAll<HTMLElement>('[data-item]')];
    const i = list.indexOf(el);
    const to =
      e.key === 'Home' ? 0 : e.key === 'End' ? list.length - 1 : e.key === 'ArrowLeft' || e.key === 'ArrowUp' ? i - 1 : i + 1;
    if (to < 0 || to >= list.length) return;
    e.preventDefault();
    e.stopPropagation();
    list[to].focus();
  };
  const onItemFocus = (e: FocusEvent, u: number, group: string) => {
    setStops((s) => (s[group] === u ? s : { ...s, [group]: u }));
    let visible = false;
    try {
      visible = (e.currentTarget as HTMLElement).matches(':focus-visible');
    } catch {
      /* old browsers */
    }
    setKbdItem(visible ? u : null);
  };
  const onItemBlur = () => setKbdItem(null);

  // ---- words that depend on the device ----
  const coarse = env.coarse;
  const modKey = env.apple ? '⌘' : 'Ctrl';
  const click = coarse ? 'Tap' : 'Click';
  const takeOutHow = coarse ? 'tap an item in a bin twice to take it back out' : `${modKey}-click an item in a bin to take it back out`;
  const cap = (s: string) => s.charAt(0).toUpperCase() + s.slice(1);
  const fitsIn = (u: number) => Array.from({ length: K }, (_, b) => b).filter((b) => st.binOf(u) !== b && st.fits(u, b));

  // ---- status (panel) ----
  const placedCount = m - loose.length;
  const solDone = !!sol && placedCount >= sol.total;
  let tone: 'info' | 'good' | 'warn' | 'sol' = 'info';
  let status: ComponentChildren;
  if (sol) {
    tone = 'sol';
    status = solDone ? 'Your own packing is kept. “Back to my attempt” returns to it.' : `Placing item ${placedCount} of ${sol.total}.`;
  } else if (claimNow) {
    tone = claimNow.right ? 'good' : 'warn';
    status = claimNow.right
      ? `Correct: no packing exists. ${level?.why ?? ''}`
      : 'A packing exists. Keep looking, or show the solution.';
  } else if (noticeNow) {
    tone = 'warn';
    status = noticeNow;
  } else if (complete) {
    tone = 'good';
    status = 'Complete. Every bin is full.';
  } else if (stuck) {
    tone = 'warn';
    status = 'Stuck. No item left fits in the free space.';
  } else if (selected !== null) {
    const f = fitsIn(selected);
    status = `The ${sizes[selected]} is picked up. ${f.length ? `It fits in bin ${andList(f.map((b) => b + 1))}.` : 'It fits in no other bin.'}`;
  } else
    status =
      packed === 0
        ? `${cap(items(m))} of total size ${goal}, for ${K} bins of ${B}.`
        : `${cap(items(loose.length))} left, of total size ${goal - packed}.`;

  // ---- context line (under the board) ----
  let hint: ComponentChildren = null;
  if (drag) {
    hint =
      drag.over === 'tray'
        ? st.binOf(drag.u) !== null
          ? `Drop to take the ${sizes[drag.u]} out.`
          : 'Drop it on a bin.'
        : typeof drag.over === 'number'
          ? st.fits(drag.u, drag.over)
            ? `Drop to put the ${sizes[drag.u]} in bin ${drag.over + 1}.`
            : `The ${sizes[drag.u]} does not fit in bin ${drag.over + 1}.`
          : 'Drop it on a bin.';
  } else if (kbdItem !== null) {
    const inBin = st.binOf(kbdItem) !== null;
    hint = (
      <>
        Press <Keys k="1" />
        {K > 1 && (
          <>
            {' '}
            {K === 2 ? 'or' : 'to'} <Keys k={String(K)} />
          </>
        )}{' '}
        to put the {sizes[kbdItem]} in {K === 1 ? 'the' : 'that'} bin{inBin && (
          <>
            , or <Keys k="0" /> to take it out
          </>
        )}
        .
      </>
    );
  } else if (selected !== null) {
    const f = fitsIn(selected);
    hint =
      st.binOf(selected) !== null
        ? `${click} another bin to move the ${sizes[selected]}, or ${click.toLowerCase()} it again to take it out.`
        : f.length
          ? `${click} a highlighted bin to put the ${sizes[selected]} there.`
          : `The ${sizes[selected]} fits in no bin. Take an item out first.`;
  } else if (stuck)
    hint = (
      <>
        Undo{!coarse && (
          <>
            {' '}
            (<Keys k="⌫" />)
          </>
        )}
        , or {takeOutHow}.
      </>
    );
  else if (complete) hint = `${cap(takeOutHow)} and try another packing.`;
  else if (packed === 0) hint = `${click} an item, then a bin. Or drag the item into the bin.`;
  else if (undoStreak >= 2) hint = `${cap(takeOutHow)} in one step.`;
  else hint = `${cap(takeOutHow)}, or drag it to another bin.`;

  // ---- polite announcements, after a pause ----
  const message = sol
    ? solDone
      ? sol.result.complete
        ? `Solution shown. ${binsText(inst, st)}. Escape returns to your packing.`
        : `No packing exists. The most that fits is ${sol.result.packed} of ${goal}. Escape returns to your packing.`
      : ''
    : `${typeof status === 'string' ? status : ''} Packed ${packed} of ${goal}.`;
  const [announce, setAnnounce] = useState('');
  const quietUntil = useRef(ctrl.version);
  useEffect(() => {
    if (!message || ctrl.version <= quietUntil.current) return;
    const t = setTimeout(() => setAnnounce(message), 450);
    return () => clearTimeout(t);
  }, [message]);

  // ---- header and brief ----
  const head = levelList.length > 1 && (
    <div class="fg-head">
      <div class="fg-levels">
        <span class="fg-levels-label" id={`${uid}-levels`}>
          Levels
        </span>
        <Choice
          class="fg-chips"
          labelledby={`${uid}-levels`}
          value={levelId}
          options={levelList.map((l, i) => ({
            value: l.id,
            content: (
              <>
                {i + 1}
                {solved.has(l.id) && <span class="fg-chip-done" aria-hidden="true" />}
              </>
            ),
            title: `${l.title}${solved.has(l.id) ? ' (solved)' : ''}`,
            aria: `Level ${i + 1}: ${l.title}${solved.has(l.id) ? ', solved' : ''}`,
          }))}
          onChange={(v) => chooseLevel(String(v))}
        />
      </div>
    </div>
  );
  const brief = level && (
    <div class="fg-brief" key={level.id}>
      <p class="fg-kicker">
        Level {levelIndex + 1} of {levelList.length}
        {solved.has(level.id) && <span class="fg-solved"> · solved</span>}
      </p>
      <p class="fg-title">{level.title}</p>
      <p class="fg-goal">{level.intro}</p>
      {level.hint && (
        <details class="fg-hint">
          <summary>Hint</summary>
          <p>{level.hint}</p>
        </details>
      )}
    </div>
  );

  // ---- the board ----
  const pill = sol ? (
    <div class="fg-pill is-sol" aria-hidden="true">
      {sol.result.complete ? `Solution · ${packed} of ${goal}` : `No packing · ${packed} of ${goal} fit`}
    </div>
  ) : complete ? (
    <div class="fg-pill is-good" aria-hidden="true">
      Complete · every bin full
    </div>
  ) : stuck ? (
    <div class="fg-pill is-warn" aria-hidden="true">
      Stuck · {packed} of {goal}
    </div>
  ) : (
    <div class="fg-pill is-score" aria-hidden="true">
      {packed} of {goal} packed
    </div>
  );

  const playable = !sol;
  const item = (u: number, group: string, tabStop: boolean) => {
    const inBin = st.binOf(u);
    const lifted = drag?.u === u;
    const where = inBin === null ? 'not in a bin' : `in bin ${inBin + 1}`;
    const act = !playable
      ? ''
      : inBin === null
        ? selected === u
          ? 'picked up'
          : `press 1${K > 1 ? ` ${K === 2 ? 'or' : 'to'} ${K}` : ''} to put it in a bin`
        : `press 0 to take it out`;
    return (
      <button
        type="button"
        key={u}
        data-item={u}
        class={`bp-item bp-pat-${itemPattern(u)}${selected === u ? ' is-selected' : ''}${lifted ? ' is-lifted' : ''}`}
        style={`--c:${itemColor(u)};--n:${sizes[u]}`}
        tabIndex={playable && tabStop ? 0 : -1}
        aria-pressed={playable ? selected === u : undefined}
        aria-disabled={!playable}
        aria-label={`Item ${u + 1}, size ${sizes[u]}, ${where}${act ? `; ${act}` : ''}`}
        title={`Item ${u + 1}, size ${sizes[u]}`}
        onPointerDown={(e) => onPointerDown(e, u)}
        onPointerMove={onPointerMove}
        onPointerUp={onPointerUp}
        onPointerCancel={onPointerCancel}
        onClick={(e) => onItemClick(e, u)}
        onKeyDown={onItemKey}
        onFocus={(e) => onItemFocus(e, u, group)}
        onBlur={onItemBlur}
      >
        <span class="bp-size">{sizes[u]}</span>
      </button>
    );
  };

  const looseStop = loose.includes(stops.tray) ? stops.tray : loose[0];
  const trayOver = drag?.over === 'tray' && st.binOf(drag.u) !== null;
  const trayTarget = moving !== null && st.binOf(moving) !== null;
  const tray = (
    <div
      class={`bp-tray${trayTarget ? ' is-target' : ''}${trayOver ? ' is-over' : ''}`}
      data-tray=""
      onClick={onTrayClick}
    >
      <div class="bp-row-head">
        <span class="bp-label" id={`${uid}-items`}>
          Items
        </span>
        {pill}
      </div>
      <div class="bp-items" role="toolbar" aria-labelledby={`${uid}-items`} data-rove="tray">
        {sizes.map((s, u) =>
          st.binOf(u) === null ? (
            item(u, 'tray', u === looseStop)
          ) : (
            <span key={`slot-${u}`} class="bp-slot" style={`--n:${s}`} aria-hidden="true" title={`Item ${u + 1} is in bin ${(st.binOf(u) ?? 0) + 1}`}>
              {s}
            </span>
          ),
        )}
        {loose.length === 0 && <span class="visually-hidden">Every item is in a bin.</span>}
      </div>
    </div>
  );

  const bins = Array.from({ length: K }, (_, b) => {
    const contents = st.contents[b];
    const load = st.load(b);
    const full = load === B;
    const ghost = moving !== null && st.binOf(moving) !== b && st.fits(moving, b) && playable;
    const blocked = moving !== null && st.binOf(moving) !== b && !st.fits(moving, b);
    const over = drag?.over === b;
    const stop = contents.includes(stops[`bin${b}`]) ? stops[`bin${b}`] : contents[0];
    return (
      <div
        key={b}
        class={`bp-bin${full ? ' is-full' : ''}${ghost ? ' is-target' : ''}${blocked ? ' is-blocked' : ''}${over ? (ghost ? ' is-over' : ' is-refuse') : ''}`}
        data-bin={b}
        role="group"
        aria-label={`Bin ${b + 1}: ${load} of ${B}${full ? ', full' : ''}`}
        onClick={() => onBinClick(b)}
      >
        <div class="bp-row-head">
          <span class="bp-label">
            Bin {b + 1}
            {kbdItem !== null && <kbd class="bp-key">{b + 1}</kbd>}
          </span>
          <span class="bp-load">
            {full ? (
              <>
                <span class="bp-check" aria-hidden="true" />
                full
              </>
            ) : (
              <>
                {load} of {B}
              </>
            )}
          </span>
        </div>
        <div class="bp-track" data-rove={`bin${b}`}>
          {contents.map((u) => item(u, `bin${b}`, u === stop))}
          {ghost && moving !== null && (
            <span class={`bp-ghost bp-pat-${itemPattern(moving)}`} style={`--c:${itemColor(moving)};--n:${sizes[moving]}`} aria-hidden="true" />
          )}
        </div>
      </div>
    );
  });

  // ---- the line under the board ----
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
      <Icon d={ICON.keyboard} />
      <span>Controls</span>
    </button>
  );
  const context = (
    <div class={`fg-context${sol ? ' is-sol' : ''}`}>
      {sol ? (
        <>
          <p class="fg-context-text">
            {!solDone ? (
              <>
                <strong>Solution.</strong> Item {placedCount} of {sol.total}.
              </>
            ) : sol.result.complete ? (
              <>
                <strong>Solution.</strong> {binsText(inst, st)}.
              </>
            ) : (
              <>
                <strong>No packing exists.</strong> {level?.why ? `${level.why} ` : ''}The bins show the most that fits:{' '}
                {sol.result.packed} of {goal}.
              </>
            )}
          </p>
          <div class="fg-context-actions">
            <button type="button" class="btn primary" onClick={() => leaveSolution('mine')} title="Back to your packing (Esc)">
              <Icon d={ICON.undo} />
              <span>Back to my attempt</span>
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
          {controlsButton}
        </>
      )}
      <ControlsPanel
        id={`${uid}-controls`}
        open={controlsOpen}
        onClose={closeControls}
        anchor={controlsBtn}
        bins={K}
        modKey={modKey}
      />
    </div>
  );

  // ---- the panel ----
  const answer = level && revealed.has(level.id) ? level.answer : null;
  const side = (
    <aside class="fg-side" aria-label="Progress">
      <div class="fg-score">
        <p class="fg-score-head">
          <span>{sol ? 'Solution' : 'Packed'}</span>
          <Tip label="What packed counts">
            The total size of the items in bins. A packing fills every bin exactly, so it packs all {goal}.
          </Tip>
        </p>
        <p class="fg-score-row">
          <span class="fg-score-num">{packed}</span>
          <span class="fg-score-of">of {goal}</span>
        </p>
        <BinMeter st={st} />
      </div>
      <dl class="fg-facts">
        <div>
          <dt>Bins</dt>
          <dd>{K}</dd>
        </div>
        <div>
          <dt>Capacity</dt>
          <dd>{B}</dd>
        </div>
        <div>
          <dt>Items</dt>
          <dd>
            {m}
            <Tip label="About the sizes">
              The sizes add up to {sizes.join(' + ')} = {goal} = {K} × {B}, so a packing leaves no free space. Berger and
              Leighton also make every size even: the string writes an item of size s as s/2 copies of PHHP.
            </Tip>
          </dd>
        </div>
        {answer && (
          <div>
            <dt>Packing exists</dt>
            <dd>
              {answer === 'yes' ? 'Yes' : 'No'}
              {answer === 'no' && level?.why && <Tip label="Why no packing exists">{level.why}</Tip>}
            </dd>
          </div>
        )}
      </dl>
      <p class={`fg-status is-${tone}`}>{status}</p>
      {!sol && (
        <div class="fg-actions">
          <div class="fg-actions-row">
            <button type="button" class="btn" onClick={undo} disabled={!ctrl.canUndo} title="Undo the last move (Backspace)">
              <Icon d={ICON.undo} />
              <span>Undo</span>
            </button>
            <button type="button" class="btn" onClick={reset} disabled={packed === 0} title="Take every item out">
              <Icon d={ICON.reset} />
              <span>Reset</span>
            </button>
          </div>
          {nextLevel && (complete || claimNow?.right || (level?.answer === 'no' && solved.has(level.id))) ? (
            <button type="button" class="btn primary fg-wide" onClick={() => chooseLevel(nextLevel.id)}>
              <span>Next level</span>
              <Icon d={ICON.next} />
            </button>
          ) : null}
          <button
            type="button"
            ref={solveRef}
            class="btn fg-wide"
            onClick={showSolution}
            title="Show a packing, or the most that fits if there is none. Your packing is kept."
          >
            <Icon d={ICON.solve} />
            <span>Show solution</span>
          </button>
          {level && !complete && (
            <button type="button" class="btn ghost fg-wide bp-claim" onClick={answerNo} title="Claim that no packing exists">
              <Icon d={ICON.no} />
              <span>Answer no</span>
            </button>
          )}
        </div>
      )}
    </aside>
  );

  return (
    <div class={`fg fg-play bp${sol ? ' is-solution' : ''}${drag ? ' is-dragging' : ''}`} ref={rootRef} onKeyDown={onKeyDown} style={`--bp-B:${B}`}>
      {head}
      {brief}
      <div class="fg-body">
        <div class="fg-main">
          <div class={`fg-stage bp-stage${bump ? ' is-bump' : ''}`}>
            <div class="bp-board">
              {tray}
              <div class="bp-bins">{bins}</div>
            </div>
          </div>
          {context}
        </div>
        {side}
      </div>
      {drag && (
        <div
          class={`bp-drag bp-pat-${itemPattern(drag.u)}`}
          style={`--c:${itemColor(drag.u)};--bp-u:${drag.w / sizes[drag.u]}px;left:${drag.x}px;top:${drag.y}px;width:${drag.w}px;height:${drag.h}px`}
          aria-hidden="true"
        >
          <span class="bp-size">{sizes[drag.u]}</span>
        </div>
      )}
      <p class="visually-hidden" aria-live="polite">
        {announce}
      </p>
    </div>
  );
}

// ---------------------------------------------------------------------------------------

/** "Bin 1: 6 + 4. Bin 2: 2 + 8" */
function binsText(inst: Instance, st: PackState): string {
  return st.contents.map((c, b) => `Bin ${b + 1}: ${c.length ? c.map((u) => inst.sizes[u]).join(' + ') : 'empty'}`).join('. ');
}

/** the bins in miniature: one segment per unit, in the colour of the item on it */
function BinMeter({ st }: { st: PackState }) {
  const B = st.inst.capacity;
  const perUnit = B <= 16;
  return (
    <div class={`bp-meter${perUnit ? '' : ' is-coarse'}`} aria-hidden="true">
      {st.contents.map((c, b) => (
        <div class="bp-meter-bin">
          {c.flatMap((u) =>
            perUnit
              ? Array.from({ length: st.inst.sizes[u] }, () => <span class={`bp-pat-${itemPattern(u)}`} style={`--c:${itemColor(u)}`} />)
              : [<span class={`bp-pat-${itemPattern(u)}`} style={`--c:${itemColor(u)};flex:${st.inst.sizes[u]}`} />],
          )}
          {perUnit
            ? Array.from({ length: st.free(b) }, () => <span class="is-free" />)
            : st.free(b) > 0 && <span class="is-free" style={`flex:${st.free(b)}`} />}
        </div>
      ))}
    </div>
  );
}

/** the list of every control, in a panel over the board ("Controls" or the ? key) */
function ControlsPanel(props: {
  id: string;
  open: boolean;
  onClose: (refocus: boolean) => void;
  anchor: { current: HTMLElement | null };
  bins: number;
  modKey: string;
}) {
  const { open, onClose, modKey, bins } = props;
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
          <Icon d={ICON.close} />
        </button>
      </div>
      <dl class="fg-ctl">
        <dt>Put an item in a bin</dt>
        <dd>
          Click or tap the item, then the bin. Or drag the item into the bin.
          <span class="fg-ctl-keys">
            <Keys k="Tab" /> to the items, <Keys k="←" /> <Keys k="→" /> between them, then <Keys k="1" />
            {bins > 1 && (
              <>
                {' '}
                {bins === 2 ? 'or' : 'to'} <Keys k={String(bins)} />
              </>
            )}{' '}
            puts the focused item in that bin.
          </span>
        </dd>
        <dt>Move an item to another bin</dt>
        <dd>Drag it there, or click it and then the other bin. With the item focused, press the other bin’s number.</dd>
        <dt>Take an item out</dt>
        <dd>
          {modKey}-click it, click it twice, or drag it back to the items. On a touch screen, tap it twice. With the item
          focused, press <Keys k="0" />.
        </dd>
        <dt>Undo</dt>
        <dd>
          The Undo button, <Keys k="⌫" /> or <Keys k={`${modKey} Z`} />.
        </dd>
        <dt>Solution</dt>
        <dd>
          Show solution packs the items, or shows the most that fits when no packing exists. <Keys k="Esc" /> returns to
          your attempt.
        </dd>
        <dt>Answer no</dt>
        <dd>Claims that no packing exists. The game says whether that is right.</dd>
        <dt>This list</dt>
        <dd>
          <Keys k="?" /> opens and closes it.
        </dd>
      </dl>
    </div>
  );
}
