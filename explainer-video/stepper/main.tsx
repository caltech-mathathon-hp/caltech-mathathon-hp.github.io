/**
 * Step through the construction: the video's scenes in a Remotion Player, one numbered step per
 * caption. A step plays its animation, then waits on the finished picture. A thin bar under the
 * picture shows where you are inside the step; drag it to look again at part of the step.
 * Keys: Space play / pause (at the end of a step: the next step), → next step (finishes a step
 * still playing), ← previous step, Shift+← / Shift+→ two seconds back / forward, R replay,
 * F full screen, Home first step. Click the picture to play or pause.
 */
import React, { useCallback, useEffect, useRef, useState } from 'react';
import { createRoot } from 'react-dom/client';
import { Player, type PlayerRef } from '@remotion/player';
import { Explainer } from '../src/Video';
import { TOTAL_FRAMES } from '../src/script';
import { FPS, W, H } from '../src/theme/consts';
import { STEPS, GROUPS, TITLE_FRAME, type Step } from './steps';
import './stepper.css';

/**
 * ?embed: the page inside the website's iframe (site/src/widgets/explainer/). It shows only the
 * player, its controls and the list of steps, on a transparent background. It posts its height to
 * the frame, and the frame posts back the site's theme (light or dark).
 */
const EMBED = new URLSearchParams(window.location.search).has('embed');
if (EMBED) {
  const root = document.documentElement;
  root.classList.add('embed');
  const height = () => window.parent.postMessage({ explainer: 'height', height: Math.ceil(root.getBoundingClientRect().height) }, '*');
  new ResizeObserver(height).observe(root);
  window.addEventListener('message', (e) => {
    if (e.source === window.parent && e.data?.explainer === 'theme') root.dataset.theme = e.data.theme === 'dark' ? 'dark' : 'light';
  });
}

const PARTS: Record<number, string> = { 1: 'The idea', 2: 'An example', 3: 'In general' };
const RATES = [0.5, 0.75, 1, 1.5, 2];
const NUDGE = 2 * FPS;

const fromHash = () => {
  const k = parseInt(window.location.hash.slice(1), 10);
  return Number.isFinite(k) && k >= 1 && k <= STEPS.length ? k - 1 : -1;
};
const clamp = (x: number, lo: number, hi: number) => Math.min(hi, Math.max(lo, x));
const clock = (frames: number) => {
  const s = Math.max(0, Math.round(frames / FPS));
  return `${Math.floor(s / 60)}:${String(s % 60).padStart(2, '0')}`;
};

// ------------------------------------------------------------------ the bar inside a step

function Icon({ kind }: { kind: 'play' | 'pause' | 'next' }) {
  return (
    <svg viewBox="0 0 20 20" width="18" height="18" aria-hidden="true">
      {kind === 'play' && <path d="M6 4.2v11.6c0 .6.7 1 1.2.7l9-5.8c.5-.3.5-1.1 0-1.4l-9-5.8C6.7 3.2 6 3.6 6 4.2z" fill="currentColor" />}
      {kind === 'pause' && (
        <g fill="currentColor">
          <rect x="5" y="4" width="3.4" height="12" rx="1" />
          <rect x="11.6" y="4" width="3.4" height="12" rx="1" />
        </g>
      )}
      {kind === 'next' && (
        <g fill="currentColor">
          <path d="M4 4.6v10.8c0 .6.7 1 1.2.7l8.2-5.4c.5-.3.5-1 0-1.3L5.2 3.9C4.7 3.6 4 4 4 4.6z" />
          <rect x="14" y="4" width="2.6" height="12" rx="1" />
        </g>
      )}
    </svg>
  );
}

function StepBar({ player, step, playing, onToggle }: { player: React.RefObject<PlayerRef | null>; step: Step | null; playing: boolean; onToggle: () => void }) {
  const [frame, setFrame] = useState(0);
  const track = useRef<HTMLDivElement>(null);
  const drag = useRef<{ wasPlaying: boolean } | null>(null);

  useEffect(() => {
    const p = player.current;
    if (!p) return;
    const on = ({ detail }: { detail: { frame: number } }) => setFrame(detail.frame);
    p.addEventListener('frameupdate', on);
    p.addEventListener('seeked', on);
    setFrame(p.getCurrentFrame());
    return () => {
      p.removeEventListener('frameupdate', on);
      p.removeEventListener('seeked', on);
    };
  }, [player]);

  const span = step ? Math.max(1, step.end - step.start) : 1;
  const at = step ? clamp(frame - step.start, 0, span) : 0;
  const done = step ? frame >= step.end - 1 : false;
  const frameAt = (clientX: number) => {
    const r = track.current!.getBoundingClientRect();
    return Math.round(step!.start + clamp((clientX - r.left) / r.width, 0, 1) * span);
  };
  const onDown = (e: React.PointerEvent) => {
    const p = player.current;
    if (!p || !step) return;
    e.currentTarget.setPointerCapture(e.pointerId);
    drag.current = { wasPlaying: p.isPlaying() };
    p.pause();
    p.seekTo(frameAt(e.clientX));
  };
  const onMove = (e: React.PointerEvent) => {
    if (drag.current && step) player.current?.seekTo(frameAt(e.clientX));
  };
  const onUp = (e: React.PointerEvent) => {
    const p = player.current;
    const d = drag.current;
    drag.current = null;
    if (p && d?.wasPlaying && step && frameAt(e.clientX) < step.end - 1) p.play();
  };

  return (
    <div className={`stepbar${step ? '' : ' is-off'}`}>
      <button className="icon" onClick={onToggle} disabled={!step} aria-label={playing ? 'Pause' : done ? 'Next step' : 'Play'} title={playing ? 'Pause (Space)' : done ? 'Next step (Space)' : 'Play (Space)'}>
        <Icon kind={playing ? 'pause' : done ? 'next' : 'play'} />
      </button>
      <div
        className="track"
        ref={track}
        onPointerDown={onDown}
        onPointerMove={onMove}
        onPointerUp={onUp}
        onPointerCancel={onUp}
        role="slider"
        aria-label="Position in this step"
        aria-valuemin={0}
        aria-valuemax={Math.round(span / FPS)}
        aria-valuenow={Math.round(at / FPS)}
      >
        <div className="rail">
          <div className="fill" style={{ width: `${(100 * at) / span}%` }} />
        </div>
        <div className="thumb" style={{ left: `${(100 * at) / span}%` }} />
      </div>
      <div className="time">
        {clock(at)} / {clock(span)}
      </div>
    </div>
  );
}

// ------------------------------------------------------------------ the picture

/** the picture: a click plays or pauses */
function Screen({ children, onClick }: { children: React.ReactNode; onClick: () => void }) {
  return (
    <div className="screen" onClick={onClick}>
      {children}
    </div>
  );
}

// ------------------------------------------------------------------ the page

function App() {
  const player = useRef<PlayerRef>(null);
  const stage = useRef<HTMLDivElement>(null);
  /** index into STEPS; −1 is the title card */
  const [cur, setCur] = useState(fromHash);
  const [playing, setPlaying] = useState(false);
  const [rate, setRate] = useState(1);
  const [through, setThrough] = useState(false);
  const curRef = useRef(cur);
  const throughRef = useRef(through);
  curRef.current = cur;
  throughRef.current = through;

  const go = useCallback((i: number, onward = false) => {
    const p = player.current;
    if (!p) return;
    if (i < 0) {
      p.pause();
      p.seekTo(TITLE_FRAME);
      setCur(-1);
      history.replaceState(null, '', '#');
      return;
    }
    const st = STEPS[Math.min(i, STEPS.length - 1)];
    setCur(st.n - 1);
    curRef.current = st.n - 1;
    history.replaceState(null, '', `#${st.n}`);
    // on from the step before, at its end: play the last moments of its scene too (its labels and
    // caption fade out), as the video does, instead of jumping over them to the next scene
    const prevEnd = st.n > 1 ? STEPS[st.n - 2].end : TITLE_FRAME;
    const f = p.getCurrentFrame();
    if (!(onward && f >= prevEnd - 1 && f < st.start)) p.seekTo(st.start);
    p.play();
  }, []);

  /** a press of "next": finish the step if it is still playing, else play the next one */
  const next = useCallback(() => {
    const p = player.current;
    if (!p) return;
    const i = curRef.current;
    if (p.isPlaying() && i >= 0) {
      p.pause();
      p.seekTo(STEPS[i].end);
      return;
    }
    if (i < STEPS.length - 1) go(i + 1, true);
  }, [go]);
  /** End: jump to the step's finished picture */
  const finish = useCallback(() => {
    const p = player.current;
    const i = curRef.current;
    if (!p || i < 0) return;
    p.pause();
    p.seekTo(STEPS[i].end);
  }, []);
  const back = useCallback(() => go(curRef.current - 1), [go]);
  const replay = useCallback(() => go(Math.max(0, curRef.current)), [go]);

  /** Space: pause, or carry on from where the step stands (at its end: the next step) */
  const toggle = useCallback(() => {
    const p = player.current;
    if (!p) return;
    const i = curRef.current;
    if (i < 0) return go(0, true);
    if (p.isPlaying()) return p.pause();
    const st = STEPS[i];
    const f = p.getCurrentFrame();
    if (f >= st.end - 1) {
      if (i < STEPS.length - 1) go(i + 1, true);
      return;
    }
    if (f < st.start) p.seekTo(st.start);
    p.play();
  }, [go]);

  /** move inside the step, by frames */
  const nudge = useCallback((d: number) => {
    const p = player.current;
    const i = curRef.current;
    if (!p || i < 0) return;
    const st = STEPS[i];
    p.seekTo(clamp(p.getCurrentFrame() + d, st.start, st.end));
  }, []);

  const fullScreen = useCallback(() => {
    if (document.fullscreenElement) document.exitFullscreen();
    else stage.current?.requestFullscreen();
  }, []);

  // pause at the end of the step (or run on into the next one in "play through" mode)
  useEffect(() => {
    const p = player.current;
    if (!p) return;
    const onFrame = ({ detail }: { detail: { frame: number } }) => {
      const i = curRef.current;
      if (i < 0 || !p.isPlaying()) return;
      const st = STEPS[i];
      if (detail.frame < st.end) return;
      if (throughRef.current && i < STEPS.length - 1) {
        setCur(i + 1);
        curRef.current = i + 1;
        history.replaceState(null, '', `#${i + 2}`);
        return;
      }
      p.pause();
      p.seekTo(st.end);
    };
    const onPlay = () => setPlaying(true);
    const onPause = () => setPlaying(false);
    p.addEventListener('frameupdate', onFrame);
    p.addEventListener('play', onPlay);
    p.addEventListener('pause', onPause);
    p.addEventListener('ended', onPause);
    // start on the title card, or on the step in the address (paused on its picture)
    const i = curRef.current;
    p.seekTo(i >= 0 ? STEPS[i].end : TITLE_FRAME);
    // a step typed into the address (#12): show its finished picture
    const onHash = () => {
      const k = fromHash();
      if (k < 0 || k === curRef.current) return;
      p.pause();
      setCur(k);
      curRef.current = k;
      p.seekTo(STEPS[k].end);
    };
    window.addEventListener('hashchange', onHash);
    return () => {
      window.removeEventListener('hashchange', onHash);
      p.removeEventListener('frameupdate', onFrame);
      p.removeEventListener('play', onPlay);
      p.removeEventListener('pause', onPause);
      p.removeEventListener('ended', onPause);
    };
  }, []);

  useEffect(() => {
    const onKey = (e: KeyboardEvent) => {
      if (e.metaKey || e.ctrlKey || e.altKey) return;
      const t = e.target as HTMLElement;
      if (t && (t.tagName === 'SELECT' || t.tagName === 'INPUT')) return;
      if (e.key === ' ' || e.key === 'k' || e.key === 'K') toggle();
      else if (e.shiftKey && e.key === 'ArrowLeft') nudge(-NUDGE);
      else if (e.shiftKey && e.key === 'ArrowRight') nudge(NUDGE);
      else if (e.key === 'j' || e.key === 'J') nudge(-NUDGE);
      else if (e.key === 'l' || e.key === 'L') nudge(NUDGE);
      else if (e.key === 'ArrowRight' || e.key === 'PageDown') next();
      else if (e.key === 'ArrowLeft' || e.key === 'PageUp') back();
      else if (e.key === 'r' || e.key === 'R') replay();
      else if (e.key === 'f' || e.key === 'F') fullScreen();
      else if (e.key === 'Home') go(0);
      else if (e.key === 'End') finish();
      else return;
      e.preventDefault();
      // a button keeps focus after a click; drop it so Space does not also press it
      if (t && t.tagName === 'BUTTON') t.blur();
    };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, [toggle, nudge, next, back, replay, go, fullScreen, finish]);

  const step: Step | null = cur >= 0 ? STEPS[cur] : null;
  return (
    <div className="page">
      {!EMBED && (
        <header className="head">
          <div>
            <div className="kicker">Berger and Leighton, 1998</div>
            <h1>Bin packing inside a fold</h1>
          </div>
          <div className="keys">
            <span><kbd>Space</kbd> play / pause</span>
            <span><kbd>←</kbd><kbd>→</kbd> step</span>
            <span><kbd>R</kbd> replay</span>
            <span><kbd>F</kbd> full screen</span>
          </div>
        </header>
      )}

      <main className="main">
        <div className="watch">
          <div className="stage" ref={stage}>
            <Screen onClick={toggle}>
              <Player
                ref={player}
                component={Explainer}
                durationInFrames={TOTAL_FRAMES}
                compositionWidth={W}
                compositionHeight={H}
                fps={FPS}
                controls={false}
                clickToPlay={false}
                spaceKeyToPlayOrPause={false}
                playbackRate={rate}
                acknowledgeRemotionLicense
                style={{ width: '100%', aspectRatio: `${W} / ${H}`, display: 'block' }}
              />
            </Screen>
            <StepBar player={player} step={step} playing={playing} onToggle={toggle} />
          </div>

          <div className="bar">
            <div className="nav">
              <button onClick={back} disabled={cur < 0} aria-label="Previous step" title="Previous step (←)">
                ← Back
              </button>
              <button onClick={replay} disabled={cur < 0} aria-label="Replay this step" title="Replay this step (R)">
                ↺ Replay
              </button>
              <button className="primary" onClick={next} disabled={cur >= STEPS.length - 1 && !playing} title="Next step (→)">
                {cur < 0 ? 'Start →' : playing ? 'Skip to end →' : 'Next step →'}
              </button>
            </div>
            <div className="where">
              {step ? (
                <>
                  Step <b>{step.n}</b> of {STEPS.length}
                </>
              ) : (
                <>{STEPS.length} steps</>
              )}
            </div>
            <div className="opts">
              <label className="speed">
                Speed
                <select value={rate} onChange={(e) => setRate(Number(e.target.value))}>
                  {RATES.map((r) => (
                    <option key={r} value={r}>
                      {r}×
                    </option>
                  ))}
                </select>
              </label>
              <label className="switch" title="Run on from step to step without stopping">
                <input type="checkbox" checked={through} onChange={(e) => setThrough(e.target.checked)} />
                <span className="knob" aria-hidden="true" />
                Play through
              </label>
            </div>
          </div>
        </div>

        <Contents cur={cur} go={go} />
      </main>
    </div>
  );
}

// ------------------------------------------------------------------ the list of steps, beside the picture

const PART_GROUPS = [1, 2, 3].map((part) => ({ part, groups: GROUPS.filter((g) => g.scene.part === part) })).filter((p) => p.groups.length);

/** every scene as a row, its steps as numbered dots; the current row stays in view */
function Contents({ cur, go }: { cur: number; go: (i: number) => void }) {
  const box = useRef<HTMLDivElement>(null);
  useEffect(() => {
    const el = box.current;
    const row = el?.querySelector<HTMLElement>('.row.is-current');
    if (!el || !row || getComputedStyle(el).position !== 'absolute') return;
    const top = row.offsetTop - 8;
    const bottom = row.offsetTop + row.offsetHeight + 8;
    if (top < el.scrollTop) el.scrollTo({ top, behavior: 'smooth' });
    else if (bottom > el.scrollTop + el.clientHeight) el.scrollTo({ top: bottom - el.clientHeight, behavior: 'smooth' });
  }, [cur]);
  return (
    <aside className="toc" aria-label="Steps">
      <div className="toc-scroll" ref={box}>
        {PART_GROUPS.map(({ part, groups }) => (
          <section key={part} className="toc-part">
            <div className="part">{PARTS[part]}</div>
            <ol className="rows">
              {groups.map(({ scene, steps }) => {
                const here = steps.some((st) => st.n - 1 === cur);
                const done = steps[steps.length - 1].n - 1 < cur;
                return (
                  <li key={scene.id} className={`row${here ? ' is-current' : done ? ' is-done' : ''}`}>
                    <button className="rtitle" onClick={() => go(steps[0].n - 1)} title={`Go to step ${steps[0].n}`}>
                      {scene.title}
                    </button>
                    <span className="dots">
                      {steps.map((st) => (
                        <button
                          key={st.n}
                          className={`pill${st.n - 1 === cur ? ' is-current' : st.n - 1 < cur ? ' is-past' : ''}`}
                          onClick={() => go(st.n - 1)}
                          title={st.text}
                          aria-label={`Step ${st.n}`}
                          aria-current={st.n - 1 === cur ? 'step' : undefined}
                        >
                          {st.n}
                        </button>
                      ))}
                    </span>
                  </li>
                );
              })}
            </ol>
          </section>
        ))}
      </div>
    </aside>
  );
}

// a hot reload runs this module again: reuse the root it made the first time
const host = document.getElementById('root') as HTMLElement & { _root?: ReturnType<typeof createRoot> };
host._root ??= createRoot(host);
host._root.render(<App />);
