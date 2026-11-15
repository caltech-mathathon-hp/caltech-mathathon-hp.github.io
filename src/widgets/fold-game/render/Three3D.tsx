/**
 * Three3D: the three.js renderer of the folding game, used for every lattice with dim 3.
 * The shell lazy-loads it (`import('./render/Three3D.tsx')`) and passes RendererProps (types.ts).
 *
 * This file owns the DOM (canvas host, HTML labels, axis gizmo, view buttons) and the lifecycle;
 * how to turn the view is taught by the shell (its hint line and Controls panel);
 * the scene graph, picking, camera fitting and the keyboard map live in three3d-scene.ts.
 * Everything (WebGL context, geometries, listeners, observers, frames) is released on unmount.
 */
import { useCallback, useEffect, useRef, useState } from 'preact/hooks';
import type { RendererProps } from './types.ts';
import { FoldScene, type SceneState } from './three3d-scene.ts';
import './three3d.css';

export default function Three3D(props: RendererProps) {
  const { controller, version, interactive, showLattice, showContacts, showIndices, height, frame, registerKeyMap, modKey } =
    props;
  const rootRef = useRef<HTMLDivElement>(null);
  const hostRef = useRef<HTMLDivElement>(null);
  const labelsRef = useRef<HTMLDivElement>(null);
  const gizmoRef = useRef<SVGSVGElement>(null);
  const sceneRef = useRef<FoldScene | null>(null);
  const [state, setState] = useState<SceneState>({ following: true, boxAvailable: false });
  const [showBox, setShowBox] = useState(true);
  const [failed, setFailed] = useState(false);

  const opts = { interactive, showLattice, showContacts, showIndices, showBox, frame, modKey };
  const optsRef = useRef(opts);
  optsRef.current = opts;
  const regRef = useRef(registerKeyMap);
  regRef.current = registerKeyMap;
  // one stable function for the shell, whatever happens to the scene
  const keyFn = useCallback((key: string, e: KeyboardEvent) => sceneRef.current?.keyMap(key, e) ?? null, []);

  // mount: create the scene; unmount: dispose everything
  useEffect(() => {
    const root = rootRef.current;
    const host = hostRef.current;
    const labels = labelsRef.current;
    const gizmo = gizmoRef.current;
    if (!root || !host || !labels || !gizmo) return;
    let scene: FoldScene;
    try {
      scene = new FoldScene({ root, host, labels, gizmo }, controller, optsRef.current, setState);
    } catch (err) {
      console.warn('[Three3D] WebGL is not available:', err);
      setFailed(true);
      return;
    }
    sceneRef.current = scene;
    return () => {
      regRef.current?.(null);
      sceneRef.current = null;
      scene.dispose();
    };
  }, []);

  // keyboard map: registered once per registerKeyMap function (the same keyFn every time)
  useEffect(() => {
    if (registerKeyMap && !failed) registerKeyMap(keyFn);
  }, [registerKeyMap, failed, keyFn]);

  // controller: follow its changes directly as well as through `version`
  useEffect(() => {
    sceneRef.current?.setController(controller);
    return controller.subscribe(() => sceneRef.current?.markDirty());
  }, [controller]);

  useEffect(() => {
    sceneRef.current?.setOptions(optsRef.current);
  }, [interactive, showLattice, showContacts, showIndices, showBox, frame, modKey]);

  useEffect(() => {
    sceneRef.current?.markDirty();
  }, [version]);

  const h = typeof height === 'number' ? `${height}px` : height;

  return (
    <div
      ref={rootRef}
      class="fg3-root"
      style={{ height: h }}
      role="group"
      aria-label="3D view of the fold"
    >
      <div ref={hostRef} class="fg3-host" />
      <div ref={labelsRef} class="fg3-labels" aria-hidden="true" />
      <svg ref={gizmoRef} class="fg3-gizmo" aria-hidden="true" />

      <div class="fg3-tools">
        {state.boxAvailable && (
          <button
            type="button"
            class={`fg3-btn${showBox ? ' is-on' : ''}`}
            aria-pressed={showBox}
            aria-label="Outline the H box"
            title="Outline the box filled by the H's"
            onClick={() => setShowBox((b) => !b)}
          >
            <svg viewBox="0 0 20 20" width="18" height="18" aria-hidden="true">
              <path d="M10 2.5 16.5 6v8L10 17.5 3.5 14V6z M3.5 6 10 9.5 16.5 6 M10 9.5v8" />
            </svg>
          </button>
        )}
        <button
          type="button"
          class={`fg3-btn${state.following ? '' : ' is-alert'}`}
          aria-label="Reset view"
          title={state.following ? 'Reset view' : 'Reset view and follow the fold'}
          onClick={() => sceneRef.current?.resetView()}
        >
          <svg viewBox="0 0 20 20" width="18" height="18" aria-hidden="true">
            <path d="M3 7V3h4 M13 3h4v4 M17 13v4h-4 M7 17H3v-4" />
            <circle cx="10" cy="10" r="2.2" />
          </svg>
        </button>
      </div>

      {failed && <div class="fg3-fail">The 3D view needs WebGL, which this browser does not provide.</div>}
    </div>
  );
}
