/**
 * The three.js half of the 3D fold renderer (Three3D.tsx owns the Preact side and the DOM).
 *
 * Draws controller.fold for any dim-3 lattice, always through lattice.embed:
 *   residues   one InstancedMesh; per-instance kind: H filled, P light with a ring (hollow look)
 *   backbone   InstancedMesh of cylinders, one per chain bond
 *   contacts   InstancedMesh of dashed cylinders, one per H–H contact
 *   lattice    faint points in a box around the fold and a grid on the floor of that box (on a
 *              lattice with two kinds of node, the diamond lattice, its edges around the fold)
 *   ghosts     legal next positions (pickable), rings on the last and the hovered residue,
 *              outline of the H core when the H's fill a box (cubic lattice)
 *
 * Input (interactive): click a ghost to place the next residue; ⌘-click / Ctrl-click a placed
 * residue to go back to it (touch: tap it twice); holding the modifier over a residue sets
 * controller.cut, drawn as faded residues after it.
 *
 * Updates are incremental: only residues from the first changed index on are rewritten, so a
 * construction can be replayed residue by residue. Rendering is on demand: a frame is drawn
 * only when the fold, the theme, the size or the camera changed.
 */
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { LineSegments2 } from 'three/addons/lines/LineSegments2.js';
import { LineSegmentsGeometry } from 'three/addons/lines/LineSegmentsGeometry.js';
import { LineMaterial } from 'three/addons/lines/LineMaterial.js';
import type { GameController } from '../engine/controller.ts';
import type { Fold } from '../engine/fold.ts';
import { type Lattice, type Vec, degree, neighbours, stepIndex, stepsAt } from '../engine/lattice.ts';
import { residueRange, token } from './types.ts';

// ---------- sizes (drawing units: neighbouring lattice points are at distance 1) ----------
const R_RES = 0.3;
const R_GHOST = 0.21;
const R_BOND = 0.075;
const R_CONTACT = 0.024;
const FOV = 30;
/** default viewing direction (from the target towards the camera): a three-quarter view */
const DEFAULT_DIR = new THREE.Vector3(0.5, 0.42, 0.76).normalize();

export interface SceneOptions {
  interactive: boolean;
  showLattice: boolean;
  showContacts: boolean;
  showIndices: boolean;
  showBox: boolean;
  /** label of the modifier for "go back to this residue" in the tooltip: '⌘' or 'Ctrl' */
  modKey?: string;
  /** lattice points to keep in frame instead of the placed residues (view mode: the whole fold) */
  frame?: readonly (readonly number[])[];
}

export interface SceneState {
  /** the camera follows the fold (false after the reader zoomed or panned) */
  following: boolean;
  /** the placed H's fill a box: the box outline can be shown */
  boxAvailable: boolean;
}

export interface SceneElements {
  /** element that receives the canvas (sized by CSS) */
  host: HTMLElement;
  /** absolutely positioned layer for HTML labels */
  labels: HTMLElement;
  /** small SVG axis gizmo */
  gizmo: SVGSVGElement;
  /** root of the widget (for focus detection) */
  root: HTMLElement;
}

/** keys handled by the camera-relative keyboard map → slot: 0 right, 1 left, 2 up, 3 down, 4 away, 5 toward */
const KEY_SLOTS: Record<string, number> = {
  ArrowRight: 0,
  ArrowLeft: 1,
  ArrowUp: 2,
  ArrowDown: 3,
  w: 4,
  W: 4,
  PageUp: 4,
  s: 5,
  S: 5,
  PageDown: 5,
};
export const KEY_GLYPHS = ['→', '←', '↑', '↓', 'W', 'S'];

// ---------- shaders ----------
const LIGHT = /* glsl */ `
vec3 fg3Shade(vec3 base, vec3 n, vec3 v, float spec, float flat_) {
  vec3 L = normalize(vec3(-0.45, 0.7, 0.55));
  float d = max(dot(n, L), 0.0);
  float hemi = 0.5 + 0.5 * n.y;
  float lit = min(0.6 + 0.12 * hemi + 0.5 * d, 1.15);
  vec3 col = base * mix(lit, 1.0, flat_);
  vec3 h = normalize(L + v);
  col += spec * pow(max(dot(n, h), 0.0), 42.0);
  return col;
}
`;

const RES_VERT = /* glsl */ `
attribute float aKind;
varying vec3 vN;
varying vec3 vV;
varying float vKind;
void main() {
  vKind = aKind;
  vec4 mv = modelViewMatrix * instanceMatrix * vec4(position, 1.0);
  vN = normalize(normalMatrix * normal);
  vV = -mv.xyz;
  gl_Position = projectionMatrix * mv;
}
`;

const RES_FRAG = /* glsl */ `
uniform vec3 uH;
uniform vec3 uP;
uniform vec3 uPFill;
uniform vec3 uBg;
varying vec3 vN;
varying vec3 vV;
varying float vKind;
${LIGHT}
void main() {
  vec3 n = normalize(vN);
  vec3 v = normalize(vV);
  float ndv = clamp(dot(n, v), 0.0, 1.0);
  // kinds 2 and 3: H and P after the truncation preview, faded towards the background
  float dim = step(1.5, vKind);
  float kind = vKind - 2.0 * dim;
  vec3 col;
  if (kind < 0.5) {
    col = fg3Shade(uH, n, v, 0.16, 0.0);
    col *= mix(0.8, 1.0, smoothstep(0.0, 0.42, ndv));
  } else {
    float ring = 1.0 - smoothstep(0.44, 0.6, ndv);
    col = fg3Shade(mix(uPFill, uP, ring), n, v, 0.06, 0.45);
  }
  col = mix(col, uBg, 0.72 * dim);
  gl_FragColor = vec4(col, 1.0);
  #include <colorspace_fragment>
}
`;

/** unit cylinder along y (radius 1, height 1); the radius is applied here, never thinner than uMinPx */
const SEG_VERT = /* glsl */ `
uniform float uRadius;
uniform float uMinPx;
uniform float uPxWorld;
uniform float uDash;
varying vec3 vN;
varying vec3 vV;
varying float vY;
varying float vDashPx;
void main() {
  vY = position.y;
  vec4 axis = modelViewMatrix * instanceMatrix * vec4(0.0, position.y, 0.0, 1.0);
  float px = uPxWorld * max(-axis.z, 1e-3);
  float r = max(uRadius, 0.5 * uMinPx * px);
  vDashPx = uDash > 0.0 ? 0.5 / (uDash * px) : 0.0;
  vec4 mv = modelViewMatrix * instanceMatrix * vec4(position.x * r, position.y, position.z * r, 1.0);
  vN = normalize(normalMatrix * mat3(instanceMatrix) * normal);
  vV = -mv.xyz;
  gl_Position = projectionMatrix * mv;
}
`;

const SEG_FRAG = /* glsl */ `
uniform vec3 uColor;
uniform float uDash;
uniform float uLit;
varying vec3 vN;
varying vec3 vV;
varying float vY;
varying float vDashPx;
${LIGHT}
void main() {
  if (uDash > 0.0 && vDashPx > 2.5 && fract(vY * uDash + 0.25) > 0.5) discard;
  vec3 col = mix(uColor, fg3Shade(uColor, normalize(vN), normalize(vV), 0.12, 0.0), uLit);
  gl_FragColor = vec4(col, 1.0);
  #include <colorspace_fragment>
}
`;

const GHOST_VERT = /* glsl */ `
varying vec3 vN;
varying vec3 vV;
void main() {
  vec4 mv = modelViewMatrix * vec4(position, 1.0);
  vN = normalize(normalMatrix * normal);
  vV = -mv.xyz;
  gl_Position = projectionMatrix * mv;
}
`;

const GHOST_FRAG = /* glsl */ `
uniform vec3 uColor;
uniform float uFill;
uniform float uRing;
varying vec3 vN;
varying vec3 vV;
void main() {
  float ndv = clamp(dot(normalize(vN), normalize(vV)), 0.0, 1.0);
  float ring = 1.0 - smoothstep(0.36, 0.62, ndv);
  gl_FragColor = vec4(uColor, mix(uFill, uRing, ring));
  #include <colorspace_fragment>
}
`;

const DOT_VERT = /* glsl */ `
uniform float uSize;
uniform float uPxWorld;
uniform float uDpr;
void main() {
  vec4 mv = modelViewMatrix * vec4(position, 1.0);
  gl_PointSize = uDpr * clamp(uSize / (uPxWorld * max(-mv.z, 1e-3)), 1.6, 9.0);
  gl_Position = projectionMatrix * mv;
}
`;

const DOT_FRAG = /* glsl */ `
uniform vec3 uColor;
uniform float uOpacity;
void main() {
  float d = length(gl_PointCoord - 0.5);
  float a = 1.0 - smoothstep(0.32, 0.5, d);
  if (a <= 0.0) discard;
  gl_FragColor = vec4(uColor, uOpacity * a);
  #include <colorspace_fragment>
}
`;

// ---------- helpers ----------
interface Colors {
  bg: THREE.Color;
  h: THREE.Color;
  p: THREE.Color;
  pFill: THREE.Color;
  bond: THREE.Color;
  backbone: THREE.Color;
  ghost: THREE.Color;
  lattice: THREE.Color;
  fg: THREE.Color;
  accent: THREE.Color;
  invalid: THREE.Color;
}

function readColors(): Colors {
  const c = (name: string, fallback: string) => {
    const col = new THREE.Color();
    try {
      col.setStyle(token(name) || fallback);
    } catch {
      col.setStyle(fallback);
    }
    return col;
  };
  const p = c('--p', '#4f7aa3');
  const bgElev = c('--bg-elev', '#ffffff');
  return {
    bg: c('--bg-sunk', '#f2f0eb'),
    h: c('--h', '#c4532f'),
    p,
    pFill: bgElev.clone().lerp(p, 0.14),
    bond: c('--bond', '#d99a1e'),
    backbone: c('--backbone', '#6d6d78'),
    ghost: c('--ghost', '#1f4f8f'),
    lattice: c('--lattice', '#d8d4cb'),
    fg: c('--fg', '#1c1c21'),
    accent: c('--accent', '#1f4f8f'),
    invalid: c('--invalid', '#b3261e'),
  };
}

function makeInstanced(geo: THREE.BufferGeometry, mat: THREE.Material, cap: number) {
  const m = new THREE.InstancedMesh(geo, mat, Math.max(1, cap));
  m.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
  m.frustumCulled = false;
  m.count = 0;
  return m;
}

/** mark instances [from, to) of an instanced attribute for upload */
function touch(attr: THREE.BufferAttribute, itemSize: number, from: number, to: number) {
  if (to <= from) return;
  attr.clearUpdateRanges();
  attr.addUpdateRange(from * itemSize, (to - from) * itemSize);
  attr.needsUpdate = true;
}

/** the largest possible number of H–H contacts of the string (capacity of the contact mesh) */
/** two frames hold the same points (reference check first; a shell may pass a fresh array) */
function sameFrame(a?: readonly (readonly number[])[], b?: readonly (readonly number[])[]): boolean {
  if (a === b) return true;
  if (!a || !b || a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) {
    const u = a[i];
    const v = b[i];
    if (u === v) continue;
    if (u.length !== v.length) return false;
    for (let d = 0; d < u.length; d++) if (u[d] !== v[d]) return false;
  }
  return true;
}

function contactCapacity(seq: readonly string[], z: number): number {
  let nh = 0;
  for (const r of seq) if (r === 'H') nh++;
  return Math.ceil((nh * Math.max(1, z - 1)) / 2) + 1;
}

const _m = new THREE.Matrix4();
const _q = new THREE.Quaternion();
const _v = new THREE.Vector3();
const _w = new THREE.Vector3();
const _s = new THREE.Vector3();
const _Y = new THREE.Vector3(0, 1, 0);

type PickHit = { kind: 'ghost'; index: number } | { kind: 'residue'; index: number } | null;

export class FoldScene {
  // three.js
  private renderer: THREE.WebGLRenderer;
  private scene = new THREE.Scene();
  private camera = new THREE.PerspectiveCamera(FOV, 1, 0.1, 4000);
  private controls: OrbitControls;
  private raycaster = new THREE.Raycaster();

  // materials
  private colors: Colors;
  private resMat: THREE.ShaderMaterial;
  private bondMat: THREE.ShaderMaterial;
  private contactMat: THREE.ShaderMaterial;
  private ghostMat: THREE.ShaderMaterial;
  private ghostHoverMat: THREE.ShaderMaterial;
  private dotMat: THREE.ShaderMaterial;
  private floorMat: LineMaterial;
  private boxMat: LineMaterial;
  private lastRingMat: THREE.MeshBasicMaterial;
  private hoverRingMat: THREE.MeshBasicMaterial;
  private previewMat: THREE.MeshBasicMaterial;

  // meshes
  private residues!: THREE.InstancedMesh;
  private bonds!: THREE.InstancedMesh;
  private contacts!: THREE.InstancedMesh;
  private capRes = 0;
  private capBond = 0;
  private capContact = 0;
  private sphereDetail = -1;
  private bondGeo = new THREE.CylinderGeometry(1, 1, 1, 10, 1, true);
  private contactGeo = new THREE.CylinderGeometry(1, 1, 1, 6, 1, true);
  private ghostGeo = new THREE.SphereGeometry(R_GHOST, 24, 16);
  private ringGeo = new THREE.RingGeometry(0.39, 0.43, 48);
  private hoverRingGeo = new THREE.RingGeometry(0.42, 0.52, 48);
  private ghosts: THREE.Mesh[] = [];
  private lastRing: THREE.Mesh;
  private hoverRing: THREE.Mesh;
  private preview: THREE.Mesh;
  private dots: THREE.Points;
  private floor: LineSegments2;
  private box: LineSegments2;
  private world = new THREE.Group();

  // fold state mirrored in the scene
  private controller: GameController;
  private lattice: Lattice | null = null;
  private fold: Fold | null = null;
  private drawn: number[][] = [];
  private pos = new Float32Array(0);
  private ci: number[] = [];
  private cj: number[] = [];
  private stepDirs: THREE.Vector3[] = [];
  private stepOpp: number[] = [];
  private cubicLike = false;
  private ghostPos: number[][] = [];
  private ghostStep: number[] = [];
  private ghostKey = '';
  private latKey = '';
  private latStale = true;
  private boxAvailable = false;
  private labelIdx: number[] = [];
  private labelKey = '';

  // view state
  private opts: SceneOptions;
  private following = true;
  private dragging = false;
  private fitActive = false;
  private fitCenter = new THREE.Vector3();
  private fitDist = 10;
  private dirGoal: THREE.Vector3 | null = null;
  private expTarget = new THREE.Vector3();
  private expDist = 10;
  private snapNext = true;
  /** opts.frame changed since the last fit */
  private frameStale = false;
  private reducedMotion = false;
  private cssW = 1;
  private cssH = 1;
  private hoverGhost = -1;
  private ownHover: number | null = null;
  /** ⌘ / Ctrl is held (truncation preview); the last input was touch; the cut drawn; contacts drawn */
  private modDown = false;
  private lastTouch = false;
  private cutDrawn: number | null = null;
  private contactCount = 0;
  private pointer: { x: number; y: number; touch: boolean } | null = null;
  private down: { x: number; y: number; t: number; id: number; touch: boolean; mod: boolean } | null = null;
  private activePointers = new Set<number>();
  private keyFocus = false;
  private keyRecent = -Infinity;
  private keyTimer = 0;
  private prevAssign = new Set<string>();

  // DOM
  private els: SceneElements;
  private idxPool: HTMLSpanElement[] = [];
  private keyPool: HTMLSpanElement[] = [];
  private tip: HTMLDivElement;
  private gizmoParts: { line: SVGLineElement; text: SVGTextElement }[] = [];
  private onState: (s: SceneState) => void;
  private lastState = '';

  // lifecycle
  private raf = 0;
  private lastFrame = 0;
  private dirty = true;
  private disposed = false;
  private ro: ResizeObserver;
  private cleanups: (() => void)[] = [];

  constructor(els: SceneElements, controller: GameController, opts: SceneOptions, onState: (s: SceneState) => void) {
    this.els = els;
    this.controller = controller;
    this.opts = { ...opts };
    this.onState = onState;
    this.reducedMotion = typeof matchMedia === 'function' && matchMedia('(prefers-reduced-motion: reduce)').matches;

    // throws if WebGL is unavailable; the component shows a fallback
    this.renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true, powerPreference: 'high-performance' });
    this.renderer.setClearColor(0x000000, 0);
    this.renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
    const canvas = this.renderer.domElement;
    canvas.className = 'fg3-canvas';
    canvas.setAttribute('aria-hidden', 'true');
    els.host.appendChild(canvas);

    this.colors = readColors();
    const col = this.colors;
    const pxUniforms = { uPxWorld: { value: 0.01 } };

    this.resMat = new THREE.ShaderMaterial({
      vertexShader: RES_VERT,
      fragmentShader: RES_FRAG,
      uniforms: { uH: { value: col.h }, uP: { value: col.p }, uPFill: { value: col.pFill }, uBg: { value: col.bg } },
    });
    const segMat = (color: THREE.Color, radius: number, minPx: number, dash: number, lit: number) =>
      new THREE.ShaderMaterial({
        vertexShader: SEG_VERT,
        fragmentShader: SEG_FRAG,
        uniforms: {
          uColor: { value: color },
          uRadius: { value: radius },
          uMinPx: { value: minPx },
          uPxWorld: pxUniforms.uPxWorld,
          uDash: { value: dash },
          uLit: { value: lit },
        },
      });
    this.bondMat = segMat(col.backbone, R_BOND, 2.2, 0, 1);
    this.contactMat = segMat(col.bond, R_CONTACT, 1.6, 7.5, 0.25);
    const ghostMat = (fill: number, ring: number) =>
      new THREE.ShaderMaterial({
        vertexShader: GHOST_VERT,
        fragmentShader: GHOST_FRAG,
        uniforms: { uColor: { value: col.ghost }, uFill: { value: fill }, uRing: { value: ring } },
        transparent: true,
        depthWrite: false,
      });
    this.ghostMat = ghostMat(0.1, 0.75);
    this.ghostHoverMat = ghostMat(0.42, 1.0);
    this.dotMat = new THREE.ShaderMaterial({
      vertexShader: DOT_VERT,
      fragmentShader: DOT_FRAG,
      uniforms: {
        uColor: { value: col.lattice },
        uOpacity: { value: 0.85 },
        uSize: { value: 0.075 },
        uPxWorld: pxUniforms.uPxWorld,
        uDpr: { value: this.renderer.getPixelRatio() },
      },
      transparent: true,
      depthWrite: false,
    });
    this.floorMat = new LineMaterial({ color: col.lattice, linewidth: 1, transparent: true, opacity: 1, depthWrite: false });
    this.boxMat = new LineMaterial({ color: col.h, linewidth: 1.5, transparent: true, opacity: 0.8 });
    this.lastRingMat = new THREE.MeshBasicMaterial({ color: col.fg, transparent: true, opacity: 0.6, side: THREE.DoubleSide });
    this.hoverRingMat = new THREE.MeshBasicMaterial({
      color: col.accent,
      transparent: true,
      opacity: 0.95,
      side: THREE.DoubleSide,
      depthTest: false,
      depthWrite: false,
    });
    this.previewMat = new THREE.MeshBasicMaterial({ color: col.ghost, transparent: true, opacity: 0.45, depthWrite: false });

    this.scene.add(this.world);
    this.lastRing = new THREE.Mesh(this.ringGeo, this.lastRingMat);
    this.hoverRing = new THREE.Mesh(this.hoverRingGeo, this.hoverRingMat);
    this.hoverRing.renderOrder = 10;
    this.preview = new THREE.Mesh(new THREE.CylinderGeometry(R_BOND * 0.8, R_BOND * 0.8, 1, 10, 1, true), this.previewMat);
    this.dots = new THREE.Points(new THREE.BufferGeometry(), this.dotMat);
    this.dots.frustumCulled = false;
    this.floor = new LineSegments2(new LineSegmentsGeometry(), this.floorMat);
    this.box = new LineSegments2(new LineSegmentsGeometry(), this.boxMat);
    for (const o of [this.lastRing, this.hoverRing, this.preview, this.dots, this.floor, this.box]) {
      o.visible = false;
      this.world.add(o);
    }

    // camera and controls
    this.camera.position.copy(DEFAULT_DIR).multiplyScalar(10);
    this.controls = new OrbitControls(this.camera, canvas);
    this.controls.enableDamping = !this.reducedMotion;
    this.controls.dampingFactor = 0.14;
    this.controls.rotateSpeed = 0.8;
    this.controls.zoomSpeed = 0.9;
    this.controls.minDistance = 0.8;
    this.controls.maxDistance = 400;
    this.controls.screenSpacePanning = true;
    this.controls.addEventListener('change', this.onControlsChange);
    this.controls.addEventListener('start', this.onControlsStart);
    this.controls.addEventListener('end', this.onControlsEnd);

    // DOM overlay
    this.tip = document.createElement('div');
    this.tip.className = 'fg3-tip';
    this.tip.hidden = true;
    els.labels.appendChild(this.tip);
    this.buildGizmo();

    // events
    const on = <K extends keyof HTMLElementEventMap>(
      el: HTMLElement | Document,
      type: K,
      fn: (e: HTMLElementEventMap[K]) => void,
      opt?: AddEventListenerOptions,
    ) => {
      el.addEventListener(type, fn as EventListener, opt);
      this.cleanups.push(() => el.removeEventListener(type, fn as EventListener, opt));
    };
    on(canvas, 'pointerdown', this.onPointerDown);
    on(canvas, 'pointermove', this.onPointerMove);
    on(canvas, 'pointerup', this.onPointerUp);
    on(canvas, 'pointercancel', this.onPointerCancel);
    on(canvas, 'pointerleave', this.onPointerLeave);
    on(document, 'focusin', this.onFocusChange);
    const onMod = (e: KeyboardEvent) => {
      if (e.key === 'Meta' || e.key === 'Control') this.setMod(e.type === 'keydown');
    };
    window.addEventListener('keydown', onMod);
    window.addEventListener('keyup', onMod);
    const onBlur = () => this.setMod(false);
    window.addEventListener('blur', onBlur);
    this.cleanups.push(() => {
      window.removeEventListener('keydown', onMod);
      window.removeEventListener('keyup', onMod);
      window.removeEventListener('blur', onBlur);
    });
    on(document, 'focusout', this.onFocusChange);
    const html = document.documentElement;
    const theme = () => this.applyTheme();
    html.addEventListener('themechange', theme);
    this.cleanups.push(() => html.removeEventListener('themechange', theme));
    canvas.addEventListener('webglcontextlost', this.onContextLost);
    this.cleanups.push(() => canvas.removeEventListener('webglcontextlost', this.onContextLost));

    this.ro = new ResizeObserver(() => this.resize());
    this.ro.observe(els.host);
    this.resize();
    this.sync();
    this.request();
  }

  // ---------- public API ----------

  setController(c: GameController) {
    if (c === this.controller) return;
    this.controller = c;
    this.following = true;
    this.snapNext = true;
    this.markDirty();
  }

  setOptions(o: SceneOptions) {
    const prev = this.opts;
    this.opts = { ...o };
    if (!sameFrame(prev.frame, o.frame)) {
      this.frameStale = true;
      this.following = true;
    } else this.opts.frame = prev.frame;
    if (o.showLattice && !prev.showLattice) this.latStale = true;
    if (o.interactive !== prev.interactive) this.ghostKey = '\u0000';
    this.markDirty();
  }

  /** the controller changed: redraw on the next frame (cheap, coalesced) */
  markDirty() {
    this.dirty = true;
    this.request();
  }

  /** back to the default view, following the fold again */
  resetView() {
    this.following = true;
    this.dirGoal = DEFAULT_DIR.clone();
    this.computeFit();
    this.fitActive = true;
    if (this.reducedMotion) this.snapFit();
    this.emitState();
    this.request();
  }

  /**
   * The camera-relative keyboard map handed to the shell: arrows move in the screen plane
   * (along the lattice step closest to that screen direction), W / PageUp away from the reader,
   * S / PageDown towards the reader. Lattices with more than 6 steps (FCC) put the remaining
   * steps on Shift + the same keys. Returns a step index or null.
   */
  keyMap = (key: string, e: KeyboardEvent): number | null => {
    if (e.ctrlKey || e.metaKey || e.altKey) return null;
    const slot = KEY_SLOTS[key];
    if (slot === undefined) return null;
    const a = this.assignment();
    const useShift = e.shiftKey && a[1].some((k) => k !== null);
    const k = (useShift ? a[1] : a[0])[slot];
    this.pingKeys();
    return k ?? null;
  };

  dispose() {
    this.disposed = true;
    if (this.raf) cancelAnimationFrame(this.raf);
    clearTimeout(this.keyTimer);
    clearTimeout(this.latTimer);
    this.ro.disconnect();
    for (const f of this.cleanups) f();
    this.controls.removeEventListener('change', this.onControlsChange);
    this.controls.removeEventListener('start', this.onControlsStart);
    this.controls.removeEventListener('end', this.onControlsEnd);
    this.controls.dispose();
    if (this.ownHover !== null && this.controller.hover === this.ownHover) this.controller.setHover(null);
    const geos = new Set<THREE.BufferGeometry>();
    const mats = new Set<THREE.Material>();
    this.scene.traverse((o) => {
      const m = o as THREE.Mesh;
      if (m.geometry) geos.add(m.geometry);
      if (m.material) (Array.isArray(m.material) ? m.material : [m.material]).forEach((x) => mats.add(x));
    });
    for (const g of [this.bondGeo, this.contactGeo, this.ghostGeo, this.ringGeo, this.hoverRingGeo]) geos.add(g);
    for (const m of [this.ghostMat, this.ghostHoverMat]) mats.add(m);
    geos.forEach((g) => g.dispose());
    mats.forEach((m) => m.dispose());
    this.renderer.dispose();
    this.renderer.forceContextLoss();
    this.renderer.domElement.remove();
    this.els.labels.replaceChildren();
    this.els.gizmo.replaceChildren();
  }

  // ---------- frame loop ----------

  private request() {
    if (!this.raf && !this.disposed) this.raf = requestAnimationFrame(this.frame);
  }

  private frame = (now: number) => {
    this.raf = 0;
    if (this.disposed) return;
    const dt = this.lastFrame ? Math.min(0.1, (now - this.lastFrame) / 1000) : 1 / 60;
    this.lastFrame = now;
    if (this.dirty) this.sync();
    let more = false;
    if (this.fitActive && this.following && !this.dragging) more = this.stepFit(dt);
    if (this.controls.update()) more = true;
    this.lastRing.quaternion.copy(this.camera.quaternion);
    this.hoverRing.quaternion.copy(this.camera.quaternion);
    this.renderer.render(this.scene, this.camera);
    this.updateOverlay();
    if (more || this.dirty) this.request();
    else this.lastFrame = 0;
  };

  // ---------- syncing the fold ----------

  private sync() {
    this.dirty = false;
    const fold = this.controller.fold;
    const lat = fold.lattice;
    const seq = fold.seq;
    const path = fold.path;
    const placed = path.length;
    let full = false;

    if (lat !== this.lattice) {
      this.setLattice(lat);
      full = true;
    }
    if (fold !== this.fold) {
      // a new fold object re-fits the view, unless a fixed frame holds the camera still
      if (this.fold && !this.opts.frame) this.following = true;
      this.fold = fold;
      full = true;
    }
    if (this.capRes < fold.length || !this.residues) {
      this.allocResidues(Math.max(1, fold.length));
      full = true;
    }
    if (this.capBond < fold.length - 1 || !this.bonds) {
      this.allocBonds(Math.max(1, fold.length - 1));
      full = true;
    }
    const cc = contactCapacity(seq, degree(lat));
    if (this.capContact < cc || !this.contacts) {
      this.allocContacts(cc);
      full = true;
    }

    // first residue that differs from what is drawn
    let k = 0;
    if (!full) {
      const m = Math.min(this.drawn.length, placed);
      while (k < m && this.drawn[k] === path[k]) k++;
    }
    const changed = full || k < placed || this.drawn.length !== placed;

    if (changed) {
      if (full) {
        this.drawn = [];
        this.ci = [];
        this.cj = [];
        k = 0;
      }
      // residues
      const rArr = this.residues.instanceMatrix.array as Float32Array;
      const kind = this.residues.geometry.getAttribute('aKind') as THREE.InstancedBufferAttribute;
      const kArr = kind.array as Float32Array;
      for (let i = k; i < placed; i++) {
        const e = lat.embed(path[i]);
        const o = i * 3;
        this.pos[o] = e[0];
        this.pos[o + 1] = e[1];
        this.pos[o + 2] = e[2];
        const b = i * 16;
        rArr.fill(0, b, b + 16);
        rArr[b] = rArr[b + 5] = rArr[b + 10] = rArr[b + 15] = 1;
        rArr[b + 12] = e[0];
        rArr[b + 13] = e[1];
        rArr[b + 14] = e[2];
        kArr[i] = seq[i] === 'H' ? 0 : 1;
      }
      this.residues.count = placed;
      touch(this.residues.instanceMatrix, 16, k, placed);
      touch(kind, 1, k, placed);

      // backbone: bond i joins residues i and i+1
      const bArr = this.bonds.instanceMatrix.array as Float32Array;
      const b0 = Math.max(0, k - 1);
      for (let i = b0; i < placed - 1; i++) this.writeSegment(bArr, i, i, i + 1);
      this.bonds.count = Math.max(0, placed - 1);
      touch(this.bonds.instanceMatrix, 16, b0, placed - 1);

      // contacts (ordered by their larger index j): drop those with j ≥ k, add those of j ≥ k
      while (this.cj.length && this.cj[this.cj.length - 1] >= k) {
        this.cj.pop();
        this.ci.pop();
      }
      const c0 = this.cj.length;
      for (let j = k; j < placed; j++) {
        if (seq[j] !== 'H') continue;
        for (const w of neighbours(lat, path[j])) {
          const i = fold.at(w);
          if (i !== undefined && i < j - 1 && seq[i] === 'H') {
            this.ci.push(i);
            this.cj.push(j);
          }
        }
      }
      // the capacity is an upper bound on the number of contacts; clamp anyway
      const nc = Math.min(this.cj.length, this.capContact);
      const cArr = this.contacts.instanceMatrix.array as Float32Array;
      for (let c = c0; c < nc; c++) this.writeSegment(cArr, c, this.ci[c], this.cj[c]);
      this.contacts.count = nc;
      this.contactCount = nc;
      touch(this.contacts.instanceMatrix, 16, c0, nc);

      this.drawn.length = Math.min(this.drawn.length, k);
      for (let i = this.drawn.length; i < placed; i++) this.drawn.push(path[i]);

      this.latStale = true;
      this.updateBox();
    }
    this.applyCut(changed);

    this.contacts.visible = this.opts.showContacts;
    if (this.opts.showLattice && this.latStale) this.maybeBuildLatticeHint();
    this.dots.visible = this.opts.showLattice && this.dots.geometry.getAttribute('position') !== undefined;
    this.floor.visible = this.opts.showLattice && this.floorCount > 0;
    this.box.visible = this.boxAvailable && this.opts.showBox;

    const ghostsChanged = this.syncGhosts();
    this.syncMarkers();
    // with a frame the fit depends on the frame only, so the camera stays still while scrubbing
    if (this.opts.frame ? this.frameStale || this.snapNext : changed || ghostsChanged || this.frameStale) {
      this.computeFit();
      if (this.following) {
        this.fitActive = true;
        if (this.snapNext || this.reducedMotion) this.snapFit();
      }
    }
    this.snapNext = false;
    this.frameStale = false;
    const lk = `${placed}|${this.opts.showIndices}`;
    if (changed || lk !== this.labelKey) {
      this.labelKey = lk;
      this.updateLabelSet();
    }
    this.emitState();
    // the pointer may now be over something else (e.g. the residue just placed)
    if (this.pointer && !this.dragging && (changed || ghostsChanged)) this.hoverAt(this.pointer.x, this.pointer.y, this.pointer.touch);
  }

  /** the cut to draw: controller.cut while it is a residue before the last one */
  private get cut(): number | null {
    const c = this.controller.cut;
    return this.opts.interactive && c !== null && c < this.controller.fold.path.length - 1 ? c : null;
  }

  /** fade the residues after the cut and hide their contacts (kinds 2/3 in the shader) */
  private applyCut(force: boolean) {
    const cut = this.cut;
    if (!force && cut === this.cutDrawn) return;
    const prev = this.cutDrawn;
    this.cutDrawn = cut;
    const fold = this.controller.fold;
    const placed = Math.min(fold.path.length, this.residues.count);
    const kind = this.residues.geometry.getAttribute('aKind') as THREE.InstancedBufferAttribute;
    const kArr = kind.array as Float32Array;
    const from = Math.max(0, Math.min(cut ?? placed, prev ?? placed, force ? 0 : placed));
    for (let i = from; i < placed; i++) kArr[i] = (fold.seq[i] === 'H' ? 0 : 1) + (cut !== null && i > cut ? 2 : 0);
    touch(kind, 1, from, placed);
    let nc = this.contactCount;
    if (cut !== null) while (nc > 0 && this.cj[nc - 1] > cut) nc--;
    this.contacts.count = nc;
  }

  private writeSegment(arr: Float32Array, slot: number, a: number, b: number) {
    const p = this.pos;
    _v.set(p[a * 3], p[a * 3 + 1], p[a * 3 + 2]);
    _w.set(p[b * 3], p[b * 3 + 1], p[b * 3 + 2]);
    _w.sub(_v);
    const len = _w.length() || 1;
    _q.setFromUnitVectors(_Y, _w.divideScalar(len));
    _v.addScaledVector(_w, len / 2);
    _s.set(1, len, 1);
    _m.compose(_v, _q, _s);
    _m.toArray(arr, slot * 16);
  }

  /** unit drawing directions of the steps at node v, and the index of each step's opposite (−1: none) */
  private stepsHere(v: Vec): { dirs: THREE.Vector3[]; opp: number[] } {
    const lat = this.controller.fold.lattice;
    const steps = stepsAt(lat, v);
    const o = lat.embed(v);
    const dirs = steps.map((s) => {
      const e = lat.embed(v.map((x, i) => x + s[i]));
      return new THREE.Vector3(e[0] - o[0], e[1] - o[1], e[2] - o[2]).normalize();
    });
    const opp = steps.map((s) => steps.findIndex((t) => t.every((x, i) => x === -s[i])));
    return { dirs, opp };
  }

  private setLattice(lat: Lattice) {
    this.lattice = lat;
    const o = lat.embed(lat.steps[0].map(() => 0));
    this.stepDirs = lat.steps.map((s) => {
      const e = lat.embed(s);
      return new THREE.Vector3(e[0] - o[0], e[1] - o[1], e[2] - o[2]).normalize();
    });
    this.stepOpp = lat.steps.map((s) => lat.steps.findIndex((t) => t.every((x, i) => x === -s[i])));
    const unit = (s: readonly number[]) => s.filter((x) => x !== 0).length === 1 && s.every((x) => Math.abs(x) <= 1);
    this.cubicLike =
      lat.steps.length === 6 &&
      lat.steps.every(unit) &&
      lat.steps.every((s) => {
        const e = lat.embed(s);
        return e.every((x, i) => Math.abs(x - s[i]) < 1e-9);
      });
    // ghost pool: one mesh per possible step
    for (const g of this.ghosts) this.world.remove(g);
    this.ghosts = lat.steps.map(() => {
      const g = new THREE.Mesh(this.ghostGeo, this.ghostMat);
      g.visible = false;
      g.renderOrder = 2;
      this.world.add(g);
      return g;
    });
    this.ghostKey = '\u0000';
    this.prevAssign.clear();
    this.latKey = '';
  }

  private allocResidues(cap: number) {
    if (this.residues) {
      this.world.remove(this.residues);
      this.residues.geometry.dispose();
      this.residues.dispose();
    }
    // fewer facets for big folds: thousands of spheres stay cheap
    const detail = cap <= 600 ? 0 : cap <= 2500 ? 1 : 2;
    const [ws, hs] = [
      [28, 18],
      [18, 12],
      [14, 10],
    ][detail];
    this.sphereDetail = detail;
    const geo = new THREE.SphereGeometry(R_RES, ws, hs);
    const kind = new THREE.InstancedBufferAttribute(new Float32Array(cap), 1);
    kind.setUsage(THREE.DynamicDrawUsage);
    geo.setAttribute('aKind', kind);
    this.residues = makeInstanced(geo, this.resMat, cap);
    this.world.add(this.residues);
    this.capRes = cap;
    this.pos = new Float32Array(cap * 3);
  }

  private allocBonds(cap: number) {
    if (this.bonds) {
      this.world.remove(this.bonds);
      this.bonds.dispose();
    }
    this.bonds = makeInstanced(this.bondGeo, this.bondMat, cap);
    this.world.add(this.bonds);
    this.capBond = cap;
  }

  private allocContacts(cap: number) {
    if (this.contacts) {
      this.world.remove(this.contacts);
      this.contacts.dispose();
    }
    this.contacts = makeInstanced(this.contactGeo, this.contactMat, cap);
    this.world.add(this.contacts);
    this.capContact = cap;
    this.ci = [];
    this.cj = [];
  }

  /** ghosts = legal next positions; returns true if they changed */
  private syncGhosts(): boolean {
    const fold = this.controller.fold;
    const lat = fold.lattice;
    const opts = this.opts.interactive && !fold.complete && this.cut === null ? fold.options() : [];
    const key = opts.map((v) => v.join(',')).join('|');
    if (key === this.ghostKey) return false;
    this.ghostKey = key;
    const last = fold.last;
    this.ghostPos = opts;
    this.ghostStep = opts.map((v) => (last ? stepIndex(lat, last, v) : -1));
    this.ghosts.forEach((g, i) => {
      const v = opts[i];
      g.visible = !!v;
      if (v) {
        const e = lat.embed(v);
        g.position.set(e[0], e[1], e[2]);
      }
    });
    this.setHoverGhost(-1);
    return true;
  }

  private syncMarkers() {
    const fold = this.controller.fold;
    const placed = fold.path.length;
    const p = this.pos;
    if (placed > 0) {
      const i = this.cut ?? placed - 1;
      this.lastRing.position.set(p[i * 3], p[i * 3 + 1], p[i * 3 + 2]);
      this.lastRing.visible = true;
      const stuck = this.opts.interactive && fold.stuck && this.cut === null;
      this.lastRingMat.color.copy(stuck ? this.colors.invalid : this.cut !== null ? this.colors.accent : this.colors.fg);
      this.lastRingMat.opacity = stuck || this.cut !== null ? 0.95 : 0.6;
    } else this.lastRing.visible = false;
    const h = this.controller.hover;
    if (h !== null && h >= 0 && h < placed && this.cut === null) {
      this.hoverRing.position.set(p[h * 3], p[h * 3 + 1], p[h * 3 + 2]);
      this.hoverRing.visible = true;
    } else this.hoverRing.visible = false;
  }

  /** H core box: on the cubic lattice, when the placed H's fill a box exactly */
  private updateBox() {
    let avail = false;
    const fold = this.controller.fold;
    if (this.cubicLike) {
      const lo = [Infinity, Infinity, Infinity];
      const hi = [-Infinity, -Infinity, -Infinity];
      let nh = 0;
      fold.path.forEach((v, i) => {
        if (fold.seq[i] !== 'H') return;
        nh++;
        for (let d = 0; d < 3; d++) {
          if (v[d] < lo[d]) lo[d] = v[d];
          if (v[d] > hi[d]) hi[d] = v[d];
        }
      });
      const ext = [0, 1, 2].map((d) => hi[d] - lo[d] + 1);
      if (nh >= 8 && ext.every((x) => x >= 2) && ext[0] * ext[1] * ext[2] === nh) {
        avail = true;
        const a = lo.map((x) => x - 0.5);
        const b = hi.map((x) => x + 0.5);
        const c = (i: number) => [i & 1 ? b[0] : a[0], i & 2 ? b[1] : a[1], i & 4 ? b[2] : a[2]];
        const edges: number[] = [];
        for (let i = 0; i < 8; i++)
          for (const bit of [1, 2, 4]) if (!(i & bit)) edges.push(...c(i), ...c(i | bit));
        (this.box.geometry as LineSegmentsGeometry).setPositions(edges);
      }
    }
    this.boxAvailable = avail;
  }

  /** residues that get an index label: all for small folds, every k-th for big ones */
  private updateLabelSet() {
    const placed = this.controller.fold.path.length;
    if (!this.opts.showIndices || placed === 0) {
      this.labelIdx = [];
      return;
    }
    const stride = [1, 2, 5, 10, 20, 50, 100, 200, 500, 1000].find((s) => placed / s <= 120) ?? 1000;
    // labels show 1-based numbers: residue 1, every multiple of the stride, and the last one
    const out: number[] = [0];
    for (let n = stride; n <= placed; n += stride) if (n > 1) out.push(n - 1);
    if (out[out.length - 1] !== placed - 1) out.push(placed - 1);
    this.labelIdx = out;
  }

  // ---------- lattice hint ----------

  private floorCount = 0;
  private latBuiltAt = -Infinity;
  private latTimer = 0;

  /** rebuild the lattice hint when the box around the fold changed, at most every 150 ms */
  private maybeBuildLatticeHint() {
    const now = performance.now();
    if (now - this.latBuiltAt > 150) {
      this.latStale = false;
      if (this.buildLatticeHint()) this.latBuiltAt = now;
    } else if (!this.latTimer) {
      this.latTimer = window.setTimeout(() => {
        this.latTimer = 0;
        this.markDirty();
      }, 160);
    }
  }

  /**
   * Faint lattice around the fold: points in the box around it (padded by one step) and a grid
   * on the layer below it (two steps wider). Small boxes get every lattice point and edge
   * (found by BFS, so any lattice works); big ones only a coarse square grid on the floor,
   * which assumes that lattice coordinate 1 is vertical (true for cubic and FCC).
   * Returns true if anything was rebuilt.
   */
  private buildLatticeHint(): boolean {
    const fold = this.controller.fold;
    const lat = fold.lattice;
    const path = fold.path;
    if (!path.length) return false;
    const lo = [...path[0]];
    const hi = [...path[0]];
    for (const v of path)
      for (let d = 0; d < 3; d++) {
        if (v[d] < lo[d]) lo[d] = v[d];
        if (v[d] > hi[d]) hi[d] = v[d];
      }
    const lo1 = lo.map((x) => x - 1);
    const hi1 = hi.map((x) => x + 1);
    for (let d = 0; d < 3; d++) {
      lo[d] -= 2;
      hi[d] += 2;
    }
    const key = lo.join(',') + ':' + hi.join(',');
    if (key === this.latKey) return false;
    this.latKey = key;
    const W = hi[0] - lo[0] + 1;
    const H = hi[1] - lo[1] + 1;
    const D = hi[2] - lo[2] + 1;
    const vol = W * H * D;
    const dotGeo = new THREE.BufferGeometry();
    let seg: number[] = [];
    let fine = false;

    if (vol <= 120_000) {
      // lattice points in the box: BFS from residue 0
      const seen = new Uint8Array(vol);
      const queue = new Int32Array(vol);
      const idx = (x: number, y: number, z: number) => x - lo[0] + W * (y - lo[1] + H * (z - lo[2]));
      const inBox = (x: number, y: number, z: number) =>
        x >= lo[0] && x <= hi[0] && y >= lo[1] && y <= hi[1] && z >= lo[2] && z <= hi[2];
      let head = 0;
      let tail = 0;
      const s0 = path[0];
      seen[idx(s0[0], s0[1], s0[2])] = 1;
      queue[tail++] = idx(s0[0], s0[1], s0[2]);
      const steps = lat.steps;
      while (head < tail) {
        const f = queue[head++];
        const x = lo[0] + (f % W);
        const y = lo[1] + (Math.floor(f / W) % H);
        const z = lo[2] + Math.floor(f / (W * H));
        for (const s of stepsAt(lat, [x, y, z])) {
          const nx = x + s[0];
          const ny = y + s[1];
          const nz = z + s[2];
          if (!inBox(nx, ny, nz)) continue;
          const g = idx(nx, ny, nz);
          if (seen[g]) continue;
          seen[g] = 1;
          queue[tail++] = g;
        }
      }
      const coords = (f: number) => [lo[0] + (f % W), lo[1] + (Math.floor(f / W) % H), lo[2] + Math.floor(f / (W * H))];
      const inner = (v: number[]) => v.every((x, d) => x >= lo1[d] && x <= hi1[d]);
      const dots: number[] = [];
      let minY = Infinity;
      let nInner = 0;
      for (let i = 0; i < tail; i++) {
        const v = coords(queue[i]);
        if (!inner(v)) continue;
        nInner++;
        const e = lat.embed(v);
        if (e[1] < minY) minY = e[1];
        if (dots.length < 3 * 6000) dots.push(e[0], e[1], e[2]);
      }
      // a dense cloud of points is noise: only for boxes of up to 6000 points
      if (nInner <= 6000 && dots.length) dotGeo.setAttribute('position', new THREE.Float32BufferAttribute(dots, 3));
      if (lat.stepsAt) {
        // two kinds of node (diamond): no step is horizontal, so no floor; the edges around the
        // fold instead (from nodes of the first kind, so that each edge is drawn once)
        const k0 = stepsAt(lat, s0);
        for (let i = 0; i < tail && seg.length <= 6 * 2400; i++) {
          const v = coords(queue[i]);
          if (!inner(v) || stepsAt(lat, v) !== k0) continue;
          const e = lat.embed(v);
          for (const w of neighbours(lat, v)) {
            if (!inner(w)) continue;
            const ew = lat.embed(w);
            seg.push(e[0], e[1], e[2], ew[0], ew[1], ew[2]);
          }
        }
        fine = seg.length <= 6 * 2400;
        if (!fine) seg = [];
      }
      // floor: the lowest layer of the inner box, extended to the outer box, joined by the steps in it
      const flat = lat.stepsAt ? [] : steps
        .map((s, i) => ({ s, i, e: lat.embed(s) }))
        .filter(({ e, i }) => Math.abs(e[1]) < 1e-9 && (this.stepOpp[i] < 0 || i < this.stepOpp[i]));
      for (let i = 0; i < tail && seg.length <= 6 * 2400; i++) {
        const v = coords(queue[i]);
        const e = lat.embed(v);
        if (Math.abs(e[1] - minY) > 1e-6) continue;
        for (const { s, e: es } of flat) {
          const nx = v[0] + s[0];
          const ny = v[1] + s[1];
          const nz = v[2] + s[2];
          if (!inBox(nx, ny, nz) || !seen[idx(nx, ny, nz)]) continue;
          seg.push(e[0], minY, e[2], e[0] + es[0], minY, e[2] + es[2]);
        }
      }
      if (!lat.stepsAt) fine = seg.length <= 6 * 2400;
    }
    if (!fine && !lat.stepsAt) {
      // coarse square grid on the floor layer, at most ~24 lines each way
      const ext = Math.max(W, D);
      const k = [1, 2, 4, 5, 8, 10, 20, 25, 50, 100, 200, 500].find((x) => ext / x <= 24) ?? 1000;
      const y0 = lo1[1];
      const x0 = Math.ceil(lo[0] / k) * k;
      const z0 = Math.ceil(lo[2] / k) * k;
      seg = [];
      const push = (a: number[], b: number[]) => {
        const ea = lat.embed(a);
        const eb = lat.embed(b);
        seg.push(ea[0], ea[1], ea[2], eb[0], eb[1], eb[2]);
      };
      for (let x = x0; x <= hi[0]; x += k) push([x, y0, lo[2]], [x, y0, hi[2]]);
      for (let z = z0; z <= hi[2]; z += k) push([lo[0], y0, z], [hi[0], y0, z]);
    }
    const floorGeo = new LineSegmentsGeometry();
    if (seg.length) floorGeo.setPositions(seg);
    this.floorCount = seg.length / 6;
    this.dots.geometry.dispose();
    this.dots.geometry = dotGeo;
    this.floor.geometry.dispose();
    this.floor.geometry = floorGeo;
    return true;
  }

  // ---------- camera ----------

  /**
   * Where the camera should be to frame the fold and its ghosts, seen from the current
   * direction (or the direction of a running reset): the target is the centre of the
   * projected extent and the distance the smallest that keeps every residue in the frustum.
   */
  private computeFit() {
    const frame = this.opts.frame;
    let placed = this.controller.fold.path.length;
    let p = this.pos;
    const pts: number[] = [];
    if (frame && frame.length) {
      // fit the given lattice points instead of the residues and ghosts
      const lat = this.controller.fold.lattice;
      p = new Float32Array(frame.length * 3);
      frame.forEach((v, i) => {
        const e = lat.embed(v as number[]);
        p[i * 3] = e[0];
        p[i * 3 + 1] = e[1];
        p[i * 3 + 2] = e[2];
      });
      placed = frame.length;
    } else for (const g of this.ghosts) if (g.visible) pts.push(g.position.x, g.position.y, g.position.z);
    const n = placed + pts.length / 3;
    const at = (i: number, d: number) => (i < placed ? p[i * 3 + d] : pts[(i - placed) * 3 + d]);

    const back = this.dirGoal ? _w.copy(this.dirGoal) : _w.copy(this.camera.position).sub(this.controls.target);
    if (!isFinite(back.x) || back.lengthSq() < 1e-6) back.copy(DEFAULT_DIR);
    back.normalize();
    const right = new THREE.Vector3().crossVectors(_Y, back);
    if (right.lengthSq() < 1e-6) right.set(1, 0, 0);
    right.normalize();
    const up = new THREE.Vector3().crossVectors(back, right);

    // centre of the bounding box, then of the extent projected on the screen plane
    const lo = [Infinity, Infinity, Infinity];
    const hi = [-Infinity, -Infinity, -Infinity];
    for (let i = 0; i < n; i++)
      for (let d = 0; d < 3; d++) {
        const x = at(i, d);
        if (x < lo[d]) lo[d] = x;
        if (x > hi[d]) hi[d] = x;
      }
    if (n === 0) {
      lo.fill(0);
      hi.fill(0);
    }
    const c = new THREE.Vector3((lo[0] + hi[0]) / 2, (lo[1] + hi[1]) / 2, (lo[2] + hi[2]) / 2);
    let r0 = Infinity;
    let r1 = -Infinity;
    let u0 = Infinity;
    let u1 = -Infinity;
    for (let i = 0; i < n; i++) {
      _v.set(at(i, 0) - c.x, at(i, 1) - c.y, at(i, 2) - c.z);
      const r = _v.dot(right);
      const u = _v.dot(up);
      if (r < r0) r0 = r;
      if (r > r1) r1 = r;
      if (u < u0) u0 = u;
      if (u > u1) u1 = u;
    }
    if (n > 0) c.addScaledVector(right, (r0 + r1) / 2).addScaledVector(up, (u0 + u1) / 2);

    const tv = Math.tan(THREE.MathUtils.degToRad(FOV) / 2);
    const th = tv * this.camera.aspect;
    const m = R_RES + 0.3;
    let dist = 0;
    for (let i = 0; i < n; i++) {
      _v.set(at(i, 0) - c.x, at(i, 1) - c.y, at(i, 2) - c.z);
      const b = _v.dot(back);
      dist = Math.max(dist, b + (Math.abs(_v.dot(right)) + m) / th, b + (Math.abs(_v.dot(up)) + m) / tv);
    }
    this.fitCenter.copy(c);
    this.fitDist = Math.max(dist * 1.05, 2.4 / Math.min(tv, th));
    this.controls.maxDistance = Math.min(3000, Math.max(60, this.fitDist * 8));
  }

  private snapFit() {
    const dir = this.dirGoal ?? _v.copy(this.camera.position).sub(this.controls.target).normalize();
    if (!isFinite(dir.x) || dir.lengthSq() < 0.5) dir.copy(DEFAULT_DIR);
    this.controls.target.copy(this.fitCenter);
    this.camera.position.copy(this.fitCenter).addScaledVector(dir, this.fitDist);
    this.dirGoal = null;
    this.fitActive = false;
    this.setExpected();
    this.camera.lookAt(this.fitCenter);
  }

  /** one step of the smooth fit; returns true while still moving */
  private stepFit(dt: number): boolean {
    const k = this.reducedMotion ? 1 : 1 - Math.exp(-dt / 0.16);
    const t = this.controls.target;
    const off = _v.copy(this.camera.position).sub(t);
    let dist = off.length();
    const dir = off.divideScalar(dist || 1);
    if (this.dirGoal) {
      _q.setFromUnitVectors(dir, this.dirGoal);
      dir.applyQuaternion(new THREE.Quaternion().slerp(_q, k));
      if (dir.angleTo(this.dirGoal) < 1e-3) {
        dir.copy(this.dirGoal);
        this.dirGoal = null;
      }
    }
    t.lerp(this.fitCenter, k);
    dist += (this.fitDist - dist) * k;
    const eps = 1e-3 * this.fitDist;
    const done = !this.dirGoal && t.distanceTo(this.fitCenter) < eps && Math.abs(dist - this.fitDist) < eps;
    if (done) {
      t.copy(this.fitCenter);
      dist = this.fitDist;
      this.fitActive = false;
    }
    this.camera.position.copy(t).addScaledVector(dir, dist);
    this.setExpected();
    return !done;
  }

  private setExpected() {
    this.expTarget.copy(this.controls.target);
    this.expDist = this.camera.position.distanceTo(this.controls.target);
  }

  private onControlsChange = () => {
    // a change of distance or target that we did not make = the reader zoomed or panned
    const dist = this.camera.position.distanceTo(this.controls.target);
    const tol = 1e-3 * Math.max(1, this.expDist);
    if (Math.abs(dist - this.expDist) > tol || this.controls.target.distanceTo(this.expTarget) > tol) {
      if (this.following) {
        this.following = false;
        this.fitActive = false;
        this.dirGoal = null;
        this.emitState();
      }
      this.setExpected();
    }
    this.request();
  };

  private onControlsStart = () => {
    this.dragging = true;
    this.dirGoal = null;
  };

  private onControlsEnd = () => {
    this.dragging = false;
    this.request();
  };

  private resize() {
    const r = this.els.host.getBoundingClientRect();
    const w = Math.max(1, Math.round(r.width));
    const h = Math.max(1, Math.round(r.height));
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    if (dpr !== this.renderer.getPixelRatio()) this.renderer.setPixelRatio(dpr);
    this.renderer.setSize(w, h, false);
    const first = this.cssW <= 1;
    this.cssW = w;
    this.cssH = h;
    this.camera.aspect = w / h;
    this.camera.updateProjectionMatrix();
    const pxWorld = (2 * Math.tan(THREE.MathUtils.degToRad(FOV) / 2)) / h;
    this.bondMat.uniforms.uPxWorld.value = pxWorld;
    this.contactMat.uniforms.uPxWorld.value = pxWorld;
    this.dotMat.uniforms.uPxWorld.value = pxWorld;
    this.dotMat.uniforms.uDpr.value = dpr;
    if (this.fold) {
      this.computeFit();
      if (this.following) {
        if (first) this.snapFit();
        else this.fitActive = true;
      }
    }
    this.request();
  }

  private applyTheme() {
    const c = readColors();
    const k = Object.keys(c) as (keyof Colors)[];
    // the uniforms hold references to these Color objects: copy in place
    for (const name of k) this.colors[name].copy(c[name]);
    this.floorMat.color = this.colors.lattice;
    this.boxMat.color = this.colors.h;
    this.hoverRingMat.color.copy(this.colors.accent);
    this.previewMat.color.copy(this.colors.ghost);
    this.syncMarkers();
    this.request();
  }

  private onContextLost = (e: Event) => {
    e.preventDefault();
  };

  // ---------- picking and pointer ----------

  private pick(x: number, y: number, touchInput: boolean, residuesOnly = false): PickHit {
    const ndc = new THREE.Vector2((x / this.cssW) * 2 - 1, -(y / this.cssH) * 2 + 1);
    this.raycaster.setFromCamera(ndc, this.camera);
    const o = this.raycaster.ray.origin;
    const d = this.raycaster.ray.direction;
    const hit = (cx: number, cy: number, cz: number, r: number) => {
      const px = cx - o.x;
      const py = cy - o.y;
      const pz = cz - o.z;
      const t = px * d.x + py * d.y + pz * d.z;
      if (t < 0) return Infinity;
      const d2 = px * px + py * py + pz * pz - t * t;
      if (d2 > r * r) return Infinity;
      return t - Math.sqrt(r * r - d2);
    };
    let bestRes = Infinity;
    let res = -1;
    const p = this.pos;
    const placed = this.residues.count;
    const rr = R_RES * (touchInput ? 1.15 : 1.02);
    for (let i = 0; i < placed; i++) {
      const t = hit(p[i * 3], p[i * 3 + 1], p[i * 3 + 2], rr);
      if (t < bestRes) {
        bestRes = t;
        res = i;
      }
    }
    let bestGhost = Infinity;
    let ghost = -1;
    const rg = R_GHOST * (touchInput ? 2.1 : 1.5);
    this.ghosts.forEach((g, i) => {
      if (!g.visible || residuesOnly) return;
      const t = hit(g.position.x, g.position.y, g.position.z, rg);
      if (t < bestGhost) {
        bestGhost = t;
        ghost = i;
      }
    });
    // ghosts sit next to residues: let a ghost win unless a residue is clearly in front of it
    if (ghost >= 0 && bestGhost < bestRes + 0.6) return { kind: 'ghost', index: ghost };
    if (res >= 0) return { kind: 'residue', index: res };
    return null;
  }

  private hoverAt(x: number, y: number, touchInput: boolean) {
    const mod = this.modDown && this.opts.interactive;
    const h = this.pick(x, y, touchInput, mod);
    this.setHoverGhost(h?.kind === 'ghost' ? h.index : -1);
    const res = h?.kind === 'residue' ? h.index : null;
    if (!touchInput) this.setResidueHover(res);
    // the truncation preview: only while the modifier is held over a residue before the last
    const c = this.controller;
    const cut = mod && res !== null && res < c.fold.path.length - 1 ? res : null;
    if (cut !== null || c.cut !== null) c.setCut(cut);
    this.els.host.style.cursor =
      h?.kind === 'ghost' || cut !== null ? 'pointer' : this.dragging ? 'grabbing' : 'grab';
  }

  private setMod(down: boolean) {
    if (down === this.modDown) return;
    this.modDown = down;
    if (this.pointer && !this.dragging) this.hoverAt(this.pointer.x, this.pointer.y, false);
    else if (!down && this.controller.cut !== null) this.controller.setCut(null);
  }

  private setResidueHover(i: number | null) {
    const c = this.controller;
    if (i === null) {
      if (this.ownHover !== null && c.hover === this.ownHover) c.setHover(null);
      this.ownHover = null;
      return;
    }
    this.ownHover = i;
    if (c.hover !== i) c.setHover(i);
  }

  private setHoverGhost(i: number) {
    if (i === this.hoverGhost) return;
    const prev = this.ghosts[this.hoverGhost];
    if (prev) {
      prev.material = this.ghostMat;
      prev.scale.setScalar(1);
    }
    this.hoverGhost = i;
    const g = this.ghosts[i];
    const last = this.controller.fold.path.length - 1;
    if (g && last >= 0) {
      g.material = this.ghostHoverMat;
      g.scale.setScalar(1.15);
      const p = this.pos;
      _v.set(p[last * 3], p[last * 3 + 1], p[last * 3 + 2]);
      _w.copy(g.position).sub(_v);
      const len = _w.length();
      this.preview.position.copy(_v).addScaledVector(_w, 0.5);
      this.preview.quaternion.setFromUnitVectors(_Y, _w.divideScalar(len));
      this.preview.scale.set(1, len, 1);
      this.preview.visible = true;
    } else this.preview.visible = false;
    this.request();
  }

  private localXY(e: PointerEvent) {
    const r = this.els.host.getBoundingClientRect();
    return { x: e.clientX - r.left, y: e.clientY - r.top };
  }

  private onPointerDown = (e: PointerEvent) => {
    this.activePointers.add(e.pointerId);
    const { x, y } = this.localXY(e);
    this.down =
      this.activePointers.size === 1
        ? { x, y, t: performance.now(), id: e.pointerId, touch: e.pointerType !== 'mouse', mod: e.ctrlKey || e.metaKey }
        : null;
    this.els.host.style.cursor = 'grabbing';
  };

  private onPointerMove = (e: PointerEvent) => {
    const { x, y } = this.localXY(e);
    const touchInput = e.pointerType !== 'mouse';
    if (!touchInput) this.modDown = e.ctrlKey || e.metaKey;
    if (this.down && Math.hypot(x - this.down.x, y - this.down.y) > (this.down.touch ? 10 : 5)) this.down = null;
    if (e.buttons === 0 && !touchInput) {
      this.pointer = { x, y, touch: false };
      this.hoverAt(x, y, false);
    }
  };

  private onPointerUp = (e: PointerEvent) => {
    this.activePointers.delete(e.pointerId);
    const d = this.down;
    this.down = null;
    const { x, y } = this.localXY(e);
    const touchInput = e.pointerType !== 'mouse';
    if (!d || d.id !== e.pointerId || performance.now() - d.t > 700) {
      if (!touchInput) this.hoverAt(x, y, false);
      return;
    }
    // a tap / click
    this.lastTouch = touchInput;
    const c = this.controller;
    // the modifier counts if it was down at either end of the click
    const mod = e.ctrlKey || e.metaKey || d.mod;
    const h = this.pick(x, y, touchInput, mod && this.opts.interactive);
    const placed = c.fold.path.length;
    if (h?.kind === 'ghost') {
      const v = this.ghostPos[h.index];
      if (v) c.extendTo(v);
    } else if (
      h?.kind === 'residue' &&
      this.opts.interactive &&
      h.index < placed - 1 &&
      (mod || (touchInput && c.hover === h.index))
    ) {
      // go back to this residue: modifier-click, or a second tap on a selected residue
      c.truncate(h.index + 1);
      if (touchInput) this.setResidueHover(null);
    } else if (touchInput) {
      // no hover on touch screens: a tap on a residue highlights it, a tap elsewhere clears
      this.setResidueHover(h?.kind === 'residue' ? h.index : null);
    }
    if (!touchInput) {
      this.pointer = { x, y, touch: false };
      this.hoverAt(x, y, false);
    } else this.els.host.style.cursor = '';
  };

  private onPointerCancel = (e: PointerEvent) => {
    this.activePointers.delete(e.pointerId);
    this.down = null;
  };

  private onPointerLeave = (e: PointerEvent) => {
    if (e.pointerType !== 'mouse') return;
    this.pointer = null;
    this.setHoverGhost(-1);
    this.setResidueHover(null);
    if (this.controller.cut !== null) this.controller.setCut(null);
  };

  // ---------- keyboard ----------

  /**
   * Which lattice step each key moves along, for the current camera: [plain keys, Shift+keys],
   * each indexed by slot (right, left, up, down, away, toward). Greedy matching of the three
   * camera axes to pairs of opposite steps, with a little hysteresis so that the mapping does
   * not flicker while the reader orbits around a diagonal view. The steps are those at the last
   * residue; where no step has an opposite (diamond: four steps to the corners of a tetrahedron),
   * each step goes to the free slot whose direction is closest to it.
   */
  private assignment(): (number | null)[][] {
    this.camera.updateMatrixWorld();
    const e = this.camera.matrixWorld.elements;
    const axes = [
      new THREE.Vector3(e[0], e[1], e[2]).normalize(), // right
      new THREE.Vector3(e[4], e[5], e[6]).normalize(), // up
      new THREE.Vector3(-e[8], -e[9], -e[10]).normalize(), // away from the reader
    ];
    const last = this.controller.fold.last;
    const here = last ? this.stepsHere(last) : { dirs: this.stepDirs, opp: this.stepOpp };
    const n = here.dirs.length;
    const next = new Set<string>();
    if (here.opp.every((o) => o < 0)) {
      // slot 2a: along axis a, slot 2a + 1: against it
      const slotDir = (slot: number) => axes[slot >> 1].clone().multiplyScalar(slot & 1 ? -1 : 1);
      const cand: { slot: number; s: number; score: number }[] = [];
      for (let slot = 0; slot < 6; slot++)
        for (let s = 0; s < n; s++)
          cand.push({ slot, s, score: slotDir(slot).dot(here.dirs[s]) + (this.prevAssign.has(`s:${slot}:${s}`) ? 0.08 : 0) });
      cand.sort((x, y) => y.score - x.score);
      const slots: (number | null)[] = [null, null, null, null, null, null];
      const used = new Array<boolean>(n).fill(false);
      for (const { slot, s } of cand) {
        if (used[s] || slots[slot] !== null) continue;
        used[s] = true;
        slots[slot] = s;
        next.add(`s:${slot}:${s}`);
      }
      this.prevAssign = next;
      return [slots, [null, null, null, null, null, null]];
    }
    const used = new Array<boolean>(n).fill(false);
    const out: (number | null)[][] = [];
    for (let round = 0; round < 2; round++) {
      const slots: (number | null)[] = [null, null, null, null, null, null];
      const cand: { a: number; s: number; score: number }[] = [];
      for (let a = 0; a < 3; a++)
        for (let s = 0; s < n; s++) {
          if (used[s]) continue;
          const sc = axes[a].dot(here.dirs[s]) + (this.prevAssign.has(`${round}:${a}:${s}`) ? 0.08 : 0);
          if (sc > 0.05) cand.push({ a, s, score: sc });
        }
      cand.sort((x, y) => y.score - x.score);
      const done = [false, false, false];
      for (const { a, s } of cand) {
        if (done[a] || used[s]) continue;
        const o = here.opp[s];
        if (o >= 0 && used[o]) continue;
        done[a] = true;
        used[s] = true;
        slots[2 * a] = s;
        next.add(`${round}:${a}:${s}`);
        if (o >= 0) {
          used[o] = true;
          slots[2 * a + 1] = o;
        }
      }
      // lattices without opposite steps: fill the remaining "negative" slots greedily
      for (let a = 0; a < 3; a++) {
        if (slots[2 * a + 1] !== null) continue;
        let best = -1;
        let bs = 0.05;
        for (let s = 0; s < n; s++) {
          if (used[s]) continue;
          const sc = -axes[a].dot(here.dirs[s]);
          if (sc > bs) {
            bs = sc;
            best = s;
          }
        }
        if (best >= 0) {
          used[best] = true;
          slots[2 * a + 1] = best;
        }
      }
      out.push(slots);
    }
    this.prevAssign = next;
    return out;
  }

  private pingKeys() {
    this.keyRecent = performance.now();
    clearTimeout(this.keyTimer);
    clearTimeout(this.latTimer);
    this.keyTimer = window.setTimeout(() => this.request(), 4100);
    this.request();
  }

  private get keyHints(): boolean {
    return this.keyFocus || performance.now() - this.keyRecent < 4000;
  }

  private onFocusChange = () => {
    // runs after focus moved; check on the next tick so activeElement is settled
    setTimeout(() => {
      if (this.disposed) return;
      const a = document.activeElement as HTMLElement | null;
      const root = this.els.root;
      let f = false;
      if (a && a !== document.body && a !== document.documentElement && (root.contains(a) || a.contains(root))) {
        try {
          f = a.matches(':focus-visible');
        } catch {
          f = true;
        }
      }
      if (f !== this.keyFocus) {
        this.keyFocus = f;
        this.request();
      }
    }, 0);
  };

  // ---------- overlay (HTML labels, gizmo) ----------

  private emitState() {
    const s: SceneState = { following: this.following, boxAvailable: this.boxAvailable };
    const key = `${s.following}|${s.boxAvailable}`;
    if (key === this.lastState) return;
    this.lastState = key;
    this.onState(s);
  }

  private project(x: number, y: number, z: number): { x: number; y: number; depth: number } | null {
    _v.set(x, y, z).applyMatrix4(this.camera.matrixWorldInverse);
    const depth = -_v.z;
    if (depth <= this.camera.near) return null;
    _v.applyMatrix4(this.camera.projectionMatrix);
    return { x: ((_v.x + 1) / 2) * this.cssW, y: ((1 - _v.y) / 2) * this.cssH, depth };
  }

  private pool(list: HTMLSpanElement[], n: number, cls: string): HTMLSpanElement[] {
    while (list.length < n) {
      const el = document.createElement('span');
      el.className = cls;
      this.els.labels.appendChild(el);
      list.push(el);
    }
    for (let i = n; i < list.length; i++) list[i].hidden = true;
    return list;
  }

  private updateOverlay() {
    const pxWorld = (2 * Math.tan(THREE.MathUtils.degToRad(FOV) / 2)) / this.cssH;
    const p = this.pos;
    const fold = this.controller.fold;
    const placed = Math.min(this.residues.count, fold.path.length);

    // residue indices
    const idx = this.opts.showIndices ? this.labelIdx.filter((i) => i < placed) : [];
    const ip = this.pool(this.idxPool, idx.length, 'fg3-label fg3-idx');
    idx.forEach((i, j) => {
      const el = ip[j];
      const q = this.project(p[i * 3], p[i * 3 + 1], p[i * 3 + 2]);
      if (!q || q.x < -20 || q.y < -20 || q.x > this.cssW + 20 || q.y > this.cssH + 20) {
        el.hidden = true;
        return;
      }
      const rpx = R_RES / (pxWorld * q.depth);
      const t = String(i + 1);
      if (el.textContent !== t) el.textContent = t;
      el.style.transform = `translate(${(q.x + rpx * 0.75).toFixed(1)}px, ${(q.y - rpx * 0.75).toFixed(1)}px)`;
      el.hidden = false;
    });

    // key glyphs on the ghosts
    const showKeys = this.keyHints && this.opts.interactive;
    const vis = showKeys ? this.ghosts.map((g, i) => (g.visible ? i : -1)).filter((i) => i >= 0) : [];
    const kp = this.pool(this.keyPool, vis.length, 'fg3-label fg3-key');
    if (vis.length) {
      const a = this.assignment();
      vis.forEach((gi, j) => {
        const el = kp[j];
        const g = this.ghosts[gi];
        const q = this.project(g.position.x, g.position.y, g.position.z);
        const step = this.ghostStep[gi];
        let glyph = '';
        for (let r = 0; r < 2 && !glyph; r++) {
          const slot = a[r].indexOf(step);
          if (slot >= 0) glyph = (r ? '⇧' : '') + KEY_GLYPHS[slot];
        }
        if (!q || !glyph) {
          el.hidden = true;
          return;
        }
        if (el.textContent !== glyph) el.textContent = glyph;
        el.style.transform = `translate(${q.x.toFixed(1)}px, ${q.y.toFixed(1)}px)`;
        el.hidden = false;
      });
    }

    // tooltip: hovered ghost (what would be placed) or hovered residue
    const tip = this.tip;
    let tipText = '';
    let tipKind = '';
    let tipAct = '';
    let tq: { x: number; y: number; depth: number } | null = null;
    const hg = this.ghosts[this.hoverGhost];
    if (hg && hg.visible && placed < fold.length) {
      tipKind = fold.seq[placed];
      tipText = `Place residue ${placed + 1}`;
      tq = this.project(hg.position.x, hg.position.y, hg.position.z);
    } else {
      const h = this.controller.hover;
      if (h !== null && h >= 0 && h < placed) {
        tipKind = fold.seq[h];
        tipText = `Residue ${h + 1}`;
        tq = this.project(p[h * 3], p[h * 3 + 1], p[h * 3 + 2]);
        if (this.opts.interactive)
          tipAct =
            h === placed - 1
              ? 'Last placed'
              : this.cut === h
                ? `Click to remove ${residueRange(h + 2, placed)}`
                : this.lastTouch
                  ? 'Tap again to go back here'
                  : `${this.opts.modKey ?? 'Ctrl'}-click to go back here`;
      }
    }
    if (tq && tipText) {
      const rpx = R_RES / (pxWorld * tq.depth);
      const html =
        `${tipText} <b class="fg3-k${tipKind}">${tipKind}</b>` + (tipAct ? `<span class="fg3-tip-act">${tipAct}</span>` : '');
      if (tip.innerHTML !== html) tip.innerHTML = html;
      const tx = Math.min(Math.max(tq.x, 30), this.cssW - 30);
      tip.style.transform = `translate(${tx.toFixed(1)}px, ${(tq.y - rpx - 8).toFixed(1)}px)`;
      tip.hidden = false;
    } else tip.hidden = true;

    this.updateGizmo();
  }

  private buildGizmo() {
    const svg = this.els.gizmo;
    const NS = 'http://www.w3.org/2000/svg';
    svg.setAttribute('viewBox', '-30 -30 60 60');
    svg.replaceChildren();
    for (const name of ['x', 'y', 'z']) {
      const line = document.createElementNS(NS, 'line');
      line.setAttribute('x1', '0');
      line.setAttribute('y1', '0');
      line.setAttribute('class', `fg3-gz-line fg3-gz-${name}`);
      const text = document.createElementNS(NS, 'text');
      text.textContent = name;
      text.setAttribute('class', 'fg3-gz-text');
      text.setAttribute('text-anchor', 'middle');
      text.setAttribute('dominant-baseline', 'central');
      svg.append(line, text);
      this.gizmoParts.push({ line, text });
    }
  }

  private updateGizmo() {
    const e = this.camera.matrixWorld.elements;
    const parts = this.gizmoParts.map((g, i) => {
      // world axis i in camera coordinates: (right·e_i, up·e_i, back·e_i)
      const x = e[i];
      const y = e[4 + i];
      const z = e[8 + i];
      return { g, x, y, z };
    });
    // draw the axes pointing away from the reader first
    parts.sort((a, b) => a.z - b.z);
    const svg = this.els.gizmo;
    for (const { g, x, y, z } of parts) {
      g.line.setAttribute('x2', (x * 17).toFixed(2));
      g.line.setAttribute('y2', (-y * 17).toFixed(2));
      g.text.setAttribute('x', (x * 24).toFixed(2));
      g.text.setAttribute('y', (-y * 24).toFixed(2));
      const op = z < -0.2 ? '0.45' : '1';
      g.line.style.opacity = op;
      g.text.style.opacity = op;
      svg.append(g.line, g.text);
    }
  }
}
