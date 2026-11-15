/**
 * The 3D stage: beads, sticks and the camera, drawn as the folding game draws them.
 * Everything is a pure function of the props, so every video frame is deterministic.
 *
 *   <Scene3D shot={shot} beads={[...]} sticks={[...]}>{(project) => <svg labels/>}</Scene3D>
 *
 * Sizes are in lattice units (neighbouring nodes at distance 1), as in the game.
 *
 * Making a crowded cube readable (all optional, see `Scene3DProps`):
 *   solids={[innerBlock()]}   the core as one opaque, lit block, so nothing shows through the gaps
 *                             between surface beads (`innerBlock` is in cube.ts)
 *   depthCue                  things further away fade a little towards the background
 *   FADE / quiet(...)         one emphasis rule: the subject at full colour, context at FADE.context
 */
import React, { useCallback, useLayoutEffect, useMemo, useState } from 'react';
import { useRemotionEnvironment } from 'remotion';
import { ThreeCanvas } from '@remotion/three';
import { useThree } from '@react-three/fiber';
import * as THREE from 'three';
import { BEAD_FRAG, BEAD_VERT, SEG_FRAG, SEG_VERT, SOLID_FRAG, SOLID_VERT } from './shaders';
import { C, W, H } from '../theme/theme';
import type { V3 } from '../model/toy';

// game sizes
export const R_RES = 0.3;
export const R_BOND = 0.075;
export const R_CONTACT = 0.028;
export const FOV = 30;
/** the game's default viewing direction (from the target towards the camera) */
export const GAME_DIR: V3 = [0.5, 0.42, 0.76];

export interface Bead {
  pos: V3;
  color: string;
  /** P's are hollow */
  hollow?: boolean;
  /** 0..1, multiplies the radius. Not for coming or going (a bead never grows from a speck): use `opacity` */
  scale?: number;
  /**
   * Dimming, 0 = full colour, 1 = background colour. The bead stays opaque, so it hides what is
   * behind it: right for a quieted bead that stays, wrong for one coming or going (it shows as a
   * pale disc in front of other beads).
   */
  fade?: number;
  /**
   * 1 = solid (default), 0 = gone. For a bead coming or going: it is drawn see-through, after the
   * solid beads and sorted back to front, so what is behind it shows through as it fades.
   */
  opacity?: number;
  /** radius, default R_RES */
  r?: number;
}

export interface Stick {
  a: V3;
  b: V3;
  color: string;
  r?: number;
  fade?: number;
  /** dashes per unit length (contacts); 0 = solid */
  dash?: number;
  /** 0..1: draw only the first part, from a towards b */
  grow?: number;
  /**
   * This stick is an edge of the box min..max (see `cubeOutline`). Edges on the box's outline as
   * the camera sees it are drawn as given. The other edges pass in front of or behind whatever is
   * in the box, so a box full of beads would have lines across its beads: they are drawn with
   * opacity `inner` (0 = not at all, the default; 1 = a full wireframe, for an empty box).
   */
  box?: { min: V3; max: V3; inner?: number };
}

/**
 * How much of a bead at `pos` to show when the beads cover the box `shell` (the cube's surface):
 * 1 on a face that looks at the camera, 0 on a face turned away, and fading out as a face turns
 * edge-on. A bead on no face of the box (inside it, or outside like a P) shows in full.
 */
function shellShown(pos: V3, shell: Shell | undefined, eye: THREE.Vector3): number {
  if (!shell) return 1;
  for (let i = 0; i < 3; i++) if (pos[i] < shell.min[i] - 1e-6 || pos[i] > shell.max[i] + 1e-6) return 1;
  const e = [eye.x, eye.y, eye.z];
  let on = false;
  let best = 0;
  for (let i = 0; i < 3; i++) {
    const hi = Math.abs(pos[i] - shell.max[i]) < 1e-6;
    const lo = Math.abs(pos[i] - shell.min[i]) < 1e-6;
    if (!hi && !lo) continue;
    on = true;
    // the cosine between the face's outward normal and the direction to the camera
    const dx = e[0] - pos[0];
    const dy = e[1] - pos[1];
    const dz = e[2] - pos[2];
    const c = ((hi ? 1 : -1) * [dx, dy, dz][i]) / Math.hypot(dx, dy, dz);
    best = Math.max(best, Math.min(1, Math.max(0, (c - 0.04) / 0.16)));
  }
  return on ? 1 - (shell.amount ?? 1) * (1 - best) : 1;
}
/** the box beads cover as a shell; `amount` 0..1 phases the hiding of its far faces in */
export interface Shell {
  min: V3;
  max: V3;
  amount?: number;
}

/** how much of a box edge to draw for a camera at `eye`: 1 on the box's outline, else its `inner` */
function boxEdgeShown(s: Stick, eye: THREE.Vector3): number {
  const b = s.box;
  if (!b) return 1;
  const e = [eye.x, eye.y, eye.z];
  let sides = 0;
  let facing = 0;
  for (let i = 0; i < 3; i++) {
    if (Math.abs(s.a[i] - s.b[i]) > 1e-6) continue;
    const hi = Math.abs(s.a[i] - b.max[i]) < 1e-6;
    const lo = Math.abs(s.a[i] - b.min[i]) < 1e-6;
    if (!hi && !lo) return 1;
    sides++;
    if (hi ? e[i] > b.max[i] : e[i] < b.min[i]) facing++;
  }
  // an edge is on the outline when exactly one of its two faces looks at the camera
  return sides === 2 && facing !== 1 ? (b.inner ?? 0) : 1;
}

/** an axis-aligned box drawn as an opaque, lit solid (the core as one block) */
export interface Solid {
  min: V3;
  max: V3;
  color: string;
  /** 0..1; below 1 it blends with what is behind it (cross-fading beads into the block) */
  opacity?: number;
  /** 0 = full colour, 1 = background */
  fade?: number;
  /** 0..1, how flat the three face tones are (0 = as lit as a bead); default 0.5 */
  soft?: number;
}

/**
 * Depth cue: beads, sticks and solids further from the camera fade towards the background.
 * `true` or a number (the amount) uses the defaults; near and far are distances in lattice units
 * from the plane through the shot's target (negative = in front of it).
 */
export type DepthCue = boolean | number | { amount?: number; near?: number; far?: number };
const CUE_DEFAULT = { amount: 0.4, near: -5, far: 11 };

/**
 * One emphasis rule for every scene: what the caption talks about is drawn at full colour
 * (subject), what it sits in is quieter (context), what is only there for orientation is faint
 * (ghost). Use as a bead's or stick's `fade`, or through `quiet`.
 */
export const FADE = { subject: 0, context: 0.3, ghost: 0.7 } as const;

/** the same beads or sticks, quieter by `amount` (fades combine: 0.5 then 0.5 is 0.75) */
export function quiet<T extends { fade?: number }>(items: T[], amount: number): T[] {
  if (amount <= 0) return items;
  return items.map((x) => ({ ...x, fade: 1 - (1 - (x.fade ?? 0)) * (1 - amount) }));
}

export interface Shot {
  /** point looked at */
  target: V3;
  /** from the target towards the camera */
  dir: V3;
  /** distance of the camera */
  dist: number;
  fov?: number;
  /** move the picture on screen by (dx, dy) px without changing the perspective (room for a legend) */
  offset?: [number, number];
}

const colorCache = new Map<string, THREE.Color>();
const col = (s: string) => {
  let c = colorCache.get(s);
  if (!c) {
    c = new THREE.Color(s);
    colorCache.set(s, c);
  }
  return c;
};

/** a camera for a shot; used inside the canvas and for projecting labels outside it */
export function cameraFor(shot: Shot, aspect = W / H): THREE.PerspectiveCamera {
  const cam = new THREE.PerspectiveCamera(shot.fov ?? FOV, aspect, 0.1, 4000);
  const d = new THREE.Vector3(...shot.dir).normalize();
  const t = new THREE.Vector3(...shot.target);
  cam.position.copy(t).addScaledVector(d, shot.dist);
  cam.up.set(0, 1, 0);
  cam.lookAt(t);
  if (shot.offset && (shot.offset[0] || shot.offset[1])) cam.setViewOffset(W, H, -shot.offset[0], -shot.offset[1], W, H);
  cam.updateMatrixWorld();
  cam.updateProjectionMatrix();
  return cam;
}

/** screen position in px of a world point */
export type Project = (p: V3) => [number, number];
export function projector(shot: Shot): Project {
  const cam = cameraFor(shot);
  const v = new THREE.Vector3();
  return (p) => {
    v.set(p[0], p[1], p[2]).project(cam);
    return [((v.x + 1) / 2) * W, ((1 - v.y) / 2) * H];
  };
}

/** blend two shots: directions are slerped, the rest linear */
export function mixShot(a: Shot, b: Shot, t: number): Shot {
  const da = new THREE.Vector3(...a.dir).normalize();
  const db = new THREE.Vector3(...b.dir).normalize();
  const qa = new THREE.Quaternion();
  const qb = new THREE.Quaternion().setFromUnitVectors(da, db);
  qa.slerp(qb, t);
  const d = da.clone().applyQuaternion(qa);
  const lerp = (x: number, y: number) => x + (y - x) * t;
  return {
    target: [lerp(a.target[0], b.target[0]), lerp(a.target[1], b.target[1]), lerp(a.target[2], b.target[2])],
    dir: [d.x, d.y, d.z],
    dist: lerp(a.dist, b.dist),
    fov: lerp(a.fov ?? FOV, b.fov ?? FOV),
    offset: [lerp(a.offset?.[0] ?? 0, b.offset?.[0] ?? 0), lerp(a.offset?.[1] ?? 0, b.offset?.[1] ?? 0)],
  };
}

/** turn a direction about the vertical axis by `deg` degrees (slow orbits) */
export function yaw(dir: V3, deg: number): V3 {
  const a = (deg * Math.PI) / 180;
  const [x, y, z] = dir;
  return [x * Math.cos(a) + z * Math.sin(a), y, -x * Math.sin(a) + z * Math.cos(a)];
}

function Rig({ shot }: { shot: Shot }) {
  const { camera } = useThree();
  const c = cameraFor(shot);
  camera.position.copy(c.position);
  camera.quaternion.copy(c.quaternion);
  if (camera instanceof THREE.PerspectiveCamera) {
    camera.fov = c.fov;
    camera.aspect = W / H;
    if (c.view) camera.setViewOffset(W, H, c.view.offsetX, c.view.offsetY, W, H);
    else camera.clearViewOffset();
    camera.updateProjectionMatrix();
  }
  camera.updateMatrixWorld();
  return null;
}

const sphereGeo = new THREE.SphereGeometry(1, 28, 20);
const cylGeo = new THREE.CylinderGeometry(1, 1, 1, 12, 1, true);
const _m = new THREE.Matrix4();
const _q = new THREE.Quaternion();
const _p = new THREE.Vector3();
const _s = new THREE.Vector3();
const _a = new THREE.Vector3();
const _b = new THREE.Vector3();
const _Y = new THREE.Vector3(0, 1, 0);

/** instance buffers grow in powers of two, so a scene that adds beads every frame reuses its mesh (smooth live playback) */
const capFor = (n: number) => Math.max(64, 2 ** Math.ceil(Math.log2(Math.max(1, n))));

/** Beads in one draw call. `soft`: see-through beads (`opacity` < 1), drawn after everything solid. */
function Beads({ beads, cue, soft = false }: { beads: Bead[]; cue: THREE.Vector3; soft?: boolean }) {
  const cap = capFor(beads.length);
  const mesh = useMemo(() => {
    const geo = sphereGeo.clone();
    geo.setAttribute('aColor', new THREE.InstancedBufferAttribute(new Float32Array(cap * 3), 3));
    geo.setAttribute('aHollow', new THREE.InstancedBufferAttribute(new Float32Array(cap), 1));
    geo.setAttribute('aFade', new THREE.InstancedBufferAttribute(new Float32Array(cap), 1));
    geo.setAttribute('aAlpha', new THREE.InstancedBufferAttribute(new Float32Array(cap), 1));
    const mat = new THREE.ShaderMaterial({
      vertexShader: BEAD_VERT,
      fragmentShader: BEAD_FRAG,
      uniforms: { uBg: { value: col(C.bg) }, uBgElev: { value: col(C.bgElev) }, uCue: { value: new THREE.Vector3() } },
      transparent: soft,
      depthWrite: !soft,
    });
    const m = new THREE.InstancedMesh(geo, mat, cap);
    m.frustumCulled = false;
    if (soft) m.renderOrder = 3;
    return m;
  }, [cap, soft]);

  useLayoutEffect(() => () => {
    mesh.geometry.dispose();
    (mesh.material as THREE.Material).dispose();
  }, [mesh]);

  (mesh.material as THREE.ShaderMaterial).uniforms.uCue.value.copy(cue);
  const g = mesh.geometry;
  const aColor = g.getAttribute('aColor') as THREE.InstancedBufferAttribute;
  const aHollow = g.getAttribute('aHollow') as THREE.InstancedBufferAttribute;
  const aFade = g.getAttribute('aFade') as THREE.InstancedBufferAttribute;
  const aAlpha = g.getAttribute('aAlpha') as THREE.InstancedBufferAttribute;
  let k = 0;
  for (const b of beads) {
    const s = (b.r ?? R_RES) * (b.scale ?? 1);
    if (s <= 0.001) continue;
    _p.set(b.pos[0], b.pos[1], b.pos[2]);
    _s.set(s, s, s);
    _m.compose(_p, _q.identity(), _s);
    mesh.setMatrixAt(k, _m);
    const c = col(b.color);
    aColor.setXYZ(k, c.r, c.g, c.b);
    aHollow.setX(k, b.hollow ? 1 : 0);
    aFade.setX(k, b.fade ?? 0);
    aAlpha.setX(k, soft ? (b.opacity ?? 1) : 1);
    k++;
  }
  mesh.count = k;
  mesh.instanceMatrix.needsUpdate = true;
  aColor.needsUpdate = true;
  aHollow.needsUpdate = true;
  aFade.needsUpdate = true;
  aAlpha.needsUpdate = true;
  return <primitive object={mesh} />;
}

/**
 * Sticks in one draw call. `soft`: these sticks are faded and drawn see-through, after the opaque
 * beads, so a line fading out in front of beads lets them show (mixing it to the background colour
 * would draw a pale line over them, which then pops when it goes).
 */
function Sticks({ sticks, lit = 1, soft = false, cue }: { sticks: Stick[]; lit?: number; soft?: boolean; cue: THREE.Vector3 }) {
  const cap = capFor(sticks.length);
  const mesh = useMemo(() => {
    const geo = cylGeo.clone();
    geo.setAttribute('aColor', new THREE.InstancedBufferAttribute(new Float32Array(cap * 3), 3));
    geo.setAttribute('aFade', new THREE.InstancedBufferAttribute(new Float32Array(cap), 1));
    geo.setAttribute('aDash', new THREE.InstancedBufferAttribute(new Float32Array(cap), 1));
    const mat = new THREE.ShaderMaterial({
      vertexShader: SEG_VERT,
      fragmentShader: SEG_FRAG,
      uniforms: { uBg: { value: col(C.bg) }, uLit: { value: lit }, uSee: { value: soft ? 1 : 0 }, uCue: { value: new THREE.Vector3() } },
      transparent: soft,
      depthWrite: !soft,
    });
    const m = new THREE.InstancedMesh(geo, mat, cap);
    m.frustumCulled = false;
    return m;
  }, [cap, lit, soft]);

  useLayoutEffect(() => () => {
    mesh.geometry.dispose();
    (mesh.material as THREE.Material).dispose();
  }, [mesh]);

  (mesh.material as THREE.ShaderMaterial).uniforms.uCue.value.copy(cue);
  const g = mesh.geometry;
  const aColor = g.getAttribute('aColor') as THREE.InstancedBufferAttribute;
  const aFade = g.getAttribute('aFade') as THREE.InstancedBufferAttribute;
  const aDash = g.getAttribute('aDash') as THREE.InstancedBufferAttribute;
  let k = 0;
  for (const s of sticks) {
    const grow = s.grow ?? 1;
    if (grow <= 0.001) continue;
    _a.set(...s.a);
    _b.set(...s.b);
    _b.sub(_a).multiplyScalar(grow);
    const len = _b.length();
    if (len < 1e-4) continue;
    _p.copy(_a).addScaledVector(_b, 0.5);
    _q.setFromUnitVectors(_Y, _b.clone().normalize());
    const r = s.r ?? R_BOND;
    _s.set(r, len, r);
    _m.compose(_p, _q, _s);
    mesh.setMatrixAt(k, _m);
    const c = col(s.color);
    aColor.setXYZ(k, c.r, c.g, c.b);
    aFade.setX(k, s.fade ?? 0);
    aDash.setX(k, s.dash ? Math.max(1, Math.round(len * s.dash)) : 0);
    k++;
  }
  mesh.count = k;
  mesh.instanceMatrix.needsUpdate = true;
  aColor.needsUpdate = true;
  aFade.needsUpdate = true;
  aDash.needsUpdate = true;
  return <primitive object={mesh} />;
}

export interface Scene3DProps {
  shot: Shot;
  beads?: Bead[];
  sticks?: Stick[];
  /** flat-coloured sticks (outlines, boxes) */
  lines?: Stick[];
  /** translucent quads, e.g. a face of the cube or the switchboard box */
  panels?: { corners: [V3, V3, V3, V3]; color: string; opacity: number }[];
  /** opaque lit boxes, e.g. `innerBlock()` from cube.ts: the core as one block */
  solids?: Solid[];
  /**
   * The box the beads cover as a shell (`CUBE_SHELL` from cube.ts). Beads and sticks on its faces
   * turned away from the camera are not drawn: seen through the gaps of the near faces they were
   * cut by the block inside, and a face turning edge-on smeared into streaks. They fade out as
   * their face turns away.
   */
  shell?: Shell;
  /** fade with distance from the camera; off by default (see `DepthCue`) */
  depthCue?: DepthCue;
  /** Labels, drawn over the picture; `project` puts a 3D point where the camera shows it. */
  children?: (project: Project) => React.ReactNode;
}

const boxGeo = new THREE.BoxGeometry(1, 1, 1);

function SolidBox({ solid, cue }: { solid: Solid; cue: THREE.Vector3 }) {
  const mat = useMemo(
    () =>
      new THREE.ShaderMaterial({
        vertexShader: SOLID_VERT,
        fragmentShader: SOLID_FRAG,
        transparent: true,
        uniforms: {
          uBg: { value: col(C.bg) },
          uColor: { value: new THREE.Color() },
          uFade: { value: 0 },
          uOpacity: { value: 1 },
          uSoft: { value: 0.5 },
          uCue: { value: new THREE.Vector3() },
        },
      }),
    [],
  );
  useLayoutEffect(() => () => mat.dispose(), [mat]);
  const u = mat.uniforms;
  u.uColor.value.copy(col(solid.color));
  u.uFade.value = solid.fade ?? 0;
  u.uOpacity.value = solid.opacity ?? 1;
  u.uSoft.value = solid.soft ?? 0.5;
  u.uCue.value.copy(cue);
  const [a, b] = [solid.min, solid.max];
  return (
    <mesh
      geometry={boxGeo}
      material={mat}
      position={[(a[0] + b[0]) / 2, (a[1] + b[1]) / 2, (a[2] + b[2]) / 2]}
      scale={[b[0] - a[0], b[1] - a[1], b[2] - a[2]]}
      renderOrder={1}
    />
  );
}

/** the cue uniform (near, far, amount) in view depth for a shot */
function cueFor(shot: Shot, cue: DepthCue | undefined): THREE.Vector3 {
  if (cue === undefined || cue === false) return new THREE.Vector3(0, 1, 0);
  const o = typeof cue === 'object' ? cue : typeof cue === 'number' ? { amount: cue } : {};
  const near = shot.dist + (o.near ?? CUE_DEFAULT.near);
  const far = shot.dist + (o.far ?? CUE_DEFAULT.far);
  return new THREE.Vector3(near, Math.max(far, near + 0.01), o.amount ?? CUE_DEFAULT.amount);
}

function Panels({ panels }: { panels: NonNullable<Scene3DProps['panels']> }) {
  return (
    <>
      {panels.map((p, i) => {
        const geo = new THREE.BufferGeometry();
        const v = p.corners.flat();
        geo.setAttribute('position', new THREE.Float32BufferAttribute(v, 3));
        geo.setIndex([0, 1, 2, 0, 2, 3]);
        return (
          <mesh key={i} geometry={geo} renderOrder={5}>
            <meshBasicMaterial color={p.color} transparent opacity={p.opacity} side={THREE.DoubleSide} depthWrite={false} />
          </mesh>
        );
      })}
    </>
  );
}

export function Scene3D({ shot, beads: allBeads = [], sticks: allSticks = [], lines = [], panels = [], solids = [], shell, depthCue, children }: Scene3DProps) {
  const project = useMemo(() => projector(shot), [shot]);
  const cue = cueFor(shot, depthCue);
  const eye = cameraFor(shot).position;
  // solid beads, and see-through ones (coming or going, or on a cube face turning away), the
  // see-through ones sorted back to front so they blend in the right order
  const beads: Bead[] = [];
  const seeThrough: { b: Bead; d: number }[] = [];
  for (const b of allBeads) {
    const o = (b.opacity ?? 1) * shellShown(b.pos, shell, eye);
    if (o <= 0.001) continue;
    if (o >= 0.999) beads.push(b);
    else seeThrough.push({ b: { ...b, opacity: o }, d: eye.distanceToSquared(new THREE.Vector3(...b.pos)) });
  }
  seeThrough.sort((x, y) => y.d - x.d);
  const softBeads = seeThrough.map((x) => x.b);
  const sticks: Stick[] = [];
  for (const s of allSticks) {
    const m = Math.min(shellShown(s.a, shell, eye), shellShown(s.b, shell, eye));
    if (m <= 0.001) continue;
    sticks.push(m >= 1 ? s : { ...s, fade: 1 - (1 - (s.fade ?? 0)) * m });
  }
  const shownLines: Stick[] = [];
  for (const l of lines) {
    const m = boxEdgeShown(l, eye);
    if (m <= 0.001) continue;
    shownLines.push(m >= 1 ? l : { ...l, fade: 1 - (1 - (l.fade ?? 0)) * m });
  }
  // In the step page a scene jumped to has to create its canvas first; until it has drawn once,
  // the labels would show over nothing. So the picture stays hidden until then and shows whole.
  // Renders wait for the canvas anyway, so they always show it.
  const { isRendering } = useRemotionEnvironment();
  const [drawn, setDrawn] = useState(isRendering);
  const onCreated = useCallback(() => {
    requestAnimationFrame(() => requestAnimationFrame(() => setDrawn(true)));
  }, []);
  return (
    <div style={{ position: 'absolute', inset: 0, opacity: drawn ? 1 : 0, transition: isRendering ? undefined : 'opacity 0.15s' }}>
      {/* dpr: at most 1.5× the 1920 × 1080 frame. The page shows it smaller than that, and a 4K
          canvas only slows playback down; renders (pixel ratio 1) are unchanged. */}
      <ThreeCanvas width={W} height={H} flat dpr={[1, 1.5]} onCreated={onCreated} gl={{ antialias: true, alpha: true }} camera={{ fov: FOV, near: 0.1, far: 4000 }} style={{ position: 'absolute', inset: 0 }}>
        <Rig shot={shot} />
        <Beads beads={beads} cue={cue} />
        {softBeads.length > 0 && <Beads beads={softBeads} cue={cue} soft />}
        <Sticks sticks={sticks.filter((s) => !s.fade)} cue={cue} />
        <Sticks sticks={shownLines.filter((s) => !s.fade)} lit={0} cue={cue} />
        <Sticks sticks={sticks.filter((s) => s.fade)} soft cue={cue} />
        <Sticks sticks={shownLines.filter((s) => s.fade)} lit={0} soft cue={cue} />
        {solids.map((s, i) => ((s.opacity ?? 1) > 0.001 ? <SolidBox key={i} solid={s} cue={cue} /> : null))}
        {panels.length > 0 && <Panels panels={panels} />}
      </ThreeCanvas>
      {children && (
        // geometricPrecision: labels that follow a moving camera glide instead of hopping a whole
        // pixel at a time
        <svg width={W} height={H} viewBox={`0 0 ${W} ${H}`} textRendering="geometricPrecision" style={{ position: 'absolute', inset: 0, overflow: 'visible' }}>
          {children(project)}
        </svg>
      )}
    </div>
  );
}
