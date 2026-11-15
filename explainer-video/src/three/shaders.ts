/**
 * Shading copied from the folding game's 3D renderer (site/src/widgets/fold-game/render/
 * three3d-scene.ts), so beads look the same here as in the game: H a filled, lit sphere; P a light
 * sphere with a coloured rim (the hollow look); backbone and contacts lit cylinders.
 * Changes: the colour is per instance (items have their own colours), a `fade` mixes a bead
 * towards the background (for dimming: it stays opaque), an `alpha` makes it see-through (for a
 * bead coming or going), and contacts get their dash count per instance.
 * Added for the video: an optional depth cue (things further from the camera fade a little towards
 * the background; off unless a scene asks for it) and lit solids (an opaque block for the core).
 */
export const LIGHT = /* glsl */ `
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

/** depth cue: uCue = (near, far, amount) in view depth; amount 0 = off */
export const CUE = /* glsl */ `
uniform vec3 uCue;
float depthCue(float depth) {
  return uCue.z * smoothstep(uCue.x, uCue.y, depth);
}
`;

export const BEAD_VERT = /* glsl */ `
attribute vec3 aColor;
attribute float aHollow;
attribute float aFade;
attribute float aAlpha;
varying vec3 vN;
varying vec3 vV;
varying vec3 vColor;
varying float vHollow;
varying float vFade;
varying float vAlpha;
varying float vDepth;
void main() {
  vColor = aColor;
  vHollow = aHollow;
  vFade = aFade;
  vAlpha = aAlpha;
  vDepth = -(modelViewMatrix * instanceMatrix * vec4(0.0, 0.0, 0.0, 1.0)).z;
  vec4 mv = modelViewMatrix * instanceMatrix * vec4(position, 1.0);
  vN = normalize(normalMatrix * mat3(instanceMatrix) * normal);
  vV = -mv.xyz;
  gl_Position = projectionMatrix * mv;
}
`;

export const BEAD_FRAG = /* glsl */ `
uniform vec3 uBg;
uniform vec3 uBgElev;
varying vec3 vN;
varying vec3 vV;
varying vec3 vColor;
varying float vHollow;
varying float vFade;
varying float vAlpha;
varying float vDepth;
${CUE}
${LIGHT}
void main() {
  vec3 n = normalize(vN);
  vec3 v = normalize(vV);
  float ndv = clamp(dot(n, v), 0.0, 1.0);
  vec3 col;
  if (vHollow < 0.5) {
    col = fg3Shade(vColor, n, v, 0.16, 0.0);
    col *= mix(0.8, 1.0, smoothstep(0.0, 0.42, ndv));
  } else {
    float ring = 1.0 - smoothstep(0.5, 0.68, ndv);
    vec3 fill = mix(uBgElev, vColor, 0.16);
    col = fg3Shade(mix(fill, vColor, ring), n, v, 0.06, 0.45);
  }
  col = mix(col, uBg, vFade);
  col = mix(col, uBg, depthCue(vDepth));
  // vAlpha < 1 only in the see-through pass (a bead coming or going): what is behind it shows
  gl_FragColor = vec4(col, vAlpha);
  #include <colorspace_fragment>
}
`;

/** unit cylinder along y; the instance matrix scales it to radius and length */
export const SEG_VERT = /* glsl */ `
attribute vec3 aColor;
attribute float aFade;
attribute float aDash;
varying vec3 vN;
varying vec3 vV;
varying float vY;
varying vec3 vColor;
varying float vFade;
varying float vDash;
varying float vDepth;
void main() {
  vY = position.y;
  vColor = aColor;
  vFade = aFade;
  vDash = aDash;
  vec4 mv = modelViewMatrix * instanceMatrix * vec4(position, 1.0);
  vDepth = -mv.z;
  vN = normalize(normalMatrix * mat3(instanceMatrix) * normal);
  vV = -mv.xyz;
  gl_Position = projectionMatrix * mv;
}
`;

export const SEG_FRAG = /* glsl */ `
uniform vec3 uBg;
uniform float uLit;
/* 1: faded sticks are see-through (drawn after the beads); 0: fade mixes to the background */
uniform float uSee;
varying vec3 vN;
varying vec3 vV;
varying float vY;
varying vec3 vColor;
varying float vFade;
varying float vDash;
varying float vDepth;
${CUE}
${LIGHT}
void main() {
  if (vDash > 0.0 && fract((vY + 0.5) * vDash + 0.25) > 0.5) discard;
  vec3 col = mix(vColor, fg3Shade(vColor, normalize(vN), normalize(vV), 0.12, 0.0), uLit);
  col = mix(col, uBg, vFade * (1.0 - uSee));
  col = mix(col, uBg, depthCue(vDepth));
  gl_FragColor = vec4(col, mix(1.0, 1.0 - vFade, uSee));
  #include <colorspace_fragment>
}
`;

/**
 * A lit solid (the core as one block): the beads' light, so its faces take three tones (top light,
 * the side away from the light darker). uSoft 0..1 flattens the tones; uFade mixes to the background.
 */
export const SOLID_VERT = /* glsl */ `
varying vec3 vN;
varying vec3 vV;
varying float vDepth;
void main() {
  vec4 mv = modelViewMatrix * vec4(position, 1.0);
  vN = normalize(normalMatrix * normal);
  vV = -mv.xyz;
  vDepth = -mv.z;
  gl_Position = projectionMatrix * mv;
}
`;

export const SOLID_FRAG = /* glsl */ `
uniform vec3 uBg;
uniform vec3 uColor;
uniform float uFade;
uniform float uOpacity;
uniform float uSoft;
varying vec3 vN;
varying vec3 vV;
varying float vDepth;
${CUE}
${LIGHT}
void main() {
  vec3 col = fg3Shade(uColor, normalize(vN), normalize(vV), 0.0, uSoft);
  col = mix(col, uBg, uFade);
  col = mix(col, uBg, depthCue(vDepth));
  gl_FragColor = vec4(col, uOpacity);
  #include <colorspace_fragment>
}
`;
