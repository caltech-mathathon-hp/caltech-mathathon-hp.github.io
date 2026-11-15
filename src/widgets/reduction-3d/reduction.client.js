/**
 * A reduction, folded: the string of a hardness proof for a bin packing instance, folded into a
 * perfect cube step by step. Two constructions share this viewer, chosen by data-construction on
 * the root: Berger and Leighton's S_B (adapter-bl.js, construction.js; the "Folded in 3D" section)
 * and the short version of the one-edge construction, with the instance on one edge (adapter-edge.js, edge-construction.js).
 *
 * mount(root) takes the markup of Reduction3D.astro (ids prefixed rd-, one widget per page) and
 * builds everything inside it: the packing board (the bin-packing game's board: drag, or click and
 * then a bin, or keys 1–K and 0), the formula of the string with
 * the current factor marked, the checks of the fold, and the three.js stage with the steps and the
 * string bar. An adapter supplies what belongs to one construction: presets, formula, steps and
 * their texts, labels on the cube, and the pieces of the string bar.
 *
 * Keys (while the widget fills most of the screen or has focus): → completes the running step or
 * folds the next one, ← goes back one step, + and − zoom.
 * Rendering pauses while the widget is off screen. The strings and folds are built in a worker
 * (build.worker.js), on the main thread if the worker cannot start.
 */
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { LineSegments2 } from 'three/addons/lines/LineSegments2.js';
import { LineSegmentsGeometry } from 'three/addons/lines/LineSegmentsGeometry.js';
import { LineMaterial } from 'three/addons/lines/LineMaterial.js';
import BL from './adapter-bl.js';
import EDGE from './adapter-edge.js';

export function mount(root) {
  const $ = (s) => root.querySelector(s);
  // the construction shown, and its code
  const A = root.dataset.construction === 'edge' ? EDGE : BL;
  const C = A.C, PRESETS = A.PRESETS;
  const fmt = (x) => Number(x).toLocaleString('en-US');
  const clamp = (x, a, b) => (x < a ? a : x > b ? b : x);
  // what the adapters may use: number format, the stage colours, labels in the scene, and the proof
  // board, for the "On the proof board" links of every step
  const X = { fmt, clamp, ST: () => ST(), makeLabel: (...a) => makeLabel(...a), cards: root.dataset.cards || '../original-proof/' };

  // ------------------------------------------------------------------ colours
  // CAT: 0 P, 1 edges, 2 back, 3 back-left edge, 4 left, 5 bottom, 6 right, 7 top, 8 interior,
  //      9 wall, 10 special, 11 filler, 12 dummy, 13 item
  // Palettes. 'hp' (the default): H's in reds (edges a light red; faces, core and paddings paler;
  // walls dark), P's grey and translucent; one version per stage. 'normal': one colour per step of
  // the construction. The items have the colours of the packing board in every palette (itemHex).
  const PALETTES = {
    normal: {
      cat: ['#a3a9b3', '#f2b33d', '#3f7ed6', '#f2b33d', '#4a90e2', '#386fc4', '#5a9cf0', '#4485dc', '#2d5aa0',
        '#b8463a', '#ff8c1a', '#4f8f86', '#9c8a6a', '#ffffff'],
      pOpacity: 1, bondOpacity: 0.55,
    },
    hp_night: {
      cat: ['#aab0b8', '#ff8a7a', '#f6c3bc', '#ff8a7a', '#f6c3bc', '#f6c3bc', '#f6c3bc', '#f6c3bc', '#efaaa2',
        '#9e1c1c', '#ff8a7a', '#fbdcd7', '#e39a91', '#ffffff'],
      pOpacity: 0.62, bondOpacity: 0.6,
    },
    hp_day: {
      cat: ['#5f6670', '#f0705e', '#f2b0a7', '#f0705e', '#f2b0a7', '#f2b0a7', '#f2b0a7', '#f2b0a7', '#ea9b91',
        '#9e1c1c', '#f0705e', '#f6c8c1', '#d6837a', '#ffffff'],
      pOpacity: 0.72, bondOpacity: 0.7,
    },
  };
  // The item colours are the site's (--item-1 … --item-4, as on the packing board and in the
  // game), read from the page and read again when the theme changes. The board tells items 5–8
  // and 9–12 apart from 1–4 by stripes and dots; here they are lighter and darker.
  let ITEM_BASE = [];
  function cssHex(expr) {
    const p = document.createElement('span');
    p.style.cssText = `position:absolute;visibility:hidden;color:${expr}`;
    root.appendChild(p);
    const c = getComputedStyle(p).color;
    p.remove();
    let v = null, m = c.match(/rgba?\(([^)]*)\)/);
    if (m) v = m[1].split(/[\s,/]+/).filter(Boolean).slice(0, 3).map((x) => +x / 255);
    else if ((m = c.match(/color\(srgb\s+([^)]*)\)/))) v = m[1].split(/[\s/]+/).filter(Boolean).slice(0, 3).map(Number);
    if (!v || v.some((x) => !Number.isFinite(x))) return '#808080';
    return '#' + v.map((x) => Math.round(clamp(x, 0, 1) * 255).toString(16).padStart(2, '0')).join('');
  }
  function readItemColours() {
    ITEM_BASE = [1, 2, 3, 4].map((k) => cssHex(`var(--item-${k})`));
    for (const k in ITEM_HEX) delete ITEM_HEX[k];
  }
  const ITEM_HEX = {};
  const mixHex = (h, to, t) => { const c = new THREE.Color(h); c.lerp(new THREE.Color(to), t); return '#' + c.getHexString(); };
  const itemHex = (u) => {
    const key = u + stage;
    if (ITEM_HEX[key]) return ITEM_HEX[key];
    let h = ITEM_BASE[u % 4] || '#808080';
    const tier = Math.floor(u / 4) % 3;
    if (tier === 1) h = mixHex(h, '#ffffff', 0.35); else if (tier === 2) h = mixHex(h, '#000000', 0.3);
    // a stage that is not the site's theme gets the colours a little lighter (night) or darker (day)
    const dark = document.documentElement.dataset.theme === 'dark';
    if (stage === 'night' && !dark) h = mixHex(h, '#ffffff', 0.25);
    else if (stage === 'day' && dark) h = mixHex(h, '#000000', 0.25);
    return (ITEM_HEX[key] = h);
  };
  // The stage: day (light, like the page) or night (dark). It follows the site's theme until the
  // reader picks one with the sun / moon button.
  const STAGES = {
    day: {
      clear: 0xf2f0eb, line: 0x7f858e, wire: 0xb5aea1, wireOp: 0.9, label: 'rgba(255,255,255,0.92)', ink: '#1c1c21', plugInk: '#7a6538',
      strip: 0x1c1c21, plugStrip: 0x8a7650, stripOp: 0.45, map: '#e9e5dc', mapEmpty: '#d6d1c6', mapLine: 'rgba(28,28,33,0.8)', mapPlug: 'rgba(122,101,56,0.9)',
    },
    night: {
      clear: 0x0e0f11, line: 0x8a919c, wire: 0x4a5466, wireOp: 0.55, label: 'rgba(14,17,22,0.78)', ink: '#ffffff', plugInk: '#dccb9f',
      strip: 0xffffff, plugStrip: 0xcdbb94, stripOp: 0.85, map: '#14171d', mapEmpty: '#262b34', mapLine: 'rgba(255,255,255,0.9)', mapPlug: 'rgba(205,187,148,0.9)',
    },
  };
  let scheme = 'hp'; // H/P colours by default (View ▸ H/P colours)
  let stage = document.documentElement.dataset.theme === 'dark' ? 'night' : 'day';
  let stageChosen = false;
  const pal = () => PALETTES[scheme === 'hp' ? 'hp_' + stage : 'normal'];
  const ST = () => STAGES[stage];
  const hexRGB = (h) => { const c = new THREE.Color(h); return [c.r, c.g, c.b]; };
  const RGB_CACHE = {};
  const rgbOf = (h) => RGB_CACHE[h] || (RGB_CACHE[h] = hexRGB(h));
  const catHex = (c) => pal().cat[c];
  const catRGB = (c) => rgbOf(catHex(c));
  const itemRGB = (u) => rgbOf(itemHex(u));

  // ------------------------------------------------------------------ state
  let RES = null;      // build result
  let V = null;        // scene data for the current build
  // where we are: cur.pos residues are folded; cur.k is the step that contains that position;
  // cur.anim, while a step is being folded, runs from anim.from to anim.to residues
  const cur = { k: 0, pos: 0, anim: null };
  let speed = 1;
  let camTween = null;
  let fmtNumeric = false;

  // ------------------------------------------------------------------ three.js base
  const glWrap = $('#rd-gl');
  const renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  renderer.localClippingEnabled = true;
  renderer.setClearColor(ST().clear);
  glWrap.appendChild(renderer.domElement);
  const scene = new THREE.Scene();
  const camera = new THREE.PerspectiveCamera(38, 1, 0.3, 20000);
  camera.position.set(60, 40, 60);
  scene.add(camera);
  scene.add(new THREE.HemisphereLight(0xffffff, 0x2a2e36, 0.8 * Math.PI));
  const headlight = new THREE.DirectionalLight(0xffffff, 0.75 * Math.PI);
  headlight.position.set(-0.4, 0.7, 0.2);
  const hlTarget = new THREE.Object3D(); hlTarget.position.set(0, 0, -1);
  camera.add(headlight); camera.add(hlTarget); headlight.target = hlTarget;
  const controls = new OrbitControls(camera, renderer.domElement);
  controls.enableDamping = true; controls.dampingFactor = 0.12;
  controls.enableZoom = false; // the wheel and two-finger scrolling scroll the page; + and − zoom
  controls.addEventListener('start', () => { camTween = null; });
  // the bonds of the chain are fat lines (a width in world units, so they scale with the beads)
  const lineMats = [];
  const bondMaterial = () => {
    const m = new LineMaterial({ color: 0x8a919c, linewidth: 0.14, worldUnits: true, transparent: true, opacity: 0.6 });
    m.resolution.set(Math.max(1, glWrap.clientWidth), Math.max(1, glWrap.clientHeight));
    lineMats.push(m);
    return m;
  };
  function zoomBy(f) {
    const d = camera.position.clone().sub(controls.target);
    const r0 = d.length(), r1 = clamp(r0 * f, controls.minDistance, controls.maxDistance);
    const u = d.normalize();
    camTween = { t: 0, dur: 0.25, p0: camera.position.clone(), t0: controls.target.clone(), t1: controls.target.clone(), u0: u, u1: u.clone(), r0, r1 };
  }
  $('#rd-zoomIn').addEventListener('click', () => zoomBy(0.8));
  $('#rd-zoomOut').addEventListener('click', () => zoomBy(1.25));

  function resize() {
    const w = glWrap.clientWidth, h = glWrap.clientHeight;
    if (!w || !h) return;
    renderer.setSize(w, h);
    camera.aspect = w / h;
    for (const m of lineMats) m.resolution.set(w, h);
    // keep the scene centred in the part of the viewport that the dock does not cover
    const dock = $('#rd-dock'), hud = $('#rd-hud');
    const dh = dock && !dock.hidden ? dock.offsetHeight + 14 : 0;
    const hh = hud && !hud.hidden ? hud.offsetHeight + 12 : 0;
    const off = clamp((dh - hh) * 0.5, -h * 0.2, h * 0.32);
    if (Math.abs(off) > 1) camera.setViewOffset(w, h, 0, off, w, h); else camera.clearViewOffset();
    camera.updateProjectionMatrix();
    // scale camera distances so the cube fits the free area between hud and dock
    const free = Math.max(80, Math.min(h - dh - hh, w * 0.95)) / h;
    const fit = clamp(0.62 / free, 0.85, 2.4);
    // when the free area changes (a narrower window, the dock growing), move the camera with it
    if (V && Math.abs(fit - fitScale) > 0.01 && !camTween) {
      const d = camera.position.clone().sub(controls.target).multiplyScalar(fit / fitScale);
      camera.position.copy(controls.target).add(d);
    }
    fitScale = fit;
  }
  let fitScale = 1;
  new ResizeObserver(resize).observe(glWrap);
  new ResizeObserver(resize).observe($('#rd-dock'));
  new ResizeObserver(resize).observe($('#rd-hud'));
  $('#rd-viewBtn').addEventListener('click', () => { $('#rd-toggles').hidden = !$('#rd-toggles').hidden; });
  resize();

  const cutPlanes = [new THREE.Plane(new THREE.Vector3(-1, 0, 0), 0), new THREE.Plane(new THREE.Vector3(0, -1, 0), 0),
    new THREE.Plane(new THREE.Vector3(0, 0, -1), 0)];

  // ------------------------------------------------------------------ helpers
  const smooth = (x) => x * x * (3 - 2 * x);
  const easeIO = (t) => (t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2);
  const toThree = (d) => { const v = new THREE.Vector3(d[0], d[1], -d[2]); return v.normalize(); };
  function setT(arr, k, x, y, z) {
    const o = 16 * k;
    arr[o] = 1; arr[o + 1] = 0; arr[o + 2] = 0; arr[o + 3] = 0;
    arr[o + 4] = 0; arr[o + 5] = 1; arr[o + 6] = 0; arr[o + 7] = 0;
    arr[o + 8] = 0; arr[o + 9] = 0; arr[o + 10] = 1; arr[o + 11] = 0;
    arr[o + 12] = x; arr[o + 13] = y; arr[o + 14] = z; arr[o + 15] = 1;
  }
  function setTS(arr, k, x, y, z, sc) {
    setT(arr, k, x, y, z);
    const o = 16 * k;
    arr[o] = sc; arr[o + 5] = sc; arr[o + 10] = sc;
  }

  // ------------------------------------------------------------------ left panel: instance
  const presetSel = $('#rd-preset');
  PRESETS.forEach((p, i) => { const o = document.createElement('option'); o.value = i; o.textContent = p.name; presetSel.appendChild(o); });
  const custom = document.createElement('option'); custom.value = 'custom'; custom.textContent = 'custom…'; presetSel.appendChild(custom);
  function loadPreset(i) {
    const p = PRESETS[i];
    $('#rd-inK').value = p.K; $('#rd-inB').value = p.B; $('#rd-inS').value = p.sizes.join(', ');
    previewInstance();
  }
  presetSel.addEventListener('change', () => { if (presetSel.value !== 'custom') loadPreset(+presetSel.value); });
  for (const id of ['#rd-inK', '#rd-inB', '#rd-inS']) $(id).addEventListener('input', () => { presetSel.value = 'custom'; previewInstance(); });

  function readInstance() {
    const K = parseInt($('#rd-inK').value, 10), B = parseInt($('#rd-inB').value, 10);
    const sizes = $('#rd-inS').value.split(/[^0-9]+/).filter(Boolean).map((x) => parseInt(x, 10));
    return { K, B, sizes };
  }
  function setStatus(msg, cls) { const s = $('#rd-status'); s.textContent = msg; s.className = 'rd-status' + (cls ? ' ' + cls : ''); }

  function previewInstance() {
    const { K, B, sizes } = readInstance();
    const chk = C.checkInstance(K, B, sizes);
    $('#rd-instSum').textContent = Number.isInteger(K) && Number.isInteger(B) && sizes.length
      ? `${K} bins of size ${B} · items ${sizes.join(', ')}` : 'incomplete';
    resetBoardIfNew(K, B, sizes);
    renderBoard();
    if (chk.errs.length) { setStatus(chk.errs[0], 'err'); renderFormula(null); return; }
    const note = A.sizeCheck(chk.P, X);
    setStatus(note.msg, note.cls);
    renderFormula(chk.P, sizes);
  }

  // ------------------------------------------------------------------ packing board
  // The bin-packing game's board (its bp- classes and styles, ../bin-pack/styles.css): the loose
  // items above, one horizontal bin per row. An item moves by dragging it, or by clicking it and
  // then a bin (or the items, to take it out); with an item focused, keys 1–K put it into a bin and
  // 0 takes it out. BD.active marks the items of the step on the stage.
  const BD = { sig: '', K: 0, B: 0, sizes: [], bins: [], active: new Set() };
  const bdLoad = (b) => BD.bins[b].reduce((a, u) => a + BD.sizes[u], 0);
  const bdBinOf = (u) => BD.bins.findIndex((l) => l.includes(u));
  const bdComplete = () => BD.sizes.length > 0 && BD.bins.flat().length === BD.sizes.length && BD.bins.every((_, b) => bdLoad(b) === BD.B);
  const bdFits = (u, b) => bdBinOf(u) !== b && BD.B - bdLoad(b) >= BD.sizes[u];
  const board = $('#rd-board');
  let sel = null; // the item picked up (by a click, a key or a drag)
  let drag = null; // { u, x0, y0, on, el, dx, dy, over }
  let kbd = false; // the last item was picked up with the keyboard: show the bin keys
  let arrived = null; // the item just put into a bin: only it plays the game's arrival animation
  const itemCss = (u) => `--c:var(--item-${(u % 4) + 1});--n:${BD.sizes[u]}`;
  const itemPat = (u) => Math.floor(u / 4) % 3;
  const packedTxt = () => BD.bins.map((l, b) => `bin ${b + 1} = {${l.map((x) => 'u' + (x + 1)).join(', ')}}`).join(', ');
  const info = (html) => { $('#rd-solveinfo').innerHTML = html; };

  function resetBoardIfNew(K, B, sizes) {
    const ok = Number.isInteger(K) && K >= 1 && K <= 6 && Number.isInteger(B) && B >= 1 && B <= 64 && sizes.length <= 24 && sizes.every((x) => x > 0 && x <= B);
    const sig = ok ? `${K}|${B}|${sizes.join(',')}` : 'bad';
    if (sig === BD.sig) return;
    BD.sig = sig; BD.K = ok ? K : 0; BD.B = B; BD.sizes = ok ? sizes.slice() : []; BD.bins = Array.from({ length: BD.K }, () => []);
    BD.active = new Set(); sel = null; BD.noSol = false;
    info(ok ? `Drag the items into the ${K} bin${K > 1 ? 's' : ''} of size ${B}, or click an item and then a bin, until every bin is full. Or press <b>Fold the string</b> and the solver packs them.` : '');
  }

  function renderBoard() {
    const hint = $('#rd-packHint');
    if (!BD.K) { board.innerHTML = '<span class="bp-empty">Enter an instance above.</span>'; hint.innerHTML = ''; return; }
    board.style.setProperty('--bp-B', String(BD.B));
    // the width of one unit, as in the game's styles: min(3.5rem, (board width − 12px) / B)
    const rem = parseFloat(getComputedStyle(document.documentElement).fontSize) || 16;
    const unit = Math.min(3.5 * rem, (board.clientWidth - 12) / BD.B);
    const moving = drag && drag.on ? drag.u : sel;
    const inBin = new Set(BD.bins.flat());
    const allActive = BD.active.size >= BD.sizes.length; // a step that reads every item marks none
    const item = (u) => {
      const b = bdBinOf(u);
      const cls = `bp-item bp-pat-${itemPat(u)}${sel === u && !(drag && drag.on) ? ' is-selected' : ''}${drag && drag.on && drag.u === u ? ' is-lifted' : ''}${BD.active.has(u) && !allActive ? ' rd-active' : ''}${u === arrived ? ' rd-new' : ''}`;
      const name = BD.sizes[u] * unit >= 4 * rem ? `<span class="rd-uname">u${u + 1}</span>` : '';
      const where = b < 0 ? 'not in a bin' : `in bin ${b + 1}`;
      return `<button type="button" class="${cls}" data-u="${u}" style="${itemCss(u)}" aria-pressed="${sel === u}" aria-label="Item u${u + 1}, size ${BD.sizes[u]}, ${where}" title="u${u + 1}, size ${BD.sizes[u]}"><span class="bp-size">${name}${BD.sizes[u]}</span></button>`;
    };
    const trayTarget = moving !== null && bdBinOf(moving) >= 0;
    const tray = `<div class="bp-tray${trayTarget ? ' is-target' : ''}${drag && drag.over === 'tray' && trayTarget ? ' is-over' : ''}" data-tray="">` +
      `<div class="bp-row-head"><span class="bp-label">Items</span></div><div class="bp-items">` +
      BD.sizes.map((s, u) => (inBin.has(u) ? `<span class="bp-slot" style="--n:${s}" aria-hidden="true" title="u${u + 1} is in bin ${bdBinOf(u) + 1}">${s}</span>` : item(u))).join('') +
      (inBin.size === BD.sizes.length ? '<span class="visually-hidden">Every item is in a bin.</span>' : '') + '</div></div>';
    const bins = BD.bins.map((list, b) => {
      const load = bdLoad(b), full = load === BD.B;
      const ghost = moving !== null && bdFits(moving, b);
      const blocked = moving !== null && bdBinOf(moving) !== b && !ghost;
      const over = drag && drag.on && drag.over === b;
      const cls = `bp-bin${full ? ' is-full' : ''}${ghost ? ' is-target' : ''}${blocked ? ' is-blocked' : ''}${over ? (ghost ? ' is-over' : ' is-refuse') : ''}`;
      return `<div class="${cls}" data-b="${b}" role="group" aria-label="Bin ${b + 1}: ${load} of ${BD.B}${full ? ', full' : ''}">` +
        `<div class="bp-row-head"><span class="bp-label">Bin ${b + 1}${sel !== null && kbd ? ` <kbd class="bp-key">${b + 1}</kbd>` : ''}</span>` +
        `<span class="bp-load">${full ? '<span class="bp-check" aria-hidden="true"></span>full' : `${load} of ${BD.B}`}</span></div>` +
        `<div class="bp-track">${list.map(item).join('')}${ghost ? `<span class="bp-ghost bp-pat-${itemPat(moving)}" style="${itemCss(moving)}" aria-hidden="true"></span>` : ''}</div></div>`;
    }).join('');
    const focused = board.contains(document.activeElement) && document.activeElement.dataset.u;
    board.innerHTML = tray + `<div class="bp-bins">${bins}</div>`;
    arrived = null;
    if (focused !== undefined && focused !== false) { const el = board.querySelector(`.bp-item[data-u="${focused}"]`); if (el) el.focus({ preventScroll: true }); }
    hint.className = 'rd-packhint' + (BD.noSol ? ' bad' : '');
    hint.innerHTML = BD.noSol ? 'no packing exists' : bdComplete() ? '<span class="bp-check" aria-hidden="true"></span>packed' : '';
  }
  new ResizeObserver(() => { if (BD.K) renderBoard(); }).observe(board);
  // mark the items of the step on the stage (without drawing the board again)
  function markActive(items) {
    BD.active = new Set(items || []);
    const all = BD.active.size >= BD.sizes.length;
    board.querySelectorAll('.bp-item').forEach((el) => el.classList.toggle('rd-active', !all && BD.active.has(+el.dataset.u)));
  }

  function boardChanged() {
    renderBoard();
    const same = RES && RES.solvable && RES.K === BD.K && RES.B === BD.B && RES.sizes.join() === BD.sizes.join()
      && BD.sizes.every((_, u) => bdBinOf(u) === RES.assign[u]);
    if (same && V) setStatus('This is the packing folded on the stage.', 'ok');
    else if (bdComplete()) setStatus(`Packed. Press Fold the string to fold ${A.strPlain} with this packing.`, 'ok');
    else setStatus('Fill every bin, or press Fold the string and the solver packs them.');
  }
  // move item u into bin b, or out of its bin (b = −1); a bin without room refuses it
  function moveItem(u, b) {
    const from = bdBinOf(u);
    sel = null;
    if (b === from) { renderBoard(); return; }
    if (b >= 0 && BD.B - bdLoad(b) < BD.sizes[u]) {
      const free = BD.B - bdLoad(b);
      renderBoard();
      info(`<span class="err">u${u + 1} (size ${BD.sizes[u]}) does not fit: bin ${b + 1} has ${free} free.</span>`);
      const el = board.querySelector(`.bp-bin[data-b="${b}"]`);
      if (el) { el.classList.add('is-refuse'); setTimeout(() => el.classList.remove('is-refuse'), 350); }
      return;
    }
    if (from >= 0) BD.bins[from].splice(BD.bins[from].indexOf(u), 1);
    if (b >= 0) { BD.bins[b].push(u); arrived = u; }
    info(bdComplete() ? `Packed by hand: ${packedTxt()}.` : `${BD.bins.flat().length} of ${BD.sizes.length} items packed.`);
    boardChanged();
  }
  function pick(u, viaKey) {
    sel = sel === u ? null : u;
    kbd = !!viaKey;
    renderBoard();
  }

  // pointer: a press that moves more than a few pixels drags the item, a press that does not is a click
  board.addEventListener('pointerdown', (e) => {
    const el = e.target.closest('.bp-item');
    if (!el || e.button > 0) return;
    drag = { u: +el.dataset.u, x0: e.clientX, y0: e.clientY, on: false, el: null, over: null };
  });
  function dropTarget(x, y) {
    const hit = document.elementFromPoint(x, y);
    const bin = hit && hit.closest && hit.closest('#rd-board .bp-bin');
    if (bin) return +bin.dataset.b;
    if (hit && hit.closest && hit.closest('#rd-board .bp-tray')) return 'tray';
    return null;
  }
  window.addEventListener('pointermove', (e) => {
    if (!drag) return;
    if (!drag.on) {
      if (Math.hypot(e.clientX - drag.x0, e.clientY - drag.y0) < 5) return;
      const src = board.querySelector(`.bp-item[data-u="${drag.u}"]`);
      if (!src) { drag = null; return; }
      const r = src.getBoundingClientRect();
      const ghost = src.cloneNode(true);
      ghost.className = `bp-drag bp-pat-${itemPat(drag.u)}`;
      ghost.removeAttribute('data-u');
      ghost.style.cssText = `${itemCss(drag.u)};width:${r.width}px;height:${r.height}px;left:${r.left}px;top:${r.top}px;display:inline-flex;align-items:center;justify-content:center`;
      document.body.appendChild(ghost);
      Object.assign(drag, { on: true, el: ghost, dx: drag.x0 - r.left, dy: drag.y0 - r.top });
      sel = null; kbd = false;
      root.classList.add('is-dragging');
      renderBoard();
    }
    drag.el.style.left = (e.clientX - drag.dx) + 'px';
    drag.el.style.top = (e.clientY - drag.dy) + 'px';
    const over = dropTarget(e.clientX, e.clientY);
    if (over !== drag.over) { drag.over = over; renderBoard(); }
  });
  function endItemDrag(e, cancel) {
    if (!drag) return;
    const d = drag;
    drag = null;
    if (!d.on) return; // a click: the click handler takes it
    d.el.remove();
    root.classList.remove('is-dragging');
    const t = cancel ? null : dropTarget(e.clientX, e.clientY);
    suppressClick = true; setTimeout(() => { suppressClick = false; }, 0);
    if (t === 'tray') moveItem(d.u, -1);
    else if (t !== null) moveItem(d.u, t);
    else renderBoard();
  }
  let suppressClick = false;
  window.addEventListener('pointerup', (e) => endItemDrag(e, false));
  window.addEventListener('pointercancel', (e) => endItemDrag(e, true));
  board.addEventListener('click', (e) => {
    if (suppressClick) return;
    const el = e.target.closest('.bp-item');
    if (el) { pick(+el.dataset.u, e.detail === 0); return; }
    if (sel === null) return;
    const bin = e.target.closest('.bp-bin');
    if (bin) moveItem(sel, +bin.dataset.b);
    else if (e.target.closest('.bp-tray') && bdBinOf(sel) >= 0) moveItem(sel, -1);
  });
  board.addEventListener('keydown', (e) => {
    const el = e.target.closest('.bp-item');
    if (!el || e.metaKey || e.ctrlKey || e.altKey) return;
    const u = +el.dataset.u;
    if (/^[1-9]$/.test(e.key) && +e.key <= BD.K) { moveItem(u, +e.key - 1); e.preventDefault(); }
    else if (e.key === '0' || e.key === 'Backspace' || e.key === 'Delete') { if (bdBinOf(u) >= 0) moveItem(u, -1); e.preventDefault(); }
    else if (e.key === 'Escape' && sel !== null) { sel = null; renderBoard(); e.preventDefault(); }
  });
  $('#rd-tReset').addEventListener('click', () => { BD.bins = BD.bins.map(() => []); sel = null; info('Bins emptied.'); boardChanged(); });
  $('#rd-tSolve').addEventListener('click', () => {
    if (!BD.K) return;
    const sol = C.solveBinPacking(BD.sizes, BD.K, BD.B);
    if (!sol.assign) { BD.noSol = true; renderBoard(); info(`Exhaustive search (${fmt(sol.nodes)} nodes): <b>no packing exists</b>.`); return; }
    BD.bins = BD.bins.map(() => []); sel = null;
    sol.assign.forEach((b, u) => BD.bins[b].push(u));
    info(`Backtracking found a packing (${fmt(sol.nodes)} search nodes).`);
    boardChanged();
  });

  // ------------------------------------------------------------------ formula
  function renderFormula(P, sizes) {
    const el = $('#rd-formula');
    if (!P) { el.innerHTML = '<span style="color:#9aa0aa">—</span>'; return; }
    el.innerHTML = A.lhs + A.formulaParts(P, sizes, fmtNumeric, X).map(([k, h]) => `<span class="f" data-f="${k}">${h}</span>`).join(' ');
    if (V) markFormula();
  }
  $('#rd-fmtTog').addEventListener('click', () => {
    fmtNumeric = !fmtNumeric;
    $('#rd-fmtTog').textContent = fmtNumeric ? 'show symbols' : 'show numbers';
    if (RES && RES.P) renderFormula(RES.P, RES.sizes); else previewInstance();
  });
  function markFormula() {
    if (!V) return;
    const st = V.steps && V.steps[cur.k];
    if (!st) return;
    // the factors of the step being folded are marked, the ones folded before it greyed; at the
    // start (nothing folded) and at the end (all of it) the formula is left plain
    const on = new Set(st.id === 'start' ? [] : st.factors || []);
    const mid = st.s > 0 && st.s < V.N;
    root.querySelectorAll('#rd-formula .f').forEach((el) => {
      const k = el.dataset.f;
      const r = V.factorRange[k];
      el.classList.toggle('on', on.has(k));
      el.classList.toggle('done', mid && !on.has(k) && !!r && r[1] <= st.s);
    });
  }

  // ------------------------------------------------------------------ build
  $('#rd-find').addEventListener('click', () => onFind());
  // The string and its fold are built in a worker (build.worker.js), so that the page does not
  // freeze on the big presets; if the worker cannot start, they are built here.
  let worker = null, workerOk = typeof Worker !== 'undefined', buildId = 0;
  const pending = new Map();
  function buildHere(K, B, sizes, given) {
    return new Promise((ok, fail) => setTimeout(() => { try { ok(C.build(K, B, sizes, given)); } catch (err) { fail(err); } }, 30));
  }
  function buildOff(K, B, sizes, given) {
    if (workerOk && !worker) {
      try {
        worker = new Worker(new URL('./build.worker.js', import.meta.url), { type: 'module' });
        worker.onmessage = (e) => { const p = pending.get(e.data.id); if (!p) return; pending.delete(e.data.id); if (e.data.error) p.fail(new Error(e.data.error)); else p.ok(e.data.res); };
        worker.onerror = (e) => {
          // the worker did not load: build on the main thread from now on
          e.preventDefault(); workerOk = false; worker.terminate(); worker = null;
          for (const [, p] of pending) buildHere(...p.args).then(p.ok, p.fail);
          pending.clear();
        };
      } catch (err) { workerOk = false; worker = null; }
    }
    if (!worker) return buildHere(K, B, sizes, given);
    const id = ++buildId;
    return new Promise((ok, fail) => {
      pending.set(id, { ok, fail, args: [K, B, sizes, given] });
      worker.postMessage({ id, construction: root.dataset.construction === 'edge' ? 'edge' : 'bl', K, B, sizes, given });
    });
  }
  // opts.atEnd: show the finished fold instead of the unfolded string (used when the page opens)
  let findSeq = 0;
  function onFind(opts = {}) {
    const { K, B, sizes } = readInstance();
    const chk = C.checkInstance(K, B, sizes);
    if (chk.errs.length) { setStatus(chk.errs[0], 'err'); return; }
    const note = A.sizeCheck(chk.P, X);
    if (note.block) { setStatus(note.msg, 'err'); return; }
    const btn = $('#rd-find');
    btn.disabled = true; btn.textContent = 'Building…';
    const given = bdComplete() ? BD.sizes.map((_, u) => bdBinOf(u)) : null;
    setStatus((given ? `Building ${A.strPlain} and folding it with your packing` : `Solving the bin packing, building ${A.strPlain} and its fold`) + (chk.P.n >= 60 ? `… (n = ${chk.P.n}, a few seconds)` : '…'));
    const seq = ++findSeq;
    const done = () => { btn.disabled = false; btn.textContent = 'Fold the string'; };
    buildOff(K, B, sizes, given).then((res) => {
      if (seq !== findSeq) return;
      done();
      showBuild(res, K, B, sizes, opts);
    }, (err) => {
      if (seq !== findSeq) return;
      console.error(err);
      done();
      setStatus('Construction failed: ' + err.message, 'err');
    });
  }
  function showBuild(res, K, B, sizes, opts) {
    res.sizes = sizes; res.K = K; res.B = B;
    if (res.error) { setStatus(res.error, 'err'); return; }
    RES = res;
    if (!res.solvable) {
      teardown();
      BD.active = new Set(); BD.noSol = true; renderBoard();
      info(`Exhaustive search (${fmt(res.solverNodes)} nodes): <b>no packing exists</b>.`);
      const nf = A.noFold(res, X);
      setStatus(nf.status, 'err');
      $('#rd-placeholder').hidden = false;
      $('#rd-placeholder').innerHTML = nf.html;
      $('#rd-hud').hidden = true; $('#rd-dock').hidden = true; $('#rd-zoom').hidden = true;
      $('#rd-checks').innerHTML = '<div class="check"><small>No fold to verify.</small></div>';
      $('#rd-checkSum').textContent = ''; $('#rd-checkSum').className = '';
      renderFormula(res.P, sizes);
      return;
    }
    // show the packing that is being folded on the board
    if (!res.given) { BD.bins = Array.from({ length: K }, () => []); res.assign.forEach((b, u) => BD.bins[b].push(u)); }
    BD.active = new Set(); sel = null; renderBoard();
    const binsTxt = Array.from({ length: K }, (_, b) => `bin ${b + 1} = {${sizes.map((s, u) => (res.assign[u] === b ? 'u' + (u + 1) : null)).filter(Boolean).join(', ')}}`).join(', ');
    info(res.given ? `Folding your packing: ${binsTxt}.` : `The solver packed the bins (${fmt(res.solverNodes)} search nodes): ${binsTxt}.`);
    const okMsg = opts.atEnd ? 'Folded and checked. This is the finished fold: press ← or drag the bar to go back through the steps.' : 'Folded and checked. Press → for the first step.';
    setStatus(res.val.ok ? okMsg : 'The fold failed a check (see below).', res.val.ok ? 'ok' : 'err');
    renderChecks(res);
    setup(res);
    renderFormula(res.P, sizes);
    const k0 = opts.atEnd ? V.steps.length - 1 : 0;
    V.hintK = k0;
    if (opts.atEnd) goStep(k0, false); else goStep(0, true);
  }

  function renderChecks(res) {
    const ok = res.val.checks.filter((c) => c.ok).length, all = res.val.checks.length;
    $('#rd-checkSum').textContent = ok === all ? `✓ all ${all} pass` : `✗ ${all - ok} of ${all} fail`;
    $('#rd-checkSum').className = ok === all ? 'ok' : 'bad';
    $('#rd-checks').innerHTML = res.val.checks.map((c) =>
      `<div class="check ${c.ok ? 'ok' : 'bad'}"><span class="m">${c.ok ? '✓' : '✗'}</span><span>${c.name}${c.detail ? ` <small>(${c.detail})</small>` : ''}</span></div>`).join('');
  }


  // ------------------------------------------------------------------ scene setup
  function teardown() {
    if (!V) return;
    for (const o of V.objects) {
      scene.remove(o);
      o.traverse((x) => {
        if (x.geometry) x.geometry.dispose();
        if (x.material) { (Array.isArray(x.material) ? x.material : [x.material]).forEach((mm) => { if (mm.map) mm.map.dispose(); mm.dispose(); }); }
      });
    }
    lineMats.length = 0;
    V = null;
  }

  const DYN_CAP = 4300, DIST_SCALE = 1.3;

  function setup(res) {
    teardown();
    // a new build starts at its first step (the old step number may not exist in it)
    cur.k = 0; cur.pos = 0; cur.anim = null;
    const { P, fold } = res;
    const n = P.n, cc = (n - 1) / 2, N = fold.N;
    const { TY, CAT, SG, segs } = fold;
    const FP = new Float32Array(3 * N);
    for (let i = 0; i < N; i++) { FP[3 * i] = fold.X[i] - cc; FP[3 * i + 1] = fold.Y[i] - cc; FP[3 * i + 2] = -(fold.Z[i] - cc); }
    const intSeg = segs.find((s) => s.key === A.interiorKey); // these H's go into their own mesh (lighter beads)
    // the big cubes draw hundreds of thousands of beads: fewer pixels keep them smooth
    renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, n > 50 ? 1.5 : 2));
    resize();

    // base colours
    const col = new Float32Array(3 * N);
    const baseRGB = (i) => {
      if (!TY[i]) return catRGB(0);
      if (CAT[i] === 13) return itemRGB(segs[SG[i]].item);
      return catRGB(CAT[i]);
    };
    for (let i = 0; i < N; i++) { const c = baseRGB(i); col[3 * i] = c[0]; col[3 * i + 1] = c[1]; col[3 * i + 2] = c[2]; }

    // which connector (string index) a P belongs to
    const connOf = new Int16Array(N).fill(-1);
    fold.strings.forEach((s, si) => { for (let i = s.connStart; i < s.connEnd; i++) connOf[i] = si; });
    const stringRGB = fold.strings.map(stringColour);

    // mesh partition (surface H / interior H / P), all in chain order
    const cntS = new Int32Array(N + 1), cntI = new Int32Array(N + 1), cntP = new Int32Array(N + 1);
    let a = 0, b = 0, c = 0;
    for (let i = 0; i < N; i++) {
      cntS[i] = a; cntI[i] = b; cntP[i] = c;
      if (TY[i]) { if (i >= intSeg.start && i < intSeg.end) b++; else a++; } else c++;
    }
    cntS[N] = a; cntI[N] = b; cntP[N] = c;
    const pIdx = new Int32Array(c);

    const big = n > 50;
    const geoH = new THREE.IcosahedronGeometry(0.47, 1);
    const geoI = big ? new THREE.IcosahedronGeometry(0.47, 0) : geoH;
    const geoP = new THREE.IcosahedronGeometry(0.25, big ? 0 : 1);
    const matH = new THREE.MeshLambertMaterial({ color: 0xffffff });
    const matP = new THREE.MeshLambertMaterial({ color: 0xffffff });
    const mk = (geo, mat, cnt) => {
      const m = new THREE.InstancedMesh(geo, mat, Math.max(1, cnt));
      m.instanceColor = new THREE.InstancedBufferAttribute(new Float32Array(3 * Math.max(1, cnt)), 3);
      m.frustumCulled = false;
      m.count = 0;
      return m;
    };
    const meshS = mk(geoH, matH, a), meshI = mk(geoI, matH, b), meshP = mk(geoP, matP, c);
    {
      const mS = meshS.instanceMatrix.array, mI = meshI.instanceMatrix.array, mP = meshP.instanceMatrix.array;
      const cS = meshS.instanceColor.array, cI = meshI.instanceColor.array, cP = meshP.instanceColor.array;
      let ia = 0, ib = 0, ic = 0;
      for (let i = 0; i < N; i++) {
        const x = FP[3 * i], y = FP[3 * i + 1], z = FP[3 * i + 2];
        if (TY[i]) {
          if (i >= intSeg.start && i < intSeg.end) { setT(mI, ib, x, y, z); cI.set(col.subarray(3 * i, 3 * i + 3), 3 * ib); ib++; }
          else { setT(mS, ia, x, y, z); cS.set(col.subarray(3 * i, 3 * i + 3), 3 * ia); ia++; }
        } else { setT(mP, ic, x, y, z); cP.set(col.subarray(3 * i, 3 * i + 3), 3 * ic); pIdx[ic] = i; ic++; }
      }
      meshP.instanceColor.setUsage(THREE.DynamicDrawUsage);
    }

    // backbone
    const bondPos = new Float32Array(Math.max(1, N - 1) * 6);
    for (let i = 0; i < N - 1; i++) bondPos.set(FP.subarray(3 * i, 3 * i + 6), 6 * i);
    const bondGeo = new LineSegmentsGeometry();
    bondGeo.setPositions(bondPos);
    bondGeo.instanceCount = 0;
    const bondMat = bondMaterial();
    const bonds = new LineSegments2(bondGeo, bondMat); bonds.frustumCulled = false;

    // dynamic: the beads in flight and the straight chain still to fold, which fades into the stage
    const dynH = mk(geoH, new THREE.MeshLambertMaterial({ color: 0xffffff }), DYN_CAP);
    const dynP = mk(geoP, new THREE.MeshLambertMaterial({ color: 0xffffff }), DYN_CAP);
    for (const d of [dynH, dynP]) { d.instanceMatrix.setUsage(THREE.DynamicDrawUsage); d.instanceColor.setUsage(THREE.DynamicDrawUsage); }
    const dynBondGeo = new LineSegmentsGeometry();
    dynBondGeo.setPositions(new Float32Array((DYN_CAP + 4) * 6));
    dynBondGeo.setColors(new Float32Array((DYN_CAP + 4) * 6));
    dynBondGeo.attributes.instanceStart.data.setUsage(THREE.DynamicDrawUsage);
    dynBondGeo.attributes.instanceColorStart.data.setUsage(THREE.DynamicDrawUsage);
    dynBondGeo.instanceCount = 0;
    const dynBondMat = bondMaterial(); dynBondMat.vertexColors = true;
    const dynBonds = new LineSegments2(dynBondGeo, dynBondMat); dynBonds.frustumCulled = false;

    // Once the interior is folded, the beads deep inside it cannot be seen. On a big cube an opaque
    // box stands in for them, and only the two outer layers of the interior stay beads (the shell).
    let shell = null, coreBox = null, shellIdx = null;
    if (n > 24) {
      const lo = 2 - cc - 1e-6, hi = n - 3 - cc + 1e-6;
      const deep = (i) => { for (let d = 0; d < 3; d++) { const v = FP[3 * i + d]; if (v < lo || v > hi) return false; } return true; };
      let nd = 0, ns = 0;
      for (let i = intSeg.start; i < intSeg.end; i++) if (TY[i]) { if (deep(i)) nd++; else ns++; }
      if (nd === (n - 4) ** 3) {
        shell = mk(geoI, matH, ns); shellIdx = new Int32Array(ns);
        const mm = shell.instanceMatrix.array;
        let k = 0;
        for (let i = intSeg.start; i < intSeg.end; i++) if (TY[i] && !deep(i)) { setT(mm, k, FP[3 * i], FP[3 * i + 1], FP[3 * i + 2]); shellIdx[k++] = i; }
        shell.count = ns; shell.visible = false;
        coreBox = new THREE.Mesh(new THREE.BoxGeometry(n - 4.06, n - 4.06, n - 4.06), new THREE.MeshLambertMaterial({ color: 0xffffff }));
        coreBox.visible = false;
      }
    }

    // target cube wireframe, filled with a faint tint until the first step has been folded
    const wire = new THREE.LineSegments(new THREE.EdgesGeometry(new THREE.BoxGeometry(n, n, n)),
      new THREE.LineBasicMaterial({ color: 0x4a5466, transparent: true, opacity: 0.55 }));
    const ghost = new THREE.Mesh(new THREE.BoxGeometry(n, n, n),
      new THREE.MeshBasicMaterial({ color: 0x4a5466, transparent: true, opacity: 0.1, depthWrite: false, side: THREE.BackSide }));
    wire.add(ghost);

    // labels on the cube (strips, bins), drawn by buildOverlay() for the current stage
    const binGroup = new THREE.Group();

    const objects = [meshS, meshI, meshP, bonds, dynH, dynP, dynBonds, wire, binGroup];
    if (shell) objects.push(shell, coreBox);
    objects.forEach((o) => scene.add(o));
    const clipMats = [matH, matP, bondMat, dynH.material, dynP.material, dynBonds.material];

    V = {
      P, n, cc, N, FP, TY, CAT, SG, segs, fold, col, connOf, stringRGB, pIdx,
      cntS, cntI, cntP, meshS, meshI, meshP, bondGeo, bonds, dynH, dynP, dynBondGeo, dynBonds, wire, binGroup,
      objects, clipMats, contactPrefix: res.val.contactPrefix, target: res.val.target,
      lastStats: '', tint: null, matP, bondMat, intStart: intSeg.start, intEnd: intSeg.end,
      shell, shellIdx, coreBox, cutState: null, ghost,
      // the unfolded chain fades into the stage from fadeA to fadeB beads past the fold
      fadeA: 0.08 * n + 3, fadeB: 0.3 * n + 6,
    };
    V.steps = A.buildSteps(res, X);
    // per-step timing
    V.steps.forEach((st, i) => {
      const len = st.e - st.s;
      st.W = clamp(Math.round(len * 0.18), 4, 3500);
      st.dur = len ? 1.15 + 0.8 * Math.log10(1 + len) : 1.5;
      st.dirPrev = i ? V.steps[i - 1].dir : st.dir;
    });
    V.overlayFrom = A.overlayFrom(V.steps);
    paintAll();
    // factor ranges for the formula
    V.factorRange = {};
    for (const f of res.str.factors) V.factorRange[f.key] = [f.start, f.end];
    segs.forEach((s) => { if (s.key === 'item') V.factorRange[s.fkey || 'item-' + s.item] = [s.start, s.end]; });

    buildTimeline();
    setupBar();
    $('#rd-placeholder').hidden = true; $('#rd-hud').hidden = false; $('#rd-dock').hidden = false; $('#rd-zoom').hidden = false;
    resize();
    controls.minDistance = 2; controls.maxDistance = 120 * n;
    camera.far = 400 * n; camera.near = Math.max(0.1, n / 200); camera.updateProjectionMatrix();
    camTween = null;
    // fixed default camera (the per-step camera flights are opt-in via View ▸ auto camera)
    const v0 = $('#rd-tgCam').checked ? V.steps[0].view : A.fixedView;
    controls.target.set(...v0.tgt.map((x) => x * n));
    camera.position.copy(controls.target).add(new THREE.Vector3(...v0.dir).normalize().multiplyScalar(v0.dist * n * DIST_SCALE * fitScale));
  }


  // the colour that highlights a linker: that of the piece it leads to
  const stringColour = (s) => (s.kind === 'item' ? itemRGB(s.item) : catRGB(s.cat !== undefined ? s.cat : s.kind === 'filler' ? 11 : 12));
  // labels on the cube for the current stage (the adapter makes them)
  function buildOverlay() {
    const g = V.binGroup;
    for (const ch of [...g.children]) {
      g.remove(ch);
      if (ch.geometry) ch.geometry.dispose();
      if (ch.material) { if (ch.material.map) ch.material.map.dispose(); ch.material.dispose(); }
    }
    for (const o of A.buildOverlay(V, RES, X)) g.add(o);
  }

  function makeLabel(text, color, n) {
    const fs = 44, pad = 14;
    const cv = document.createElement('canvas');
    const ctx = cv.getContext('2d');
    ctx.font = `600 ${fs}px -apple-system, Segoe UI, Roboto, sans-serif`;
    const tw = Math.ceil(ctx.measureText(text).width);
    cv.width = tw + 2 * pad; cv.height = fs + 2 * pad;
    ctx.font = `600 ${fs}px -apple-system, Segoe UI, Roboto, sans-serif`;
    ctx.fillStyle = ST().label;
    const r = 16; const w = cv.width, h = cv.height;
    ctx.beginPath(); ctx.moveTo(r, 0); ctx.arcTo(w, 0, w, h, r); ctx.arcTo(w, h, 0, h, r); ctx.arcTo(0, h, 0, 0, r); ctx.arcTo(0, 0, w, 0, r); ctx.fill();
    ctx.fillStyle = color; ctx.textBaseline = 'middle'; ctx.fillText(text, pad, h / 2 + 2);
    const tex = new THREE.CanvasTexture(cv);
    tex.colorSpace = THREE.SRGBColorSpace;
    tex.minFilter = THREE.LinearFilter;
    const spr = new THREE.Sprite(new THREE.SpriteMaterial({ map: tex, depthTest: false, transparent: true }));
    const hWorld = 0.045 * n;
    spr.scale.set(hWorld * w / h, hWorld, 1);
    spr.userData.w = hWorld * w / h;
    spr.renderOrder = 10;
    return spr;
  }


  // ------------------------------------------------------------------ timeline & step UI
  function buildTimeline() {
    const tl = $('#rd-timeline');
    tl.innerHTML = '';
    let grp = null, pills = null;
    V.steps.forEach((st, i) => {
      if (st.groupName !== grp) {
        grp = st.groupName;
        const g = document.createElement('div'); g.className = 'grp';
        g.innerHTML = `<div class="gl">${grp}</div><div class="pills"></div>`;
        tl.appendChild(g); pills = g.querySelector('.pills');
      }
      const b = document.createElement('button');
      b.className = 'pill'; b.textContent = i; b.title = st.title.replace(/<[^>]+>/g, '');
      b.addEventListener('click', () => { goStep(i, true); });
      pills.appendChild(b);
    });
  }

  function prettyTitle(t) {
    // turn X^{...} / X^123 into superscripts
    return t.replace(/S_B/g, 'S<sub>B</sub>').replace(/_\{([^}]*)\}/g, '<sub>$1</sub>').replace(/\^\{([^}]*)\}/g, '<sup>$1</sup>').replace(/\^([0-9,]+)/g, '<sup>$1</sup>');
  }

  function stepUI() {
    const st = V.steps[cur.k];
    root.querySelectorAll('#rd-timeline .pill').forEach((p, i) => {
      p.classList.toggle('cur', i === cur.k);
      p.classList.toggle('done', i < cur.k);
    });
    $('#rd-stepTag').innerHTML = prettyTitle(`Step ${cur.k} of ${V.steps.length - 1}${st.tag ? ` · ${st.tag}` : ''}`);
    $('#rd-stepTitle').innerHTML = prettyTitle(st.title);
    $('#rd-stepBody').innerHTML = st.body + A.refs(st, X);
    $('#rd-stepinfo').scrollTop = 0;
    if (st.e > st.s) {
      let h = 0; for (let i = st.s; i < st.e; i++) h += V.TY[i];
      $('#rd-stepRes').textContent = `folds residues ${fmt(st.s + 1)}–${fmt(st.e)} of ${fmt(V.N)}  ·  ${fmt(h)} H, ${fmt(st.e - st.s - h)} P`;
    } else $('#rd-stepRes').textContent = st.id === 'start' ? `${fmt(V.N)} residues, nothing placed yet` : 'view of the finished fold';
    markFormula();
    markActive(st.items);
    $('#rd-hint').hidden = cur.k !== 0;
    // the status first says how to move through the steps; once the reader does, it says less
    if (V.hintK !== undefined && cur.k !== V.hintK) { V.hintK = undefined; if (RES.val.ok) setStatus('Folded and checked.', 'ok'); }
  }

  // jump to step k (its start, then fold it if animate; else straight to its end)
  function goStep(k, animate) {
    if (!V) return;
    k = clamp(k, 0, V.steps.length - 1);
    const st = V.steps[k];
    if (animate && st.e > st.s) startAnim(st.s, st.e, k);
    else { cur.anim = null; cur.pos = st.e; }
    setStep(k, true);
  }
  // make k the current step: its colours, cut-away, texts (and camera, if asked for)
  function setStep(k, moveCamera) {
    cur.k = k;
    const st = V.steps[k];
    $('#rd-tgCut').checked = !!st.cut;
    applyTint(st);
    applyVisibility();
    stepUI();
    if (moveCamera && $('#rd-tgCam').checked) flyTo(st.view, 1.4);
  }
  function startAnim(from, to, k) {
    const st = V.steps[k], len = to - from;
    cur.anim = { from, to, t: 0, W: clamp(Math.round(len * 0.18), 4, 3500), dur: 1.15 + 0.8 * Math.log10(1 + len),
      dir0: from === st.s ? st.dirPrev : st.dir, dir1: st.dir };
    cur.pos = from;
  }
  // the step whose residues contain position pos (step 0 at the very start)
  function stepOfPos(pos) {
    if (pos <= 0) return 0;
    for (let k = 0; k < V.steps.length; k++) { const st = V.steps[k]; if (st.e > st.s && pos > st.s && pos <= st.e) return k; }
    return V.steps.length - 1;
  }
  // dragging along the string: jump to any residue
  function scrubTo(pos) {
    cur.anim = null;
    cur.pos = pos;
    const k = stepOfPos(pos);
    if (k !== cur.k) setStep(k, false);
  }

  function applyTint(st) {
    const key = st.tint ? st.tint.join(',') + '|' + (st.tintAmt || 0.6) : '';
    if (V.tint === key) return;
    V.tint = key;
    const set = new Set(st.tint || []);
    const amt = st.tintAmt || 0.6;
    const { pIdx, connOf, stringRGB, col, meshP } = V;
    const arr = meshP.instanceColor.array;
    const g = catRGB(0);
    for (let s = 0; s < pIdx.length; s++) {
      const i = pIdx[s], cs = connOf[i];
      let r = g[0], gg = g[1], b = g[2];
      if (cs >= 0 && set.has(cs)) { const t = stringRGB[cs]; r += (t[0] - r) * amt; gg += (t[1] - gg) * amt; b += (t[2] - b) * amt; }
      arr[3 * s] = r; arr[3 * s + 1] = gg; arr[3 * s + 2] = b;
      col[3 * i] = r; col[3 * i + 1] = gg; col[3 * i + 2] = b;
    }
    meshP.instanceColor.needsUpdate = true;
  }

  // re-colour everything for the current scheme (H's by category/item, P's grey or tinted)
  function paintAll() {
    if (!V) return;
    const { N, TY, CAT, SG, segs, col, meshS, meshI } = V;
    const cS = meshS.instanceColor.array, cI = meshI.instanceColor.array;
    let ia = 0, ib = 0;
    for (let i = 0; i < N; i++) {
      if (!TY[i]) continue;
      const c = CAT[i] === 13 ? itemRGB(segs[SG[i]].item) : catRGB(CAT[i]);
      col[3 * i] = c[0]; col[3 * i + 1] = c[1]; col[3 * i + 2] = c[2];
      if (i >= V.intStart && i < V.intEnd) { cI[3 * ib] = c[0]; cI[3 * ib + 1] = c[1]; cI[3 * ib + 2] = c[2]; ib++; }
      else { cS[3 * ia] = c[0]; cS[3 * ia + 1] = c[1]; cS[3 * ia + 2] = c[2]; ia++; }
    }
    meshS.instanceColor.needsUpdate = true; meshI.instanceColor.needsUpdate = true;
    if (V.shell) {
      const cc = V.shell.instanceColor.array, si = V.shellIdx;
      for (let k = 0; k < si.length; k++) { const i = si[k]; cc[3 * k] = col[3 * i]; cc[3 * k + 1] = col[3 * i + 1]; cc[3 * k + 2] = col[3 * i + 2]; }
      V.shell.instanceColor.needsUpdate = true;
      V.coreBox.material.color.setRGB(...col.subarray(3 * V.shellIdx[0], 3 * V.shellIdx[0] + 3));
    }
    V.stringRGB = V.fold.strings.map(stringColour);
    V.tint = null;
    if (V.steps) applyTint(V.steps[Math.min(cur.k, V.steps.length - 1)]);
    const sc = pal(), st = ST();
    for (const m of [V.matP, V.dynP.material]) { m.transparent = sc.pOpacity < 1; m.opacity = sc.pOpacity; m.depthWrite = sc.pOpacity >= 1; m.needsUpdate = true; }
    for (const m of [V.bondMat, V.dynBonds.material]) m.opacity = sc.bondOpacity;
    V.bondMat.color.setHex(st.line);
    V.lineRGB = rgbOf(st.line); V.clearRGB = rgbOf(st.clear);
    V.wire.material.color.setHex(st.wire); V.wire.material.opacity = st.wireOp;
    V.ghost.material.color.setHex(st.wire);
    buildOverlay();
    if (barPieces.length) drawBar(true);
  }
  // the legend in the corner: a big H bead and a small P bead in the current colours
  function renderLegend() {
    $('#rd-lgH').style.fill = scheme === 'hp' ? catHex(1) : catHex(4);
    $('#rd-lgP').style.fill = catHex(0);
    $('#rd-lgP').style.fillOpacity = String(Math.max(0.55, pal().pOpacity));
  }
  function applyStage() {
    root.dataset.stage = stage;
    renderer.setClearColor(ST().clear);
    const night = stage === 'night';
    const b = $('#rd-stageBtn');
    b.textContent = night ? '☀' : '☾';
    b.title = night ? 'Day view' : 'Night view'; b.setAttribute('aria-label', b.title);
    paintAll();
    renderLegend();
  }
  $('#rd-stageBtn').addEventListener('click', () => { stage = stage === 'day' ? 'night' : 'day'; stageChosen = true; applyStage(); });
  document.documentElement.addEventListener('themechange', (e) => {
    readItemColours();
    if (!stageChosen) stage = e.detail === 'dark' ? 'night' : 'day';
    applyStage();
  });
  // explanation, step numbers and counters stay hidden until the reader asks for them
  $('#rd-explain').addEventListener('click', () => {
    const open = root.dataset.explain !== '1';
    root.dataset.explain = open ? '1' : '0';
    $('#rd-explain').textContent = open ? 'Hide explanation' : 'Explain';
    $('#rd-explain').setAttribute('aria-expanded', String(open));
  });
  $('#rd-tgHP').addEventListener('change', () => {
    scheme = $('#rd-tgHP').checked ? 'hp' : 'normal';
    paintAll();
    renderLegend();
  });

  function applyVisibility() {
    if (!V) return;
    const st = V.steps[cur.k];
    const showP = $('#rd-tgP').checked;
    V.meshP.visible = showP; V.dynP.visible = showP;
    const showB = $('#rd-tgBond').checked;
    V.bonds.visible = showB; V.dynBonds.visible = showB;
    V.binGroup.visible = $('#rd-tgLab').checked && cur.k >= V.overlayFrom;
    const cut = $('#rd-tgCut').checked;
    if (V.cutState !== cut) {
      V.cutState = cut;
      for (const m of V.clipMats) { m.clippingPlanes = cut ? cutPlanes : null; m.clipIntersection = true; m.needsUpdate = true; }
    }
  }
  for (const id of ['#rd-tgP', '#rd-tgBond', '#rd-tgLab', '#rd-tgCut']) $(id).addEventListener('change', applyVisibility);
  $('#rd-tgCam').addEventListener('change', () => { if ($('#rd-tgCam').checked && V) flyTo(V.steps[cur.k].view, 1.2); });

  // → : finish the step being folded, else fold the rest of this step, else the next step.
  // ← : back to where this step started (the end of the step before).
  function stepForward() {
    if (!V) return;
    if (cur.anim) { cur.pos = cur.anim.to; cur.anim = null; return; }
    const st = V.steps[cur.k];
    if (st.e > st.s && cur.pos < st.e) { startAnim(cur.pos, st.e, cur.k); return; }
    if (cur.k < V.steps.length - 1) goStep(cur.k + 1, true);
  }
  function stepBack() {
    if (!V) return;
    if (cur.anim) { cur.pos = cur.anim.from; cur.anim = null; }
    const st = V.steps[cur.k];
    if (st.e > st.s && cur.pos > st.s) { cur.pos = st.s; setStep(stepOfPos(cur.pos), true); return; }
    if (cur.k > 0) { const k = cur.k - 1; cur.pos = V.steps[k].e; setStep(k, true); }
  }
  $('#rd-bNext').addEventListener('click', stepForward);
  $('#rd-bPrev').addEventListener('click', stepBack);
  $('#rd-speed').addEventListener('input', () => {
    speed = Math.pow(2, ($('#rd-speed').value - 50) / 20);
    $('#rd-speedLbl').textContent = (speed < 1 ? speed.toFixed(2) : speed.toFixed(1)) + '×';
  });
  // the widget takes ← → while at least half of it is on screen, or while focus is inside it
  const inView = () => {
    const r = root.getBoundingClientRect();
    const seen = Math.min(r.bottom, window.innerHeight) - Math.max(r.top, 0);
    return seen >= 0.5 * Math.min(r.height, window.innerHeight);
  };
  // rendering pauses while the widget is off screen (assumed on screen until told otherwise)
  let onScreen = true;
  new IntersectionObserver((es) => { for (const e of es) onScreen = e.isIntersecting; }).observe(root);
  window.addEventListener('keydown', (e) => {
    if (!V || e.defaultPrevented || e.metaKey || e.ctrlKey || e.altKey) return;
    const a = document.activeElement;
    if (!root.contains(a) && !inView()) return;
    if (a && /INPUT|SELECT|TEXTAREA/.test(a.tagName)) return;
    if (e.key === 'ArrowRight') { stepForward(); e.preventDefault(); }
    else if (e.key === 'ArrowLeft') { stepBack(); e.preventDefault(); }
    else if (e.key === '+' || e.key === '=') { zoomBy(0.8); e.preventDefault(); }
    else if (e.key === '-' || e.key === '_') { zoomBy(1.25); e.preventDefault(); }
  });

  // ------------------------------------------------------------------ camera
  function flyTo(view, dur) {
    const n = V.n;
    const tgt = new THREE.Vector3(...(view.tgt || [0, 0, 0])).multiplyScalar(n);
    const dir = new THREE.Vector3(...view.dir).normalize();
    camTween = { t: 0, dur, p0: camera.position.clone(), t0: controls.target.clone(), t1: tgt, u1: dir, r1: view.dist * n * DIST_SCALE * fitScale };
    const d0 = camTween.p0.clone().sub(camTween.t0);
    camTween.r0 = d0.length(); camTween.u0 = d0.normalize();
  }
  function slerpDir(u0, u1, t) {
    const dot = clamp(u0.dot(u1), -1, 1);
    const ang = Math.acos(dot);
    if (ang < 1e-3) return u0.clone().lerp(u1, t).normalize();
    if (Math.PI - ang < 1e-2) { // opposite: go over the top
      const mid = new THREE.Vector3(0, 1, 0);
      return t < 0.5 ? slerpDir(u0, mid, t * 2) : slerpDir(mid, u1, t * 2 - 1);
    }
    const s = Math.sin(ang);
    return u0.clone().multiplyScalar(Math.sin((1 - t) * ang) / s).add(u1.clone().multiplyScalar(Math.sin(t * ang) / s));
  }
  function updateCamera(dt) {
    if (!camTween) return;
    camTween.t = Math.min(1, camTween.t + dt / camTween.dur);
    const e = easeIO(camTween.t);
    const tgt = camTween.t0.clone().lerp(camTween.t1, e);
    const u = slerpDir(camTween.u0, camTween.u1, e);
    const r = camTween.r0 + (camTween.r1 - camTween.r0) * e;
    controls.target.copy(tgt);
    camera.position.copy(tgt).add(u.multiplyScalar(r));
    if (camTween.t >= 1) camTween = null;
  }

  // ------------------------------------------------------------------ per-frame bead update
  const vA = new THREE.Vector3(), vD = new THREE.Vector3(), vD0 = new THREE.Vector3(), vD1 = new THREE.Vector3();
  function updateBeads() {
    const st = V.steps[cur.k];
    const { FP, TY, N, col } = V;
    const an = cur.anim;
    let s, e, W, t, f, placed, dir0, dir1;
    if (an) {
      s = an.from; e = an.to; W = an.W; t = an.t; dir0 = an.dir0; dir1 = an.dir1;
      f = s + (e - s + W) * easeIO(t);
      placed = t >= 1 ? e : clamp(Math.floor(f - W) + 1, s, e);
    } else {
      s = e = f = placed = cur.pos; W = 1; t = 1; dir0 = dir1 = st.dir;
    }
    const len = e - s;
    V.placed = placed;
    V.meshS.count = V.cntS[placed]; V.meshI.count = V.cntI[placed]; V.meshP.count = V.cntP[placed];
    {
      // the faint fill of the target cube fades out over the first folded step
      const e1 = V.steps[1] ? Math.max(1, V.steps[1].e) : 1;
      const a = 1 - clamp(placed / e1, 0, 1);
      V.ghost.visible = a > 0.01; V.ghost.material.opacity = 0.12 * a;
    }
    if (V.shell) {
      const boxed = placed >= V.intEnd && !V.cutState;
      V.meshI.visible = !boxed; V.shell.visible = boxed; V.coreBox.visible = boxed;
    }
    V.bondGeo.instanceCount = Math.max(0, placed - 1);

    // tail anchor and direction
    vD0.copy(toThree(dir0)); vD1.copy(toThree(dir1));
    vD.copy(vD0).lerp(vD1, smooth(Math.min(1, t * 3))).normalize();
    const ta = easeIO(t);
    let bx0, by0, bz0;
    if (s > 0) { bx0 = FP[3 * (s - 1)]; by0 = FP[3 * (s - 1) + 1]; bz0 = FP[3 * (s - 1) + 2]; }
    else { bx0 = FP[0] - vD0.x; by0 = FP[1] - vD0.y; bz0 = FP[2] - vD0.z; }
    let bx1 = bx0, by1 = by0, bz1 = bz0;
    if (len > 0) { bx1 = FP[3 * (e - 1)]; by1 = FP[3 * (e - 1) + 1]; bz1 = FP[3 * (e - 1) + 2]; }
    vA.set(bx0 + (bx1 - bx0) * ta + vD.x, by0 + (by1 - by0) * ta + vD.y, bz0 + (bz1 - bz0) * ta + vD.z);
    const g = Math.min(f, e);
    const fA = V.fadeA, fB = V.fadeB, cl = V.clearRGB, ln = V.lineRGB;
    const hi = Math.min(N, Math.ceil(Math.max(f, e) + fB) + 1, placed + DYN_CAP - 2);

    const mH = V.dynH.instanceMatrix.array, mP = V.dynP.instanceMatrix.array;
    const cH = V.dynH.instanceColor.array, cP = V.dynP.instanceColor.array;
    const bondBuf = V.dynBondGeo.attributes.instanceStart.data, bp = bondBuf.array;
    const bondCol = V.dynBondGeo.attributes.instanceColorStart.data, bc = bondCol.array;
    let nh = 0, np = 0, nb = 0;
    let px = 0, py = 0, pz = 0, pa = 0, havePrev = false;
    if (placed > 0) { px = FP[3 * (placed - 1)]; py = FP[3 * (placed - 1) + 1]; pz = FP[3 * (placed - 1) + 2]; havePrev = true; }
    for (let j = placed; j < hi; j++) {
      let x, y, z, a = 0; // a: how far the bead has faded into the stage (0 not at all, 1 gone)
      if (j < e && j < f) {
        const p = smooth(Math.min(1, (f - j) / W));
        x = vA.x + (FP[3 * j] - vA.x) * p; y = vA.y + (FP[3 * j + 1] - vA.y) * p; z = vA.z + (FP[3 * j + 2] - vA.z) * p;
      } else {
        const o = j - g;
        a = smooth(clamp((o - fA) / (fB - fA), 0, 1));
        if (a >= 0.999) break;
        x = vA.x + vD.x * o; y = vA.y + vD.y * o; z = vA.z + vD.z * o;
      }
      const sc = 1 - 0.55 * a;
      if (TY[j]) {
        setTS(mH, nh, x, y, z, sc);
        for (let c = 0; c < 3; c++) cH[3 * nh + c] = col[3 * j + c] + (cl[c] - col[3 * j + c]) * a;
        nh++;
      } else {
        setTS(mP, np, x, y, z, sc);
        for (let c = 0; c < 3; c++) cP[3 * np + c] = col[3 * j + c] + (cl[c] - col[3 * j + c]) * a;
        np++;
      }
      if (havePrev) {
        const o = 6 * nb; bp[o] = px; bp[o + 1] = py; bp[o + 2] = pz; bp[o + 3] = x; bp[o + 4] = y; bp[o + 5] = z;
        for (let c = 0; c < 3; c++) { bc[o + c] = ln[c] + (cl[c] - ln[c]) * pa; bc[o + 3 + c] = ln[c] + (cl[c] - ln[c]) * a; }
        nb++;
      }
      px = x; py = y; pz = z; pa = a; havePrev = true;
    }
    V.dynH.count = nh; V.dynP.count = np;
    const upload = (attr, count) => { attr.clearUpdateRanges(); attr.addUpdateRange(0, Math.max(1, count)); attr.needsUpdate = true; };
    upload(V.dynH.instanceMatrix, nh * 16); upload(V.dynP.instanceMatrix, np * 16);
    upload(V.dynH.instanceColor, nh * 3); upload(V.dynP.instanceColor, np * 3);
    for (const buf of [bondBuf, bondCol]) { buf.clearUpdateRanges(); buf.addUpdateRange(0, Math.max(1, nb * 6)); buf.needsUpdate = true; }
    V.dynBondGeo.instanceCount = nb;
  }

  // ------------------------------------------------------------------ the string bar
  // The whole string from left to right: H pieces full height in their colours, runs of P's as a
  // thin grey line, the part not folded yet faded. The arrow marks how far the fold has got;
  // dragging along the bar folds or unfolds to any residue.
  const bar = $('#rd-bar'), barCv = $('#rd-barCv'), marker = $('#rd-marker'), barTip = $('#rd-barTip');
  let barPieces = [], barW = 0, barH = 0, barShown = -1, barDrag = false;
  function setupBar() {
    barPieces = A.barPieces(V);
    bar.setAttribute('aria-valuemax', String(V.N));
    barShown = -1;
    drawBar(true);
  }
  const pieceColor = (p) => (p.kind === 'P' ? catHex(0) : p.kind === 'item' ? itemHex(p.item) : p.kind === 'filler' ? catHex(11) : p.kind === 'dummy' ? catHex(12) : catHex(p.cat));
  function drawBar(force) {
    if (!V || !barPieces.length) return;
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    const w = Math.max(1, Math.round(barCv.clientWidth * dpr)), h = Math.max(1, Math.round(barCv.clientHeight * dpr));
    if (w !== barW || h !== barH) { barCv.width = barW = w; barCv.height = barH = h; force = true; }
    const placed = V.placed;
    if (!force && placed === barShown) return;
    barShown = placed;
    const ctx = barCv.getContext('2d'), sx = w / V.N, xm = placed * sx;
    ctx.clearRect(0, 0, w, h);
    for (const done of [false, true]) {
      ctx.save();
      ctx.beginPath();
      if (done) ctx.rect(0, 0, xm, h); else ctx.rect(xm, 0, w - xm, h);
      ctx.clip();
      ctx.globalAlpha = done ? 1 : 0.32;
      for (const p of barPieces) {
        let x0 = p.s * sx, x1 = p.e * sx;
        if (p.min && x1 - x0 < 2 * dpr) { const c = (x0 + x1) / 2; x0 = c - dpr; x1 = c + dpr; }
        const thin = p.kind === 'P';
        ctx.fillStyle = pieceColor(p);
        ctx.fillRect(x0, thin ? h * 0.38 : 0, Math.max(x1 - x0, 0.6), thin ? h * 0.24 : h);
      }
      ctx.restore();
    }
    marker.style.left = (100 * placed / V.N) + '%';
    bar.setAttribute('aria-valuenow', String(placed));
    bar.setAttribute('aria-valuetext', `${fmt(placed)} of ${fmt(V.N)} letters folded`);
  }
  const posAt = (x) => { const r = barCv.getBoundingClientRect(); return clamp(Math.round(((x - r.left) / r.width) * V.N), 0, V.N); };
  const pieceAt = (pos) => barPieces.find((p) => pos >= p.s && pos < p.e) || barPieces[barPieces.length - 1];
  bar.addEventListener('pointerdown', (e) => {
    if (!V) return;
    barDrag = true;
    bar.setPointerCapture(e.pointerId);
    scrubTo(posAt(e.clientX));
    e.preventDefault();
  });
  bar.addEventListener('pointermove', (e) => {
    if (!V || !barPieces.length) return;
    const pos = posAt(e.clientX);
    if (barDrag) scrubTo(pos);
    const r = barCv.getBoundingClientRect();
    barTip.textContent = pieceAt(pos).label;
    barTip.style.left = (clamp(e.clientX - r.left, 0, r.width) / r.width * 100) + '%';
    barTip.hidden = false;
  });
  const endDrag = (e) => { barDrag = false; try { bar.releasePointerCapture(e.pointerId); } catch (err) { /* already released */ } };
  bar.addEventListener('pointerup', endDrag);
  bar.addEventListener('pointercancel', endDrag);
  bar.addEventListener('pointerleave', () => { if (!barDrag) barTip.hidden = true; });

  // ------------------------------------------------------------------ main loop
  let lastT = performance.now(), statAcc = 0;
  function frame(now) {
    requestAnimationFrame(frame);
    const dt = Math.min(0.05, (now - lastT) / 1000); lastT = now;
    if (!onScreen) return;
    if (V) {
      if (cur.anim) {
        cur.anim.t += dt * speed / cur.anim.dur;
        if (cur.anim.t >= 1) { cur.pos = cur.anim.to; cur.anim = null; }
      }
      updateBeads();
      drawBar(false);
      statAcc += dt;
      if (statAcc > 0.1) {
        statAcc = 0;
        const pl = V.placed;
        const txt = `<span class="k">residues placed</span> ${fmt(pl)} / ${fmt(V.N)}<br><span class="k" title="neighbouring H's, consecutive ones included, as the paper counts">H–H pairs</span> ${fmt(V.contactPrefix[pl])} / ${fmt(V.target)}<br><span class="k">cube</span> ${V.n}×${V.n}×${V.n} &nbsp;<span class="k">step</span> ${cur.k}/${V.steps.length - 1}`;
        if (txt !== V.lastStats) { $('#rd-stats').innerHTML = txt; V.lastStats = txt; }
      }
    }
    updateCamera(dt);
    controls.update();
    renderer.render(scene, camera);
  }
  requestAnimationFrame(frame);

  // ------------------------------------------------------------------ init
  root.dataset.explain = '0';
  readItemColours();
  applyStage();
  loadPreset(0);
  // the page opens on the first preset, already folded, so that the finished cube is there at once
  onFind({ atEnd: true });
}
