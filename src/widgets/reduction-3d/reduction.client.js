/**
 * The reduction, folded: Berger and Leighton's string S_B for a bin packing instance, folded into a
 * perfect cube step by step as in §3.2.3 (the "Folded in 3D" section).
 *
 * mount(root) takes the markup of Reduction3D.astro (ids prefixed rd-, one widget per page) and
 * builds everything inside it: the packing board (drag and drop), the parameters, the formula of
 * S_B with the current factor marked, the front-face map, the checks of the fold, and the three.js
 * stage with the step timeline. The construction itself is in construction.js.
 *
 * Keys (while the widget fills most of the screen or has focus): → completes the running step or
 * folds the next one, ← goes back one step, Space plays all steps.
 * Rendering pauses while the widget is off screen.
 */
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { LineSegments2 } from 'three/addons/lines/LineSegments2.js';
import { LineSegmentsGeometry } from 'three/addons/lines/LineSegmentsGeometry.js';
import { LineMaterial } from 'three/addons/lines/LineMaterial.js';
import * as C from './construction.js';

export function mount(root) {
  const $ = (s) => root.querySelector(s);
  // the proof board, for the "On the proof board" links of every step
  const CARDS = root.dataset.cards || '../original-proof/';
  const card = (id, label) => `<a href="${CARDS}#step-bl-${id}" target="_blank" rel="noopener">${label}</a>`;
  const fmt = (x) => Number(x).toLocaleString('en-US');
  const clamp = (x, a, b) => (x < a ? a : x > b ? b : x);

  // ------------------------------------------------------------------ presets & colours
  const PRESETS = [
    { name: 'K = 2, B = 4, U = {2, 4, 2}', K: 2, B: 4, sizes: [2, 4, 2] },
    { name: 'K = 2, B = 8, U = {4, 2, 6, 2, 2}', K: 2, B: 8, sizes: [4, 2, 6, 2, 2] },
    { name: 'K = 2, B = 8, U = {2, 4, 2, 2, 4, 2}', K: 2, B: 8, sizes: [2, 4, 2, 2, 4, 2] },
    { name: 'K = 2, B = 6, U = {2, 2, 4, 2, 2}', K: 2, B: 6, sizes: [2, 2, 4, 2, 2] },
    { name: 'unsolvable: K = 2, B = 8, U = {6, 6, 4}', K: 2, B: 8, sizes: [6, 6, 4] },
    { name: 'the running example: K = 2, B = 10, U = {6, 2, 8, 4} (n = 80, heavy)', K: 2, B: 10, sizes: [6, 2, 8, 4] },
    { name: 'K = 3, B = 12, U = {6, 4, 4, 4, 2, 2, 8, 6} (n = 80, heavy)', K: 3, B: 12, sizes: [6, 4, 4, 4, 2, 2, 8, 6] },
  ];
  // CAT: 0 P, 1 edges, 2 back, 3 back-left edge, 4 left, 5 bottom, 6 right, 7 top, 8 interior,
  //      9 wall, 10 special, 11 filler, 12 dummy, 13 item
  // Palettes. 'hp' (the default): H's in reds (edges a light red; faces, core and paddings paler;
  // walls dark), P's grey and translucent, items in bright colours; one version per stage.
  // 'normal': one colour per step of the construction.
  const PALETTES = {
    normal: {
      cat: ['#a3a9b3', '#f2b33d', '#3f7ed6', '#f2b33d', '#4a90e2', '#386fc4', '#5a9cf0', '#4485dc', '#2d5aa0',
        '#b8463a', '#ff8c1a', '#4f8f86', '#9c8a6a', '#ffffff'],
      items: ['#ffd23f', '#4cc9ff', '#3ee07a', '#ff5dc8', '#c77dff', '#ff9f43', '#9ef01a', '#00e5c0', '#ff6b6b', '#a0c4ff'],
      pOpacity: 1, bondOpacity: 0.55,
    },
    hp_night: {
      cat: ['#aab0b8', '#ff8a7a', '#f6c3bc', '#ff8a7a', '#f6c3bc', '#f6c3bc', '#f6c3bc', '#f6c3bc', '#efaaa2',
        '#9e1c1c', '#ff8a7a', '#fbdcd7', '#e39a91', '#ffffff'],
      items: ['#39ff14', '#00f0ff', '#ff00ff', '#ffff00', '#bc13fe', '#00ff9f', '#4d4dff', '#ccff00', '#7df9ff', '#ff9f00'],
      pOpacity: 0.62, bondOpacity: 0.6,
    },
    hp_day: {
      cat: ['#5f6670', '#f0705e', '#f2b0a7', '#f0705e', '#f2b0a7', '#f2b0a7', '#f2b0a7', '#f2b0a7', '#ea9b91',
        '#9e1c1c', '#f0705e', '#f6c8c1', '#d6837a', '#ffffff'],
      items: ['#2bd60f', '#00b4e0', '#e000e0', '#f2c200', '#a312f0', '#00c98a', '#3d3dff', '#90c000', '#1fb2d4', '#ff8a00'],
      pOpacity: 0.72, bondOpacity: 0.7,
    },
  };
  // The stage: day (light, like the page) or night (dark). It follows the site's theme until the
  // reader picks one with the sun / moon button.
  const STAGES = {
    day: {
      clear: 0xf2f0eb, line: 0x7f858e, wire: 0xb5aea1, wireOp: 0.9, label: 'rgba(255,255,255,0.92)', ink: '#1c1c21', plugInk: '#7a6538',
      strip: 0x1c1c21, plugStrip: 0x8a7650, stripOp: 0.45, map: '#e9e5dc', mapEmpty: '#d6d1c6', mapLine: 'rgba(28,28,33,0.8)', mapPlug: 'rgba(122,101,56,0.9)',
    },
    night: {
      clear: 0x0e1116, line: 0x8a919c, wire: 0x4a5466, wireOp: 0.55, label: 'rgba(14,17,22,0.78)', ink: '#ffffff', plugInk: '#dccb9f',
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
  const itemHex = (u) => { const a = pal().items; return a[u % a.length]; };
  const catRGB = (c) => rgbOf(catHex(c));
  const itemRGB = (u) => rgbOf(itemHex(u));

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
    fitScale = clamp(0.62 / free, 0.85, 2.4);
  }
  let fitScale = 1;
  new ResizeObserver(resize).observe(glWrap);
  new ResizeObserver(resize).observe($('#rd-dock'));
  new ResizeObserver(resize).observe($('#rd-hud'));
  $('#rd-viewBtn').addEventListener('click', () => { $('#rd-toggles').hidden = !$('#rd-toggles').hidden; });
  resize();

  const cutPlanes = [new THREE.Plane(new THREE.Vector3(-1, 0, 0), 0), new THREE.Plane(new THREE.Vector3(0, -1, 0), 0),
    new THREE.Plane(new THREE.Vector3(0, 0, -1), 0)];

  // ------------------------------------------------------------------ state
  let RES = null;      // build result
  let V = null;        // scene data for the current build
  // where we are: cur.pos residues are folded; cur.k is the step that contains that position;
  // cur.anim, while a step is being folded, runs from anim.from to anim.to residues
  const cur = { k: 0, pos: 0, anim: null };
  let speed = 1;
  let camTween = null;
  let fmtNumeric = false;

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
    if (chk.errs.length) { setStatus(chk.errs[0], 'err'); renderParams(null); renderFormula(null); return; }
    if (chk.P.q > 6) { setStatus(`q = ${chk.P.q} gives n = ${chk.P.n} (${fmt(chk.P.n ** 3)} H's), too large for the browser. Use K ≤ 3 and B ≤ 27.`, 'err'); }
    else if (chk.P.q === 6) setStatus(`Heavy: q = 6 gives n = 80, i.e. 512,000 H's (~620k residues). Takes a few seconds.`);
    else setStatus('');
    renderParams(chk.P, sizes);
    renderFormula(chk.P, sizes);
  }

  // ------------------------------------------------------------------ drag-and-drop packing board
  const BD = { sig: '', K: 0, B: 0, sizes: [], bins: [], active: new Set() };
  const bdLoad = (b) => BD.bins[b].reduce((a, u) => a + BD.sizes[u], 0);
  const bdBinOf = (u) => BD.bins.findIndex((l) => l.includes(u));
  const bdComplete = () => BD.sizes.length > 0 && BD.bins.flat().length === BD.sizes.length && BD.bins.every((_, b) => bdLoad(b) === BD.B);
  function resetBoardIfNew(K, B, sizes) {
    const ok = Number.isInteger(K) && K >= 1 && K <= 6 && Number.isInteger(B) && B >= 1 && B <= 64 && sizes.length <= 24 && sizes.every((x) => x > 0 && x <= B);
    const sig = ok ? `${K}|${B}|${sizes.join(',')}` : 'bad';
    if (sig === BD.sig) return;
    BD.sig = sig; BD.K = ok ? K : 0; BD.B = B; BD.sizes = ok ? sizes.slice() : []; BD.bins = Array.from({ length: BD.K }, () => []);
    BD.active = new Set();
    $('#rd-solveinfo').innerHTML = ok ? `Drag the items into the ${K} bins of size B = ${B} until every bin is exactly full, or press <b>Fold the string</b> and the solver packs them.` : '';
  }
  function renderBoard() {
    if (!BD.K) { $('#rd-tPool').innerHTML = '<span class="tempty">—</span>'; $('#rd-tBins').innerHTML = ''; $('#rd-packHint').textContent = ''; return; }
    const U = Math.max(9, Math.min(22, Math.floor(168 / BD.B)));
    const inBin = new Set(BD.bins.flat());
    const blk = (u) => `<div class="tblk${BD.active.has(u) ? ' active' : ''}" data-u="${u}" style="--c:${itemHex(u)};height:${Math.max(8, BD.sizes[u] * U - 3)}px"><span>u${u + 1}</span><b>${BD.sizes[u]}</b></div>`;
    $('#rd-tPool').innerHTML = BD.sizes.map((_, u) => (inBin.has(u) ? '' : blk(u))).join('') || '<span class="tempty">all items packed</span>';
    $('#rd-tBins').innerHTML = BD.bins.map((list, b) => {
      const ld = bdLoad(b);
      return `<div class="tcol"><div class="tbin" data-b="${b}" style="--u:${U}px;height:${BD.B * U + 5}px">${list.map(blk).join('')}</div>` +
        `<div class="tcap${ld === BD.B ? ' full' : ''}">bin ${b + 1} · ${ld}/${BD.B}</div></div>`;
    }).join('');
    $('#rd-packHint').textContent = bdComplete() ? '✓ packed' : '';
    $('#rd-packHint').style.color = 'var(--diff-1-ink)';
  }
  function boardChanged() {
    renderBoard();
    if (RES && RES.solvable && RES.K === BD.K) {
      const same = BD.sizes.every((_, u) => bdBinOf(u) === RES.assign[u]);
      if (!same) setStatus(bdComplete() ? 'Packing changed: press Fold the string to fold this packing.' : 'Packing changed. Finish it, or press Fold the string and the solver fills the bins.', 'err');
    } else if (bdComplete()) setStatus('Packed. Press Fold the string to fold S_B with this packing.', 'ok');
  }
  let drag = null;
  document.addEventListener('pointerdown', (e) => {
    const el = e.target.closest && e.target.closest('#rd-tetris .tblk');
    if (!el) return;
    e.preventDefault();
    const r = el.getBoundingClientRect();
    const ghost = el.cloneNode(true);
    ghost.classList.add('ghost'); ghost.classList.remove('active');
    ghost.style.left = r.left + 'px'; ghost.style.top = r.top + 'px'; ghost.style.height = r.height + 'px';
    document.body.appendChild(ghost);
    el.classList.add('dragging');
    drag = { u: +el.dataset.u, ghost, el, dx: e.clientX - r.left, dy: e.clientY - r.top };
  });
  function dropTarget(x, y) {
    for (const b of root.querySelectorAll('#rd-tBins .tbin')) {
      const r = b.getBoundingClientRect();
      if (x >= r.left - 8 && x <= r.right + 8 && y >= r.top - 40 && y <= r.bottom + 8) return { bin: +b.dataset.b };
    }
    const p = $('#rd-tPool').getBoundingClientRect();
    if (x >= p.left && x <= p.right && y >= p.top && y <= p.bottom) return { pool: true };
    return null;
  }
  document.addEventListener('pointermove', (e) => {
    if (!drag) return;
    drag.ghost.style.left = (e.clientX - drag.dx) + 'px';
    drag.ghost.style.top = (e.clientY - drag.dy) + 'px';
    const t = dropTarget(e.clientX, e.clientY);
    root.querySelectorAll('#rd-tBins .tbin').forEach((b) => b.classList.toggle('over', !!t && t.bin === +b.dataset.b));
    $('#rd-tPool').classList.toggle('over', !!t && !!t.pool);
  });
  document.addEventListener('pointerup', (e) => {
    if (!drag) return;
    const { u } = drag;
    const t = dropTarget(e.clientX, e.clientY);
    drag.ghost.remove(); drag.el.classList.remove('dragging');
    drag = null;
    $('#rd-tPool').classList.remove('over');
    const from = bdBinOf(u);
    if (t && t.bin !== undefined && t.bin !== from) {
      const free = BD.B - bdLoad(t.bin);
      if (free < BD.sizes[u]) {
        renderBoard();
        $('#rd-solveinfo').innerHTML = `<span style="color:var(--diff-3-ink)">u${u + 1} (size ${BD.sizes[u]}) does not fit: bin ${t.bin + 1} has only ${free} free.</span>`;
        const bel = root.querySelector(`#rd-tBins .tbin[data-b="${t.bin}"]`);
        if (bel) { bel.classList.add('bad'); setTimeout(() => bel.classList.remove('bad'), 350); }
        return;
      }
      if (from >= 0) BD.bins[from].splice(BD.bins[from].indexOf(u), 1);
      BD.bins[t.bin].push(u);
    } else if (t && t.pool && from >= 0) {
      BD.bins[from].splice(BD.bins[from].indexOf(u), 1);
    } else { renderBoard(); return; }
    $('#rd-solveinfo').innerHTML = bdComplete()
      ? `Packed by hand: ${BD.bins.map((l, b) => `bin ${b + 1} = {${l.map((x) => 'u' + (x + 1)).join(', ')}}`).join(', ')}.`
      : `${BD.bins.flat().length} of ${BD.sizes.length} items packed.`;
    boardChanged();
  });
  $('#rd-tReset').addEventListener('click', () => { BD.bins = BD.bins.map(() => []); $('#rd-solveinfo').textContent = 'Bins emptied.'; boardChanged(); });
  $('#rd-tSolve').addEventListener('click', () => {
    if (!BD.K) return;
    const sol = C.solveBinPacking(BD.sizes, BD.K, BD.B);
    if (!sol.assign) { $('#rd-solveinfo').innerHTML = `Exhaustive search (${fmt(sol.nodes)} nodes): <b>no packing exists</b>.`; return; }
    BD.bins = BD.bins.map(() => []);
    sol.assign.forEach((b, u) => BD.bins[b].push(u));
    $('#rd-solveinfo').innerHTML = `Backtracking found a packing (${fmt(sol.nodes)} search nodes).`;
    boardChanged();
  });

  function renderParams(P, sizes) {
    const t = $('#rd-params');
    if (!t) return; // the parameters card is not shown (kept for pages that want it)
    if (!P) { t.innerHTML = ''; return; }
    const { q, n, T, c, K, B } = P;
    const str = C.buildString(P, sizes);
    const N = str.types.length;
    const M = q + (q - K) + sizes.length;
    const rows = [
      ['q = 2·max(K, ⌈B<sup>1/3</sup>⌉)', q],
      ['n = q(2q+1) + 2', n],
      ['T = (2q−1)(n−2)  (bin size)', fmt(T)],
      ['c', c],
      ['|S<sub>B</sub>|  (residues)', fmt(N)],
      ['H residues = n³', fmt(n ** 3)],
      ['P residues', fmt(N - n ** 3)],
      ['linkers, each of cn+2 = ' + fmt(c * n + 2) + ' P\'s', M],
      ['most H–H pairs, 3n²(n−1)', fmt(3 * n * n * (n - 1))],
    ];
    t.innerHTML = rows.map(([a, b]) => `<tr><td>${a}</td><td>${b}</td></tr>`).join('');
  }

  // ------------------------------------------------------------------ formula
  function formulaParts(P, sizes, num) {
    const { q, n, T, c, K, B } = P; const m = n - 2;
    const e = (sym, val) => (num ? fmt(val) : sym);
    const parts = [
      ['edges', `(PHP)<sup>${e('9n−10', 9 * n - 10)}</sup>`],
      ['back', `(PHHP)<sup>${e('(n−2)²/2', m * m / 2)}</sup>`],
      ['bl', `(PHP)<sup>${e('n−2', m)}</sup>`],
      ['p4', 'P<sup>4</sup>'],
      ['faces', `((PHHP)<sup>${e('(n−2)²/2', m * m / 2)}</sup>P<sup>7</sup>)<sup>3</sup>`],
      ['top', `(PHHP)<sup>${e('(n−2)²/2−1', m * m / 2 - 1)}</sup>`],
      ['int', `PH<sup>${e('(n−2)³+2', m ** 3 + 2)}</sup>`],
      ['down', `P<sup>${e('8+q', 8 + q)}</sup>`],
      ['walls', `((PHP)<sup>${e('q', q)}</sup>(PHHP)<sup>${e('(n−2)/2', m / 2)}</sup>(PHP)<sup>${e('2q+1', 2 * q + 1)}</sup>P<sup>4</sup>(PHHP)<sup>${e('(n−2)/2', m / 2)}</sup>(PHP)<sup>${e('q', q)}</sup>P<sup>${e('2q', 2 * q)}</sup>)<sup>${e('q', q)}</sup>`],
      ['special', `PH(P<sup>${e('2q+6', 2 * q + 6)}</sup>H)<sup>${e('q−1', q - 1)}</sup>P`],
      ['fill', `(P<sup>${e('cn', c * n)}</sup>(PHHP)<sup>${e('(T−B)/2', (T - B) / 2)}</sup>)<sup>${e('q', q)}</sup>`],
      ['dummy', `(P<sup>${e('cn', c * n)}</sup>(PHHP)<sup>${e('B/2', B / 2)}</sup>)<sup>${e('q−K', q - K)}</sup>`],
    ];
    let items;
    if (num) items = sizes.map((s, u) => `<span class="f" data-f="item-${u}">(P<sup>${fmt(c * n)}</sup>(PHHP)<sup>${s / 2}</sup>)</span>`).join('');
    else items = '∏<sub>u∈U</sub>(P<sup>cn</sup>(PHHP)<sup>s(u)/2</sup>)';
    parts.push(['items', items]);
    return parts;
  }
  function renderFormula(P, sizes) {
    const el = $('#rd-formula');
    if (!P) { el.innerHTML = '<span style="color:#9aa0aa">—</span>'; return; }
    el.innerHTML = '<i>S</i><sub>B</sub> = ' + formulaParts(P, sizes, fmtNumeric).map(([k, h]) => `<span class="f" data-f="${k}">${h}</span>`).join(' ');
    if (V) markFormula();
  }
  $('#rd-fmtTog').addEventListener('click', () => {
    fmtNumeric = !fmtNumeric;
    $('#rd-fmtTog').textContent = fmtNumeric ? 'show symbols' : 'show numbers';
    if (RES && RES.P) renderFormula(RES.P, RES.sizes); else previewInstance();
  });
  function markFormula() {
    if (!V) return;
    const st = V.steps[cur.k];
    const on = new Set(st.factors || []);
    root.querySelectorAll('#rd-formula .f').forEach((el) => {
      const k = el.dataset.f;
      const r = V.factorRange[k];
      el.classList.toggle('on', on.has(k));
      el.classList.toggle('done', !on.has(k) && r && r[1] <= st.s && st.s > 0);
    });
  }

  // ------------------------------------------------------------------ build
  $('#rd-find').addEventListener('click', onFind);
  function onFind() {
    const { K, B, sizes } = readInstance();
    const chk = C.checkInstance(K, B, sizes);
    if (chk.errs.length) { setStatus(chk.errs[0], 'err'); return; }
    if (chk.P.q > 6) { setStatus(`q = ${chk.P.q} gives n = ${chk.P.n}: too large. Use K ≤ 3 and B ≤ 27.`, 'err'); return; }
    $('#rd-find').disabled = true;
    const given = bdComplete() ? BD.sizes.map((_, u) => bdBinOf(u)) : null;
    setStatus((given ? 'Building S_B and folding it with your packing' : 'Solving the bin packing, building S_B and its fold') + (chk.P.q === 6 ? '… (n = 80, a few seconds)' : '…'));
    setTimeout(() => {
      let res;
      try { res = C.build(K, B, sizes, given); } catch (err) { console.error(err); setStatus('Construction failed: ' + err.message, 'err'); $('#rd-find').disabled = false; return; }
      res.sizes = sizes; res.K = K; res.B = B;
      $('#rd-find').disabled = false;
      if (res.error) { setStatus(res.error, 'err'); return; }
      RES = res;
      renderParams(res.P, sizes);
      if (!res.solvable) {
        teardown();
        BD.active = new Set(); renderBoard();
        $('#rd-packHint').textContent = '(no solution)'; $('#rd-packHint').style.color = 'var(--diff-3-ink)';
        $('#rd-solveinfo').innerHTML = `Exhaustive search (${fmt(res.solverNodes)} nodes): <b>no packing exists</b>.`;
        setStatus('No packing exists, so by §3.2.4 S_B has no fold with its H\'s in a perfect cube.', 'err');
        $('#rd-placeholder').hidden = false;
        $('#rd-placeholder').innerHTML = `<div><b>No packing exists.</b><br>By §3.2.4, any fold of S<sub>B</sub> (${fmt(res.str.types.length)} residues, n = ${res.P.n}) whose H's formed a perfect ${res.P.n}³ cube would yield a packing.<br>So no fold of this string reaches 3n²(n−1) = ${fmt(3 * res.P.n ** 2 * (res.P.n - 1))} H–H pairs.</div>`;
        $('#rd-hud').hidden = true; $('#rd-dock').hidden = true; $('#rd-zoom').hidden = true;
        $('#rd-checks').innerHTML = '<div class="check"><small>No fold to verify.</small></div>';
        renderFormula(res.P, sizes);
        return;
      }
      // show the packing that is being folded on the board
      if (!res.given) { BD.bins = Array.from({ length: K }, () => []); res.assign.forEach((b, u) => BD.bins[b].push(u)); }
      BD.active = new Set(); renderBoard();
      const binsTxt = Array.from({ length: K }, (_, b) => `bin ${b + 1} = {${sizes.map((s, u) => (res.assign[u] === b ? 'u' + (u + 1) : null)).filter(Boolean).join(', ')}}`).join(', ');
      $('#rd-solveinfo').innerHTML = res.given ? `Folding your packing: ${binsTxt}.` : `The bins were not full, so backtracking packed them (${fmt(res.solverNodes)} search nodes): ${binsTxt}.`;
      setStatus(res.val.ok ? 'Folded and checked. Press → for the first step.' : 'The fold failed a check (see below).', res.val.ok ? 'ok' : 'err');
      renderChecks(res);
      setup(res);
      renderFormula(res.P, sizes);
      goStep(0, true);
    }, 40);
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

  const TAIL_VIS = 260, DYN_CAP = 4300, DIST_SCALE = 1.3;
  const FIXED_VIEW = { dir: [1.0, 0.72, 1.1], dist: 3.0, tgt: [0.1, -0.05, 0] };

  function setup(res) {
    teardown();
    const { P, fold } = res;
    const n = P.n, cc = (n - 1) / 2, N = fold.N;
    const { TY, CAT, SG, segs } = fold;
    const FP = new Float32Array(3 * N);
    for (let i = 0; i < N; i++) { FP[3 * i] = fold.X[i] - cc; FP[3 * i + 1] = fold.Y[i] - cc; FP[3 * i + 2] = -(fold.Z[i] - cc); }
    const intSeg = segs.find((s) => s.key === 'int');

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
    const stringRGB = fold.strings.map((s) => (s.kind === 'item' ? itemRGB(s.item) : catRGB(s.kind === 'filler' ? 11 : 12)));

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

    // dynamic (in flight + visible tail)
    const dynH = mk(geoH, new THREE.MeshLambertMaterial({ color: 0xffffff }), DYN_CAP);
    const dynP = mk(geoP, new THREE.MeshLambertMaterial({ color: 0xffffff }), DYN_CAP);
    for (const d of [dynH, dynP]) { d.instanceMatrix.setUsage(THREE.DynamicDrawUsage); d.instanceColor.setUsage(THREE.DynamicDrawUsage); }
    const dynBondGeo = new LineSegmentsGeometry();
    dynBondGeo.setPositions(new Float32Array((DYN_CAP + 4) * 6));
    dynBondGeo.attributes.instanceStart.data.setUsage(THREE.DynamicDrawUsage);
    dynBondGeo.instanceCount = 0;
    const dynBonds = new LineSegments2(dynBondGeo, bondMaterial()); dynBonds.frustumCulled = false;
    const tailGeo = new THREE.BufferGeometry();
    tailGeo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(6), 3).setUsage(THREE.DynamicDrawUsage));
    const tail = new THREE.Line(tailGeo, new THREE.LineBasicMaterial({ color: 0x8a919c, transparent: true, opacity: 0.45 }));
    tail.frustumCulled = false;

    // target cube wireframe
    const wire = new THREE.LineSegments(new THREE.EdgesGeometry(new THREE.BoxGeometry(n, n, n)),
      new THREE.LineBasicMaterial({ color: 0x4a5466, transparent: true, opacity: 0.55 }));

    // strip outlines and labels, drawn by buildStripOverlay() for the current stage
    const binGroup = new THREE.Group();

    const objects = [meshS, meshI, meshP, bonds, dynH, dynP, dynBonds, tail, wire, binGroup];
    objects.forEach((o) => scene.add(o));
    const clipMats = [matH, matP, bondMat, dynH.material, dynP.material, dynBonds.material, tail.material];

    // front face lookup for the mini-map
    const frontIdx = new Int32Array(n * n).fill(-1);
    for (let i = 0; i < N; i++) if (TY[i] && fold.Z[i] === 0) frontIdx[fold.X[i] + fold.Y[i] * n] = i;
    const hexOf = (i) => {
      if (CAT[i] === 13) return itemHex(segs[SG[i]].item);
      return catHex(CAT[i]);
    };

    V = {
      P, n, cc, N, FP, TY, CAT, SG, segs, fold, col, connOf, stringRGB, pIdx,
      cntS, cntI, cntP, meshS, meshI, meshP, bondGeo, bonds, dynH, dynP, dynBondGeo, dynBonds, tail, wire, binGroup,
      objects, clipMats, frontIdx, hexOf, contactPrefix: res.val.contactPrefix, target: res.val.target,
      lastFace: -1, lastStats: '', tint: null, matP, bondMat, intStart: intSeg.start, intEnd: intSeg.end,
    };
    V.steps = buildSteps(res);
    V.wallStep = V.steps.findIndex((s) => s.id === 'walls');
    paintAll();
    // factor ranges for the formula
    V.factorRange = {};
    for (const f of res.str.factors) V.factorRange[f.key] = [f.start, f.end];
    segs.forEach((s) => { if (s.key === 'item') V.factorRange['item-' + s.item] = [s.start, s.end]; });

    buildTimeline();
    setupFace();
    setupBar();
    $('#rd-placeholder').hidden = true; $('#rd-hud').hidden = false; $('#rd-dock').hidden = false; $('#rd-zoom').hidden = false;
    resize();
    controls.minDistance = 2; controls.maxDistance = 120 * n;
    camera.far = 400 * n; camera.near = Math.max(0.1, n / 200); camera.updateProjectionMatrix();
    camTween = null;
    // fixed default camera (the per-step camera flights are opt-in via View ▸ auto camera)
    const v0 = $('#rd-tgCam').checked ? V.steps[0].view : FIXED_VIEW;
    controls.target.set(...v0.tgt.map((x) => x * n));
    camera.position.copy(controls.target).add(new THREE.Vector3(...v0.dir).normalize().multiplyScalar(v0.dist * n * DIST_SCALE * fitScale));
  }

  function buildStripOverlay() {
    const g = V.binGroup, n = V.n, cc = V.cc, K = RES.K, st = ST();
    for (const ch of [...g.children]) {
      g.remove(ch);
      if (ch.geometry) ch.geometry.dispose();
      if (ch.material) { if (ch.material.map) ch.material.map.dispose(); ch.material.dispose(); }
    }
    V.fold.bins.forEach((bn, j) => {
      const x0 = 1 - cc - 0.5, x1 = n - 2 - cc + 0.5, y0 = bn.rb + 1 - cc - 0.5, y1 = bn.rt - 1 - cc + 0.5, z = cc + 0.55;
      const geo = new THREE.BufferGeometry().setFromPoints([
        new THREE.Vector3(x0, y0, z), new THREE.Vector3(x1, y0, z), new THREE.Vector3(x1, y1, z), new THREE.Vector3(x0, y1, z), new THREE.Vector3(x0, y0, z)]);
      g.add(new THREE.Line(geo, new THREE.LineBasicMaterial({ color: j < K ? st.strip : st.plugStrip, transparent: true, opacity: st.stripOp })));
      const items = bn.contents.filter((x) => x.kind === 'item').map((x) => `u${x.item + 1}`);
      const text = j < K ? `strip ${j + 1}: ${items.join(' + ')}` : `strip ${j + 1}: plug`;
      const spr = makeLabel(text, j < K ? st.ink : st.plugInk, n);
      spr.position.set(-cc - 1.5 - spr.userData.w / 2, (bn.rt + bn.rb) / 2 - cc, cc + 1);
      g.add(spr);
    });
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

  // ------------------------------------------------------------------ steps (the paper's structure)
  // The steps of §3.2.3, in the words of the proof board (glossary on the Original proof page);
  // `cards` link each step to its cards there (ids of src/content/proof-steps/bl/*.mdx).
  function buildSteps(res) {
    const { P, fold } = res;
    const { q, n, T, c, K, B } = P; const m = n - 2, cn = c * n;
    const segs = fold.segs, sizes = res.sizes, assign = res.assign;
    const N = fold.N;
    const byKey = (k) => segs.filter((s) => s.key === k);
    const span = (list) => ({ s: list[0].start, e: list[list.length - 1].end });
    const tailFront = [1, 0.3, -0.7];
    const steps = [];
    const G = ['the string', 'the frame', 'periods', 'strips', 'wrap-up'];
    const add = (o) => { o.groupName = G[o.group]; steps.push(o); };
    const M = fold.strings.length;
    const FRAME = [['frame', '10 Folding the frame']];

    add({ id: 'start', group: 0, s: 0, e: 0, dir: [1, 0, 0], factors: ['edges', 'back', 'bl', 'p4', 'faces', 'top', 'int', 'down', 'walls', 'special', 'fill', 'dummy', 'items'],
      view: { dir: [1.0, 0.45, 1.05], dist: 3.3, tgt: [0.75, 0.25, 0] },
      cards: [['string', '4 Spelling the string'], ['cube', '3 Why a cube']],
      tag: '§3.2.2 · Fig. 3', title: 'The string S_B, still unfolded',
      body: `<p>The instance on the left has K = ${K} bins of size B = ${B} and ${sizes.length} items of even size, adding up to BK = ${B * K}. Berger and Leighton turn it into the string <b>S<sub>B</sub></b> of Fig. 3, with</p>
        <p class="eq">q = 2·max(K, ⌈B<sup>1/3</sup>⌉) = ${q}, &nbsp; n = q(2q+1)+2 = ${n}, &nbsp; T = (2q−1)(n−2) = ${T}, &nbsp; c = 52.</p>
        <p>S<sub>B</sub> has ${fmt(N)} letters, exactly n³ = ${fmt(n ** 3)} of them H. A fold has the most H–H pairs, 3n²(n−1) = ${fmt(3 * n * n * (n - 1))}, exactly when its H's fill an ${n}×${n}×${n} cube (the wireframe), and such a perfect fold exists exactly when the items can be packed. Press <b>→</b> to fold S<sub>B</sub> one step at a time with the packing on the left; <b>←</b> goes back, and dragging along the bar below jumps to any letter of the string.</p>` });

    add({ id: 'edges', group: 1, ...span(byKey('edges')), dir: [0, 0, 1], factors: ['edges'], view: { dir: [1.0, 0.85, -0.85], dist: 2.6, tgt: [0, 0, 0] },
      cards: [...FRAME, ['local-rules', '5 The counts match']],
      tag: '§3.2.3 · Figs. 2, 4', title: `The corner rod: (PHP)^${9 * n - 10}`,
      body: `<p>Every H of a rod sits between two P's. In a perfect fold an H next to a P lies on the surface, and a lone H between two P's lies on an edge. Consecutive H's of the rod are neighbours, joined by a staple of two P's outside the cube that switches between the two outer sides of the edge (Fig. 2).</p>
        <p>The ${9 * n - 10} H's of the corner rod start at (n−2, n−1, n−1), run around the top face, down the back-right edge and around the bottom face, and end at (n−2, 0, n−1). They pass every corner and fill nine of the twelve edges. The three edges still empty share no corner.</p>` });
    add({ id: 'back', group: 1, ...span(byKey('back')), dir: [0, 0, 1], factors: ['back'], view: { dir: [0.45, 0.4, -1.2], dist: 2.5, tgt: [0, 0, 0] },
      cards: FRAME, tag: '§3.2.3 · Fig. 6', title: `Back face ribbon: (PHHP)^${fmt(m * m / 2)}`,
      body: `<p>In a ribbon every H has exactly one P beside it, so it lies on a face, and its H's come two at a time. The ${fmt(m * m / 2)} pairs snake through the ${m}×${m} inside of the back face column by column, with the P's turning just behind the face. Since n−2 = ${m} is even, the snake ends on the side where it started, at (1, 1, n−1).</p>` });
    add({ id: 'bl', group: 1, ...span(byKey('bl')), dir: [0, 0, 1], factors: ['bl'], view: { dir: [-1.0, 0.45, -0.95], dist: 2.5, tgt: [0, 0, 0] },
      cards: FRAME, tag: '§3.2.3', title: `The tenth-edge rod: (PHP)^${m}`,
      body: `<p>The tenth-edge rod fills the inside of the back-left edge, from (0, 1, n−1) up to (0, n−2, n−1); the corner rod has already filled its two corners. Its last P lands at (0, n−2, n).</p>` });
    add({ id: 'left', group: 1, s: byKey('p4')[0].start, e: byKey('p7a')[0].end, dir: [-1, 0, 0], factors: ['p4', 'faces'], view: { dir: [-1.3, 0.4, 0.3], dist: 2.5, tgt: [0, 0, 0] },
      cards: FRAME, tag: '§3.2.3 · Fig. 7', title: 'Left face ribbon: P⁴ (PHHP)^{(n−2)²/2} P⁷',
      body: `<p>P⁴ hops from (0, n−2, n) to (−2, n−2, n−2), so that the chain reaches the left face without meeting anything already placed. The face ribbon snakes from S<sub>L</sub> = (0, n−2, n−2) to F<sub>L</sub> = (0, 1, n−2). Then P⁷ goes around the bottom-left edge at distance at least 2 from the cube: seven P's, because the sites just outside the edge are taken by its staples.</p>` });
    add({ id: 'bottom', group: 1, s: byKey('bottom')[0].start, e: byKey('p7b')[0].end, dir: [0, -1, 0], factors: ['faces'], view: { dir: [0.4, -1.3, 0.55], dist: 2.5, tgt: [0, 0, 0] },
      cards: FRAME, tag: '§3.2.3 · Fig. 7', title: 'Bottom face ribbon: (PHHP)^{(n−2)²/2} P⁷',
      body: `<p>The bottom face ribbon snakes from S<sub>B</sub> = (1, 0, n−2) to F<sub>B</sub> = (n−2, 0, n−2), and P⁷ goes around the bottom-right edge.</p>` });
    add({ id: 'right', group: 1, s: byKey('right')[0].start, e: byKey('p7c')[0].end, dir: [1, 0, 0], factors: ['faces'], view: { dir: [1.3, 0.3, -0.3], dist: 2.5, tgt: [0, 0, 0] },
      cards: FRAME, tag: '§3.2.3 · Fig. 7', title: 'Right face ribbon: (PHHP)^{(n−2)²/2} P⁷',
      body: `<p>The right face ribbon snakes from S<sub>R</sub> = (n−1, 1, n−2) to F<sub>R</sub> = (n−1, n−2, n−2), and P⁷ goes around the top-right edge. This is the last of the three P⁷ in ((PHHP)<sup>(n−2)²/2</sup>P⁷)³.</p>` });
    add({ id: 'top', group: 1, ...span(byKey('top')), dir: [0, 1, 0], factors: ['top'], view: { dir: [0.35, 1.3, 0.5], dist: 2.5, tgt: [0, 0, 0] },
      cards: FRAME, tag: '§3.2.3 · Fig. 7', title: `Top face ribbon: (PHHP)^${fmt(m * m / 2 - 1)}, two H's short`,
      body: `<p>The top face ribbon runs from S<sub>T</sub> = (n−2, n−1, n−2) to F<sub>T</sub> = (n−4, n−1, 1). It has one pair fewer than the other face ribbons, so the nodes (n−3, n−1, 1) and (n−2, n−1, 1) stay free: the way into the inside and the way out.</p>` });
    add({ id: 'int', group: 1, ...span(byKey('int')), dir: [0, 1, 0], cut: true, factors: ['int'], view: { dir: [1, 0.9, 1], dist: 2.6, tgt: [0, 0, 0] },
      cards: FRAME, tag: '§3.2.3', title: `The core: P H^${fmt(m ** 3 + 2)}`,
      body: `<p>The core is one run of ${fmt(m ** 3 + 2)} H's. It enters through (n−3, n−1, 1) and fills the ${fmt(m ** 3)} inside nodes layer by layer, in a snake that turns back at every layer and leaves the column i = n−2, k = 1 free. It then climbs that column and leaves through (n−2, n−1, 1). A corner of the cube is cut away so that you can watch.</p>` });
    add({ id: 'down', group: 1, ...span(byKey('down')), dir: [1, 0, -0.6], factors: ['down'], view: { dir: [1.0, 0.65, 0.95], dist: 1.45, tgt: [0.36, 0.3, 0.4] },
      cards: [...FRAME, ['skeleton', '6 Two edges stay free']], tag: '§3.2.3', title: `To the front face: P^${8 + q}`,
      body: `<p>P<sup>8+q</sup> goes around the P's already placed to (n−1, n−1−q, −2) = (${n - 1}, ${n - 1 - q}, −2), just in front of the front-right edge. The frame is done: everything is filled except the n×(n−2) nodes of the front face (k = 0), with the two free edges at its sides.</p>` });

    add({ id: 'walls', group: 2, ...span(byKey('walls')), dir: [1, 0, -0.6], factors: ['walls'], view: { dir: [0.4, 0.12, 1.2], dist: 2.3, tgt: [0.02, 0, 0.2] },
      cards: [['build-walls', '11 Building the walls']], tag: '§3.2.3 · Fig. 8', title: `${q} periods: the walls`,
      body: `<p>Each of the q = ${q} periods is (PHP)<sup>q</sup>(PHHP)<sup>(n−2)/2</sup>(PHP)<sup>2q+1</sup>P⁴(PHHP)<sup>(n−2)/2</sup>(PHP)<sup>q</sup>P<sup>2q</sup> (the paper's bin wall): a short rod of q H's up the right free edge, a wall of n−2 H's straight across the face, a long rod of 2q+1 H's down the left free edge, four P's around the corner, a wall back, and another short rod. The P<sup>2q</sup> hop to the next period runs at distance 2 from the cube.</p>
        <p>The walls cut the front face into q = ${q} strips of (2q−1)(n−2) = T = ${T} nodes. Every period leaves one node of the right edge free, between its two short rods.</p>` });
    add({ id: 'special', group: 2, ...span(byKey('special')), dir: [1, 0, -0.6], factors: ['special'], view: { dir: [1.0, 0.12, 1.0], dist: 2.0, tgt: [0.38, 0, 0.3] },
      cards: [['build-walls', '11 Building the walls'], ['free-edges', '7 One length per edge']], tag: '§3.2.3 · Fig. 8', title: 'The spaced rod: PH(P^{2q+6}H)^{q−1}P',
      body: `<p>The spaced rod (the paper's special q-string) puts one lone H into the free node of every period, from bottom to top. The 2q+6 = ${2 * q + 6} P's between two of its H's run at distance 3 from the cube, around the staples of the short rods and the hops between periods. Its last P is at (n−1, n−2−q, −1). All 12n−16 = ${fmt(12 * n - 16)} lone H's of S<sub>B</sub> now fill the twelve edges.</p>` });

    const fill = byKey('filler'), dummy = byKey('dummy'), items = byKey('item');
    const STRIPS = [['fill-strips', '12 Filling the strips']];
    add({ id: 'fill', group: 3, ...span(fill), dir: tailFront, factors: ['fill'], tint: fill.map((s) => s.string), view: { dir: [0.32, 0.1, 1.2], dist: 2.4, tgt: [-0.04, -0.02, 0.2] },
      cards: STRIPS, tag: '§3.2.3', title: `Paddings: (P^{cn}(PHHP)^{(T−B)/2})^${q}`,
      body: `<p>The rest of S<sub>B</sub> is ribbons, each after a linker of exactly cn+2 = ${fmt(cn + 2)} P's. First every strip gets a padding of T−B = ${T - B} H's. Two paddings never fit into one strip, since 2(T−B) > T, so every strip keeps exactly B = ${B} free nodes. Inside a strip the ribbons follow a snake, and each starts on an even node.</p>
        <p>The linkers (highlighted) leave the face, drop to a plane of their own in front of the cube and fold their surplus into small boxes of P's under the cube, to use up their fixed length.</p>` });
    if (dummy.length) {
      add({ id: 'dummy', group: 3, ...span(dummy), dir: tailFront, factors: ['dummy'], tint: dummy.map((s) => s.string), view: { dir: [0.32, 0.1, 1.2], dist: 2.4, tgt: [-0.04, -0.02, 0.2] },
        cards: STRIPS, tag: '§3.2.3', title: `Plugs: (P^{cn}(PHHP)^{B/2})^${q - K}`,
        body: `<p>q − K = ${q - K} plug${q - K > 1 ? 's' : ''} of B = ${B} H's fill strip${q - K > 1 ? 's' : ''} ${K + 1}${q - K > 1 ? '–' + q : ''}. Exactly K = ${K} strips keep B free nodes, one for each bin of the instance.</p>` });
    }
    const binLoad = new Array(K).fill(0);
    items.forEach((sg) => {
      const u = sg.item, s = sizes[u], bn = assign[u];
      binLoad[bn] += s;
      const left = B - binLoad[bn];
      add({ id: 'item', item: u, group: 3, s: sg.start, e: sg.end, dir: tailFront, factors: ['items', 'item-' + u], tint: [sg.string], items: [u],
        view: { dir: [0.32, 0.1, 1.2], dist: 2.4, tgt: [-0.04, -0.02, 0.2] },
        cards: [...STRIPS, ['linkers', '14 Loops take up slack']], tag: '§3.2.3 · the product over u ∈ U', title: `Item u${u + 1} (size ${s}) into strip ${bn + 1}`,
        body: `<p>The item ribbon (PHHP)<sup>${s / 2}</sup> of u${u + 1} goes into strip ${bn + 1}, the strip of bin ${bn + 1} in the packing on the left. Its ${s} H's continue the snake there, and strip ${bn + 1} has ${left} free node${left === 1 ? '' : 's'} left. The ribbon starts on an even node and so ends on an odd one, which gives the next linker the right parity.</p>
          <p>Its linker (highlighted) has exactly cn+2 = ${fmt(cn + 2)} P's. It drops to its own plane at k = −${sg.depth}, is routed there around the other linkers, and folds its surplus into a small box of P's under the cube.</p>` });
    });
    add({ id: 'conn', group: 4, s: N, e: N, dir: tailFront, factors: ['fill', 'dummy', 'items'], tint: fold.strings.map((_, i) => i), tintAmt: 0.85, view: { dir: [1.2, -0.25, 1.0], dist: 3.2, tgt: [0, -0.35, 0.3] },
      cards: [['crossbar', '13 Untangling the linkers'], ['linkers', '14 Loops take up slack']], tag: '§3.2.3 · Lemmas 3.3–3.8', title: 'The linkers',
      body: `<p>Consecutive ribbons of S<sub>B</sub> can land in strips far apart, so each is joined to the next by a linker of exactly cn+2 = ${fmt(cn + 2)} P's through the space in front of the cube (coloured here by the ribbon each one leads to). The paper routes them through a switchboard of disjoint paths, which allows any order of the items, and loops each one away from the cube to use up its length. That is where c = 52 comes from.</p>
        <p class="note">With only ${M} linkers a simpler routing does the same job here: each linker drops straight to its own plane k = −D, is routed in that plane around the ends of the deeper ones, and folds its surplus into a small box of P's under the front of the cube (the paper loops it away from the cube instead). The parity works out because every ribbon starts on an even node and ends on an odd one.</p>` });
    const stripTxt = fold.bins.map((bn, j) => {
      if (j >= K) return `strip ${j + 1}: plug`;
      const its = bn.contents.filter((s) => s.kind === 'item').map((s) => `u${s.item + 1} (${sizes[s.item]})`);
      return `strip ${j + 1}: ${its.join(' + ')} = ${B}`;
    }).join(' · ');
    add({ id: 'read', group: 4, s: N, e: N, dir: tailFront, factors: [], items: sizes.map((_, u) => u), view: { dir: [0, 0, 1], dist: 2.5, tgt: [-0.1, 0, 0] },
      cards: [['packing', '9 Reading off a packing'], ['walls', '8 Walls run straight'], ['conclusion', '15 Folding is NP-complete']],
      tag: '§3.2.4', title: 'Reading off the packing',
      body: `<p>The converse holds for <i>every</i> perfect fold of S<sub>B</sub>, not only this one. The 12n−16 lone H's fill exactly the 12n−16 edge nodes, two edges stay free, the short and long rods fill those in one way only, and the walls run straight across the front face, cutting it into q strips of T nodes. Every ribbon lies inside one face or one strip, each strip takes one padding, and q−K strips take a plug. So the items fill the other K strips of B nodes <b>exactly</b>: a packing.</p>
        <p>The front face of this fold: ${stripTxt}.</p>` });

    // per-step timing
    steps.forEach((st, i) => {
      const len = st.e - st.s;
      st.W = clamp(Math.round(len * 0.18), 4, 3500);
      st.dur = len ? 1.15 + 0.8 * Math.log10(1 + len) : 1.5;
      st.dirPrev = i ? steps[i - 1].dir : st.dir;
    });
    return steps;
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
    return t.replace(/S_B/g, 'S<sub>B</sub>').replace(/\^\{([^}]*)\}/g, '<sup>$1</sup>').replace(/\^([0-9,]+)/g, '<sup>$1</sup>');
  }

  function stepUI() {
    const st = V.steps[cur.k];
    root.querySelectorAll('#rd-timeline .pill').forEach((p, i) => {
      p.classList.toggle('cur', i === cur.k);
      p.classList.toggle('done', i < cur.k);
    });
    $('#rd-stepTag').innerHTML = prettyTitle(`Step ${cur.k} of ${V.steps.length - 1} · ${st.tag}`);
    $('#rd-stepTitle').innerHTML = prettyTitle(st.title);
    $('#rd-stepBody').innerHTML = st.body + (st.cards ? `<p class="rd-cards">On the proof board: ${st.cards.map(([id, label]) => card(id, label)).join(' · ')}</p>` : '');
    $('#rd-stepinfo').scrollTop = 0;
    if (st.e > st.s) {
      let h = 0; for (let i = st.s; i < st.e; i++) h += V.TY[i];
      $('#rd-stepRes').textContent = `folds residues ${fmt(st.s + 1)}–${fmt(st.e)} of ${fmt(V.N)}  ·  ${fmt(h)} H, ${fmt(st.e - st.s - h)} P`;
    } else $('#rd-stepRes').textContent = st.id === 'start' ? `${fmt(V.N)} residues, nothing placed yet` : 'view of the finished fold';
    markFormula();
    BD.active = new Set(st.items || []); renderBoard();
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
    V.stringRGB = V.fold.strings.map((s) => (s.kind === 'item' ? itemRGB(s.item) : catRGB(s.kind === 'filler' ? 11 : 12)));
    V.tint = null;
    if (V.steps) applyTint(V.steps[Math.min(cur.k, V.steps.length - 1)]);
    const sc = pal(), st = ST();
    for (const m of [V.matP, V.dynP.material]) { m.transparent = sc.pOpacity < 1; m.opacity = sc.pOpacity; m.depthWrite = sc.pOpacity >= 1; m.needsUpdate = true; }
    for (const m of [V.bondMat, V.dynBonds.material]) { m.opacity = sc.bondOpacity; m.color.setHex(st.line); }
    V.tail.material.opacity = Math.min(0.5, sc.bondOpacity + 0.1); V.tail.material.color.setHex(st.line);
    V.wire.material.color.setHex(st.wire); V.wire.material.opacity = st.wireOp;
    buildStripOverlay();
    if (barPieces.length) drawBar(true);
    V.lastFace = -1;
    renderFaceLegend();
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
    renderBoard();
    renderLegend();
  }
  $('#rd-stageBtn').addEventListener('click', () => { stage = stage === 'day' ? 'night' : 'day'; stageChosen = true; applyStage(); });
  document.documentElement.addEventListener('themechange', (e) => {
    if (stageChosen) return;
    stage = e.detail === 'dark' ? 'night' : 'day';
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
    renderBoard();
    renderLegend();
  });

  function applyVisibility() {
    if (!V) return;
    const st = V.steps[cur.k];
    const showP = $('#rd-tgP').checked;
    V.meshP.visible = showP; V.dynP.visible = showP;
    const showB = $('#rd-tgBond').checked;
    V.bonds.visible = showB; V.dynBonds.visible = showB; V.tail.visible = true;
    V.binGroup.visible = $('#rd-tgLab').checked && cur.k >= V.wallStep && st.id !== 'walls';
    const cut = $('#rd-tgCut').checked;
    for (const m of V.clipMats) { m.clippingPlanes = cut ? cutPlanes : null; m.clipIntersection = true; m.needsUpdate = true; }
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
    if (!V || e.metaKey || e.ctrlKey || e.altKey) return;
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
    const hi = Math.min(N, Math.ceil(Math.max(f, s)) + TAIL_VIS, placed + DYN_CAP - 2);

    const mH = V.dynH.instanceMatrix.array, mP = V.dynP.instanceMatrix.array;
    const cH = V.dynH.instanceColor.array, cP = V.dynP.instanceColor.array;
    const bondBuf = V.dynBondGeo.attributes.instanceStart.data, bp = bondBuf.array;
    let nh = 0, np = 0, nb = 0;
    let px = 0, py = 0, pz = 0, havePrev = false;
    if (placed > 0) { px = FP[3 * (placed - 1)]; py = FP[3 * (placed - 1) + 1]; pz = FP[3 * (placed - 1) + 2]; havePrev = true; }
    for (let j = placed; j < hi; j++) {
      let x, y, z;
      if (j < e && j < f) {
        const p = smooth(Math.min(1, (f - j) / W));
        x = vA.x + (FP[3 * j] - vA.x) * p; y = vA.y + (FP[3 * j + 1] - vA.y) * p; z = vA.z + (FP[3 * j + 2] - vA.z) * p;
      } else {
        const o = j - g;
        x = vA.x + vD.x * o; y = vA.y + vD.y * o; z = vA.z + vD.z * o;
      }
      if (TY[j]) { setT(mH, nh, x, y, z); cH[3 * nh] = col[3 * j]; cH[3 * nh + 1] = col[3 * j + 1]; cH[3 * nh + 2] = col[3 * j + 2]; nh++; }
      else { setT(mP, np, x, y, z); cP[3 * np] = col[3 * j]; cP[3 * np + 1] = col[3 * j + 1]; cP[3 * np + 2] = col[3 * j + 2]; np++; }
      if (havePrev) { const o = 6 * nb; bp[o] = px; bp[o + 1] = py; bp[o + 2] = pz; bp[o + 3] = x; bp[o + 4] = y; bp[o + 5] = z; nb++; }
      px = x; py = y; pz = z; havePrev = true;
    }
    V.dynH.count = nh; V.dynP.count = np;
    const upload = (attr, count) => { attr.clearUpdateRanges(); attr.addUpdateRange(0, Math.max(1, count)); attr.needsUpdate = true; };
    upload(V.dynH.instanceMatrix, nh * 16); upload(V.dynP.instanceMatrix, np * 16);
    upload(V.dynH.instanceColor, nh * 3); upload(V.dynP.instanceColor, np * 3);
    bondBuf.clearUpdateRanges(); bondBuf.addUpdateRange(0, Math.max(1, nb * 6)); bondBuf.needsUpdate = true;
    V.dynBondGeo.instanceCount = nb;
    // the rest of the unfolded chain, as a line
    const tp = V.tail.geometry.attributes.position.array;
    if (hi < N) {
      const o1 = hi - 1 - g, o2 = Math.min(N - 1 - g, 60 * V.n);
      tp[0] = vA.x + vD.x * o1; tp[1] = vA.y + vD.y * o1; tp[2] = vA.z + vD.z * o1;
      tp[3] = vA.x + vD.x * o2; tp[4] = vA.y + vD.y * o2; tp[5] = vA.z + vD.z * o2;
    } else { for (let i = 0; i < 6; i++) tp[i] = 0; }
    V.tail.geometry.attributes.position.needsUpdate = true;
    V.tail.visible = hi < N;
  }

  // ------------------------------------------------------------------ mini-map of the front face
  let faceCtx = null, faceScale = 1;
  function setupFace() {
    const cv = $('#rd-face');
    if (!cv) return;
    faceScale = Math.max(2, Math.floor(228 / V.n));
    cv.width = cv.height = faceScale * V.n;
    faceCtx = cv.getContext('2d');
    renderFaceLegend();
    V.lastFace = -1;
  }
  function renderFaceLegend() {
    if (!V || !RES || !RES.assign || !$('#rd-faceLegend')) return;
    const its = RES.sizes.map((s, u) => `<div><i style="background:${itemHex(u)}"></i>u${u + 1} (${s}) → strip ${RES.assign[u] + 1}</div>`).join('');
    $('#rd-faceLegend').innerHTML = `${its}<div><i style="background:${catHex(11)}"></i>padding (T−B = ${RES.P.T - RES.P.B})</div>` +
      (RES.P.q > RES.K ? `<div><i style="background:${catHex(12)}"></i>plug (strip of no bin)</div>` : '') +
      `<div><i style="background:${catHex(9)}"></i>periods &nbsp;<i style="background:${catHex(10)}"></i>spaced rod</div>`;
  }
  function drawFace() {
    if (!faceCtx) return;
    const placed = V.placed;
    if (placed === V.lastFace) return;
    V.lastFace = placed;
    const n = V.n, s = faceScale, ctx = faceCtx;
    const st = ST();
    ctx.fillStyle = st.map; ctx.fillRect(0, 0, n * s, n * s);
    const gap = s >= 4 ? 1 : 0;
    for (let y = 0; y < n; y++) for (let x = 0; x < n; x++) {
      const i = V.frontIdx[x + y * n];
      ctx.fillStyle = i >= 0 && i < placed ? V.hexOf(i) : st.mapEmpty;
      ctx.fillRect(x * s, (n - 1 - y) * s, s - gap, s - gap);
    }
    if (cur.k >= V.wallStep) {
      ctx.lineWidth = 1;
      V.fold.bins.forEach((bn, j) => {
        ctx.strokeStyle = j < RES.K ? st.mapLine : st.mapPlug;
        const x0 = 1 * s - 0.5, y0 = (n - 1 - (bn.rt - 1)) * s - 0.5;
        ctx.strokeRect(x0, y0, (n - 2) * s, (bn.rt - bn.rb - 1) * s);
      });
    }
  }

  // ------------------------------------------------------------------ the string bar
  // The whole of S_B from left to right: H pieces full height in their colours, runs of P's as a
  // thin grey line, the part not folded yet faded. The arrow marks how far the fold has got;
  // dragging along the bar folds or unfolds to any residue.
  const bar = $('#rd-bar'), barCv = $('#rd-barCv'), marker = $('#rd-marker'), barTip = $('#rd-barTip');
  let barPieces = [], barW = 0, barH = 0, barShown = -1, barDrag = false;
  const PIECE_NAMES = {
    edges: 'corner rod', back: 'back face ribbon', bl: 'tenth-edge rod', p4: 'P-hop', left: 'left face ribbon', p7a: 'P-hop',
    bottom: 'bottom face ribbon', p7b: 'P-hop', right: 'right face ribbon', p7c: 'P-hop', top: 'top face ribbon', int: 'core',
    down: 'P-hop to the front face', walls: 'periods: walls and rods', special: 'spaced rod',
  };
  function setupBar() {
    barPieces = [];
    for (const sg of V.segs) {
      if (sg.key === 'filler' || sg.key === 'dummy' || sg.key === 'item') {
        const str = V.fold.strings[sg.string];
        const name = sg.key === 'filler' ? 'padding' : sg.key === 'dummy' ? 'plug' : `item u${sg.item + 1}`;
        barPieces.push({ s: sg.start, e: str.connEnd, kind: 'P', label: `linker before the ${name}` });
        barPieces.push({ s: str.connEnd, e: sg.end, kind: sg.key, item: sg.item, label: `${name}, into strip ${sg.bin + 1}`, min: true });
      } else barPieces.push({ s: sg.start, e: sg.end, cat: sg.cat, kind: sg.cat === 0 ? 'P' : 'H', label: PIECE_NAMES[sg.key] || sg.label, min: sg.key === 'special' });
    }
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
        drawFace();
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
  applyStage();
  loadPreset(0);
}
