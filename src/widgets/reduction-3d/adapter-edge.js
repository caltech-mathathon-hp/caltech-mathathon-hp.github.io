/**
 * The short version of the one-edge construction (edge-construction.js) for the 3D viewer (reduction.client.js): the presets, the
 * formula of S, the steps of Section 5 (Table 1) with their texts, the bin labels on the shelf edge
 * and the pieces of the string bar. adapter-bl.js does the same for Berger and Leighton.
 *
 * Coordinates in the texts are the paper's: the cube is {0..N}³ with N = n − 1, y points up and z
 * away from the viewer, so z = 0 is the front face and the shelf E* = {(x, 0, 0)} its bottom edge.
 */
import * as THREE from 'three';
import * as C from './edge-construction.js';

// K is the number of bins m (the viewer's name for it)
const PRESETS = [
  { name: 'm = 2, B = 2, items {1, 1, 2}', K: 2, B: 2, sizes: [1, 1, 2] },
  { name: 'm = 1, B = 2, items {1, 1} (n = 16, tiny)', K: 1, B: 2, sizes: [1, 1] },
  { name: 'm = 2, B = 1, items {1, 1} (n = 24)', K: 2, B: 1, sizes: [1, 1] },
  { name: 'm = 3, B = 2, items {1, 2, 1, 2}', K: 3, B: 2, sizes: [1, 2, 1, 2] },
  { name: 'm = 2, B = 3, items {2, 1, 1, 2} (n = 60)', K: 2, B: 3, sizes: [2, 1, 1, 2] },
  { name: 'unsolvable: m = 2, B = 3, items {2, 2, 2}', K: 2, B: 3, sizes: [2, 2, 2] },
  { name: 'm = 3, B = 3, items {1, 2, 1, 2, 3} (n = 60)', K: 3, B: 3, sizes: [1, 2, 1, 2, 3] },
];

const sub = (s) => `<sub>${s}</sub>`;
const sup = (s) => `<sup>${s}</sup>`;
const D = (r) => `D${sub(r)}`;

function formulaParts(P, sizes, num, { fmt }) {
  const { n, N0, lambda, m, B, nz } = P;
  const e = (sym, val) => (num ? fmt(val) : sym);
  const parts = [
    ['core', `H${sup(e('N₀', N0))}`],
    ['pp', 'PP'],
    ['A', D(e('9n−10', 9 * n - 10))],
    ['link0', `P${sup(e('λ', lambda))}`],
    ['F1', D(e('n−2', n - 2))],
    ['teth1', `P${sup(e('n', n))}`],
    ['seps', `H(P${sup(e('B+6', B + 6))}H)${sup(e('m', m))}`],
    ['teth2', `P${sup(e('n', n))}`],
    ['F2', D(e('n−2', n - 2))],
  ];
  if (num) parts.push(['items', nz.a.map((a, i) => `<span class="f" data-f="item-${i}">P${sup(fmt(lambda))}${D(a)}</span>`).join(' ') + ' P']);
  else parts.push(['items', `P${sup('λ')}${D(`a${sub(1)}`)} ⋯ P${sup('λ')}${D(`a${sub('k')}`)} P`]);
  parts.push(['def', `<br><small>D${sub('r')} = H(PPH)${sup('r−1')}` + (num ? '' : `, N₀ = n³−12n+16, λ = 4n+2k`) + '</small>']);
  return parts;
}

function buildSteps(res, { fmt }) {
  const { P, fold, sizes, assign } = res;
  const { n, N, N0, lambda, k, m, B, nz } = P;
  const segs = fold.segs, len = fold.N;
  const one = (key) => segs.find((s) => s.key === key);
  const span = (...keys) => ({ s: one(keys[0]).start, e: one(keys[keys.length - 1]).end });
  const steps = [];
  const G = ['the string', 'the skeleton', 'the shelf', 'the items', 'wrap-up'];
  const add = (o) => { o.groupName = G[o.group]; steps.push(o); };
  const shelfView = { dir: [0.3, 0.12, 1.2], dist: 1.9, tgt: [0, -0.36, 0.3] };
  const underView = { dir: [0.9, -1.0, 0.9], dist: 2.9, tgt: [0, -0.45, 0] };
  const tailDown = [0, -1, -0.6];
  const m0 = res.K, B0 = res.B;
  const itemsTxt = sizes.join(', ');
  const scaled = nz.a.map((a, i) => (nz.itemOf[i] < 0 ? `<b>${a}</b>` : a)).join(', ');

  add({ id: 'start', group: 0, s: 0, e: 0, dir: [-1, 0, 0], factors: ['core', 'pp', 'A', 'link0', 'F1', 'teth1', 'seps', 'teth2', 'F2', 'items'],
    view: { dir: [-1.0, 0.45, 1.05], dist: 3.3, tgt: [-0.75, 0.25, 0] },
    tag: '', title: 'The string S, still unfolded',
    body: `<p>The instance on the left asks whether the items ${itemsTxt} fill ${m0} bin${m0 > 1 ? 's' : ''} of size ${B0} exactly. The construction first multiplies B and every size by 6${nz.added ? `, and since m is even it adds one item of size B (in bold) and a bin for it, so that m becomes odd` : ''}: m = ${m}, B = ${B}, and the k = ${k} items have sizes ${scaled}. Then n = m(B+1)+3 = ${n}, and</p>
      <p class="eq">S = H${sup('N₀')} PP ${D('9n−10')} P${sup('λ')} ${D('n−2')} P${sup('n')} H(P${sup('B+6')}H)${sup('m')} P${sup('n')} ${D('n−2')} P${sup('λ')}${D(`a${sub(1)}`)} ⋯ P${sup('λ')}${D(`a${sub('k')}`)} P</p>
      <p>with the dense runs D${sub('r')} = H(PPH)${sup('r−1')}, N₀ = n³−12n+16 = ${fmt(N0)} and λ = 4n+2k = ${lambda}. S has ${fmt(len)} letters, exactly n³ = ${fmt(n ** 3)} of them H. A fold is perfect when its H's fill an ${n}×${n}×${n} cube (the wireframe), and S has a perfect fold exactly when the items can be packed. Press <b>→</b> to fold S one step at a time with the packing on the left; <b>←</b> goes back, and dragging along the bar below jumps to any letter.</p>` });

  add({ id: 'core', group: 1, ...span('core'), dir: [-1, 0, 0], cut: true, factors: ['core'], view: { dir: [1, 0.9, 1], dist: 2.6, tgt: [0, 0, 0] },
    tag: '', title: 'The core: H^{N₀}',
    body: `<p>The core is one run of N₀ = ${fmt(N0)} H's. It fills the whole cube except its <b>skeleton</b>, the 12n−16 = ${fmt(12 * n - 16)} nodes on the twelve edges, layer by layer: the bottom layer along a cycle through the inside of the bottom face, every middle layer along a cycle through the layer without its four corners, and the top layer like the bottom one. Each layer is left where the next one is entered. A corner of the cube is cut away so that you can watch.</p>
      <p>The H's of the core have H's next to them in the string, so on their own they could lie anywhere in the cube. The rest of S is what pins everything down.</p>` });

  add({ id: 'A', group: 1, ...span('pp', 'A'), dir: [0, 1, 0], factors: ['pp', 'A'], view: { dir: [1.0, 0.8, 0.9], dist: 2.6, tgt: [0, 0, 0] },
    tag: '', title: 'The run A = D_{9n−10} on nine edges',
    body: `<p>In a dense run D${sub('r')} = H(PPH)${sup('r−1')} every H has P's on both sides in the string. Those two P's lie outside the cube, so in a perfect fold the H has two open sides: it lies on an edge or at a corner. Consecutive H's of the run are neighbours, joined by a staple of two P's outside the cube, and the staples alternate between the two open sides of the edge.</p>
      <p>PP leaves the cube at the top. A starts at (0, N, N−1) and runs through all eight corners, (0, N, 0), (0, 0, 0), (0, 0, N), (0, N, N), (N, N, N), (N, 0, N), (N, 0, 0), (N, N, 0), to (N, N, N−1): 9n−10 = ${fmt(9 * n - 10)} H's on nine of the twelve edges. The three edges left free share no corner: the top front edge E₁, the bottom back edge E₂, and the bottom front edge E*, the <b>shelf</b> that will carry the instance.</p>` });

  add({ id: 'link0', group: 1, ...span('link0'), dir: [1, 0, 0], factors: ['link0'], tint: [0], view: { dir: [1.3, -0.35, 0.7], dist: 2.8, tgt: [0.1, -0.2, 0] },
    tag: '', title: 'A linker: P^{λ}',
    body: `<p>A <b>linker</b> of λ = 4n+2k = ${lambda} P's (highlighted) takes the chain from the end of A to the start of F₁. It steps out to (N+2, N, N−1), goes straight down the right side to a level of its own, y = −2, runs there, and comes back up in front of the front face to (N−1, N, −3).</p>
      <p>λ is more than any such route needs. Our write-up uses up the surplus with a loop in front of the cube; here it is folded into a flat meander under the cube, which leaves the shelf in view.</p>` });

  add({ id: 'F1', group: 1, ...span('F1'), dir: [0, 1, 0], factors: ['F1'], view: { dir: [0.4, 0.7, 1.2], dist: 2.4, tgt: [0, 0.2, 0] },
    tag: '', title: 'F₁ = D_{n−2} on the top front edge',
    body: `<p>The run F₁ fills the inside of E₁, from (N−1, N, 0) to (1, N, 0), with its staples alternating between above the edge and in front of it.</p>` });

  add({ id: 'teth1', group: 2, ...span('teth1'), dir: [0, 0, -1], factors: ['teth1'], view: { dir: [0.35, 0.2, 1.2], dist: 2.4, tgt: [0, 0, 0] },
    tag: '', title: 'An end tether: P^{n} down the front face',
    body: `<p>The tether P${sup('n')} joins the last H of F₁ to the first separator σ₁ on the shelf. It is only just long enough. F₁ lies on the top edge of the front face, the shelf is its bottom edge n−1 rows lower, and n P's outside the cube make n+1 steps: one out, n−1 down, one back in. So the tether hangs straight down (it is <b>taut</b>), and σ₁ sits right below the end of F₁, at x = 1, one end of the shelf.</p>` });

  const sepSeg = one('seps');
  add({ id: 'seps', group: 2, s: sepSeg.start, e: sepSeg.end, dir: [0, -0.6, -1], factors: ['seps'], view: shelfView,
    tag: '', title: 'Separators and bins: H(P^{B+6}H)^{m}',
    body: `<p>The m+1 = ${m + 1} lone H's σ₁, …, σ${sub('m+1')} are the <b>separators</b>. They sit on the shelf at x${sub('j')} = 1 + (j−1)(B+1) = ${fold.xs.join(', ')}, and between two of them lie B = ${B} free nodes: a <b>bin</b>. The inner tether P${sup('B+6')} from one separator to the next runs below the shelf and in front of it.</p>
      <p>Why B+6? A tether of B+6 P's makes B+7 steps, so two consecutive separators are at most B+5 apart along the edge, in every perfect fold, and the gap between them holds at most B+4 nodes. The items that fill a gap have sizes divisible by 6, so the gap is a multiple of 6, hence at most B. The two end tethers pin σ₁ and σ${sub('m+1')} to the ends of the shelf, so the m gaps hold mB = ${fmt(m * B)} nodes in all, and every gap is exactly B.</p>` });

  add({ id: 'teth2', group: 2, ...span('teth2'), dir: [0, -1, 0], factors: ['teth2'], view: { dir: [1.0, -0.8, 0.5], dist: 2.6, tgt: [0, -0.2, 0] },
    tag: '', title: 'The other end tether: P^{n} under the bottom face',
    body: `<p>The second end tether, again only just long enough, runs from σ${sub('m+1')} at (N−1, 0, 0) straight back under the bottom face to the bottom back edge. It pins σ${sub('m+1')} to the other end of the shelf.</p>` });

  add({ id: 'F2', group: 2, ...span('F2'), dir: [0, -1, 0.4], factors: ['F2'], view: { dir: [0.7, -0.6, -1.1], dist: 2.5, tgt: [0, -0.2, 0] },
    tag: '', title: 'F₂ = D_{n−2} on the bottom back edge',
    body: `<p>The run F₂ fills the inside of E₂, from (N−1, 0, N) to (1, 0, N). Now every node of the cube is filled except the bins on the shelf, mB = ${fmt(m * B)} nodes, and the rest of S is the k = ${k} items, each a dense run after a linker, with mB lone H's in all.</p>` });

  const load = new Array(m).fill(0);
  let first = true;
  segs.filter((s) => s.key === 'item').forEach((sg) => {
    const u = sg.item, j = sg.bin, a = sg.size, added = sg.added;
    load[j] += a;
    const left = B - load[j];
    const name = added ? 'the added item' : `item u${u + 1}`;
    const into = added
      ? `<p>m was even, so the construction added an item of size B = ${B}. It fills bin ${j + 1}, the bin added with it, on its own.</p>`
      : `<p>Then D${sub(a)} lays item u${u + 1} (size ${sizes[u]}, times 6: ${a}) into bin ${j + 1}, the bin of u${u + 1} in the packing on the left. ${left ? `Bin ${j + 1} has ${left} free node${left === 1 ? '' : 's'} left.` : `Bin ${j + 1} is now full.`}</p>`;
    add({ id: 'item', group: 3, s: sg.start, e: sg.end, dir: tailDown, factors: ['items', sg.fkey], tint: [sg.string], items: added ? [] : [u], view: shelfView,
      tag: '', title: added ? `The added item (size ${a}) into bin ${j + 1}` : `Item u${u + 1} (size ${a}) into bin ${j + 1}`,
      body: `<p>The linker P${sup('λ')} before ${name} (highlighted) starts just below the end of the previous run, goes straight down to its own level y = ${sg.level}, runs there under the cube and comes back up below the first node of the item.</p>${into}` +
        (first ? `<p>Inside a bin the items follow each other from one end, in odd bins from the right and in even bins from the left. So every item starts on an odd column and ends on an even one, which gives every linker the parity that λ needs.</p>` : '') });
    first = false;
  });

  add({ id: 'linkers', group: 4, s: len, e: len, dir: tailDown, factors: ['link0', 'items'], tint: fold.strings.map((_, i) => i), tintAmt: 0.85, view: underView,
    tag: '', title: 'The linkers',
    body: `<p>All k+1 = ${k + 1} linkers at once, each coloured like the run it leads to. Each has a level of its own below the cube: it goes straight down, runs on its level and comes straight back up, so no two of them meet, whatever the order of the items. λ = 4n+2k is long enough for every route, and since the items start on odd and end on even columns the parity works out.</p>
      <p class="note">Our write-up uses up the surplus of each linker with a rectangle in front of the cube on its level; here it is a flat meander under the cube on the same level. Turn the cube to look at it from below.</p>` });

  const binTxt = fold.bins.map((bn) => {
    const its = bn.contents.map((i) => (nz.itemOf[i] < 0 ? `the added item (${nz.a[i]})` : `u${nz.itemOf[i] + 1} (${nz.a[i]})`));
    return `bin ${bn.j}: ${its.join(' + ')} = ${B}`;
  }).join(' · ');
  add({ id: 'read', group: 4, s: len, e: len, dir: tailDown, factors: [], items: sizes.map((_, u) => u), view: shelfView,
    tag: '', title: 'Reading off the packing',
    body: `<p>The converse holds for <i>every</i> perfect fold of S, not only this one. S has exactly 12n−16 lone H's, as many as the skeleton has nodes, and each of them lies on an edge, so they fill the skeleton and the core fills the rest. A, the longest run, needs nine edges through all eight corners, which leaves three free edges with no corner in common; F₁ and F₂ take two of them and the separators and the items the third, the shelf. The end tethers are taut and pin σ₁ and σ${sub('m+1')} to the ends of the shelf, the inner tethers keep every gap at most B+4, and since all sizes are multiples of 6 every gap is exactly B. The items between two separators fill one bin exactly: a packing.</p>
      <p>The shelf of this fold (sizes times 6): ${binTxt}.</p>` });
  return steps;
}

// a bracket in front of every bin on the shelf, with its contents below it
function buildOverlay(V, res, { ST, makeLabel }) {
  const out = [], n = V.n, cc = V.cc, st = ST(), nz = res.P.nz;
  const yTop = -cc + 0.55, yBot = -cc - 1.55, z = cc + 3.4;
  V.fold.bins.forEach((bn) => {
    const added = bn.contents.some((i) => nz.itemOf[i] < 0);
    const x0 = bn.x0 - cc - 0.45, x1 = bn.x1 - cc + 0.45;
    const geo = new THREE.BufferGeometry().setFromPoints([
      new THREE.Vector3(x0, yTop, z), new THREE.Vector3(x0, yBot, z), new THREE.Vector3(x1, yBot, z), new THREE.Vector3(x1, yTop, z)]);
    out.push(new THREE.Line(geo, new THREE.LineBasicMaterial({ color: added ? st.plugStrip : st.strip, transparent: true, opacity: st.stripOp })));
    const its = bn.contents.map((i) => (nz.itemOf[i] < 0 ? 'added item' : `u${nz.itemOf[i] + 1}`));
    const spr = makeLabel(`bin ${bn.j}: ${its.join(' + ')}`, added ? st.plugInk : st.ink, n);
    spr.position.set((x0 + x1) / 2, yBot - 1.2 - 0.03 * n, z);
    out.push(spr);
  });
  return out;
}

const PIECE_NAMES = {
  core: 'the core', pp: 'PP', A: 'the run A, on nine edges', link0: 'linker to F₁', F1: 'F₁, on the top front edge',
  teth1: 'end tether down the front face', teth2: 'end tether under the bottom face', F2: 'F₂, on the bottom back edge',
};
function barPieces(V) {
  const out = [], { segs, fold, TY } = V;
  for (const sg of segs) {
    if (sg.key === 'seps') {
      // separators as ticks, the inner tethers between them as runs of P's
      let j = 0;
      for (let i = sg.start; i < sg.end;) {
        if (TY[i]) { j++; out.push({ s: i, e: i + 1, kind: 'H', cat: 9, label: `separator σ${j}`, min: true }); i++; continue; }
        let e = i; while (e < sg.end && !TY[e]) e++;
        out.push({ s: i, e, kind: 'P', label: `inner tether from σ${j} to σ${j + 1}` });
        i = e;
      }
    } else if (sg.key === 'item') {
      const ce = fold.strings[sg.string].connEnd;
      const name = sg.added ? 'the added item' : `item u${sg.item + 1}`;
      out.push({ s: sg.start, e: ce, kind: 'P', label: `linker to ${name}` });
      out.push({ s: ce, e: sg.end, kind: 'item', item: sg.item, label: `${name}, into bin ${sg.bin + 1}`, min: true });
    } else out.push({ s: sg.start, e: sg.end, cat: sg.cat, kind: sg.cat === 0 ? 'P' : 'H', label: PIECE_NAMES[sg.key] || sg.label, min: true });
  }
  return out;
}

export default {
  id: 'edge',
  C,
  PRESETS,
  lhs: '<i>S</i> = ',
  strPlain: 'S',
  interiorKey: 'core',
  // the default camera: the front face and the shelf at its bottom, from the right and a little above
  fixedView: { dir: [0.5, 0.16, 1.1], dist: 2.7, tgt: [0.02, -0.1, 0.05] },
  sizeCheck(P, { fmt }) {
    if (P.n > 80) return { msg: `After scaling, n = m(B+1)+3 = ${P.n} (${fmt(P.n ** 3)} H's): too large for the browser. Use m ≤ 3 and B ≤ 4, or m ≤ 5 and B ≤ 2.`, cls: 'err', block: true };
    if (P.n >= 60) return { msg: `Heavy: n = ${P.n}, i.e. ${fmt(P.n ** 3)} H's. Takes a few seconds.`, cls: '' };
    return { msg: '', cls: '' };
  },
  formulaParts,
  buildSteps,
  overlayFrom: (steps) => steps.findIndex((s) => s.id === 'seps') + 1,
  buildOverlay,
  barPieces,
  refs: () => '',
  noFold: (res, { fmt }) => ({
    status: 'No packing exists, so S has no perfect fold.',
    html: `<div><b>No packing exists.</b><br>A perfect fold of S (${fmt(res.str.types.length)} letters, n = ${res.P.n}) would give a packing.<br>So the H's of S cannot fill an ${res.P.n}³ cube, and no fold reaches 3n²(n−1) = ${fmt(3 * res.P.n ** 2 * (res.P.n - 1))} H–H pairs.</div>`,
  }),
};
