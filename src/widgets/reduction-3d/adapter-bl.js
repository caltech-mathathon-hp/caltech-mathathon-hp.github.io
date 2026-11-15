/**
 * Berger and Leighton's construction (construction.js) for the 3D viewer (reduction.client.js):
 * the presets, the formula of S_B, the steps of §3.2.3 with their texts and proof-board cards, the
 * strip labels on the front face and the pieces of the string bar. adapter-edge.js does the same
 * for the short version of the one-edge construction.
 */
import * as THREE from 'three';
import * as C from './construction.js';

const PRESETS = [
  { name: 'K = 2, B = 4, U = {2, 4, 2}', K: 2, B: 4, sizes: [2, 4, 2] },
  { name: 'K = 2, B = 3, U = {1, 2, 2, 1} (odd, so doubled)', K: 2, B: 3, sizes: [1, 2, 2, 1] },
  { name: 'K = 2, B = 4, U = {1, 3, 2, 2} (odd, so doubled)', K: 2, B: 4, sizes: [1, 3, 2, 2] },
  { name: 'K = 2, B = 8, U = {4, 2, 6, 2, 2}', K: 2, B: 8, sizes: [4, 2, 6, 2, 2] },
  { name: 'K = 2, B = 8, U = {2, 4, 2, 2, 4, 2}', K: 2, B: 8, sizes: [2, 4, 2, 2, 4, 2] },
  { name: 'K = 2, B = 6, U = {2, 2, 4, 2, 2}', K: 2, B: 6, sizes: [2, 2, 4, 2, 2] },
  { name: 'unsolvable: K = 2, B = 8, U = {6, 6, 4}', K: 2, B: 8, sizes: [6, 6, 4] },
  { name: 'the running example: K = 2, B = 10, U = {6, 2, 8, 4} (n = 80, heavy)', K: 2, B: 10, sizes: [6, 2, 8, 4] },
  { name: 'K = 3, B = 12, U = {6, 4, 4, 4, 2, 2, 8, 6} (n = 80, heavy)', K: 3, B: 12, sizes: [6, 4, 4, 4, 2, 2, 8, 6] },
];

function formulaParts(P, sizes, num, { fmt }) {
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
  if (num) items = (P.sizes || sizes).map((s, u) => `<span class="f" data-f="item-${u}">(P<sup>${fmt(c * n)}</sup>(PHHP)<sup>${s / 2}</sup>)</span>`).join('');
  else items = '∏<sub>u∈U</sub>(P<sup>cn</sup>(PHHP)<sup>s(u)/2</sup>)';
  parts.push(['items', items]);
  return parts;
}

// The steps of §3.2.3, in the words of the proof board (glossary on the Original proof page);
// `cards` link each step to its cards there (ids of src/content/proof-steps/bl/*.mdx).
// The steps of §3.2.3, in the words of the proof board (glossary on the Original proof page);
// `cards` link each step to its cards there (ids of src/content/proof-steps/bl/*.mdx).
function buildSteps(res, { fmt }) {
  const { P, fold } = res;
  const { q, n, T, c, K, B } = P; const m = n - 2, cn = c * n;
  // sizes and B are those of the string (doubled if the instance had an odd number, see
  // construction.js normalise); res.sizes and P.origB are the ones entered
  const segs = fold.segs, sizes = P.sizes, assign = res.assign;
  const doubled = P.f === 2;
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
    body: (doubled
      ? `<p>The instance on the left has K = ${K} bins of size ${P.origB} and the items ${res.sizes.join(', ')}. The ribbons of the string hold their H's two at a time, so the construction needs even sizes, and here some are odd. Doubling every size and the bin size changes nothing about which items fit together, so we work with B = ${B} and the items ${sizes.join(', ')}, adding up to BK = ${B * K}. Berger and Leighton turn this into the string <b>S<sub>B</sub></b> of Fig. 3, with</p>`
      : `<p>The instance on the left has K = ${K} bins of size B = ${B} and ${sizes.length} items of even size, adding up to BK = ${B * K}. Berger and Leighton turn it into the string <b>S<sub>B</sub></b> of Fig. 3, with</p>`) + `
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
      body: `<p>The item ribbon (PHHP)<sup>${s / 2}</sup> of u${u + 1}${doubled ? ` (size ${res.sizes[u]}, doubled: ${s})` : ''} goes into strip ${bn + 1}, the strip of bin ${bn + 1} in the packing on the left. Its ${s} H's continue the snake there, and strip ${bn + 1} has ${left} free node${left === 1 ? '' : 's'} left. The ribbon starts on an even node and so ends on an odd one, which gives the next linker the right parity.</p>
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
      <p>The front face of this fold${doubled ? ' (sizes doubled)' : ''}: ${stripTxt}.</p>` });

  return steps;
}

// strip outlines and labels on the front face
function buildOverlay(V, res, { ST, makeLabel }) {
  const out = [], n = V.n, cc = V.cc, K = res.K, st = ST();
  V.fold.bins.forEach((bn, j) => {
    const x0 = 1 - cc - 0.5, x1 = n - 2 - cc + 0.5, y0 = bn.rb + 1 - cc - 0.5, y1 = bn.rt - 1 - cc + 0.5, z = cc + 0.55;
    const geo = new THREE.BufferGeometry().setFromPoints([
      new THREE.Vector3(x0, y0, z), new THREE.Vector3(x1, y0, z), new THREE.Vector3(x1, y1, z), new THREE.Vector3(x0, y1, z), new THREE.Vector3(x0, y0, z)]);
    out.push(new THREE.Line(geo, new THREE.LineBasicMaterial({ color: j < K ? st.strip : st.plugStrip, transparent: true, opacity: st.stripOp })));
    const items = bn.contents.filter((x) => x.kind === 'item').map((x) => `u${x.item + 1}`);
    const text = j < K ? `strip ${j + 1}: ${items.join(' + ')}` : `strip ${j + 1}: plug`;
    const spr = makeLabel(text, j < K ? st.ink : st.plugInk, n);
    spr.position.set(-cc - 1.5 - spr.userData.w / 2, (bn.rt + bn.rb) / 2 - cc, cc + 1);
    out.push(spr);
  });
  return out;
}

// the pieces of the string bar: H pieces in their colours, runs of P's thin
const PIECE_NAMES = {
  edges: 'corner rod', back: 'back face ribbon', bl: 'tenth-edge rod', p4: 'P-hop', left: 'left face ribbon', p7a: 'P-hop',
  bottom: 'bottom face ribbon', p7b: 'P-hop', right: 'right face ribbon', p7c: 'P-hop', top: 'top face ribbon', int: 'core',
  down: 'P-hop to the front face', walls: 'periods: walls and rods', special: 'spaced rod',
};

function barPieces(V) {
  const barPieces = [];
  for (const sg of V.segs) {
    if (sg.key === 'filler' || sg.key === 'dummy' || sg.key === 'item') {
      const str = V.fold.strings[sg.string];
      const name = sg.key === 'filler' ? 'padding' : sg.key === 'dummy' ? 'plug' : `item u${sg.item + 1}`;
      barPieces.push({ s: sg.start, e: str.connEnd, kind: 'P', label: `linker before the ${name}` });
      barPieces.push({ s: str.connEnd, e: sg.end, kind: sg.key, item: sg.item, label: `${name}, into strip ${sg.bin + 1}`, min: true });
    } else barPieces.push({ s: sg.start, e: sg.end, cat: sg.cat, kind: sg.cat === 0 ? 'P' : 'H', label: PIECE_NAMES[sg.key] || sg.label, min: sg.key === 'special' });
  }
  return barPieces;
}

export default {
  id: 'bl',
  C,
  PRESETS,
  lhs: '<i>S</i><sub>B</sub> = ',
  strPlain: 'S_B',
  interiorKey: 'int',
  // the default camera: the front face with the strips, from the right and above
  fixedView: { dir: [1.0, 0.72, 1.1], dist: 3.0, tgt: [0.1, -0.05, 0] },
  // warnings about the size of the cube; block: too large to build in the browser
  sizeCheck(P, { fmt }) {
    if (P.q > 6) return { msg: `q = ${P.q} gives n = ${P.n} (${fmt(P.n ** 3)} H's), too large for the browser. Use K ≤ 3 and B ≤ 27 (B ≤ 13 if a size or B is odd, since those instances are doubled).`, cls: 'err', block: true };
    const dbl = P.f === 2 ? ` Some numbers are odd, so all of them are doubled: B = ${P.B}, sizes ${P.sizes.join(', ')}.` : '';
    if (P.q === 6) return { msg: `Heavy: q = 6 gives n = 80, i.e. 512,000 H's (~620k residues). Takes a few seconds.${dbl}`, cls: '' };
    return { msg: dbl.trim(), cls: '' };
  },
  formulaParts,
  buildSteps,
  overlayFrom: (steps) => steps.findIndex((s) => s.id === 'walls') + 1,
  buildOverlay,
  barPieces,
  refs: (st, { cards }) => (st.cards ? `<p class="rd-cards">On the proof board: ${st.cards.map(([id, label]) => `<a href="${cards}#step-bl-${id}" target="_blank" rel="noopener">${label}</a>`).join(' · ')}</p>` : ''),
  noFold: (res, { fmt }) => ({
    status: 'No packing exists, so by §3.2.4 S_B has no fold with its H\'s in a perfect cube.',
    html: `<div><b>No packing exists.</b><br>By §3.2.4, any fold of S<sub>B</sub> (${fmt(res.str.types.length)} residues, n = ${res.P.n}) whose H's formed a perfect ${res.P.n}³ cube would yield a packing.<br>So no fold of this string reaches 3n²(n−1) = ${fmt(3 * res.P.n ** 2 * (res.P.n - 1))} H–H pairs.</div>`,
  }),
};
