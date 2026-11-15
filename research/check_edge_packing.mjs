/** Complete coordinate certificates for the one-edge cubic HP construction.
 * Run: node research/check_edge_packing.mjs
 * Finite certificates supplement the universal proof in edge_packing_proof.md.
 * This checker does not import the earlier construction or its verifier.
 */
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const FRONT = [0, 0, -1], BACK = [0, 0, 1];
const LEFT = [-1, 0, 0], RIGHT = [1, 0, 0];
const TOP = [0, 1, 0], BOTTOM = [0, -1, 0];
const range = (a, b) => Array.from({ length: b - a }, (_, i) => a + i);
const add = (p, v) => p.map((x, i) => x + v[i]);
const same = (p, q) => p.every((x, i) => x === q[i]);
const dist = (p, q) => p.reduce((s, x, i) => s + Math.abs(x - q[i]), 0);
const parity = p => ((p[0] + p[1] + p[2]) % 2 + 2) % 2;
const E = t => 'PHP'.repeat(t);
const F = t => { assert(t > 0 && t % 2 === 0); return 'PHHP'.repeat(t / 2); };

function* line(p, q) {
  assert(p.filter((x, i) => x !== q[i]).length <= 1);
  p = [...p]; yield p;
  const axis = p.findIndex((x, i) => x !== q[i]);
  if (axis < 0) return;
  while (p[axis] !== q[axis]) {
    p = [...p]; p[axis] += Math.sign(q[axis] - p[axis]); yield p;
  }
}
function polyline(points) {
  return points.flatMap((p, i) => i ? [...line(points[i - 1], p)].slice(1) : [p]);
}
function snake(outer, inner, point) {
  return outer.flatMap((v, i) => (i % 2 ? [...inner].reverse() : inner).map(w => point(v, w)));
}
function normals(p, L) {
  return p.flatMap((x, k) => x === 0 || x === L
    ? [[0, 0, 0].map((_, j) => j === k ? (x === 0 ? -1 : 1) : 0)] : []);
}
function* straightEdge(hs, incoming, other) {
  let v = incoming;
  for (const h of hs) {
    const w = same(v, incoming) ? other : incoming;
    yield ['P', add(h, v)]; yield ['H', h]; yield ['P', add(h, w)]; v = w;
  }
}
function* face(hs, normal) {
  assert(hs.length % 2 === 0);
  for (let i = 0; i < hs.length; i += 2) {
    yield ['P', add(hs[i], normal)]; yield ['H', hs[i]];
    yield ['H', hs[i + 1]]; yield ['P', add(hs[i + 1], normal)];
  }
}
function* skeleton(hs, L) {
  const labels = Array(hs.length); labels[hs.length - 1] = BACK;
  for (let i = hs.length - 2; i >= 0; --i) {
    const common = normals(hs[i], L).filter(v => normals(hs[i + 1], L).some(w => same(v, w)));
    assert.equal(common.length, 2);
    labels[i] = common.find(v => !same(v, labels[i + 1]));
  }
  let incoming = normals(hs[0], L).find(v => !same(v, labels[0]));
  for (let i = 0; i < hs.length; i++) {
    yield ['P', add(hs[i], incoming)]; yield ['H', hs[i]];
    yield ['P', add(hs[i], labels[i])]; incoming = labels[i];
  }
}

function parameters(q, B) {
  assert(q >= 2 && B >= 6 && B % 2 === 0);
  const g = B + 6, d = (q + 1) * g + q * B, n = d + 2;
  assert(d % 2 === 0 && B + 5 < d + 1);
  return { q, B, g, d, n, L: n - 1, K: 8 * n };
}
function block(word, first, last, normalFirst, normalLast, generate) {
  assert.equal(parity(first), 0); assert.equal(parity(last), 1);
  return { word, first, last, normalFirst, normalLast, generate };
}
function modules(p) {
  const { q, B, g, d, L } = p;
  const edges = polyline([[d,L,L],[0,L,L],[0,L,0],[L,L,0],[L,L,L],
    [L,0,L],[L,0,0],[0,0,0],[0,0,L],[d,0,L]]);
  assert.equal(edges.length, 9 * d + 8);
  const A = block(E(9*d+8)+F(d*d)+E(d), [d,L,L], [0,d,L], null, BACK,
    function* () {
      yield* skeleton(edges, L);
      yield* face(snake(range(1,d+1).reverse(), range(1,d+1), (x,y) => [x,y,L]), BACK);
      yield* straightEdge(range(1,d+1).map(y => [0,y,L]), BACK, LEFT);
    });
  const left = block(F(d*d), [0,1,1], [0,d,1], LEFT, LEFT,
    function* () { yield* face(snake(range(1,d+1), range(1,d+1), (y,z) => [0,y,z]), LEFT); });
  const bottom = block(F(d*d), [d,0,d], [d,0,1], BOTTOM, BOTTOM,
    function* () { yield* face(snake(range(1,d+1).reverse(), range(1,d+1).reverse(), (z,x) => [x,0,z]), BOTTOM); });
  const right = block(F(d*d), [L,1,d], [L,d,d], RIGHT, RIGHT,
    function* () { yield* face(snake(range(1,d+1), range(1,d+1).reverse(), (y,z) => [L,y,z]), RIGHT); });
  const D = block('P'+'H'.repeat(d**3+2)+'P'+F(d*d-2), [d,L,1], [d-1,L,1], TOP, TOP,
    function* () {
      yield ['P',[d,L+1,1]]; yield ['H',[d,L,1]];
      const layer = snake(range(1,d+1).reverse(), range(1,d+1).reverse(), (y,x) => [x,y]);
      for (let z = 1; z <= d; z++) {
        for (const [x,y] of (z % 2 ? layer : [...layer].reverse())) yield ['H',[x,y,z]];
      }
      yield ['H',[d,L,d]]; yield ['P',[d,L+1,d]];
      const top = snake(range(1,d+1).reverse(), range(1,d+1).reverse(), (z,x) => [x,L,z]);
      yield* face(top.slice(1,-1), TOP);
    });
  const Wword = E(1)+F(d)+E(g)+('P'.repeat(B+2)+E(g)).repeat(q)+F(d)+E(d-1);
  const W = block(Wword, [0,d,0], [0,d-1,0], LEFT, LEFT,
    function* () {
      yield* straightEdge([[0,d,0]], LEFT, FRONT);
      yield* face(range(1,d+1).map(x => [x,d,0]), FRONT);
      for (let j = q; j >= 0; --j) {
        const lo = 1 + j * (g + B);
        if (j < q) {
          const old = [L,lo+g+B,-1], next = [L,lo+g-1,-1];
          const route = polyline([old,[L,old[1],-2],[L,next[1],-2],next]).slice(1,-1);
          assert.equal(route.length, B + 2);
          for (const v of route) yield ['P',v];
        }
        yield* straightEdge(range(lo,lo+g).reverse().map(y => [L,y,0]), FRONT, RIGHT);
      }
      yield* face(range(1,d+1).reverse().map(x => [x,1,0]), FRONT);
      yield* straightEdge(range(1,d).map(y => [0,y,0]), FRONT, LEFT);
    });
  const G = block(F(d*(d-2)), [d,2,0], [d,d-1,0], FRONT, FRONT,
    function* () { yield* face(snake(range(2,d), range(1,d+1).reverse(), (y,x) => [x,y,0]), FRONT); });
  return [A,left,bottom,right,D,W,G];
}

/** Corner route with disjoint depth bands {h,h+1}. */
function cornerRoute(p, index, old, next) {
  const { L, K } = p, h = 4 + 2 * index;
  let a = old.last, b = next.first, va = old.normalLast, vb = next.normalFirst;
  let ia = va.findIndex(v => v), ib = vb.findIndex(v => v);
  assert.notEqual(ia, ib);
  const it = [0,1,2].find(i => i !== ia && i !== ib);
  const reverse = a[it] < b[it];
  if (reverse) { [a,b,va,vb] = [b,a,vb,va]; [ia,ib] = [ib,ia]; }
  const sa = va[ia], sb = vb[ib], ba = sa > 0 ? L : 0, bb = sb > 0 ? L : 0;
  const s = -sb * (a[ib] - bb), r = -sa * (b[ia] - ba);
  const t0 = a[it], t1 = b[it];
  assert(t0 !== t1 && s >= 0 && s <= L && r >= 0 && r <= L);
  const base = 4*h+s+r+Math.abs(t0-t1)+6, target = K+3;
  assert(base <= target && (target-base) % 2 === 0);
  const T = Math.max(t0,t1)+1+(target-base)/2;
  const points = [[0,-s,t0],[h,-s,t0],[h,h+1,t0],[h,h+1,T],
    [h+1,h+1,T],[h+1,h+1,t1],[-r,h+1,t1],[-r,0,t1]];
  const global = ([u,v,t]) => {
    const out = [0,0,0]; out[ia] = ba+sa*u; out[ib] = bb+sb*v; out[it] = t; return out;
  };
  const path = polyline(points.map(global));
  if (reverse) path.reverse();
  a = old.last; b = next.first; va = old.normalLast; vb = next.normalFirst;
  assert.equal(path.length, target+1);
  assert(same(path[0],a) && same(path[1],add(a,va)));
  assert(same(path.at(-2),add(b,vb)) && same(path.at(-1),b));
  return path;
}
function itemRoute(p, index, old, next) {
  const { L, K } = p, h = 20 + index;
  const u = old.last[1], v = next.first[1]; assert.notEqual(u,v);
  const R = (K+3-2*h-Math.abs(u-v))/2;
  assert(Number.isInteger(R) && R >= 1);
  const path = polyline([[L,u,0],[L+h,u,0],[L+h,u,-R],
    [L+h,v,-R],[L+h,v,0],[L,v,0]]);
  assert.equal(path.length,K+4); return path;
}

class CertificateCheck {
  constructor(p, expected) {
    this.p = p; this.expected = expected; this.index = 0; this.positions = new Set();
    this.hydrophobic = new Uint8Array(p.n**3); this.hCount = 0; this.bonds = 0; this.backboneHH = 0;
    this.bounds = [[Infinity,-Infinity],[Infinity,-Infinity],[Infinity,-Infinity]];
  }
  push(label, v) {
    const { n, L } = this.p;
    assert.equal(label,this.expected[this.index],`literal word at ${this.index}`);
    if (this.previous) assert.equal(dist(v,this.previous),1,`backbone step ${this.index}`);
    if (label === 'H' && this.previousLabel === 'H') this.backboneHH++;
    const stride = 64*n, offset = 16*n;
    for (let k = 0; k < 3; k++) {
      assert(Number.isSafeInteger(v[k]) && v[k] >= -offset && v[k] < stride-offset);
      this.bounds[k][0] = Math.min(this.bounds[k][0],v[k]); this.bounds[k][1] = Math.max(this.bounds[k][1],v[k]);
    }
    const key = ((v[0]+offset)*stride+v[1]+offset)*stride+v[2]+offset;
    assert(!this.positions.has(key),`collision at ${v} (residue ${this.index})`); this.positions.add(key);
    const inside = v.every(x => 0 <= x && x <= L);
    assert.equal(inside,label === 'H',`H/P cube label ${v}`);
    if (label === 'H') {
      const [x,y,z] = v, index = x+n*(y+n*z), H = this.hydrophobic;
      this.bonds += (x>0 ? H[index-1] : 0)+(x<L ? H[index+1] : 0)
        +(y>0 ? H[index-n] : 0)+(y<L ? H[index+n] : 0)
        +(z>0 ? H[index-n*n] : 0)+(z<L ? H[index+n*n] : 0);
      assert.equal(H[index],0); H[index] = 1; this.hCount++;
    }
    this.previous = v; this.previousLabel = label; this.index++;
  }
  append(generator) { for (const [label,v] of generator) this.push(label,v); }
  finish() {
    const { n,d } = this.p;
    assert.equal(this.index,this.expected.length); assert.equal(this.hCount,n**3);
    assert(this.hydrophobic.every(v => v === 1));
    assert.equal(this.bonds,3*n*n*(n-1)); assert.equal(this.backboneHH,d**3+3*d*d);
    assert.equal(this.bonds-this.backboneHH,2*n**3-4);
  }
}

function check(q,B,sizes,groups) {
  const p = parameters(q,B), { d,g,L,K,n } = p;
  assert.equal(groups.length,q); assert(sizes.every(a => a >= 2 && a % 2 === 0));
  assert.deepEqual(groups.flat().toSorted((a,b) => a-b),sizes.map((_,i) => i));
  assert(groups.every(group => group.reduce((sum,i) => sum+sizes[i],0) === B));
  const fixed = modules(p), items = Array(sizes.length), portRows = [];
  groups.forEach((group,j) => {
    let y = 1+g+j*(g+B);
    for (const i of group) {
      const lo = y, hi = y+sizes[i];
      items[i] = block(E(sizes[i]),[L,lo,0],[L,hi-1,0],RIGHT,RIGHT,
        function* () { yield* straightEdge(range(lo,hi).map(t => [L,t,0]),RIGHT,FRONT); });
      portRows.push(lo,hi-1); y = hi;
    }
    assert.equal(y,1+g+j*(g+B)+B);
  });
  assert.equal(new Set(portRows).size,portRows.length);
  assert(portRows.every(y => y < d-1));
  const blocks = [...fixed,...items], expected = blocks.map(b => b.word).join('P'.repeat(K));
  const checker = new CertificateCheck(p,expected); checker.append(blocks[0].generate());
  for (let j = 1; j < blocks.length; j++) {
    const route = j <= 7 ? cornerRoute(p,j,blocks[j-1],blocks[j])
      : itemRoute(p,j-7,blocks[j-1],blocks[j]);
    assert.equal(route.length,K+4);
    checker.append(route.slice(2,-2).map(v => ['P',v]));
    checker.append(blocks[j].generate());
  }
  checker.finish();
  assert.equal(checker.index,d**3+12*d*d+36*d+24+q*(B+2)+(sizes.length+6)*K);
  return { q,B,sizes,groups,separatorH:g,side:n,connectorPs:K,residues:checker.index,
    hCount:checker.hCount,bondScore:checker.bonds,backboneHH:checker.backboneHH,
    nonbackboneScore:checker.bonds-checker.backboneHH,bounds:checker.bounds,
    strictThreePartition:sizes.length===3*q && sizes.every(a => B<4*a && 2*a<B),
    status:'PASS: literal single word, every step, global injectivity, all H/P labels, cube coverage, and both scores' };
}

/** Independent local BFS verifies the extra four transverse steps in the gap lemma. */
function checkGapDistances() {
  const results = [];
  for (let gap = 0; gap <= 12; gap++) {
    const end = gap+1, start = [0,0,0], target = [0,end,0];
    const key = v => v.join(',');
    const allowed = ([u,y,z]) => {
      if (u < -2 || u > 4 || z < -4 || z > 2 || y < -4 || y > end+4) return false;
      if ((u===0 && z===0) && (y===0 || y===end)) return true;
      if (u<=0 && z>=0) return false;
      // Every other first-layer site is used by a different E-block P.
      if ((u===1 && z===0) || (u===0 && z===-1)) return u===0 && (y===0 || y===end);
      return true;
    };
    const queue = [[start,0]], visited = new Set([key(start)]); let distance;
    for (let index=0; index<queue.length; index++) {
      const [v,steps] = queue[index]; if (same(v,target)) { distance=steps; break; }
      for (let k=0; k<3; k++) for (const sign of [-1,1]) {
        const w=[...v]; w[k]+=sign; const code=key(w);
        if (steps===0 && same(w,target)) continue; // The connector must start with a P.
        if (allowed(w) && !visited.has(code)) { visited.add(code); queue.push([w,steps+1]); }
      }
    }
    assert.equal(distance,gap===0 ? 3 : gap+5); results.push({gap,shortestEdges:distance});
  }
  return results;
}

/** Exhaust all marker placements for small edges, without assuming their order. */
function checkMarkerPlacements() {
  const reports=[];
  for (const q of [2,3,4]) for (const B of [2,4,6]) {
    const g=B+6,d=(q+1)*g+q*B;
    let solutions=0,states=0;
    for (const singleton of [1,d]) {
      const targets=singleton===1 ? [2,d] : [1,d-1];
      function search(placed) {
        states++;
        if (placed.length===q+1) {
          if (!targets.includes(placed.at(-1).end)) return;
          const sorted=[...placed].sort((a,b)=>a.lo-b.lo);
          assert.equal(sorted[0].lo,1); assert.equal(sorted.at(-1).hi,d);
          assert(sorted.slice(1).every((v,i)=>v.lo-sorted[i].hi-1===B));
          assert(placed.every(v=>v.direction===placed[0].direction));
          solutions++; return;
        }
        for (let lo=1;lo+g-1<=d;lo++) for (const direction of [-1,1]) {
          const hi=lo+g-1,start=direction===1?lo:hi,end=direction===1?hi:lo;
          if (placed.some(v=>!(hi<v.lo || lo>v.hi))) continue;
          if (!placed.length) { if (start!==singleton) continue; }
          else {
            const distance=Math.abs(start-placed.at(-1).end);
            const minimum=distance===1?3:distance+4;
            if (minimum>B+5) continue;
          }
          search([...placed,{lo,hi,start,end,direction}]);
        }
      }
      search([]);
    }
    assert.equal(solutions,2); reports.push({q,B,g,d,states,solutions});
  }
  return reports;
}

const cases = [
  [2,6,Array(6).fill(2),[[0,2,4],[1,3,5]]],
  [3,6,Array(9).fill(2),[[8,1,5],[0,7,3],[6,4,2]]],
  [2,12,Array(6).fill(4),[[5,2,0],[3,1,4]]],
  [2,20,[6,8,6,6,6,8],[[1,3,4],[5,0,2]]],
  // A non-3-Partition exact packing checks that the argument only needs even sizes.
  [2,6,[2,4,4,2],[[1,0],[3,2]]],
];
const report = { construction:'one edge, two face crossings, long separators',
  gapDistanceChecks:checkGapDistances(),markerPlacementChecks:checkMarkerPlacements(),cases:[] };
for (const args of cases) {
  const result = check(...args); report.cases.push(result);
  process.stdout.write(JSON.stringify(result)+'\n');
}
writeFileSync(fileURLToPath(new URL('./edge_packing_verification.json',import.meta.url)),JSON.stringify(report,null,2)+'\n');
process.stdout.write('All complete coordinate certificates and gap-distance checks passed.\n');
