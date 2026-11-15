/**
 * Fold it yourself: a game on Berger and Leighton's reduction (original-proof page, under "Folding a small instance").
 * A small bin packing instance becomes the string S_B (three reading steps: the puzzle, the four building blocks,
 * the string block by block), and the reader folds S_B into a 12×12×12 cube one piece at a time: the corner rod,
 * the back face, the door and the core, the walls, the items in the strips, and the linkers, which the reader routes.
 * Hints, Next step (instant) and Show solution (played out) on every folding step.
 *
 * mount(root) builds everything inside root (class g-root; styles.css, classes prefixed g-, and the site's fg- and bp-
 * patterns re-scoped under .g-root). Rendering: three.js with the shaders of the fold game; colours from tokens.css,
 * re-read on 'themechange'. Generated from the proof-map draft by to-site.mjs; edit with care.
 */
import * as THREE from 'three';

export function mount(root) {
"use strict";
const q=2, n=q*(2*q+1)+2, L=n-1, T=(2*q-1)*(n-2), LAM=n*n, RW=k=>1+k*(2*q+1), ZL=l=>-(q+2)-l, N3=n*n*n, SCORE=3*n*n*(n-1);
const PAL=['#c0792b','#5f8a3a','#4d6fa8','#9c4f6e','#2f8a8a','#a0522d','#6b5fb0','#8a8a2f','#b0476b','#3d7a52','#7a5c3d','#5a6f8c'];
const CPAL=['#1f4f8f','#0f6f73','#d99a1e','#7a4b9e','#c4532f','#2f7a4d','#a86f12','#1f5f9e','#6b6b75','#a34f61','#4f7aa3','#8a8a2f'];
/* item u is drawn in the site's --item-(u mod 4 + 1); items 5 to 8 in a lighter tint of the same four (the site stripes them) */
function itemCol(u){ const b=[C.i1,C.i2,C.i3,C.i4][u%4]||'#0f6f73'; return u>=4? mixc(b,C.bgElev||'#ffffff',0.4) : b; }
const C={H:'#d8342e', fill:'#b5aa90', dummy:'#9a9387', edge:'#3a3f48', face:'#9aa0a8', inner:'#c3c7ce', wall:'#15171c', conn:'#b9bfc8', ink:'#15171c', ghost:'#c5cad1', ok:'#2f8a4e', bad:'#c0392b', note:'#9a6200', sel:'#1f5fbf'};
const DIRS=[[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1]];
function seq(a,b){ const o=[]; if(a<=b) for(let i=a;i<=b;i++) o.push(i); else for(let i=a;i>=b;i--) o.push(i); return o; }
const adj=(a,b)=>Math.abs(a[0]-b[0])+Math.abs(a[1]-b[1])+Math.abs(a[2]-b[2])===1;
const same=(a,b)=>a[0]===b[0]&&a[1]===b[1]&&a[2]===b[2];
const K3=p=>p[0]+','+p[1]+','+p[2], K2=(x,y)=>x+','+y;
const isInt=p=>p[0]>0&&p[0]<L&&p[1]>0&&p[1]<L&&p[2]>0&&p[2]<L;
const inCube=p=>p[0]>=0&&p[0]<=L&&p[1]>=0&&p[1]<=L&&p[2]>=0&&p[2]<=L;
const fmt=x=>x.toLocaleString('en-US');
const sp=(b,e)=>`${b}<sup>${e}</sup>`;
const SB='<i>S</i><sub>B</sub>';

/* ---------------- levels ---------------- */
const LEVELS=[
  {name:'One bin', items:[6,4,2], K:1, blurb:'One real bin and one spare bin.'},
  {name:'Two bins', items:[2,2,4], K:2, blurb:'Two real bins and no spare bin, so the block D is empty.'},
  {name:'Four items', items:[4,4,2,6], K:2, blurb:'Split four items into two bins of B = 8.'},
  {name:'No packing?', items:[6,6,4], K:2, no:true, blurb:'Can these items be packed? If they cannot, the string has no perfect fold (card 9).'},
  {name:'Five items', items:[8,2,6,4,4], K:2, blurb:'Two bins of B = 12.'},
  {name:'Many linkers', items:[2,2,2,2,2,4], K:1, layers:3, blurb:'Nine linkers to route, and only 3 routing layers.'},
  {name:'Big items', items:[10,4,6,8], K:2, layers:2, blurb:'Two bins of B = 14, and only 2 routing layers.'},
  {name:'Tight', items:[2,4,6,8,2,6], K:2, layers:2, blurb:'Six items, eight linkers, two routing layers.'}
];
const lvB=lv=>lv.items.reduce((a,b)=>a+b,0)/lv.K;
function tailBlocks(lv){ const B=lvB(lv), o=[];
  const blk=(id,kind,size,u)=>({id,kind,size,u, get col(){ return kind==='item'? itemCol(u) : kind==='fill'? C.fill : C.dummy; }});
  for(let k=0;k<q;k++) o.push(blk('F'+(k+1),'fill',T-B));
  for(let j=0;j<q-lv.K;j++) o.push(blk('D'+(j+1),'dummy',B));
  lv.items.forEach((s,u)=>o.push(blk('u'+(u+1),'item',s,u)));
  return o; }
function solvePacking(sizes,K,B){ const idx=sizes.map((s,i)=>i).sort((a,b)=>sizes[b]-sizes[a]); const load=new Array(K).fill(0), asg=new Array(sizes.length).fill(-1);
  const rec=i=>{ if(i===idx.length) return load.every(l=>l===B); const u=idx[i], s=sizes[u], tried=new Set();
    for(let j=0;j<K;j++){ if(load[j]+s>B||tried.has(load[j])) continue; tried.add(load[j]); load[j]+=s; asg[u]=j; if(rec(i+1)) return true; load[j]-=s; asg[u]=-1; } return false; };
  return rec(0)? asg : null; }

/* ---------------- the string ---------------- */
function sbBlocks(P){ const {q,n,T,Lam,B,K,items}=P, b=[];
  b.push({id:'X1', runs:[['PHP',9*n-10]]});
  b.push({id:'X2', runs:[['PHHP',(n-2)**2/2]]});
  b.push({id:'X3', runs:[['PHP',n-2],['P',4]]});
  b.push({id:'X4', runs:[...[0,1,2].flatMap(()=>[['PHHP',(n-2)**2/2],['P',7]]), ['PHHP',(n-2)**2/2-1]]});
  b.push({id:'X5', runs:[['P',1],['H',(n-2)**3+2],['P',8+q]]});
  const wall=[['PHP',q],['PHHP',(n-2)/2],['PHP',2*q+1],['P',4],['PHHP',(n-2)/2],['PHP',q],['P',2*q]];
  b.push({id:'W', runs:Array.from({length:q},()=>wall).flat()});
  b.push({id:'S', runs:[['P',1],['H',1], ...Array.from({length:q-1},()=>[['P',2*q+6],['H',1]]).flat(), ['P',1]]});
  b.push({id:'F', runs:Array.from({length:q},()=>[['P',Lam],['PHHP',(T-B)/2]]).flat()});
  b.push({id:'D', runs:Array.from({length:q-K},()=>[['P',Lam],['PHHP',B/2]]).flat()});
  b.push({id:'I', runs:items.flatMap(s=>[['P',Lam],['PHHP',s/2]])});
  return b; }
const blockLen=bl=>bl.runs.reduce((a,[u,r])=>a+u.length*r,0);
function sbLetters(blocks){ const N=blocks.reduce((a,b)=>a+blockLen(b),0), out=new Uint8Array(N); let i=0;
  for(const b of blocks) for(const [u,r] of b.runs){ const pat=[...u].map(c=>c==='H'?1:0); for(let k=0;k<r;k++) for(const v of pat) out[i++]=v; } return out; }
const toyP=lv=>({q,n,T,Lam:LAM,B:lvB(lv),K:lv.K,items:lv.items});
function realP(lv){ const B=lvB(lv), qq=2*Math.max(lv.K,Math.ceil(Math.sqrt(B))), nn=qq*(2*qq+1)+2; return {q:qq,n:nn,T:(2*qq-1)*(nn-2),Lam:nn*nn,B,K:lv.K,items:lv.items}; }

const SLOTS=[
  {id:'X1', nm:'X<sub>1</sub>', role:'the nine edges and all eight corners', col:'edge'},
  {id:'X2', nm:'X<sub>2</sub>', role:'the back face', col:'face'},
  {id:'X3', nm:'X<sub>3</sub>', role:'the tenth edge, then a hop to the left face', col:'edge'},
  {id:'X4', nm:'X<sub>4</sub>', role:'left, bottom, right and top faces, with two top sites left open', col:'face'},
  {id:'X5', nm:'X<sub>5</sub>', role:'the interior, entered and left through the two open sites', col:'inner'},
  {id:'W',  nm:'W', role:'the q bin walls', col:'wall'},
  {id:'S',  nm:'Σ', role:'the spaced rod, one H per wall', col:'H'},
  {id:'F',  nm:'F', role:'one padding per bin', col:'fill'},
  {id:'D',  nm:'D', role:'plugs that close the q − K spare bins', col:'dummy'},
  {id:'I',  nm:'I', role:'one string per item', col:PAL[2]}
];
function cardsFor(lv){ const B=lvB(lv), K=lv.K;
  const c=[
    {id:'X1', slot:'X1', num:sp('(PHP)',9*n-10), sym:sp('(PHP)','9n−10')},
    {id:'X2', slot:'X2', num:sp('(PHHP)',(n-2)**2/2), sym:sp('(PHHP)','(n−2)²/2')},
    {id:'X3', slot:'X3', num:sp('(PHP)',n-2)+' '+sp('P',4), sym:sp('(PHP)','n−2')+' '+sp('P',4)},
    {id:'X4', slot:'X4', num:sp('('+sp('(PHHP)',(n-2)**2/2)+' '+sp('P',7)+')',3)+' '+sp('(PHHP)',(n-2)**2/2-1), sym:sp('('+sp('(PHHP)','(n−2)²/2')+' '+sp('P',7)+')',3)+' '+sp('(PHHP)','(n−2)²/2 − 1')},
    {id:'X5', slot:'X5', num:'P '+sp('H',(n-2)**3+2)+' '+sp('P',8+q), sym:'P '+sp('H','(n−2)³+2')+' '+sp('P','8+q')},
    {id:'W', slot:'W', num:sp('('+sp('(PHP)',q)+' '+sp('(PHHP)',(n-2)/2)+' '+sp('(PHP)',2*q+1)+' '+sp('P',4)+' '+sp('(PHHP)',(n-2)/2)+' '+sp('(PHP)',q)+' '+sp('P',2*q)+')',q),
      sym:sp('('+sp('(PHP)','q')+' '+sp('(PHHP)','(n−2)/2')+' '+sp('(PHP)','2q+1')+' '+sp('P',4)+' '+sp('(PHHP)','(n−2)/2')+' '+sp('(PHP)','q')+' '+sp('P','2q')+')','q')},
    {id:'S', slot:'S', num:'PH '+sp('P',2*q+6)+'H P', sym:'PH '+sp('('+sp('P','2q+6')+'H)','q−1')+' P'},
    {id:'F', slot:'F', num:sp('('+sp('P',LAM)+' '+sp('(PHHP)',(T-B)/2)+')',q), sym:sp('('+sp('P','Λ')+' '+sp('(PHHP)','(T−B)/2')+')','q')},
    {id:'D', slot:'D', num: K===q? 'empty, since q − K = 0' : sp('('+sp('P',LAM)+' '+sp('(PHHP)',B/2)+')',q-K), sym:sp('('+sp('P','Λ')+' '+sp('(PHHP)','B/2')+')','q−K')},
    {id:'I', slot:'I', num: lv.items.map(s=>sp('P',LAM)+sp('(PHHP)',s/2)).join(' · '), sym:'∏<sub>u</sub> '+sp('P','Λ')+' '+sp('(PHHP)','s(u)/2')},
    {id:'d1', slot:null, num:sp('(PHHP)',9*n-10), sym:sp('(PHHP)','9n−10'), why:'(PHHP) keeps its H\'s on a face, not on edges. An edge site needs an H with two P neighbours outside the cube: PHP (card 5).'},
    {id:'d2', slot:null, num:'P '+sp('H',(n-2)**3)+' '+sp('P',8+q), sym:'P '+sp('H','(n−2)³')+' '+sp('P','8+q'), why:'The interior run also fills the two open sites on the top face, so it needs (n−2)³ + 2 H\'s.'},
    {id:'d3', slot:null, num:sp('(PHP)',(n-2)**2/2), sym:sp('(PHP)','(n−2)²/2'), why:'(PHP) forces every H onto an edge. A face is filled by pairs of H\'s with one P each: (PHHP).'},
    {id:'d4', slot:null, num:sp('('+sp('P',LAM)+' '+sp('(PHHP)',T/2)+')',q), sym:sp('('+sp('P','Λ')+' '+sp('(PHHP)','T/2')+')','q'), why:'A padding of size T would fill a whole bin and leave no room for the items. The padding has size T − B.'}
  ];
  let s=7+lv.items.length*13; const rnd=()=>{ s=(s*1103515245+12345)%2147483648; return s/2147483648; };
  for(let i=c.length-1;i>0;i--){ const j=Math.floor(rnd()*(i+1)); [c[i],c[j]]=[c[j],c[i]]; }
  return c; }

/* ---------------- the fold (canonical coordinates, as in buildFold) ---------------- */
class Builder{
  constructor(){ this.r=[]; this.blk=0; this.marks={}; }
  mark(k){ this.marks[k]=this.r.length; }
  add(h,p,st,cat,b,extra){ this.r.push(Object.assign({p,h:h?1:0,st,cat,b},extra||{})); }
  out(p){ return DIRS.map(d=>[p[0]+d[0],p[1]+d[1],p[2]+d[2]]).filter(v=>v.some(c=>c<0||c>L)); }
  edgeRun(st,cat,Hs,first,last){
    const pp=[], N=Hs.map(h=>this.out(h));
    const dfs=(i,prev)=>{ if(i===Hs.length) return true;
      for(const a of N[i]){ if(i===0&&first&&!same(a,first)) continue; if(prev&&!adj(prev,a)) continue;
        for(const b of N[i]){ if(b===a) continue; if(i===Hs.length-1&&last&&!same(b,last)) continue;
          if(i+1<Hs.length && !N[i+1].some(x=>adj(b,x))) continue;
          pp[i]=[a,b]; if(dfs(i+1,b)) return true; } }
      return false; };
    if(!dfs(0,null)) throw new Error('edge P placement failed ('+cat+')');
    const b=this.blk++; Hs.forEach((h,i)=>{ this.add(0,pp[i][0],st,cat,b); this.add(1,h,st,cat,b); this.add(0,pp[i][1],st,cat,b); });
  }
  face(st,cat,Hs,extra){ const b=this.blk++; Hs.forEach((h,i)=>{ const nv=this.out(h)[0]; if(i%2===0){ this.add(0,nv,st,cat,b,extra); this.add(1,h,st,cat,b,extra); } else { this.add(1,h,st,cat,b,extra); this.add(0,nv,st,cat,b,extra); } }); }
  conn(st,pts,extra){ const b=this.blk++; pts.forEach(p=>this.add(0,p,st,'conn',b,extra)); }
}
const E9=()=>[ ...seq(n-2,0).map(x=>[x,L,L]), ...seq(L-1,0).map(z=>[0,L,z]), ...seq(1,L).map(x=>[x,L,0]), ...seq(1,L).map(z=>[L,L,z]),
               ...seq(L-1,0).map(y=>[L,y,L]), ...seq(L-1,0).map(z=>[L,0,z]), ...seq(L-1,0).map(x=>[x,0,0]), ...seq(1,L).map(z=>[0,0,z]), ...seq(1,n-2).map(x=>[x,0,L]) ];
const BACK_START=[n-2,1,L], BACK_END=[1,1,L];
function canonBack(){ const o=[]; seq(n-2,1).forEach((x,ci)=>(ci%2===0?seq(1,n-2):seq(n-2,1)).forEach(y=>o.push([x,y,L]))); return o; }
function stageX1(Bd){ Bd.mark('X1'); Bd.edgeRun('edges9','edge9',E9(),null,[n-2,0,n]); }
function stageBack(Bd,cells){ Bd.mark('X2'); Bd.face('back','back',cells);
  Bd.mark('X3'); Bd.edgeRun('edge10','edge10',seq(1,n-2).map(y=>[0,y,L]),[0,1,n],[0,n-2,n]);
  Bd.conn('edge10',[[-1,n-2,n],[-2,n-2,n],[-2,n-2,n-1],[-2,n-2,n-2]]); }
function sideFaces(){ const left=[],bottom=[],right=[],top=[];
  seq(n-2,1).forEach((y,i)=>(i%2===0?seq(n-2,1):seq(1,n-2)).forEach(z=>left.push([0,y,z])));
  seq(1,n-2).forEach((x,i)=>(i%2===0?seq(n-2,1):seq(1,n-2)).forEach(z=>bottom.push([x,0,z])));
  seq(1,n-2).forEach((y,i)=>(i%2===0?seq(n-2,1):seq(1,n-2)).forEach(z=>right.push([L,y,z])));
  seq(n-2,1).forEach((z,i)=>(i%2===0?seq(n-2,1):(z===1?seq(1,n-4):seq(1,n-2))).forEach(x=>top.push([x,L,z])));
  return {left,bottom,right,top}; }
const DOOR=[[n-3,L,1],[n-2,L,1]];
function stageSides(Bd,full){ const {left,bottom,right,top}=sideFaces(), zz=n-2;
  Bd.mark('X4'); Bd.face('faces','face',left);
  Bd.conn('faces',[[-2,1],[-2,0],[-2,-1],[-2,-2],[-1,-2],[0,-2],[1,-2]].map(([a,b])=>[a,b,zz]));
  Bd.face('faces','face',bottom);
  Bd.conn('faces',[[n-2,-2],[n-1,-2],[n,-2],[n+1,-2],[n+1,-1],[n+1,0],[n+1,1]].map(([a,b])=>[a,b,zz]));
  Bd.face('faces','face',right);
  Bd.conn('faces',[[n+1,n-2],[n+1,n-1],[n+1,n],[n+1,n+1],[n,n+1],[n-1,n+1],[n-2,n+1]].map(([a,b])=>[a,b,zz]));
  if(!full) return;
  Bd.face('faces','face',top);
  Bd.mark('X5');
  { const b=Bd.blk++; Bd.add(0,[n-3,n,1],'interior','int',b);
    const layer=[]; seq(n-3,1).forEach(x=>layer.push([x,1])); seq(2,n-2).forEach((z,i)=>(i%2===0?seq(1,n-2):seq(n-2,1)).forEach(x=>layer.push([x,z])));
    const rev=layer.slice().reverse();
    Bd.add(1,[n-3,L,1],'interior','int',b);
    for(let li=0; li<n-2; li++){ const y=n-2-li, lay=li%2===0?layer:rev; for(const [x,z] of lay) Bd.add(1,[x,y,z],'interior','int',b); }
    for(const y of seq(1,n-2)) Bd.add(1,[n-2,y,1],'interior','int',b);
    Bd.add(1,[n-2,L,1],'interior','int',b);
    [[n-2,n,1],[n-2,n+1,1],[n-2,n+1,0],[n-2,n+1,-1],[n-2,n+1,-2],[n-2,n,-2],[n-2,n-1,-2],[L,L,-2], ...seq(1,q).map(j=>[L,L-j,-2])].forEach(p=>Bd.add(0,p,'interior','int',b)); }
}
const FR=(x,t,z)=>[L-x,L-t,z];
const WALL_ROWS=(()=>{ const s=new Set(); for(let k=0;k<q;k++){ s.add(L-RW(k)); s.add(L-(RW(k)+2*q)); } return s; })();   // y of the wall lines
const SPECIAL_Y=(()=>{ const o=[]; for(let k=q-1;k>=0;k--) o.push(L-(RW(k)+q)); return o; })();                    // y of the special H's (at x = L)
function stageWalls(Bd){ Bd.mark('W');
  const eS=(cat,x,rows,sideX)=>{ const b=Bd.blk++; rows.forEach((t,j)=>{ const f=FR(x,t,-1), s=FR(sideX,t,0), o=j%2===0; Bd.add(0,o?f:s,'walls',cat,b); Bd.add(1,FR(x,t,0),'walls',cat,b); Bd.add(0,o?s:f,'walls',cat,b); }); };
  const wS=(row,xs)=>{ const b=Bd.blk++; for(let i=0;i<xs.length;i+=2){ const a=xs[i], c=xs[i+1]; Bd.add(0,FR(a,row,-1),'walls','wallLine',b); Bd.add(1,FR(a,row,0),'walls','wallLine',b); Bd.add(1,FR(c,row,0),'walls','wallLine',b); Bd.add(0,FR(c,row,-1),'walls','wallLine',b); } };
  const cP=pts=>{ const b=Bd.blk++; pts.forEach(p=>Bd.add(0,p,'walls','conn',b)); };
  for(let k=0;k<q;k++){ const r0=RW(k), T2=r0+2*q;
    eS('wallR',0,seq(r0+q-1,r0),-1);
    wS(r0,seq(1,n-2));
    eS('wallL',L,seq(r0,T2),L+1);
    cP([[L+1,T2,-1],[L+1,T2,-2],[L,T2,-2],[L-1,T2,-2]].map(a=>FR(...a)));
    wS(T2,seq(n-2,1));
    eS('wallR',0,seq(T2,r0+q+1),-1);
    if(k<q-1) cP(seq(r0+q+1,r0+3*q).map(t=>FR(0,t,-2)));
    else cP([...seq(-2,-(q+1)).map(z=>FR(0,r0+q+1,z)), ...seq(-(q+1),-2).map(z=>FR(0,r0+q,z))]);
  } }
function stageSigma(Bd){ Bd.mark('S');
  const rows=[]; for(let k=q-1;k>=0;k--) rows.push(RW(k)+q);
  const b=Bd.blk++, A=(h,p,cat)=>Bd.add(h,p,'special',cat,b);
  A(0,FR(0,rows[0],-1),'special'); A(1,FR(0,rows[0],0),'special');
  for(let i=1;i<rows.length;i++){ const s=rows[i-1], s2=rows[i];
    if(i%2===1){ A(0,FR(-1,s,0),'special'); A(0,FR(-2,s,0),'conn'); A(0,FR(-3,s,0),'conn'); for(let t=s-1;t>=s2;t--) A(0,FR(-3,t,0),'conn'); A(0,FR(-2,s2,0),'conn'); A(0,FR(-1,s2,0),'special'); }
    else { A(0,FR(0,s,-1),'special'); A(0,FR(0,s,-2),'conn'); A(0,FR(0,s,-3),'conn'); for(let t=s-1;t>=s2;t--) A(0,FR(0,t,-3),'conn'); A(0,FR(0,s2,-2),'conn'); A(0,FR(0,s2,-1),'special'); }
    A(1,FR(0,s2,0),'special'); }
  A(0,FR(0,rows[rows.length-1],-1),'special');
}
function binCells(k){ const r0=RW(k);
  const mk=xs=>{ const c=[]; xs.forEach((x,ci)=>{ const ts=seq(r0+1, r0+2*q-1); (ci%2===0?ts:ts.slice().reverse()).forEach(t=>c.push([x,L-t,0])); }); return c; };
  let c=mk(seq(1,n-2)); if((c[0][0]+c[0][1])%2) c=mk(seq(n-2,1)); return c; }
const BIN_CELLS=Array.from({length:q},(_,k)=>binCells(k));
const SIGMA_END=[L,L-q-1];   // column below the last P of Σ (canonical)

/* ---------------- game state ---------------- */
const PH_IDS=['A1','A2','A3','B1','B2','B3','B4','B5','B6','B7'];
const STORE='bl-proof-map-game-v1';
let saved={stars:{}}; try{ const s=JSON.parse(localStorage.getItem(STORE)||'null'); if(s&&s.stars) saved=s; }catch(e){}
const persist=()=>{ try{ localStorage.setItem(STORE, JSON.stringify(saved)); }catch(e){} };
function newState(li){ const lv=LEVELS[li], tail=tailBlocks(lv);
  return { li, lv, tail, cards:cardsFor(lv), ph:0, done:PH_IDS.map(()=>false), hints:PH_IDS.map(()=>0), autos:0, hintTotal:0, finished:false, impossible:false,
    A1:{B:'',n:'',T:'',Lam:''}, A2:{slots:{}, sel:null, bad:{}}, A3:{edge:'',face:'',inner:''},
    trail:[], tStart:null, tEnd:null, mirror:false, back:[], door:[], rows:[], wsub:1, spec:[],
    strIdx:0, asg:Object.fromEntries(tail.map(b=>[b.id, b.kind==='fill'? +b.id.slice(1)-1 : b.kind==='dummy'? lv.K+(+b.id.slice(1))-1 : -1])), selBlock:null,
    conns:tail.map(()=>({layer:null, path:[], full:null})), selConn:0, reveal:null, msg:null }; }
let S=newState(0);
const mx=x=>S.mirror? L-x : x;              // canonical <-> shown (an involution)
const tp=p=>S.mirror? [L-p[0],p[1],p[2]] : p;

/* tail layout: canonical cells of each tail block, consumed in string order */
function tailLayout(){ const used=new Array(q).fill(0), out=[];
  S.tail.forEach(b=>{ const k=S.asg[b.id]; if(k<0){ out.push(null); return; } const c=BIN_CELLS[k].slice(used[k], used[k]+b.size); used[k]+=b.size; out.push({cells:c, over:c.length<b.size, bin:k}); });
  return out; }
function binLoads(){ const l=new Array(q).fill(0); S.tail.forEach(b=>{ const k=S.asg[b.id]; if(k>=0) l[k]+=b.size; }); return l; }
/* linker endpoints, shown coordinates [x,y] */
function endpoints(){ const lay=tailLayout(); return S.tail.map((b,i)=>{ const prev = i===0 ? SIGMA_END : (lay[i-1] && lay[i-1].cells[lay[i-1].cells.length-1]);
  const nxt = lay[i] && lay[i].cells[0]; return { A: prev? [mx(prev[0]),prev[1]] : null, B: nxt? [mx(nxt[0]),nxt[1]] : null }; }); }
const maxLayers=()=>S.lv.layers || S.tail.length;
const needSteps=l=>LAM-5-2*l;   // drawn steps on layer l so that the linker has exactly Λ P's
function connCells3(i,useFull){ const c=S.conns[i], E=endpoints()[i]; if(c.layer==null||!E.A||!E.B) return [];
  const z=ZL(c.layer), o=[], path=(useFull&&c.full)||c.path;
  for(let zz=-2; zz>z; zz--) o.push([E.A[0],E.A[1],zz]);
  for(const p of path) o.push([p[0],p[1],z]);
  if(c.full) for(let zz=z+1; zz<=-2; zz++) o.push([E.B[0],E.B[1],zz]);
  return o; }

/* While you lay X₁, each edge you click is filled with its stretch of (PHP)…: an H on every site of the edge, the corners
   included once, and two P's sticking out of the cube beside each H. (Once the step is checked, the fold uses the trail of
   card 10; it has the same H sites.) */
function previewTrail(Bd){ const sites=[], seen=new Set(); let cur=S.tStart, lastStart=0;
  const push=p=>{ const k=K3(p); if(!seen.has(k)){ seen.add(k); sites.push(p); } };
  push(CORNER(cur));
  S.trail.forEach((key,j)=>{ const e=EDGES.find(x=>x.key===key), nxt= e.a===cur? e.b : e.a, A=CORNER(cur), B=CORNER(nxt); if(j===S.trail.length-1) lastStart=sites.length;
    for(let t=1;t<=L;t++) push([A[0]+(B[0]-A[0])*t/L, A[1]+(B[1]-A[1])*t/L, A[2]+(B[2]-A[2])*t/L]); cur=nxt; });
  const b=Bd.blk++, used=new Set(); let prevB=null;
  sites.forEach((h,i)=>{ if(i===lastStart) Bd.mark('last');
    const outs=Bd.out(h).filter(o=>!used.has(K3(o))), nextOuts=sites[i+1]? Bd.out(sites[i+1]) : [];
    const a=outs.find(o=>prevB&&adj(o,prevB)) || outs[0], bb=outs.find(o=>o!==a && nextOuts.some(x=>adj(o,x))) || outs.find(o=>o!==a);
    if(a){ used.add(K3(a)); Bd.add(0,a,'edges9','edge9',b); } Bd.add(1,h,'edges9','edge9',b); if(bb){ used.add(K3(bb)); Bd.add(0,bb,'edges9','edge9',b); } prevB=bb||a; }); }

/* the residues shown for the current state (shown coordinates) */
function buildResidues(ph){
  const Bd=new Builder(), d=S.done, at=i=>ph===i;
  try{
    if(d[3]) stageX1(Bd); else if(at(3) && S.trail.length) previewTrail(Bd);
    if(d[4]) stageBack(Bd, S.back.map(c=>tp([c[0],c[1],L])));
    else if(at(4) && S.back.length){ Bd.mark('X2p'); Bd.face('back','back',S.back.map(c=>tp([c[0],c[1],L]))); Bd.marks.last=Bd.marks.X2p+2*Math.min(S.backPrev||0,S.back.length); }
    if(d[5]) stageSides(Bd,true); else if(at(5)) stageSides(Bd,false);
    if(d[6]||(at(6)&&S.wsub>=2)) stageWalls(Bd);
    if(d[6]) stageSigma(Bd);
    if(d[7]||at(7)||at(8)||at(9)){
      const lay=tailLayout(), ep=endpoints(); Bd.mark('tail');
      S.tail.forEach((b,i)=>{ const L2=lay[i]; if(!L2) return;
        const routed = (d[8]||at(8)||at(9)) && S.conns[i].full;
        if(routed){ const bb=Bd.blk++; for(const p of connCells3(i,true)) Bd.add(0,tp(p),'route','conn',bb,{ci:i}); }
        const bb=Bd.blk++, c=L2.cells;
        for(let h=0;h+1<c.length;h+=2){ const a=c[h], e=c[h+1], ex={ti:i, gap: h===0 && !routed};
          Bd.add(0,[a[0],a[1],-1],'items',b.kind,bb,ex); Bd.add(1,a,'items',b.kind,bb,{ti:i}); Bd.add(1,e,'items',b.kind,bb,{ti:i}); Bd.add(0,[e[0],e[1],-1],'items',b.kind,bb,{ti:i}); } });
    }
  }catch(e){ console.error(e); }
  const res=Bd.r; if(S.mirror) for(const r of res) r.p=[L-r.p[0],r.p[1],r.p[2]];
  return {res, marks:Bd.marks};
}
function resColors(r){
  let hc=C.H, bc=C.edge;
  if(r.st==='items'){ const b=S.tail[r.ti]; hc=b.col; bc=b.col; }
  if(r.st==='route'){ bc=CPAL[r.ci%CPAL.length]; }
  return {hc,bc}; }

/* ---------------- 3D view ---------------- */
const BALL_R=0.38, P_R=0.25;
function mixc(a,b,t){ const h=x=>{ x=x.replace('#',''); const v=parseInt(x,16); return [v>>16&255,v>>8&255,v&255]; }; const A=h(a),B=h(b); return `rgb(${A.map((v,i)=>Math.round(v*(1-t)+B[i]*t)).join(',')})`; }
class GView{
  constructor(box){
    this.box=box; this.cv=document.createElement('canvas'); box.appendChild(this.cv); this.ctx=this.cv.getContext('2d');
    this.yaw=0.55; this.pitch=0.42; this.c=[L/2,L/2,L/2]; this.span=n+2; this.sc=null; this.xray=false; this.hideP=false; this.onPick=null; this.on=false; this.tw=null; this.cache={};
    let drag=null;
    box.addEventListener('pointerdown',e=>{ if(e.button!==0) return; drag={x:e.clientX,y:e.clientY,yaw:this.yaw,pitch:this.pitch,moved:false}; try{ box.setPointerCapture(e.pointerId); }catch(_){} });
    box.addEventListener('pointermove',e=>{ if(!drag) return; const dx=e.clientX-drag.x, dy=e.clientY-drag.y; if(!drag.moved && Math.hypot(dx,dy)<5) return; drag.moved=true; this.tw=null;
      this.yaw=drag.yaw+dx*0.008; this.pitch=Math.max(-1.45,Math.min(1.45,drag.pitch+dy*0.008)); this.request(); });
    box.addEventListener('pointerup',e=>{ if(drag && !drag.moved && this.onPick){ const r=box.getBoundingClientRect(); this.onPick(e.clientX-r.left, e.clientY-r.top); } drag=null; });
    box.addEventListener('pointercancel',()=>{ drag=null; });
    this.ro=new ResizeObserver(()=>this.resize());
  }
  start(){ if(this.on) return; this.on=true; this.ro.observe(this.box); this.resize(); }
  stop(){ this.on=false; this.ro.disconnect(); }
  setView(v,anim){ if(!anim){ this.yaw=v[0]; this.pitch=v[1]; this.tw=null; this.request(); return; }
    let dy=v[0]-this.yaw; dy=((dy+Math.PI)%(2*Math.PI)+2*Math.PI)%(2*Math.PI)-Math.PI;
    this.tw={y0:this.yaw,p0:this.pitch,dy,dp:v[1]-this.pitch,t0:performance.now()}; this.request(); }
  request(){ if(this.raf) return; this.raf=requestAnimationFrame(()=>{ this.raf=0; this.draw(); }); setTimeout(()=>{ if(this.raf){ cancelAnimationFrame(this.raf); this.raf=0; this.draw(); } }, 80); }
  resize(){ const r=this.box.getBoundingClientRect(); if(!r.width||!r.height) return; const d=Math.min(devicePixelRatio||1,2); this.dpr=d; this.W=r.width; this.H=r.height;
    this.cv.width=Math.round(r.width*d); this.cv.height=Math.round(r.height*d); this.ctx.setTransform(d,0,0,d,0,0); this.cache={}; this.draw(); }
  proj(p){ const x=p[0]-this.c[0], y=p[1]-this.c[1], z=p[2]-this.c[2]; const cy=Math.cos(this.yaw), sy=Math.sin(this.yaw), cp=Math.cos(this.pitch), s=Math.sin(this.pitch);
    const x1=-(x*cy+z*sy), z1=-x*sy+z*cy, y2=y*cp+z1*s, z2=-y*s+z1*cp; const D=this.span*2.6, k=D/Math.max(D*0.15,D+z2); return {x:this.W/2+this.S*x1*k, y:this.H/2-this.S*y2*k, z:z2, k}; }
  sprite(col,isH){ const key=col+(isH?'H':'P'); if(this.cache[key]) return this.cache[key];
    const R=Math.ceil(this.S*BALL_R*1.25*this.dpr)+2, sz=2*R+2, c=document.createElement('canvas'); c.width=c.height=sz; const g=c.getContext('2d'), m=sz/2;
    const gr=g.createRadialGradient(m-R*0.35,m-R*0.4,R*0.08,m,m,R);
    if(isH){ gr.addColorStop(0,mixc(col,'#ffffff',0.6)); gr.addColorStop(0.45,col); gr.addColorStop(1,mixc(col,'#000000',0.4)); g.fillStyle=gr; g.beginPath(); g.arc(m,m,R-1,0,7); g.fill(); }
    else { gr.addColorStop(0,'#ffffff'); gr.addColorStop(0.6,mixc(C.P,'#ffffff',0.88)); gr.addColorStop(1,mixc(C.P,'#ffffff',0.6)); g.fillStyle=gr; g.beginPath(); g.arc(m,m,R-1,0,7); g.fill(); g.strokeStyle=C.P; g.lineWidth=Math.max(1,R*0.08); g.stroke(); }
    return (this.cache[key]={c,R,sz}); }
  draw(){
    if(!this.on||!this.W) return; const ctx=this.ctx, sc=this.sc; ctx.clearRect(0,0,this.W,this.H);
    if(this.tw){ const t=Math.min(1,(performance.now()-this.tw.t0)/450), e=t<.5?2*t*t:1-Math.pow(-2*t+2,2)/2; this.yaw=this.tw.y0+this.tw.dy*e; this.pitch=this.tw.p0+this.tw.dp*e; if(t<1) this.request(); else this.tw=null; }
    this.S=Math.min(this.W,this.H)/(this.span*1.3); if(!sc) return;
    let lim=Infinity; if(sc.reveal){ const t=(performance.now()-sc.reveal.t0)/sc.reveal.dur; if(t<1){ lim=sc.reveal.from+(sc.reveal.to-sc.reveal.from)*t; this.request(); } else sc.reveal=null; }
    const m=L, E=[[0,0,0],[m,0,0],[m,m,0],[0,m,0],[0,0,m],[m,0,m],[m,m,m],[0,m,m]].map(p=>this.proj(p));
    ctx.strokeStyle=C.rule; ctx.lineWidth=1; [[0,1],[1,2],[2,3],[3,0],[4,5],[5,6],[6,7],[7,4],[0,4],[1,5],[2,6],[3,7]].forEach(([a,b])=>{ ctx.beginPath(); ctx.moveTo(E[a].x,E[a].y); ctx.lineTo(E[b].x,E[b].y); ctx.stroke(); });
    const items=[], xr=this.xray, hp=this.hideP;
    for(const p of sc.ghosts){ const P=this.proj(p); items.push({z:P.z,k:2,P}); }
    for(const b of sc.bonds){ if(b.i>=lim) continue; if(b.hasP&&(hp||xr)) continue; if(b.inner&&!xr) continue; const A=this.proj(b.a), B=this.proj(b.b); items.push({z:Math.max(A.z,B.z)+0.02,k:1,A,B,b}); }
    for(const b of sc.balls){ if(b.i>=lim) continue; if(!b.h&&(hp||xr)) continue; if(b.inner&&!xr) continue; const P=this.proj(b.p); items.push({z:P.z,k:0,P,b}); }
    for(const mk of sc.marks){ const P=this.proj(mk.p); items.push({z:P.z-0.05,k:3,P,mk}); }
    items.sort((u,v)=>v.z-u.z);
    const dotR=Math.max(1.1,this.S*0.055);
    for(const it of items){
      if(it.k===2){ ctx.globalAlpha=0.9; ctx.fillStyle=C.ghost; ctx.beginPath(); ctx.arc(it.P.x,it.P.y,dotR*it.P.k,0,7); ctx.fill(); }
      else if(it.k===1){ const b=it.b; ctx.globalAlpha=xr&&!b.inner?0.08:b.al; ctx.strokeStyle=b.col; ctx.lineCap='round'; ctx.lineWidth=Math.max(1,this.S*b.w*it.A.k); ctx.beginPath(); ctx.moveTo(it.A.x,it.A.y); ctx.lineTo(it.B.x,it.B.y); ctx.stroke(); }
      else if(it.k===0){ const b=it.b, s=this.sprite(b.h?b.col:'#fff',b.h); ctx.globalAlpha= xr&&!b.inner ? 0.1 : b.al; const w=2*this.S*(b.h?BALL_R:P_R)*1.25*it.P.k*(s.sz/(2*s.R)); ctx.drawImage(s.c, it.P.x-w/2, it.P.y-w/2, w, w); }
      else { const mk=it.mk, r=this.S*(mk.r||0.3)*it.P.k; ctx.globalAlpha=mk.al==null?1:mk.al; if(mk.ring){ ctx.strokeStyle=mk.col; ctx.lineWidth=mk.lw||2; if(mk.dash) ctx.setLineDash([4,3]); ctx.beginPath(); ctx.arc(it.P.x,it.P.y,r,0,7); ctx.stroke(); ctx.setLineDash([]); } else { ctx.fillStyle=mk.col; ctx.beginPath(); if(mk.sq) ctx.rect(it.P.x-r,it.P.y-r,2*r,2*r); else ctx.arc(it.P.x,it.P.y,r,0,7); ctx.fill(); } }
    }
    ctx.globalAlpha=1;
    for(const ln of sc.lines){ const A=this.proj(ln.a), B=this.proj(ln.b); ctx.globalAlpha=ln.al==null?1:ln.al; ctx.strokeStyle=ln.col; ctx.lineWidth=ln.w||2; ctx.lineCap='round'; if(ln.dash) ctx.setLineDash(ln.dash); ctx.beginPath(); ctx.moveTo(A.x,A.y); ctx.lineTo(B.x,B.y); ctx.stroke(); ctx.setLineDash([]); }
    ctx.globalAlpha=1;
    for(const lb of sc.labels){ const P=this.proj(lb.p); ctx.font='500 12px "Inter", system-ui, sans-serif'; const w=ctx.measureText(lb.text).width+10;
      const x=Math.max(4,Math.min(this.W-w-4,P.x+(lb.dx||0)-w/2)), y=Math.max(4,Math.min(this.H-22,P.y+(lb.dy||0)-10));
      ctx.fillStyle=lb.bg||C.bgElev; ctx.globalAlpha=0.94; ctx.fillRect(x,y,w,19); ctx.globalAlpha=1; ctx.fillStyle=lb.col||C.ink; ctx.textBaseline='middle'; ctx.fillText(lb.text,x+5,y+10); }
  }
  pickPoint(mx_,my_,pts,rad){ let best=-1, bd=1e9, bz=1e9; pts.forEach((p,i)=>{ const P=this.proj(p), d=Math.hypot(P.x-mx_,P.y-my_), R=rad||Math.max(9,this.S*0.55*P.k); if(d<=R && (d<bd-2 || (Math.abs(d-bd)<=2 && P.z<bz))){ best=i; bd=d; bz=P.z; } }); return best; }
  pickSeg(mx_,my_,segs){ let best=-1, bd=14; segs.forEach(([a,b],i)=>{ const A=this.proj(a), B=this.proj(b), vx=B.x-A.x, vy=B.y-A.y, l2=vx*vx+vy*vy||1; let t=((mx_-A.x)*vx+(my_-A.y)*vy)/l2; t=Math.max(0,Math.min(1,t)); const d=Math.hypot(A.x+t*vx-mx_, A.y+t*vy-my_); if(d<bd){ bd=d; best=i; } }); return best; }
}

/* ---------------- 3D view, WebGL ----------------
   Same look as the Mathathon site's fold game (src/widgets/fold-game/render/three3d-scene.ts): instanced spheres with
   H filled and P pale with a ring, backbone cylinders, faint lattice points, translucent "ghost" spheres for the sites
   you can click. Same interface as GView; if three.js or WebGL is unavailable, GView's 2D drawing is used instead.
   The 2D canvas stays on top and carries the overlays (selected edges, paths, rings and labels). */
const R_RES=0.3, R_P=0.26, R_BOND=0.075, FOV=30;
const GLSL_LIGHT=`
vec3 fg3Shade(vec3 base, vec3 n, vec3 v, float spec, float flat_) {
  vec3 L = normalize(vec3(-0.45, 0.7, 0.55));
  float d = max(dot(n, L), 0.0);
  float hemi = 0.5 + 0.5 * n.y;
  float lit = min(0.6 + 0.12 * hemi + 0.5 * d, 1.15);
  vec3 col = base * mix(lit, 1.0, flat_);
  vec3 h = normalize(L + v);
  col += spec * pow(max(dot(n, h), 0.0), 42.0);
  return col;
}`;
const RES_VS=`attribute float aKind; attribute vec3 aCol; attribute float aDim;
varying vec3 vN; varying vec3 vV; varying float vKind; varying vec3 vCol; varying float vDim;
void main(){ vKind=aKind; vCol=aCol; vDim=aDim; vec4 mv=modelViewMatrix*instanceMatrix*vec4(position,1.0); vN=normalize(normalMatrix*mat3(instanceMatrix)*normal); vV=-mv.xyz; gl_Position=projectionMatrix*mv; }`;
const RES_FS=`uniform vec3 uP; uniform vec3 uPFill; uniform vec3 uBg;
varying vec3 vN; varying vec3 vV; varying float vKind; varying vec3 vCol; varying float vDim;
${GLSL_LIGHT}
void main(){ vec3 n=normalize(vN), v=normalize(vV); float ndv=clamp(dot(n,v),0.0,1.0); vec3 col;
  if(vKind<0.5){ col=fg3Shade(vCol,n,v,0.16,0.0); col*=mix(0.8,1.0,smoothstep(0.0,0.42,ndv)); }
  else if(vKind<1.5){ float ring=1.0-smoothstep(0.44,0.6,ndv); col=fg3Shade(mix(uPFill,uP,ring),n,v,0.06,0.45); }
  else { col=fg3Shade(vCol,n,v,0.1,0.25); }
  col=mix(col,uBg,vDim); gl_FragColor=vec4(col,1.0);
  #include <colorspace_fragment>
}`;
const SEG_VS=`uniform float uRadius; uniform float uMinPx; uniform float uPxWorld; attribute vec3 aCol; attribute float aDim;
varying vec3 vN; varying vec3 vV; varying vec3 vCol; varying float vDim;
void main(){ vCol=aCol; vDim=aDim; vec4 axis=modelViewMatrix*instanceMatrix*vec4(0.0,position.y,0.0,1.0); float px=uPxWorld*max(-axis.z,1e-3); float r=max(uRadius,0.5*uMinPx*px);
  vec4 mv=modelViewMatrix*instanceMatrix*vec4(position.x*r,position.y,position.z*r,1.0); vN=normalize(normalMatrix*mat3(instanceMatrix)*normal); vV=-mv.xyz; gl_Position=projectionMatrix*mv; }`;
const SEG_FS=`uniform vec3 uBg; varying vec3 vN; varying vec3 vV; varying vec3 vCol; varying float vDim;
${GLSL_LIGHT}
void main(){ vec3 col=fg3Shade(vCol,normalize(vN),normalize(vV),0.12,0.0); col=mix(col,uBg,vDim); gl_FragColor=vec4(col,1.0);
  #include <colorspace_fragment>
}`;
const GHOST_VS=`attribute vec3 aCol; varying vec3 vN; varying vec3 vV; varying vec3 vCol;
void main(){ vCol=aCol; vec4 mv=modelViewMatrix*instanceMatrix*vec4(position,1.0); vN=normalize(normalMatrix*mat3(instanceMatrix)*normal); vV=-mv.xyz; gl_Position=projectionMatrix*mv; }`;
const GHOST_FS=`uniform float uFill; uniform float uRing; varying vec3 vN; varying vec3 vV; varying vec3 vCol;
void main(){ float ndv=clamp(dot(normalize(vN),normalize(vV)),0.0,1.0); float ring=1.0-smoothstep(0.36,0.62,ndv); gl_FragColor=vec4(vCol,mix(uFill,uRing,ring));
  #include <colorspace_fragment>
}`;
const DOT_VS=`uniform float uSize; uniform float uPxWorld; uniform float uDpr;
void main(){ vec4 mv=modelViewMatrix*vec4(position,1.0); gl_PointSize=uDpr*clamp(uSize/(uPxWorld*max(-mv.z,1e-3)),1.6,9.0); gl_Position=projectionMatrix*mv; }`;
const DOT_FS=`uniform vec3 uColor; uniform float uOpacity;
void main(){ float d=length(gl_PointCoord-0.5); float a=1.0-smoothstep(0.32,0.5,d); if(a<=0.0) discard; gl_FragColor=vec4(uColor,uOpacity*a);
  #include <colorspace_fragment>
}`;
class GLView extends GView{
  constructor(box){ super(box); this.ready=false; this.zoom=1; this.built=null;
    Object.assign(this.cv.style,{position:'absolute',inset:'0',pointerEvents:'none'});
    box.addEventListener('wheel',e=>{ if(!this.ready) return; e.preventDefault(); this.zoom=Math.max(0.6,Math.min(2,this.zoom*Math.exp(e.deltaY*0.0012))); this.request(); },{passive:false});
    try{ this.initGL(THREE); }catch(e){ console.warn('Fold it yourself: WebGL unavailable, using the 2D view.', e); } }
  initGL(T){
    this.T=T; const r=new T.WebGLRenderer({antialias:true, alpha:true}); r.setClearColor(0x000000,0); r.setPixelRatio(Math.min(devicePixelRatio||1,2));
    Object.assign(r.domElement.style,{position:'absolute',inset:'0',width:'100%',height:'100%',display:'block'}); this.box.insertBefore(r.domElement,this.cv);
    this.r=r; this.scene=new T.Scene(); this.cam=new T.PerspectiveCamera(FOV,1,0.1,4000);
    this.U={uPxWorld:{value:0.01}};
    this.colors();
    this.resMat=new T.ShaderMaterial({vertexShader:RES_VS, fragmentShader:RES_FS, uniforms:{uP:{value:this.col.P}, uPFill:{value:this.col.PFill}, uBg:{value:this.col.bg}}});
    this.segMat=new T.ShaderMaterial({vertexShader:SEG_VS, fragmentShader:SEG_FS, uniforms:{uRadius:{value:R_BOND}, uMinPx:{value:2.0}, uPxWorld:this.U.uPxWorld, uBg:{value:this.col.bg}}});
    this.ghostMat=new T.ShaderMaterial({vertexShader:GHOST_VS, fragmentShader:GHOST_FS, uniforms:{uFill:{value:0.12}, uRing:{value:0.8}}, transparent:true, depthWrite:false});
    this.dotMat=new T.ShaderMaterial({vertexShader:DOT_VS, fragmentShader:DOT_FS, uniforms:{uColor:{value:this.col.lattice}, uOpacity:{value:0.9}, uSize:{value:0.075}, uPxWorld:this.U.uPxWorld, uDpr:{value:r.getPixelRatio()}}, transparent:true, depthWrite:false});
    this.meshes={}; this.dots=new T.Points(new T.BufferGeometry(), this.dotMat); this.dots.frustumCulled=false; this.scene.add(this.dots);
    { // a grid on the floor under the cube, as on the site's board
      const pts=[], y=-1.5, a=-2, b=L+2; for(let k=a;k<=b;k++) pts.push(k,y,a, k,y,b, a,y,k, b,y,k);
      const g=new T.BufferGeometry(); g.setAttribute('position',new T.Float32BufferAttribute(pts,3));
      this.floorMat=new T.LineBasicMaterial({color:this.col.lattice}); this.floor=new T.LineSegments(g,this.floorMat); this.floor.frustumCulled=false; this.scene.add(this.floor); }
    this._v=new T.Vector3(); this._w=new T.Vector3(); this._a=new T.Vector3(); this._m=new T.Matrix4(); this._q=new T.Quaternion(); this._s=new T.Vector3(); this._Y=new T.Vector3(0,1,0); this._c=new T.Color();
    this.ready=true; this.resize(); }
  colors(){ const T=this.T, c=s=>{ const k=new T.Color(); try{ k.setStyle(s); }catch(_){ k.setStyle('#888888'); } return k; };
    const bgE=c(C.bgElev||'#ffffff'), p=c(C.P||'#4f7aa3'); this.col={P:p, PFill:bgE.clone().lerp(p,0.14), bg:c(C.board||'#f2f0eb'), lattice:c(C.ghost||'#d8d4cb')};
    if(this.resMat){ this.resMat.uniforms.uP.value=this.col.P; this.resMat.uniforms.uPFill.value=this.col.PFill; this.resMat.uniforms.uBg.value=this.col.bg; this.segMat.uniforms.uBg.value=this.col.bg; this.dotMat.uniforms.uColor.value=this.col.lattice; } if(this.floorMat) this.floorMat.color=this.col.lattice; }
  themeChanged(){ if(!this.ready) return; this.colors(); this.built=null; this.request(); }
  resize(){ super.resize(); if(!this.ready||!this.W) return; this.r.setSize(this.W,this.H,false); this.cam.aspect=this.W/this.H; this.cam.updateProjectionMatrix(); this.draw(); }
  /* an instanced mesh with its own geometry (instanced attributes live on the geometry), grown when needed */
  inst(key,mat,count,attrs,segs){ const T=this.T; let m=this.meshes[key];
    if(!m || m.userData.cap<count){ if(m){ this.scene.remove(m); m.geometry.dispose(); m.dispose&&m.dispose(); }
      const cap=Math.max(16,Math.ceil(count*1.25)), geo= segs==='cyl' ? new T.CylinderGeometry(1,1,1,8,1,true) : new T.SphereGeometry(1,segs||14,segs?Math.round(segs*0.7):10);
      for(const [nm,sz] of attrs) geo.setAttribute(nm,new T.InstancedBufferAttribute(new Float32Array(cap*sz),sz));
      m=new T.InstancedMesh(geo,mat,cap); m.userData.cap=cap; m.frustumCulled=false; m.instanceMatrix.setUsage(T.DynamicDrawUsage); this.scene.add(m); this.meshes[key]=m; }
    m.count=count; return m; }
  build(){ const sc=this.sc, xr=this.xray, hp=this.hideP, M=this._m, Q=this._q, S3=this._s, V=this._v, W2=this._w, col=this._c, T=this.T;
    const setC=(arr,j,s)=>{ try{ col.setStyle(s); }catch(_){ col.setStyle('#888888'); } arr[3*j]=col.r; arr[3*j+1]=col.g; arr[3*j+2]=col.b; };
    const balls=sc.balls.filter(b=>!((!b.h&&(hp||xr)) || (b.inner&&!xr)));
    const mr=this.inst('res',this.resMat,balls.length,[['aKind',1],['aCol',3],['aDim',1]], balls.length>2500?10:14), kA=mr.geometry.getAttribute('aKind'), cA=mr.geometry.getAttribute('aCol'), dA=mr.geometry.getAttribute('aDim');
    balls.forEach((b,j)=>{ const rad=b.h?R_RES:R_P; M.makeScale(rad,rad,rad).setPosition(b.p[0],b.p[1],b.p[2]); mr.setMatrixAt(j,M); kA.array[j]=b.h?0:1; setC(cA.array,j,b.col||'#c4532f');
      let dim=1-Math.min(1,b.al==null?1:b.al); if(xr&&!b.inner) dim=Math.max(dim,0.9); dA.array[j]=Math.min(0.93,dim); });
    mr.instanceMatrix.needsUpdate=true; kA.needsUpdate=cA.needsUpdate=dA.needsUpdate=true; this.ballIdx=balls.map(b=>b.i);
    const bonds=sc.bonds.filter(b=>!((b.hasP&&(hp||xr)) || (b.inner&&!xr)));
    const mb=this.inst('bond',this.segMat,bonds.length,[['aCol',3],['aDim',1]],'cyl'), bc=mb.geometry.getAttribute('aCol'), bd=mb.geometry.getAttribute('aDim');
    bonds.forEach((b,j)=>{ V.set(b.a[0],b.a[1],b.a[2]); W2.set(b.b[0],b.b[1],b.b[2]); const len=V.distanceTo(W2); W2.sub(V).normalize(); Q.setFromUnitVectors(this._Y,W2);
      V.set((b.a[0]+b.b[0])/2,(b.a[1]+b.b[1])/2,(b.a[2]+b.b[2])/2); S3.set(1,len,1); M.compose(V,Q,S3); mb.setMatrixAt(j,M);
      setC(bc.array,j,b.col||'#6d6d78'); let dim=b.al<0.2?0.9:0; if(xr&&!b.inner) dim=0.92; bd.array[j]=dim; });
    mb.instanceMatrix.needsUpdate=true; bc.needsUpdate=bd.needsUpdate=true; this.bondIdx=bonds.map(b=>b.i);
    const solid=sc.marks.filter(m=>!m.ring), ghost=sc.marks.filter(m=>m.ring&&m.ghost);
    const mm=this.inst('mark',this.resMat,solid.length,[['aKind',1],['aCol',3],['aDim',1]],12), mk=mm.geometry.getAttribute('aKind'), mc=mm.geometry.getAttribute('aCol'), md=mm.geometry.getAttribute('aDim');
    solid.forEach((m,j)=>{ const rad=Math.min(0.42,(m.r||0.3)); M.makeScale(rad,rad,rad).setPosition(m.p[0],m.p[1],m.p[2]); mm.setMatrixAt(j,M); mk.array[j]=2; setC(mc.array,j,m.col); md.array[j]=m.al!=null&&m.al<1?(1-m.al)*0.6:0; });
    mm.instanceMatrix.needsUpdate=true; mk.needsUpdate=mc.needsUpdate=md.needsUpdate=true;
    const mg=this.inst('ghost',this.ghostMat,ghost.length,[['aCol',3]],18), gc=mg.geometry.getAttribute('aCol');
    ghost.forEach((m,j)=>{ M.makeScale(0.21,0.21,0.21).setPosition(m.p[0],m.p[1],m.p[2]); mg.setMatrixAt(j,M); setC(gc.array,j,m.col); });
    mg.instanceMatrix.needsUpdate=true; gc.needsUpdate=true; mg.renderOrder=5;
    const dp=new Float32Array(sc.ghosts.length*3); sc.ghosts.forEach((p,j)=>{ dp[3*j]=p[0]; dp[3*j+1]=p[1]; dp[3*j+2]=p[2]; });
    this.dots.geometry.dispose(); this.dots.geometry=new T.BufferGeometry(); this.dots.geometry.setAttribute('position',new T.BufferAttribute(dp,3));
    this.built={sc, xr, hp}; }
  camUpdate(){ const t=this._a.set(this.c[0],this.c[1],this.c[2]), cp=Math.cos(this.pitch), half=Math.tan(FOV*Math.PI/360), asp=this.W/this.H;
    this.dist=(this.span*0.5)/(half*Math.min(1,asp))*1.32*this.zoom;
    this.cam.position.set(t.x+Math.sin(this.yaw)*cp*this.dist, t.y+Math.sin(this.pitch)*this.dist, t.z-Math.cos(this.yaw)*cp*this.dist);
    this.cam.up.set(0,1,0); this.cam.lookAt(t); this.cam.updateMatrixWorld(); this.S=this.H/(2*this.dist*half); this.U.uPxWorld.value=2*half/this.H; }
  proj(p){ if(!this.ready) return super.proj(p); const v=this._w.set(p[0],p[1],p[2]); const d=v.distanceTo(this.cam.position); v.project(this.cam); return {x:(v.x+1)/2*this.W, y:(1-v.y)/2*this.H, z:v.z, k:this.dist/Math.max(d,1e-3)}; }
  draw(){
    if(!this.ready) return super.draw(); if(!this.on||!this.W) return; const sc=this.sc;
    if(this.tw){ const t=Math.min(1,(performance.now()-this.tw.t0)/450), e=t<.5?2*t*t:1-Math.pow(-2*t+2,2)/2; this.yaw=this.tw.y0+this.tw.dy*e; this.pitch=this.tw.p0+this.tw.dp*e; if(t<1) this.request(); else this.tw=null; }
    this.camUpdate(); const ctx=this.ctx; ctx.clearRect(0,0,this.W,this.H); if(!sc){ this.r.render(this.scene,this.cam); return; }
    if(!this.built || this.built.sc!==sc || this.built.xr!==this.xray || this.built.hp!==this.hideP) this.build();
    let lim=Infinity; if(sc.reveal){ const t=(performance.now()-sc.reveal.t0)/sc.reveal.dur; if(t<1){ lim=sc.reveal.from+(sc.reveal.to-sc.reveal.from)*t; this.request(); } else sc.reveal=null; }
    const upto=arr=>{ if(lim===Infinity) return arr.length; let lo=0, hi=arr.length; while(lo<hi){ const m=(lo+hi)>>1; if(arr[m]<lim) lo=m+1; else hi=m; } return lo; };
    this.meshes.res.count=upto(this.ballIdx); this.meshes.bond.count=upto(this.bondIdx);
    this.r.render(this.scene,this.cam);
    // overlays on the 2D canvas: cube frame, selected edges and paths, rings, labels
    const m=L, E=[[0,0,0],[m,0,0],[m,m,0],[0,m,0],[0,0,m],[m,0,m],[m,m,m],[0,m,m]].map(p=>this.proj(p));
    ctx.globalAlpha=0.8; ctx.strokeStyle=C.rule; ctx.lineWidth=1; [[0,1],[1,2],[2,3],[3,0],[4,5],[5,6],[6,7],[7,4],[0,4],[1,5],[2,6],[3,7]].forEach(([a,b])=>{ ctx.beginPath(); ctx.moveTo(E[a].x,E[a].y); ctx.lineTo(E[b].x,E[b].y); ctx.stroke(); });
    for(const ln of sc.lines){ const A=this.proj(ln.a), B=this.proj(ln.b); ctx.globalAlpha=ln.al==null?1:ln.al; ctx.strokeStyle=ln.col; ctx.lineWidth=ln.w||2; ctx.lineCap='round'; if(ln.dash) ctx.setLineDash(ln.dash); ctx.beginPath(); ctx.moveTo(A.x,A.y); ctx.lineTo(B.x,B.y); ctx.stroke(); ctx.setLineDash([]); }
    for(const mk of sc.marks){ if(!mk.ring||mk.ghost) continue; const P=this.proj(mk.p), r=this.S*(mk.r||0.3)*P.k; ctx.globalAlpha=mk.al==null?1:mk.al; ctx.strokeStyle=mk.col; ctx.lineWidth=mk.lw||2; if(mk.dash) ctx.setLineDash([4,3]); ctx.beginPath(); ctx.arc(P.x,P.y,r,0,7); ctx.stroke(); ctx.setLineDash([]); }
    ctx.globalAlpha=1;
    for(const lb of sc.labels){ const P=this.proj(lb.p); ctx.font='600 12px "Inter", system-ui, sans-serif'; const w=ctx.measureText(lb.text).width+12;
      const x=Math.max(4,Math.min(this.W-w-4,P.x+(lb.dx||0)-w/2)), y=Math.max(4,Math.min(this.H-24,P.y+(lb.dy||0)-11));
      ctx.fillStyle=lb.bg||C.bgElev; ctx.strokeStyle=C.rule; ctx.lineWidth=1; ctx.beginPath(); if(ctx.roundRect) ctx.roundRect(x,y,w,21,4); else ctx.rect(x,y,w,21); ctx.fill(); if(!lb.bg) ctx.stroke(); ctx.fillStyle=lb.col||C.ink; ctx.textBaseline='middle'; ctx.fillText(lb.text,x+6,y+11); }
    { // axis gizmo, bottom left (site: .fg3-gizmo)
      const e=this.cam.matrixWorldInverse.elements, ox=30, oy=this.H-30, len=17; ctx.globalAlpha=1; ctx.lineWidth=1.5; ctx.lineCap='round'; ctx.font='600 10px "Inter", system-ui, sans-serif'; ctx.textBaseline='middle'; ctx.textAlign='center';
      [['x',[1,0,0]],['y',[0,1,0]],['z',[0,0,1]]].forEach(([nm,d])=>{ const vx=e[0]*d[0]+e[4]*d[1]+e[8]*d[2], vy=e[1]*d[0]+e[5]*d[1]+e[9]*d[2];
        ctx.strokeStyle=C.muted; ctx.beginPath(); ctx.moveTo(ox,oy); ctx.lineTo(ox+vx*len,oy-vy*len); ctx.stroke(); ctx.fillStyle=C.muted; ctx.fillText(nm,ox+vx*(len+7),oy-vy*(len+7)); });
      ctx.textAlign='left'; }
  }
}

/* ---------------- routing map (plan view of the layers under the front face) ---------------- */
const MX0=-8, MX1=19, NC=MX1-MX0+1;
class MapView{
  constructor(box){ this.box=box; this.cv=document.createElement('canvas'); box.appendChild(this.cv); this.ctx=this.cv.getContext('2d'); this.hover=null; this.onCell=null;
    this.cv.addEventListener('click',e=>{ const c=this.cellAt(e); if(c&&this.onCell) this.onCell(c); });
    this.cv.addEventListener('mousemove',e=>{ const c=this.cellAt(e); if((c&&!this.hover)||(!c&&this.hover)||(c&&this.hover&&(c[0]!==this.hover[0]||c[1]!==this.hover[1]))){ this.hover=c; this.draw(); } });
    this.cv.addEventListener('mouseleave',()=>{ this.hover=null; this.draw(); });
    this.ro=new ResizeObserver(()=>this.resize()); this.ro.observe(box); }
  resize(){ const r=this.box.getBoundingClientRect(); if(!r.width) return; const d=Math.min(devicePixelRatio||1,2); this.W=r.width; this.H=r.height; this.cv.width=Math.round(r.width*d); this.cv.height=Math.round(r.height*d); this.ctx.setTransform(d,0,0,d,0,0); this.draw(); }
  cellAt(e){ const r=this.cv.getBoundingClientRect(), cs=r.width/NC, x=MX1-Math.floor((e.clientX-r.left)/cs), y=MX1-Math.floor((e.clientY-r.top)/cs); return (x>=MX0&&x<=MX1&&y>=MX0&&y<=MX1)? [x,y] : null; }
  draw(){ if(!this.W) return; const ctx=this.ctx, cs=this.W/NC, X=x=>(MX1-x+0.5)*cs, Y=y=>(MX1-y+0.5)*cs; ctx.clearRect(0,0,this.W,this.H);
    ctx.fillStyle=C.bgElev; ctx.fillRect(0,0,this.W,this.H);
    ctx.strokeStyle=C.rule; ctx.globalAlpha=0.5; ctx.lineWidth=1; for(let i=0;i<=NC;i++){ ctx.beginPath(); ctx.moveTo(i*cs,0); ctx.lineTo(i*cs,this.H); ctx.stroke(); ctx.beginPath(); ctx.moveTo(0,i*cs); ctx.lineTo(this.W,i*cs); ctx.stroke(); }
    ctx.globalAlpha=1; ctx.fillStyle=C.board; ctx.strokeStyle=C.conn; ctx.fillRect(X(L)-cs/2,Y(L)-cs/2,n*cs,n*cs); ctx.strokeRect(X(L)-cs/2,Y(L)-cs/2,n*cs,n*cs);
    const lay=tailLayout(); lay.forEach((t,i)=>{ if(!t) return; ctx.fillStyle=S.tail[i].col; ctx.globalAlpha=0.28; for(const c of t.cells) ctx.fillRect(X(mx(c[0]))-cs/2+1,Y(c[1])-cs/2+1,cs-2,cs-2); }); ctx.globalAlpha=1;
    ctx.fillStyle=C.muted; ctx.font=`500 ${Math.max(9,cs*0.6)}px "Inter", system-ui, sans-serif`; ctx.textBaseline='bottom'; ctx.fillText('front face (seen from the front)', X(L)-cs/2, Y(L)-cs/2-2);
    const sel=S.selConn, cur=S.conns[sel], lay3=cur.layer||1, ep=endpoints(), bad=routeConflicts();
    // obstacles on the current layer: shafts that pass through it
    ep.forEach((E,j)=>{ if(j===sel||!E.A) return; const c=S.conns[j]; if(c.layer!=null && c.layer<lay3) return; for(const P of [E.A,E.B]){ if(!P) continue; ctx.fillStyle=C.ink; ctx.beginPath(); ctx.arc(X(P[0]),Y(P[1]),cs*0.18,0,7); ctx.fill(); } });
    // paths
    const drawPath=(pts,col,w,al,dash)=>{ if(pts.length<2) return; ctx.globalAlpha=al; ctx.strokeStyle=col; ctx.lineWidth=w; ctx.lineJoin='round'; ctx.lineCap='round'; if(dash) ctx.setLineDash(dash); ctx.beginPath(); pts.forEach((p,i)=>i?ctx.lineTo(X(p[0]),Y(p[1])):ctx.moveTo(X(p[0]),Y(p[1]))); ctx.stroke(); ctx.setLineDash([]); ctx.globalAlpha=1; };
    S.conns.forEach((c,j)=>{ if(j===sel||c.layer==null) return; const col=CPAL[j%CPAL.length];
      if(c.layer===lay3){ if(c.full) drawPath(c.full,col,cs*0.16,0.45); drawPath(c.path,col,cs*0.32,0.9); } else drawPath(c.path,col,Math.max(1,cs*0.08),0.35,[3,3]); });
    const scol=CPAL[sel%CPAL.length];
    if(cur.full) drawPath(cur.full,scol,cs*0.16,0.5);
    drawPath(cur.path,scol,cs*0.42,1);
    // endpoints
    ep.forEach((E,j)=>{ const col=CPAL[j%CPAL.length], big=j===sel; ctx.globalAlpha= big?1:0.85;
      if(E.A){ ctx.fillStyle=col; ctx.beginPath(); ctx.arc(X(E.A[0]),Y(E.A[1]),cs*(big?0.42:0.32),0,7); ctx.fill(); }
      if(E.B){ ctx.fillStyle=C.bgElev; ctx.strokeStyle=col; ctx.lineWidth=big?3:2; const r=cs*(big?0.36:0.28); ctx.fillRect(X(E.B[0])-r,Y(E.B[1])-r,2*r,2*r); ctx.strokeRect(X(E.B[0])-r,Y(E.B[1])-r,2*r,2*r); }
      if(bad.has(j)&&E.A){ ctx.strokeStyle=C.bad; ctx.lineWidth=2; ctx.beginPath(); ctx.arc(X(E.A[0]),Y(E.A[1]),cs*0.6,0,7); ctx.stroke(); }
      ctx.globalAlpha=1; ctx.fillStyle= '#fff'; ctx.font=`600 ${Math.max(8,cs*0.45)}px "JetBrains Mono", monospace`; ctx.textAlign='center'; ctx.textBaseline='middle'; if(E.A) ctx.fillText(String(j+1),X(E.A[0]),Y(E.A[1])+0.5); ctx.fillStyle=col; if(E.B) ctx.fillText(String(j+1),X(E.B[0]),Y(E.B[1])+0.5); ctx.textAlign='left'; });
    // hover preview
    const hv=this.hover; if(hv && cur.path.length){ const last=cur.path[cur.path.length-1]; if((hv[0]===last[0])!==(hv[1]===last[1])){ const r=walkLine(sel,last,hv); ctx.globalAlpha=0.6; ctx.strokeStyle= r.ok? scol : C.bad; ctx.lineWidth=cs*0.2; ctx.setLineDash([4,4]); ctx.beginPath(); ctx.moveTo(X(last[0]),Y(last[1])); ctx.lineTo(X(hv[0]),Y(hv[1])); ctx.stroke(); ctx.setLineDash([]); ctx.globalAlpha=1; } }
    if(hv){ ctx.strokeStyle=C.ink; ctx.lineWidth=1; ctx.strokeRect(X(hv[0])-cs/2+0.5,Y(hv[1])-cs/2+0.5,cs-1,cs-1); }
  }
}
/* obstacles for linker i on layer l: other linkers' cells on l, and the shafts that pass through l */
function obstacles(i,l){ const o=new Set(), ep=endpoints();
  S.conns.forEach((c,j)=>{ if(j===i) return; const E=ep[j];
    if(c.layer===l) for(const p of (c.full||c.path)) o.add(K2(p[0],p[1]));
    if(c.layer==null || c.layer>=l){ if(E.A) o.add(K2(E.A[0],E.A[1])); if(E.B) o.add(K2(E.B[0],E.B[1])); } });
  return o; }
function walkLine(i,from,to){ const c=S.conns[i], l=c.layer||1, ob=obstacles(i,l), own=new Set(c.path.map(p=>K2(p[0],p[1]))), E=endpoints()[i];
  const dx=Math.sign(to[0]-from[0]), dy=Math.sign(to[1]-from[1]), cells=[]; let x=from[0], y=from[1];
  while(x!==to[0]||y!==to[1]){ x+=dx; y+=dy; const k=K2(x,y); if(ob.has(k)) return {ok:false, cells, block:[x,y], why:'shaft'}; if(own.has(k)) return {ok:false, cells, block:[x,y], why:'self'}; cells.push([x,y]); if(x===E.B[0]&&y===E.B[1]) break; }
  return {ok:true, cells}; }
function padPath(cells,need,blocked){ const p=cells.slice(); let extra=need-(p.length-1); if(extra<0||extra%2) return null; let guard=0;
  while(extra>0 && guard++<60){ const own=new Set(p.map(c=>K2(c[0],c[1]))), free=(x,y)=>!blocked.has(K2(x,y))&&!own.has(K2(x,y)), want=extra/2; let best=null;
    for(let s=0;s<p.length-1;s++){ const u=p[s], v=p[s+1], dx=v[0]-u[0], dy=v[1]-u[1];
      for(const d of [[-dy,dx],[dy,-dx]]){ let h=0; while(h<want && free(u[0]+d[0]*(h+1),u[1]+d[1]*(h+1)) && free(v[0]+d[0]*(h+1),v[1]+d[1]*(h+1))) h++; if(!h) continue;
        const outw=(u[0]-L/2)*d[0]+(u[1]-L/2)*d[1], sc=h*1000+outw; if(!best||sc>best.sc) best={s,d,h,sc}; } }
    if(!best) return null; const {s,d,h}=best, u=p[s], v=p[s+1], ins=[];
    for(let j=1;j<=h;j++) ins.push([u[0]+d[0]*j,u[1]+d[1]*j]); for(let j=h;j>=1;j--) ins.push([v[0]+d[0]*j,v[1]+d[1]*j]);
    p.splice(s+1,0,...ins); extra-=2*h; }
  return extra===0? p : null; }
function finishConn(i){ const c=S.conns[i]; c.full=padPath(c.path, needSteps(c.layer), obstacles(i,c.layer)); return !!c.full; }
function routeConflicts(){ const seen=new Map(), bad=new Set(); S.conns.forEach((c,i)=>{ if(c.layer==null) return; for(const p of connCells3(i,true)){ const k=K3(p); if(seen.has(k)&&seen.get(k)!==i){ bad.add(i); bad.add(seen.get(k)); } else seen.set(k,i); } }); return bad; }
function bfsRoute(i,l){ const E=endpoints()[i], ob=obstacles(i,l), key=(x,y)=>K2(x,y), prev=new Map([[key(E.A[0],E.A[1]),null]]), Qx=[E.A]; let h=0;
  while(h<Qx.length){ const u=Qx[h++]; if(u[0]===E.B[0]&&u[1]===E.B[1]) break;
    for(const [dx,dy] of [[1,0],[-1,0],[0,1],[0,-1]]){ const x=u[0]+dx, y=u[1]+dy, k=key(x,y); if(x<MX0||x>MX1||y<MX0||y>MX1||prev.has(k)||ob.has(k)) continue; prev.set(k,u); Qx.push([x,y]); } }
  if(!prev.has(key(E.B[0],E.B[1]))) return null; const path=[]; let u=E.B; while(u){ path.push(u); u=prev.get(key(u[0],u[1])); } path.reverse(); return path; }
function autoRoute(i){ const c=S.conns[i], tryL=[...(c.layer?[c.layer]:[]), ...seq(1,maxLayers())]; const keep={layer:c.layer,path:c.path,full:c.full};
  for(const l of tryL){ c.layer=l; c.full=null; const p=bfsRoute(i,l); if(!p) continue; c.path=p; if(finishConn(i) && !routeConflicts().has(i)) return l; }
  Object.assign(c,keep); return null; }

/* ---------------- DOM ---------------- */
const bar=null, tb=null; root.classList.add('game');
root.innerHTML=`
  <div class="fg">
    <div class="fg-head">
      <div class="fg-levels"><span class="fg-levels-label">Levels</span><div class="fg-chips" id="g-levels"></div><button type="button" class="btn ghost g-howbtn" data-act="howto">How to play</button></div>
      <nav class="g-rail" id="g-rail" aria-label="Phases"></nav>
    </div>
    <div class="g-howto" id="g-howto" hidden>
      <p class="fg-kicker">How to play</p>
      <p class="fg-title">Turn a packing puzzle into a folded protein</p>
      <p class="fg-goal">Berger and Leighton proved that folding HP strings is hard by turning any bin-packing puzzle into a single HP string. The H's of that string can fill a perfect cube exactly when the puzzle has a solution. The game first shows you how a puzzle becomes its string, built from four simple building blocks. Then you fold that string into the cube yourself, step by step, and discover why each block can only go to one place.</p>
      <div class="g-howto-steps">
        <figure><svg viewBox="0 0 120 70" aria-hidden="true"><rect x="8" y="10" width="46" height="52" rx="3" class="hw-bin"/><rect x="66" y="10" width="46" height="52" rx="3" class="hw-bin"/><rect x="12" y="38" width="38" height="20" rx="2" style="fill:var(--item-1)"/><rect x="12" y="26" width="38" height="10" rx="2" style="fill:var(--item-2)"/><rect x="70" y="30" width="38" height="28" rx="2" style="fill:var(--item-3)"/><rect x="70" y="18" width="38" height="10" rx="2" style="fill:var(--item-4)"/></svg>
          <figcaption><b>The puzzle</b>Items of different sizes must fill the bins exactly.</figcaption></figure>
        <span class="g-arr" aria-hidden="true">→</span>
        <figure><svg viewBox="0 0 120 70" aria-hidden="true">${[...'PHPPHHPPHHPPHPPHHP'].map((c,k)=>`<circle cx="${8+k*6}" cy="35" r="2.6" class="${c==='H'?'hw-h':'hw-p'}"/>`).join('')}<text x="60" y="58" class="hw-t">S<tspan baseline-shift="sub" font-size="7">B</tspan> = X₁ X₂ … I</text></svg>
          <figcaption><b>Part 1 · the string</b>Steps 1–3, just reading: the puzzle, the four building blocks, and the string they make.</figcaption></figure>
        <span class="g-arr" aria-hidden="true">→</span>
        <figure><svg viewBox="0 0 120 70" aria-hidden="true"><path d="M40 22 L70 12 L96 22 L66 32 Z" class="hw-face"/><path d="M40 22 L66 32 L66 62 L40 52 Z" class="hw-face2"/><path d="M66 32 L96 22 L96 52 L66 62 Z" class="hw-face3"/></svg>
          <figcaption><b>Part 2 · the fold, the game</b>Steps 4–10: lay each block into the 12×12×12 cube: edges, faces, walls, then the items into the bins.</figcaption></figure>
      </div>
      <ul class="g-howto-list">
        <li>Each step has a <b>Your move</b> box that says exactly what to click or type.</li>
        <li><b>Check</b> tests your answer. <b>Stuck? Get a hint</b> gives a clue. <b>Next step</b> lets the game do the step for you, so you can always keep going.</li>
        <li><b>Explanation</b>, in the panel, links to the matching part of the proof.</li>
        <li>In the 3D view, drag or use <b>W A S D</b> (or the arrow keys) to turn the cube, scroll or <b>Q / E</b> to zoom, and <b>R</b> to reset the view. Solid orange balls are H's, pale balls are P's, and see-through blue balls are the sites you can click.</li>
      </ul>
      <div class="g-actions"><button type="button" class="btn primary" data-act="start">Start playing</button></div>
    </div>
    <div class="fg-brief" id="g-brief"></div>
    <div class="fg-body">
      <div class="fg-main">
        <div class="fg-strip" id="g-top"></div>
        <div class="fg-stage">
          <div class="g-view" id="g-view"></div>
          <div class="fg-pill" id="g-pill"></div>
          <div class="g-tools" id="g-tools"><button type="button" data-v="front">Front</button><button type="button" data-v="back">Back</button><button type="button" data-v="top">Top</button><button type="button" data-v="phase">This step</button><button type="button" data-v="xray" aria-pressed="false">X-ray</button><button type="button" data-v="ptoggle" aria-pressed="false">Hide P’s</button></div>
        </div>
        <div class="g-legend" id="g-legend"></div>
        <div class="fg-context" id="g-context"></div>
      </div>
      <aside class="fg-side" id="g-left"></aside>
    </div>
  </div>`;
const elLevels=root.querySelector('#g-levels'), elRail=root.querySelector('#g-rail'), elLeft=root.querySelector('#g-left'), elTop=root.querySelector('#g-top'), elLegend=root.querySelector('#g-legend'), elBrief=root.querySelector('#g-brief'), elCtx=root.querySelector('#g-context'), elPill=root.querySelector('#g-pill');
/* colours of the 3D view come from the site's tokens, so they follow its light and dark themes */
function readTheme(){ const cs=getComputedStyle(root), v=(k,d)=>(cs.getPropertyValue(k).trim()||d);
  Object.assign(C,{H:v('--h','#c4532f'), i1:v('--item-1','#0f6f73'), i2:v('--item-2','#d99a1e'), i3:v('--item-3','#7a4b9e'), i4:v('--item-4','#a34f61'), fill:v('--item-pad','#8b8b95'), dummy:v('--rule-strong','#c9c3b7'), P:v('--p','#4f7aa3'), edge:v('--backbone','#6d6d78'), face:v('--fg-subtle','#8b8b95'), inner:v('--lattice','#d8d4cb'), wall:v('--fg','#1c1c21'), conn:v('--rule-strong','#c9c3b7'),
    ink:v('--fg','#1c1c21'), ghost:v('--lattice','#d8d4cb'), ok:v('--st-proved','#2f7a4d'), bad:v('--invalid','#b3261e'), note:v('--bond','#d99a1e'), sel:v('--accent','#1f4f8f'), bgElev:v('--bg-elev','#fff'), muted:v('--fg-muted','#55555f'), board:v('--bg-sunk','#f2f0eb'), rule:v('--rule','#e2ded5')}); }
new MutationObserver(()=>{ readTheme(); view.cache={}; view.themeChanged&&view.themeChanged(); if(shown) refreshAll(); }).observe(document.documentElement,{attributes:true,attributeFilter:['data-theme']});
const view=new GLView(root.querySelector('#g-view'));
let mapView=null;
const VIEWS={front:[0.3,0.22], back:[Math.PI+0.62,0.45], top:[0.15,1.2], below:[-0.7,-0.55], iso:[0.55,0.42]};
root.querySelector('#g-tools').addEventListener('click',e=>{ const b=e.target.closest('[data-v]'); if(!b) return; const v=b.dataset.v;
  if(v==='xray'){ view.xray=!view.xray; b.setAttribute('aria-pressed',view.xray); view.request(); return; }
  if(v==='ptoggle'){ view.hideP=!view.hideP; b.setAttribute('aria-pressed',view.hideP); b.textContent=view.hideP?'Show P’s':'Hide P’s'; view.request(); return; }
  if(v==='phase'){ view.setView(PH[PH_IDS[S.ph]].cam||VIEWS.iso,true); return; }
  view.setView(VIEWS[v],true); });

/* ---------------- phases ---------------- */
const CARDS={problems:'2 Why bin packing', cube:'3 Why a cube', string:'4 Spelling the string', 'local-rules':'5 The counts match', skeleton:'6 Two edges stay free', 'free-edges':'7 One length per edge', walls:'8 Walls run straight', packing:'9 Reading off a packing', frame:'10 Folding the frame', 'build-walls':'11 Building the walls', 'fill-strips':'12 Filling the strips', crossbar:'13 Untangling the linkers', linkers:'14 Loops take up slack', conclusion:'15 Folding is NP-complete', idea:'1 Turning packing into folding'};
const REFCARD={'r0-2':'problems','r0-4':'conclusion','r3-1':'string','r3-2':'string','r3-3':'string','r3-4':'local-rules','s2':'local-rules','r2-3':'local-rules','r2-4':'local-rules','r2-5':'local-rules','r2-6':'local-rules','r5-2':'local-rules','r4-2':'frame','r4-3':'frame','r5-3':'skeleton','r4-4':'build-walls','r5-4':'free-edges','r5-8':'packing','r5-1':'packing','r4-5':'fill-strips','r4-6':'crossbar','r4-1':'linkers','r1-6':'cube','r6-1':'conclusion'};
const ref=(id)=>{ const c=REFCARD[id]||'idea'; return `<a class="g-ref" href="#step-bl-${c}">${CARDS[c]} →</a>`; };
const refsHTML=refs=>[...new Set(refs.map(([id])=>REFCARD[id]||'idea'))].map(c=>`<a class="g-ref" href="#step-bl-${c}">${CARDS[c]} →</a>`).join('');
const formRow=(key,label,f,val,cls)=>`<label for="g-in-${key}">${label}</label><span class="f">${f}</span><input id="g-in-${key}" data-k="${key}" inputmode="numeric" autocomplete="off" value="${val}" class="${cls||''}">`;
const PH={};
/* ---------------- Part 1: from the puzzle to the string ----------------
   Three explained steps, nothing to solve: the puzzle, the four building blocks, and the string S_B block by block.
   The game proper is Part 2, folding that string. */

/* the puzzle drawn like the site's bin-packing game (src/widgets/bin-pack): an item is a bar as long as its size,
   a bin is a track with one dot per unit of capacity */
const bpBar=(n,col,label,extra)=>`<span class="bp-item ${extra||''}" style="--n:${n};--c:${col}"><span class="bp-size">${label==null?n:label}</span></span>`;
function puzzleBoard(){ const B=lvB(S.lv), it=S.lv.items;
  return `<div class="bp" style="--bp-B:${Math.max(B,...it)}"><div class="bp-board">
    <div class="bp-tray"><div class="bp-row-head"><span class="bp-label">Items</span></div><div class="bp-items">${it.map((s,u)=>bpBar(s,itemCol(u),null,'is-static')).join('')}</div></div>
    <div class="bp-bins">${Array.from({length:S.lv.K},(_,k)=>`<div class="bp-bin"><div class="bp-row-head"><span class="bp-label">Bin ${k+1}</span><span class="bp-load">holds ${B}</span></div><div class="bp-track"></div></div>`).join('')}</div>
  </div></div>`; }
const puzzleSentence=()=>{ const it=S.lv.items, B=lvB(S.lv), K=S.lv.K, sum=it.reduce((a,b)=>a+b,0);
  return `Here there ${it.length===1?'is':'are'} ${it.length} items, of sizes ${it.join(', ')}, and ${K} bin${K>1?'s':''} of size ${B}: the sizes add up to ${sum} = ${K} × ${B}.`; };

PH.A1={ part:1, explainer:true, short:'The puzzle', title:'The puzzle: bin packing', kicker:'card 2',
  task:()=>`Bin packing gives some items, each with a size, and some bins of equal size, and asks whether the items fill the bins exactly. ${puzzleSentence()}`,
  move:()=>'Look at the puzzle, then press <b>Continue</b>. Berger and Leighton write any such puzzle as one HP string. This game is about folding that string, and the fold will turn out to solve the puzzle.',
  ui:el=>{ el.innerHTML=puzzleBoard()+`<p class="g-note">${S.lv.no? 'Can these items fill the bins? Keep the question in mind: the fold will answer it.' : 'You do not need to solve it now. You will pack these items later, inside the cube.'}</p>`; },
  explain:()=>`<p>The reduction turns every bin-packing instance into an HP string ${SB}. If the items fit, ${SB} has a <em>perfect</em> fold, one whose H's fill a cube exactly; if they do not fit, it has none. So a fast way to fold HP strings would give a fast way to solve bin packing, which is NP-hard.</p><p>In the proof the cube is big even for small puzzles. The game uses a scale model with a ${n}×${n}×${n} cube (q = ${q}), small enough to fold by hand: the same blocks with smaller exponents.</p>`,
  refs:[['r0-2','card 2 · The problems'],['r0-4','card 15 · Main theorem'],['r3-1','card 4 · Parameters']] };

/* the four building blocks, each with a small cross-section of the cube */
const bbBall=(x,y,h)=>h?`<circle cx="${x}" cy="${y}" r="6.5" class="bb-h"/>`:`<circle cx="${x}" cy="${y}" r="5.6" class="bb-p"/>`;
const bbChain=pts=>`<polyline points="${pts.map(p=>p[0]+','+p[1]).join(' ')}" class="bb-bond"/>`+pts.map(p=>bbBall(p[0],p[1],p[2])).join('');
const bbCube=`<rect x="40" y="36" width="140" height="80" rx="2" class="bb-cube"/><text x="154" y="96" class="bb-t" text-anchor="end">inside the cube</text>`;
const BLOCKS=[
  {pat:'PHP', name:'PHP · an edge', svg:bbCube+bbChain([[24,44,0],[48,44,1],[48,20,0]]), text:'The H has two P neighbours, and a P can never be inside a cube full of H\'s. An H with two free sides is on an <b>edge</b> of the cube (or a corner). A run (PHP)(PHP)… walks along the edges.', ref:['r2-4','card 5']},
  {pat:'PHHP', name:'PHHP · a face', svg:bbCube+bbChain([[64,22,0],[64,44,1],[80,44,1],[80,22,0],[96,22,0],[96,44,1],[112,44,1],[112,22,0]]), text:'Each H has one P outside, so it lies on the <b>surface</b>. The two P\'s between pairs fold back like a hairpin, so the next pair is next to this one. A run of PHHP snakes over <b>one face</b>.', ref:['r2-6','card 5']},
  {pat:'HHH…H', name:'a run of H\'s · the inside', svg:bbCube+bbChain([[64,60,1],[80,60,1],[96,60,1],[112,60,1],[128,60,1],[128,76,1],[112,76,1],[96,76,1],[80,76,1],[64,76,1]]), text:'No P next to it, so nothing stops it from going <b>inside</b>. It is the only kind of block that can fill the interior.', ref:['r5-2','card 5']},
  {pat:'PPP…P', name:'a run of P\'s · a wire', svg:bbCube+bbChain([[18,96,0],[18,80,0],[18,64,0],[18,48,0],[18,32,0],[18,16,0],[34,16,0],[50,16,0],[66,16,0],[82,16,0],[98,16,0],[114,16,0]]), text:'Only P\'s, so it stays <b>outside</b>, like a wire. It takes the string from where one block ends to where the next one starts.', ref:['r4-6','cards 13–14']}
];
const patHTML=p=>[...p].map(c=>c==='H'?'<b class="bb-kh">H</b>':c==='P'?'<b class="bb-kp">P</b>':c).join('');
PH.A2={ part:1, explainer:true, short:'Building blocks', title:'The four building blocks', kicker:'card 5',
  task:()=>`A perfect fold puts the H's on all ${fmt(N3)} sites of a ${n}×${n}×${n} cube, so <b>every P has to sit outside the cube</b>. That one rule turns four short patterns into building blocks: each can only go to one kind of place.`,
  move:()=>'Read the four building blocks, then press <b>Continue</b>. The string in the next step is made of nothing else.',
  ui:el=>{ el.innerHTML=`<div class="bb-grid">${BLOCKS.map(b=>`<figure class="bb-card"><svg viewBox="0 0 170 104" aria-hidden="true">${b.svg}</svg><figcaption><span class="bb-pat">${patHTML(b.pat)}</span><b>${b.name.split(' · ')[1]}</b><span>${b.text}</span>${ref(b.ref[0])}</figcaption></figure>`).join('')}</div>`; },
  explain:()=>`<p>Card 5: once the H's fill a cube, every P lies outside it. Then an H next to a P is on the surface (card 5), an H between two P's is on an edge (card 5), and H P P H forces the two H's to be neighbours, because the two P's make a U-turn outside (card 5). Put together, (PHP)<sup>r</sup> is a path along edges and (PHHP)<sup>r</sup> a path on one face (card 5).</p>`,
  refs:[['s2','Building blocks'],['r2-3','card 5'],['r2-5','card 5']] };

/* the string, block by block; the 3D view shows where each block will go */
function stringFacts(id){ const B=lvB(S.lv), K=S.lv.K;
  return {X1:['PHP',`${9*n-10} H's: the ${n-2} inner sites of nine edges (9 × ${n-2}), plus all 8 corners.`],
    X2:['PHHP',`${(n-2)**2} H's in ${(n-2)**2/2} pairs: one whole face, the back.`],
    X3:['PHP',`${n-2} H's for one more edge, the tenth. Then P⁴, a short hop to the next face.`],
    X4:['PHHP',`Four more faces, ${(n-2)**2} sites each, with short hops P⁷ between them. The last face is left 2 sites short: a door into the cube.`],
    X5:['HHH…H',`${fmt((n-2)**3)} H's for the interior plus 2 for the door. Then a run P<sup>${8+q}</sup> to the front face.`],
    W:['PHP + PHHP',`The ${q} bin walls on the front face: rods (PHP) down the two side edges, and straight lines (PHHP) across the face. They cut the front face into ${q} bins of ${T} sites.`],
    S:['PHP',`${q} single H's, one for the gap each wall leaves on the edge.`],
    F:['PPP…P + PHHP',`${q} paddings of T − B = ${T-B} sites, one per bin, each after a linker of ${LAM} P's.`],
    D:['PPP…P + PHHP', K<q? `${q-K} block${q-K>1?'s':''} of B = ${B} sites that close the spare bin${q-K>1?'s':''}, each after a linker of ${LAM} P's.` : `Empty in this level: every bin is a real bin (q − K = 0).`],
    I:['PPP…P + PHHP',`One block per item, as long as the item (sizes ${S.lv.items.join(', ')}), each after a linker of ${LAM} P's. Which bin each one goes to is the packing.`]}[id]; }
function regionFor(id){ const o=[], face=(f)=>{ for(let a=1;a<=n-2;a++) for(let b=1;b<=n-2;b++) o.push(f(a,b)); };
  if(id==='X1') return E9(); if(id==='X3') return seq(1,n-2).map(y=>[0,y,L]);
  if(id==='X2'){ face((a,b)=>[a,b,L]); return o; }
  if(id==='X4'){ face((a,b)=>[0,a,b]); face((a,b)=>[a,0,b]); face((a,b)=>[L,a,b]); face((a,b)=>[a,L,b]); return o.filter(p=>!DOOR.some(d=>same(d,p))); }
  if(id==='X5'){ for(let x=1;x<L;x++) for(let y=1;y<L;y++) for(let z=1;z<L;z++) o.push([x,y,z]); return o.concat(DOOR); }
  if(id==='W'){ WALL_ROWS.forEach(y=>{ for(let x=1;x<=n-2;x++) o.push([x,y,0]); }); for(let y=1;y<=n-2;y++){ o.push([0,y,0]); if(!SPECIAL_Y.includes(y)) o.push([L,y,0]); } return o; }
  if(id==='S') return SPECIAL_Y.map(y=>[L,y,0]);
  const lay=tailLayout(), kinds={F:'fill',D:'dummy'};
  if(id==='I'){ const used=new Set(); lay.forEach(t=>{ if(t) t.cells.forEach(c=>used.add(K3(c))); }); BIN_CELLS.forEach(cs=>cs.forEach(c=>{ if(!used.has(K3(c))) o.push(c); })); return o; }
  S.tail.forEach((b,i)=>{ if(b.kind===kinds[id] && lay[i]) o.push(...lay[i].cells); }); return o; }
const camFor=id=>({X2:[Math.PI+0.5,0.35], X3:[Math.PI+0.5,0.35], X5:[0.55,0.42], W:[0.25,0.18], S:[0.25,0.18], F:[0.18,0.12], D:[0.18,0.12], I:[0.18,0.12]})[id]||VIEWS.iso;
PH.A3={ part:1, explainer:true, short:'The string', title:'The string, block by block', kicker:'card 4',
  task:()=>`Here is the HP string ${SB} for this puzzle: ${fmt(sbLetters(sbBlocks(toyP(S.lv))).length)} letters in ten blocks. Each block is made of the building blocks, and each is sized to fill one part of the cube <em>exactly</em>. The view shows where each block goes.`,
  move:()=> S.strIdx<SLOTS.length? `Block ${S.strIdx+1} of ${SLOTS.length}. Read it, see where it goes in the view, then press <b>Next block</b>.` : 'That is the whole string. Press <b>Start folding</b> to begin the game.',
  ui:el=>{ const k=S.strIdx, card=id=>S.cards.find(c=>c.slot===id);
    if(k<SLOTS.length){ const s=SLOTS[k], c=card(s.id), [bb,fact]=stringFacts(s.id);
      el.innerHTML=`<div class="str-card" style="--c:${C[s.col]||s.col}"><p class="str-name"><span class="str-sw"></span><span>${s.nm}</span><span class="g-note">fills ${s.role}</span></p>
        <p class="str-num">${c.num}</p><p class="g-note">${c.sym}</p><p class="str-bb">Building block: <span class="bb-pat">${patHTML(bb)}</span></p><p>${fact}</p></div>`; }
    else el.innerHTML=`<div class="str-card" style="--c:var(--accent)"><p class="str-name">The whole string</p><p>${fmt(N3)} H's in all, exactly the number of sites of the ${n}×${n}×${n} cube: ${12*n-16} H's between two P's for the ${12*n-16} edge sites, ${fmt(6*(n-2)**2)} H's in pairs for the face sites, and ${fmt((n-2)**3)} in the long run for the interior. Nothing is left over, so each block has only one kind of place it can go.</p><p>That is what you fold now, one block at a time.</p></div>`;
    el.insertAdjacentHTML('beforeend',`<div class="g-actions"><button type="button" class="btn" data-sact="prev"${k?'':' disabled'}>← Previous</button>${k<SLOTS.length?`<button type="button" class="btn primary" data-sact="next">Next block →</button>`:`<button type="button" class="btn primary" data-act="cont">Start folding →</button>`}</div>${k<SLOTS.length?`<p><button type="button" class="g-hintlink" data-act="cont">Skip to folding →</button></p>`:''}`);
    el.addEventListener('click',e=>{ const b=e.target.closest('[data-sact]'); if(!b) return; S.strIdx=Math.max(0,Math.min(SLOTS.length,S.strIdx+(b.dataset.sact==='next'?1:-1))); refreshAll(); const id=SLOTS[Math.min(S.strIdx,SLOTS.length-1)].id; view.setView(camFor(id),true); }); },
  explain:()=>`<p>${SB} = X₁X₂X₃X₄X₅ W Σ F D I (card 4). Card 5 counts its H's by their neighbours in the string: exactly 12n − 16 H's lie between two P's, as many as edge sites; exactly (n − 2)³ have an H on both sides, as many as interior sites; the rest, 6(n − 2)², match the face sites. This exact match is what makes the converse work: in a perfect fold no block has room to go anywhere else.</p>`,
  refs:[['r3-2','card 4 · The string'],['r3-4','card 5 · Counting H\'s']] };

/* B1: the nine edges */
const CORNER=c=>[(c&1)?L:0,(c&2)?L:0,(c&4)?L:0];
const EDGES=(()=>{ const o=[]; for(let a=0;a<8;a++) for(const bit of [1,2,4]){ const b=a|bit; if(b!==a && !(a&bit)) o.push({key:a+'-'+b,a,b}); } return o; })();
const CANON_TRAIL=['6-7','2-6','2-3','3-7','5-7','1-5','0-1','0-4','4-5'];
PH.B1={ part:2, short:'Nine edges', title:'Lay X₁ along nine edges', kicker:'card 10', blocks:['X1'],
  task:()=>`X₁ = (PHP)<sup>${9*n-10}</sup> is one path along the cube's edges. Click nine edges in order. Each edge must continue from the end of the one before.`,
  ui:el=>{ el.innerHTML=`<p class="g-note">Edges so far: <b>${S.trail.length}</b> / 9${S.trail.length?` · click the last edge again to undo it`:''}.</p><div class="g-actions"><button type="button" class="btn" data-act="undo"${S.trail.length?'':' disabled'}>Undo edge</button><button type="button" class="btn" data-act="clear"${S.trail.length?'':' disabled'}>Clear</button></div>`;
    el.querySelector('[data-act=undo]').onclick=()=>{ b1Undo(); refreshAll(); }; el.querySelector('[data-act=clear]').onclick=()=>{ S.trail=[]; S.tStart=S.tEnd=null; refreshAll(); }; },
  pick:(mx_,my_)=>{ const i=view.pickSeg(mx_,my_,EDGES.map(e=>[CORNER(e.a),CORNER(e.b)])); if(i<0) return; const e=EDGES[i];
    if(S.trail.includes(e.key)){ if(S.trail[S.trail.length-1]===e.key){ b1Undo(); refreshAll(); } else say('That edge is already in X₁. A fold visits each site once.','bad'); return; }
    if(S.trail.length>=9){ say('X₁ already covers nine edges.','bad'); return; }
    if(!S.trail.length){ S.trail.push(e.key); S.tStart=e.a; S.tEnd=e.b; }
    else { let end=S.tEnd; if(S.trail.length===1 && e.a!==end && e.b!==end && (e.a===S.tStart||e.b===S.tStart)){ [S.tStart,S.tEnd]=[S.tEnd,S.tStart]; end=S.tEnd; }
      if(e.a!==end && e.b!==end){ say('That edge does not touch the end of the path (the ringed corner). X₁ is one connected path.','bad'); return; }
      S.trail.push(e.key); S.tEnd = e.a===end? e.b : e.a; }
    say(null); S.reveal={stage:"last"}; refreshAll(); if(S.trail.length===9) runCheck(); },
  check:()=>{ if(S.trail.length<9) return {ok:false, msg:`X₁ has ${9*n-10} H's: exactly nine edges and the eight corners. You have ${S.trail.length} edges.`};
    const free=EDGES.map(e=>e.key).filter(k=>!S.trail.includes(k));
    if(!free.includes('0-2')||!free.includes('1-3')) return {ok:false, msg:'Leave the left and right edges of the front face free: the bin walls W will fill them (card 11).'};
    const third=free.find(k=>k!=='0-2'&&k!=='1-3');
    if(third!=='4-6'&&third!=='5-7') return {ok:false, msg:'The three free edges share no corner, as they must (card 6). But this construction lays X₃ down a vertical edge of the back face. Leave a vertical back edge free instead.'};
    S.mirror = third==='5-7';
    return {ok:true, msg:`X₁ is down: ${9*n-10} H's on nine edges and all eight corners, with every P outside the cube. The tenth edge (${S.mirror?'back left':'back right'}, seen from the front) is left for X₃, and the two side edges of the front face are left for the walls.`}; },
  hints:()=>[ 'X₁ is one connected path, so every edge you click must start where the previous one ended.',
    'Three edges must stay free: the left and right edges of the front face (for the walls) and one vertical edge at the back (for X₃). They are drawn dashed now.',
    'One solution: start at the top back corner on the left (seen from the front), go around the top face, down the back left edge, and around the bottom face.' ],
  auto:()=>{ S.trail=CANON_TRAIL.slice(); S.tStart=7; S.tEnd=5; },
  explain:()=>`<p>In (PHP)<sup>r</sup> each H sits between two P's. Both P's lie outside the cube, so the H needs two outside neighbours and must sit on an edge (card 5). Consecutive H's are joined by HPPH and must be neighbours (card 5), so X₁ is a path along the edges. It has 9n − 10 = 9(n − 2) + 8 H's, exactly nine edges and all eight corners.</p><p>Three edges stay free, and they share no corner. The converse shows that this is forced (card 6). One is filled by X₃ = (PHP)<sup>n−2</sup>. The other two must hold the wall strings, so they are opposite edges of the front face.</p>`,
  refs:[['r2-4','card 5 · PHP forces an edge'],['r4-2','card 10 · Edges and back face'],['r5-3','card 6 · Nine edges']], cam:VIEWS.iso };
function b1Undo(){ if(!S.trail.length) return; const k=S.trail.pop(), e=EDGES.find(x=>x.key===k); if(!S.trail.length){ S.tStart=S.tEnd=null; return; } S.tEnd = e.a===S.tEnd? e.b : e.a; }

/* B2: the back face */
const backStart=()=>tp(BACK_START), backEnd=()=>tp(BACK_END);
PH.B2={ part:2, short:'Back face', title:'Snake X₂ over the back face', kicker:'card 10', blocks:['X2','X3'],
  task:()=>`X₂ = (PHHP)<sup>${(n-2)**2/2}</sup> fills the ${(n-2)**2} face sites of the back face in one path. Start at the green ring and end at the blue ring. Click a site in the same row or column as the end of your path to extend it in a straight line.`,
  ui:el=>{ el.innerHTML=`<p class="g-note">Sites so far: <b>${S.back.length}</b> / ${(n-2)**2}. Click a site on the path to cut the path back to it.</p><div class="g-actions"><button type="button" class="btn" data-act="clear"${S.back.length?'':' disabled'}>Clear</button></div>`;
    el.querySelector('[data-act=clear]').onclick=()=>{ S.back=[]; refreshAll(); }; },
  pick:(mx_,my_)=>{ const cand=[]; for(let x=1;x<=n-2;x++) for(let y=1;y<=n-2;y++) cand.push([x,y,L]); const i=view.pickPoint(mx_,my_,cand); if(i<0) return; const c=cand[i], P=S.back, st=backStart();
    if(!P.length){ if(c[0]===st[0]&&c[1]===st[1]){ S.backPrev=0; P.push([c[0],c[1]]); say(null); S.reveal={stage:"last"}; refreshAll(); } else say('Start at the green ring. It is the only back-face site next to the last H of X₁, and X₁ ends with HP while X₂ starts with PH, so the two H\'s must be neighbours (card 5).','bad'); return; }
    const at=P.findIndex(p=>p[0]===c[0]&&p[1]===c[1]); if(at>=0){ P.length=at+1; say(null); refreshAll(); return; }
    const last=P[P.length-1]; if((c[0]===last[0])===(c[1]===last[1])){ say('Click a site in the same row or column as the end of the path.','bad'); return; }
    const dx=Math.sign(c[0]-last[0]), dy=Math.sign(c[1]-last[1]), add=[]; let x=last[0], y=last[1];
    while(x!==c[0]||y!==c[1]){ x+=dx; y+=dy; if(P.some(p=>p[0]===x&&p[1]===y)){ say('The path cannot cross itself: each site holds one residue.','bad'); return; } add.push([x,y]); }
    S.backPrev=P.length; P.push(...add); say(null); S.reveal={stage:"last"}; refreshAll(); if(P.length===(n-2)**2) runCheck(); },
  check:()=>{ const P=S.back, en=backEnd(); if(P.length<(n-2)**2) return {ok:false, msg:`The snake must cover all ${(n-2)**2} sites of the back face. X₂ has exactly that many H's.`};
    const last=P[P.length-1]; if(last[0]!==en[0]||last[1]!==en[1]) return {ok:false, msg:'The snake must end at the blue ring. X₂ ends with HP and X₃ starts with PH, so the last H of X₂ must neighbour the first H of X₃ on the free back edge.'};
    return {ok:true, msg:`The back face is full. X₃ = (PHP)<sup>${n-2}</sup> then has only one place to go, the free back edge, followed by P⁴, which hops to the left face.`}; },
  hints:()=>[ 'The green ring sits next to the end of X₁ and the blue ring next to the free back edge, where X₃ starts. Every site of the face is used exactly once.',
    `Go column by column. A face has n − 2 = ${n-2} columns, an even number, so a column-by-column snake ends on the same side it started. The dashed line shows one.` ],
  auto:()=>{ S.back=canonBack().map(p=>{ const t=tp(p); return [t[0],t[1]]; }); },
  explain:()=>`<p>In (PHHP)<sup>r</sup> every H has a P neighbour outside the cube, so it lies on the surface (card 5). The two H's of a pair are neighbours, and the HPPH between pairs forces the next pair to be adjacent (card 5). So the block is a path of face sites. It cannot jump to another face in the middle (card 5). X₂ has (n − 2)² H's, exactly one face.</p><p>Any path through all the sites works. The proof uses a vertical snake (Figure 6). Since n − 2 is even, it ends on the side where it began, next to the tenth edge.</p>`,
  refs:[['r2-5','card 5 · HPPH forces neighbours'],['r2-6','card 5 · Gadgets give paths'],['r4-2','card 10 · Edges and back face']], cam:[Math.PI+0.16,0.14], focus:p=>p[2]>=L };

/* B3: side faces, the door and the interior */
const doorT=()=>DOOR.map(tp);
PH.B3={ part:2, short:'Faces & door', title:'Four faces, the door and the interior', kicker:'card 10', blocks:['X4','X5'],
  task:()=>`X₄ has filled the left, bottom and right faces (hopping between them with P⁷). Its last block, (PHHP)<sup>${(n-2)**2/2-1}</sup>, snakes over the top face row by row from the back, as the dashed arrows show. It is one pair short. Click the two top-face sites it leaves open: the door for X₅.`,
  ui:el=>{ el.innerHTML=`<p class="g-note">Door sites chosen: <b>${S.door.length}</b> / 2.</p><div class="g-actions"><button type="button" class="btn" data-act="clear"${S.door.length?'':' disabled'}>Clear</button></div>`; el.querySelector('[data-act=clear]').onclick=()=>{ S.door=[]; refreshAll(); }; },
  pick:(mx_,my_)=>{ const cand=[]; for(let x=1;x<=n-2;x++) for(let z=1;z<=n-2;z++) cand.push([x,L,z]); const i=view.pickPoint(mx_,my_,cand); if(i<0) return; const c=cand[i];
    const at=S.door.findIndex(p=>same(p,c)); if(at>=0) S.door.splice(at,1); else if(S.door.length<2) S.door.push(c); else { say('Two sites only. Click a chosen site to remove it.','bad'); return; }
    say(null); refreshAll(); if(S.door.length===2) runCheck(); },
  check:()=>{ const D=doorT(); if(S.door.length<2) return {ok:false, msg:'Choose two top-face sites.'};
    const ok=D.every(p=>S.door.some(c=>same(c,p))); if(ok) return {ok:true, msg:`X₄ ends next to the first door site. X₅ = P H<sup>${(n-2)**3+2}</sup> P<sup>${8+q}</sup> enters there, fills the ${fmt((n-2)**3)} interior sites layer by layer, and leaves through the second. Then P<sup>${8+q}</sup> walks to the front face. Turn on X-ray to see the interior.`};
    const inRow=S.door.every(c=>c[2]===1); return {ok:false, msg: inRow? 'Right row. Now follow the snake: which two sites does it reach last?' : 'Not those. The snake runs row by row from the back (z = n − 2) toward the front, so the open sites are in the last row it reaches.'}; },
  hints:()=>[ 'The top-face snake has (n − 2)² − 2 sites. It runs row by row, changing direction each time, from the back row toward the front row.',
    `There are ${n-2} rows, an even number, so the last row is run in the same direction as the second row. The two open sites are at its far end, next to the front face.` ],
  auto:()=>{ S.door=doorT(); },
  explain:()=>`<p>X₄ fills the left, bottom, right and top faces with snakes like the back face. Between faces it hops around an edge with a P⁷ that stays outside the cube. Its last block is one PHHP short, so two top-face sites stay open. They are the door.</p><p>X₅ = P H<sup>(n−2)³+2</sup> P<sup>8+q</sup> enters through one door site. A run of H's has no constraint, so it can fill the interior in any order: here a layer-by-layer snake. It leaves through the other door site, and P<sup>8+q</sup> takes the string to the front face, where the bins are built.</p>`,
  refs:[['r4-3','card 10 · Side faces and interior'],['r5-2','card 5 · Who sits where']], cam:[0.04,1.36], focus:p=>p[1]>=L&&p[0]>0&&p[0]<L&&p[2]>0&&p[2]<L };

/* B4: the bin walls */
PH.B4={ part:2, short:'Bin walls', title:'Build the bin walls', kicker:'card 11', blocks:['W','S'],
  task:()=> S.wsub===1
    ? `Everything but the front face is full. W builds q = ${q} walls. Each wall is a frame: a line of ${n-2} H's across the face, the rods down both sides, and a line back. Click a front-face row to place a wall line. You need ${2*q} lines that cut the face into ${q} bins of ${2*q-1} rows.`
    : `The walls are up. The long rods fill the ${S.mirror?'left':'right'} edge. On the ${S.mirror?'right':'left'} edge the short rods leave one gap in each wall. Click the ${q} gaps: the special H's of Σ go there.`,
  ui:el=>{ el.innerHTML = S.wsub===1 ? `<p class="g-note">Wall lines chosen: <b>${S.rows.length}</b> / ${2*q}. Click a row again to remove it.</p><div class="g-actions"><button type="button" class="btn" data-act="clear"${S.rows.length?'':' disabled'}>Clear</button></div>` : `<p class="g-note">Gaps found: <b>${S.spec.length}</b> / ${q}.</p>`;
    const b=el.querySelector('[data-act=clear]'); if(b) b.onclick=()=>{ S.rows=[]; refreshAll(); }; },
  pick:(mx_,my_)=>{
    if(S.wsub===1){ const cand=[]; for(let x=1;x<=n-2;x++) for(let y=1;y<=n-2;y++) cand.push([x,y,0]); const i=view.pickPoint(mx_,my_,cand); if(i<0) return; const y=cand[i][1];
      const at=S.rows.indexOf(y); if(at>=0) S.rows.splice(at,1); else if(S.rows.length<2*q) S.rows.push(y); else { say(`${2*q} lines already. Click one to remove it.`,'bad'); return; }
      say(null); refreshAll(); if(S.rows.length===2*q) runCheck(); return; }
    const sx=mx(L), cand=SPECIAL_Y.map(y=>[sx,y,0]).concat(seq(1,n-2).filter(y=>!SPECIAL_Y.includes(y)).flatMap(y=>[[0,y,0],[L,y,0]])).concat(SPECIAL_Y.map(y=>[mx(0),y,0]));
    const i=view.pickPoint(mx_,my_,cand); if(i<0) return; const c=cand[i];
    if(i>=SPECIAL_Y.length){ say('That site is already filled by a rod. Look for the sites that are still empty, on the edge with the short short rods.','bad'); return; }
    if(!S.spec.some(p=>same(p,c))) S.spec.push(c); say(null); refreshAll(); if(S.spec.length===q) runCheck(); },
  check:()=>{
    if(S.wsub===1){ const ok=S.rows.length===2*q && S.rows.every(y=>WALL_ROWS.has(y));
      if(ok){ S.wsub=2; return {ok:'sub', msg:`Those are the walls: ${q} frames of ${2*q+1} rows. Each wall string runs: short rod down one edge, a line across, a long rod down the other edge, P⁴, a line back, a short rod. Now find the gaps.`}; }
      return {ok:false, msg:`Not quite. The ${S.mirror?'left':'right'} edge has ${n-2} = q(2q + 1) sites and is filled by long rods only (card 7). So each wall takes ${2*q+1} consecutive rows: a line, ${2*q-1} bin rows, a line.`}; }
    if(S.spec.length<q) return {ok:false, msg:'Find all the gaps.'};
    return {ok:true, msg:`Σ = PH(P<sup>${2*q+6}</sup>H)<sup>${q-1}</sup>P puts one H of the spaced rod in each gap, hopping outside the cube between walls. Every edge site is now full, and the front face holds ${q} empty bins of T = ${T} sites.`}; },
  hints:()=> S.wsub===1 ? [ `The walls use all ${n-2} rows of the side edges, and a wall's frame has ${2*q+1} rows. So the walls are rows 1–${2*q+1} and ${2*q+2}–${2*(2*q+1)} counted from the top.`, `The lines are the top and bottom rows of each frame: rows 1, ${2*q+1}, ${2*q+2} and ${2*(2*q+1)} from the top.` ]
    : [ `Each wall puts two short rods on the ${S.mirror?'right':'left'} edge: 2q = ${2*q} sites of its ${2*q+1} rows. The middle row of each wall stays empty.` ],
  auto:()=>{ if(S.wsub===1){ S.rows=[...WALL_ROWS]; return; } S.spec=SPECIAL_Y.map(y=>[mx(L),y,0]); },
  explain:()=>`<p>W is q copies of one wall string: a short rod on one edge, a straight line of (PHHP)<sup>(n−2)/2</sup> across the face, a long rod on the opposite edge, P⁴, a line back, and another short rod. Each wall is a frame around a bin of (n − 2) × (2q − 1) = ${T} sites.</p><p>In the converse the walls are forced. An edge of n − 2 = q(2q + 1) sites filled exactly by short rods and long rods must use long rods only (card 7). The lines must be straight (card 8). Σ fills the q sites that the short rods leave, one per wall.</p>`,
  refs:[['r4-4','card 11 · The bin walls'],['r5-4','card 7 · card 7'],['r5-8','card 9 · The bins appear']], cam:[0.06,0.06], focus:p=>p[2]<=0 };

/* B5: packing */
PH.B5={ part:2, short:'Packing', title:'Pack the bins', kicker:'card 12', blocks:['F','D','I'],
  task:()=>`The walls are up, so the front face is now ${q} bins of ${T} sites each. The end of the string fills them. Each bin already holds its <b>padding</b>, a block of T − B = ${T-lvB(S.lv)} sites (the grey bar)${q>S.lv.K?`, and the spare bin${q-S.lv.K>1?'s are':' is'} closed by a block of B = ${lvB(S.lv)}`:''}. What is left in each real bin is exactly B = ${lvB(S.lv)} sites. Packing the items there is the puzzle from step 1.`,
  move:()=>`Click an <b>item</b>, then a <b>bin</b> (the board above the cube, or the bin in the cube itself). Fill every bin to exactly ${T}. Click an item in a bin to take it out again.`+(S.lv.no?' If you think it cannot be done, press <b>No packing exists</b>.':''),
  top:'bins',
  ui:el=>{ el.innerHTML=`<p class="g-note">Each block lands in its bin in string order, snaking through the bin's sites; the cube below shows where.</p><div class="g-actions"><button type="button" class="btn" data-act="none">No packing exists</button></div>`;
    el.addEventListener('click',e=>{ if(e.target.closest('[data-act=none]')) b5None(); }); },
  pick:(mx_,my_)=>{ if(!S.selBlock){ say('Select a block first.','info'); return; } const cand=[], kOf=[]; BIN_CELLS.forEach((cs,k)=>cs.forEach(c=>{ cand.push(tp(c)); kOf.push(k); })); const i=view.pickPoint(mx_,my_,cand); if(i<0) return; b5Move(S.selBlock,kOf[i]); },
  check:()=>{ if(S.impossible) return {ok:'level', msg:''}; const loads=binLoads(); if(S.tail.some(b=>S.asg[b.id]<0)) return {ok:false, msg:'Place every block.'};
    const fill=Array.from({length:q},(_,k)=>S.tail.filter(b=>b.kind==='fill'&&S.asg[b.id]===k).length);
    if(fill.some(f=>f>1)) return {ok:false, msg:`Two paddings take 2(T − B) = ${2*(T-lvB(S.lv))} > ${T} sites. A bin has room for only one.`};
    const k=loads.findIndex(l=>l!==T); if(k>=0) return {ok:false, msg:`Bin ${k+1} holds ${loads[k]} of ${T} sites. Every bin must be filled exactly, or some H ends up off the cube.`};
    return {ok:true, msg:`Every bin is exactly full. The items in bins with a padding and no plug are your packing: ${Array.from({length:q},(_,j)=>j).filter(j=>!S.tail.some(b=>b.kind==='dummy'&&S.asg[b.id]===j)).map(j=>`{${S.tail.filter(b=>b.kind==='item'&&S.asg[b.id]===j).map(b=>b.size).join(', ')}}`).join(' and ')}.`}; },
  hints:()=>[ `Each bin takes one padding (T − B = ${T-lvB(S.lv)})${q>S.lv.K?`; the spare bin${q-S.lv.K>1?'s':''} also take${q-S.lv.K>1?'':'s'} a plug`:''}. Then the items must fill the remaining room, B = ${lvB(S.lv)} in each real bin. That is the packing problem itself.`,
    (()=>{ const a=solvePacking(S.lv.items,S.lv.K,lvB(S.lv)); if(!a) return `Try to reach ${lvB(S.lv)} in each bin. Sizes ${S.lv.items.join(', ')}: which subsets add up to ${lvB(S.lv)}?`; const g=S.lv.items.map((s,u)=>({s,u})).filter(x=>a[x.u]===0); return `One real bin can take ${g.map(x=>'u'+(x.u+1)).join(', ')} (${g.map(x=>x.s).join(' + ')} = ${lvB(S.lv)}).`; })() ],
  auto:()=>{ const B=lvB(S.lv), a=solvePacking(S.lv.items,S.lv.K,B); if(!a){ b5None(true); return; }
    S.tail.forEach(b=>{ if(b.kind==='fill') S.asg[b.id]=+b.id.slice(1)-1; else if(b.kind==='dummy') S.asg[b.id]=S.lv.K+(+b.id.slice(1))-1; else S.asg[b.id]=a[b.u]; }); S.selBlock=null; },
  explain:()=>`<p>After Σ the string is F, D and I: a padding of T − B per bin, then a plug for each of the q − K spare bins, then one item ribbon of size s(u) per item. Each block comes after its own run P<sup>Λ</sup>, and each one snakes through its bin starting on an even site (card 12). A bin is filled exactly when its blocks add up to T.</p><p>Since 2(T − B) > T, each bin holds exactly one padding. The plugs close q − K bins, and the items must fill the other K bins with exactly B each: a packing. That is how cards 6–9 reads a packing off any perfect fold. With no packing, there is no perfect fold (card 9).</p>`,
  refs:[['r4-5','card 12 · Items in the bins'],['r5-8','card 9 · The bins appear'],['r5-1','card 9 · Soundness']], cam:[0.06,0.06], focus:p=>p[2]<=0 };
function b5Move(id,k){ const b=S.tail.find(x=>x.id===id);
  if(k>=0 && S.asg[id]!==k){ const free=T-binLoads()[k]; if(b.size>free){ say(`The ${b.size} does not fit in bin ${k+1}: it has ${free} free site${free===1?'':'s'}. Take an item out first.`,'bad'); return; } }
  S.asg[id]=k; S.selBlock=null; say(null); refreshAll(); if(S.tail.every(b=>S.asg[b.id]>=0) && binLoads().every(l=>l===T)) runCheck(); }
/* the packing board, drawn like the site's bin-packing game: bars as long as their size, one dot per free site */
function binsBoard(){ const loads=binLoads(), sel=S.selBlock&&S.tail.find(b=>b.id===S.selBlock), lay=tailLayout();
  const bar=(b,inBin)=>{ const fixed=b.kind!=='item', label=b.kind==='fill'?`padding ${b.size}`:b.kind==='dummy'?`closes ${b.size}`:b.size;
    return fixed? `<span class="bp-item is-static ${b.kind==='fill'?'bp-pat-1':'bp-pat-2'}" style="--n:${b.size};--c:${b.col}" title="${b.kind==='fill'?'Padding, T − B sites':'Block of B sites closing a spare bin'}"><span class="bp-size">${label}</span></span>`
      : `<button type="button" class="bp-item${S.selBlock===b.id?' is-selected':''}" data-bb="${b.id}" style="--n:${b.size};--c:${b.col}" aria-label="Item u${b.u+1}, size ${b.size}${inBin?', in a bin':''}"><span class="bp-size">${label}</span></button>`; };
  const loose=S.tail.filter(b=>b.kind==='item'&&S.asg[b.id]<0);
  return `<div class="bp" style="--bp-B:${T}"><div class="bp-board">
    <div class="bp-tray${sel&&S.asg[sel.id]>=0?' is-target':''}" data-bbin="-1"><div class="bp-row-head"><span class="bp-label">Items</span>${S.impossible?'':''}</div><div class="bp-items">${loose.map(b=>bar(b,false)).join('')||'<span class="g-note">All items are in bins.</span>'}</div></div>
    <div class="bp-bins">${Array.from({length:q},(_,k)=>{ const inBin=S.tail.filter(b=>S.asg[b.id]===k), full=loads[k]===T, fits=sel&&S.asg[sel.id]!==k&&sel.size<=T-loads[k], spare=S.tail.some(b=>b.kind==='dummy'&&S.asg[b.id]===k);
      return `<div class="bp-bin${full?' is-full':''}${fits?' is-target':''}${sel&&!fits&&S.asg[sel.id]!==k?' is-blocked':''}" data-bbin="${k}"><div class="bp-row-head"><span class="bp-label">Bin ${k+1}${spare?' · spare':''}</span><span class="bp-load">${full?'<span class="bp-check"></span>':''}${loads[k]} of ${T}</span></div>
        <div class="bp-track">${inBin.map(b=>bar(b,true)).join('')}${fits?`<span class="bp-ghost" style="--n:${sel.size};--c:${sel.col}"></span>`:''}</div></div>`; }).join('')}</div>
  </div></div>`; }
function b5None(fromAuto){ const a=solvePacking(S.lv.items,S.lv.K,lvB(S.lv));
  if(a){ say(`There is a packing. Keep trying, or ask for a hint.`,'bad'); return; }
  S.impossible=true; S.done[7]=true; S.done[8]=true; S.done[9]=true; if(!fromAuto) {} finishLevel(); }

/* B6: routing */
PH.B6={ part:2, short:'Routing', title:'Route the linkers', kicker:'cards 13–14', blocks:['F','D','I'],
  task:()=>`Between two blocks in the bins, the string has a run of exactly ${LAM} P's: a wire that must stay outside the cube. Each wire goes from the end of one block (a <b>dot</b> on the map) down to a routing layer under the front face, runs along that layer, and comes back up at the start of the next block (a <b>square</b>). Two linkers on the same layer cannot cross, and a wire going down to a deep layer blocks its spot on the layers above. You have ${maxLayers()} layer${maxLayers()>1?'s':''}.`,
  ui:el=>{ const ep=endpoints(), bad=routeConflicts(), name=i=> i===0? `Σ → ${S.tail[0].id}` : `${S.tail[i-1].id} → ${S.tail[i].id}`;
    const c=S.conns[S.selConn], st=i=>{ const k=S.conns[i]; if(k.full) return bad.has(i)?['bad','collides']:['ok',`✓ ${k.path.length-1} + ${needSteps(k.layer)-(k.path.length-1)} stretch`]; if(k.path.length>1) return ['',`${k.path.length-1} steps`]; return ['','—']; };
    el.innerHTML=`<div class="g-conns">${S.conns.map((k,i)=>{ const [cl,tx]=st(i); return `<button type="button" class="g-conn ${i===S.selConn?'on':''} ${cl}" data-c="${i}"><span class="sw" style="background:${CPAL[i%CPAL.length]}"></span><span>${i+1}. ${name(i)}${k.layer?` · layer ${k.layer}`:''}</span><span class="ln">${tx}</span></button>`; }).join('')}</div>
      <div class="g-layers"><span>Layer for linker ${S.selConn+1}:</span>${seq(1,maxLayers()).map(l=>`<button type="button" data-l="${l}" class="${c.layer===l?'on':''}">${l}</button>`).join('')}</div>
      <p class="g-note">Layer ℓ lies at depth z = ${ZL(1)}, ${ZL(2)}, …; a linker on layer ℓ must draw exactly ${needSteps(1)} − 2(ℓ − 1) steps. You draw the route; once it reaches the square, the game adds a hairpin outside the cube to make up the length.</p>
      <div class="g-actions"><button type="button" class="btn" data-act="undo"${c.path.length>1?'':' disabled'}>Undo segment</button><button type="button" class="btn" data-act="clear"${c.layer||c.path.length?'':' disabled'}>Clear linker</button></div>`;
    el.addEventListener('click',e=>{ const b=e.target.closest('[data-c]'); if(b){ S.selConn=+b.dataset.c; say(null); refreshAll(); return; }
      const l=e.target.closest('[data-l]'); if(l){ const k=S.conns[S.selConn]; k.layer=+l.dataset.l; if(!k.path.length) k.path=[ep[S.selConn].A]; if(k.full && !finishConn(S.selConn)) say('No room to stretch this linker on that layer.','bad'); else say(null); refreshAll(); return; }
      const a=e.target.closest('[data-act]'); if(!a) return; const k=S.conns[S.selConn];
      if(a.dataset.act==='clear'){ k.layer=null; k.path=[]; k.full=null; }
      else { k.full=null; if(k.segs&&k.segs.length){ k.path.length=k.segs.pop(); } else k.path.length=Math.max(1,k.path.length-1); }
      say(null); refreshAll(); }); },
  check:()=>{ const bad=routeConflicts(), open=S.conns.findIndex(k=>!k.full); if(open>=0) return {ok:false, msg:`Linker ${open+1} is not finished.`};
    if(bad.size) return {ok:false, msg:`Linkers ${[...bad].map(i=>i+1).join(', ')} collide. Some shaft probably runs through a path on a shallower layer.`};
    return {ok:true, msg:`All ${S.conns.length} linkers are routed, each with exactly Λ = ${LAM} P's and no collisions.`}; },
  hints:()=>{ const i=S.conns.findIndex(k=>!k.full), keep=JSON.stringify(S.conns), l= i>=0? autoRoute(i) : null; S.conns=JSON.parse(keep);
    return [ 'Linkers on different layers never meet, except that a deep linker\'s shafts pass through every layer above it. A linker on layer 1 has to steer around the dots of all the deeper linkers.',
      'The length is never the problem. A route from a dot to a square always has an odd number of steps, as needed, because every block starts on an even site (card 12). So a hairpin of the right size always fixes the length.',
      i<0? 'All linkers are drawn.' : l? `Try linker ${i+1} on layer ${l}.` : `Linker ${i+1} does not fit on any layer as things stand. Clear a linker that blocks it, or move one to another layer.` ]; },
  auto:()=>{ let i=S.conns.findIndex(k=>!k.full); if(i<0) return; if(!S.conns[S.selConn].full) i=S.selConn; const l=autoRoute(i);
    if(l==null){ const k=S.conns[i], keep=S.lv.layers; S.lv.layers=null; const l2=autoRoute(i); S.lv.layers=keep; if(l2!=null){ k.extraLayer=true; say(`Linker ${i+1} did not fit in ${maxLayers()} layers, so the game used layer ${l2}. The proof gives every linker a layer of its own.`,'info'); } }
    S.selConn = S.conns.findIndex(k=>!k.full); if(S.selConn<0) S.selConn=i; },
  explain:()=>`<p>The tail blocks are joined by runs P<sup>Λ</sup>. Each run leaves the last H of one block, dips below the front face, and comes back up under the first H of the next block. P's have no constraint except that they sit outside the cube, so these runs are free linkers.</p><p>cards 13–14 routes linker <i>i</i> in its own plane, deeper than all the earlier ones, then stretches it to exactly Λ + 2 vertices by pushing it away from the cube. The game uses linkers of Λ = n² = ${LAM} P's, as in the draft proof map; the paper's 52n + 2 works the same way. The parity works because every block starts on an even site. The paper does the same job with a 3D crossbar switch (card 13). Here you route with a limited number of layers, so paths in a layer have to avoid each other.</p>`,
  refs:[['r4-6','cards 13–14 · Routing the linkers'],['r3-1','Remark: Λ = n²']], top:'map', cam:[0.75,0.32] };
function routeClick(c){ if(S.playing) return; const i=S.selConn, k=S.conns[i], E=endpoints()[i];
  const other=endpoints().findIndex((e,j)=>j!==i && e.A && e.A[0]===c[0]&&e.A[1]===c[1]);
  if(k.layer==null){ if(other>=0){ S.selConn=other; refreshAll(); return; } if(c[0]===E.A[0]&&c[1]===E.A[1]){ k.layer=1; k.path=[E.A]; refreshAll(); return; } say('Pick a layer for this linker first, or click its dot.','info'); return; }
  if(!k.path.length) k.path=[E.A];
  const at=k.path.findIndex(p=>p[0]===c[0]&&p[1]===c[1]); if(at>=0){ k.path.length=at+1; k.full=null; k.segs=(k.segs||[]).filter(s=>s<=at); say(null); refreshAll(); return; }
  if(k.full){ if(other>=0){ S.selConn=other; refreshAll(); return; } say('This linker is finished. Click a cell on its path to cut it back.','info'); return; }
  const last=k.path[k.path.length-1]; if((c[0]===last[0])===(c[1]===last[1])){ if(other>=0){ S.selConn=other; refreshAll(); return; } say('Click a cell in the same row or column as the end of the path.','bad'); return; }
  const r=walkLine(i,last,c); if(!r.ok){ say(r.why==='self'?'A path cannot cross itself.':`Blocked at (${r.block[0]}, ${r.block[1]}): something already uses that site on layer ${k.layer}.`,'bad'); refreshAll(); return; }
  (k.segs=k.segs||[]).push(k.path.length); k.path.push(...r.cells); const end=k.path[k.path.length-1];
  if(end[0]===E.B[0]&&end[1]===E.B[1]){ if(k.path.length-1>needSteps(k.layer)){ say(`Too long for layer ${k.layer}: at most ${needSteps(k.layer)} steps.`,'bad'); }
    else if(!finishConn(i)) say('There is no room to stretch this linker to its exact length here. Try another layer.','bad');
    else { say(`Linker ${i+1} reaches its square: ${k.path.length-1} steps drawn and ${needSteps(k.layer)-(k.path.length-1)} added by the hairpin, so the run has exactly ${LAM} P's.`,'ok'); const nx=S.conns.findIndex(z=>!z.full); if(nx>=0) S.selConn=nx; }
    refreshAll(); if(S.conns.every(z=>z.full)) runCheck(); return; }
  say(null); refreshAll(); }

/* B7: the final check */
PH.B7={ part:2, short:'Check', title:'Check the whole fold', kicker:'cards 10–14', blocks:[],
  task:()=>`Every residue of ${SB} now has a site. The game checks the fold the way cards 10–14 needs it.`,
  ui:el=>{ const r=fullCheck(); el.innerHTML=`<ul class="checks">${r.items.map(([ok,t])=>`<li class="${ok?'ok':'bad'}"><span>${t}</span></li>`).join('')}</ul>`; S._check=r; },
  check:()=>{ const r=S._check||fullCheck(); return r.ok? {ok:'level', msg:''} : {ok:false, msg:'Something is off; see the list.'}; },
  hints:()=>['Nothing to do here: read the list.'], auto:()=>{},
  explain:()=>`<p>A fold is <em>perfect</em> when its H's fill an n×n×n cube. By card 3 that is the same as reaching score 3n²(n − 1), the most any string with n³ H's can get. So a packing gives a perfect fold of ${SB} (cards 10–14), and cards 6–9 shows the converse.</p>`,
  refs:[['r4-1','cards 10–14 · Completeness'],['r1-6','card 3 · The threshold'],['r6-1','card 15 · Main theorem']], cam:VIEWS.back };
/* "Your move": what to click or type in each step, in one or two plain sentences */
PH.B1.move=()=> S.trail.length? `Click an edge that touches the <b>ringed corner</b> to continue the path (${S.trail.length} of 9 so far). Click the last edge again to undo it.` : 'Click any <b>edge</b> of the cube in the view to start the path X₁. You will lay it along 9 of the 12 edges.';
PH.B2.move=()=> S.back.length? `Click a <b>highlighted site</b> to extend the path in a straight line (${S.back.length} of ${(n-2)**2} sites). Cover every site and end on the <b>blue ring</b>.` : 'Click the <b>green ring</b> to start the path on the back face.';
PH.B3.move=()=>'The dashed line shows how the snake starts on the top face. Follow it row by row in your head, and click the <b>two sites</b> it never reaches.';
PH.B4.move=()=> S.wsub===1? `Click a <b>row</b> of the front face to lay a wall line on it; click it again to remove it. Place ${2*q} lines (${S.rows.length} so far).` : `Click the <b>${q} empty sites</b> left on the edge of the front face.`;
PH.B5.move=()=>`Click a <b>block</b> in the panel, then click <b>Bin 1</b> or <b>Bin 2</b> (or a bin in the view). Both bins must end at exactly ${T}.`+(S.lv.no?' If you think it cannot be done, press <b>No packing exists</b>.':'');
PH.B6.move=()=>'1. Pick a <b>linker</b> in the panel. 2. Pick a <b>layer</b> for it. 3. On the map, click cells in straight lines from its <b>dot</b> to its <b>square</b>. The game makes up the exact length.';
PH.B7.move=()=>'Nothing to click: read the checks in the panel, then press <b>Check</b> to finish the level.';

PH.B1.ctx='Click an edge of the cube to lay X₁ on it. Drag or use W A S D to turn the view, scroll or Q / E to zoom.';
PH.B5.ctx='Click an item on the board above, then a bin. Drag or use W A S D to turn the view.';
PH.B6.ctx='Draw on the map above; the cube shows the linkers you have finished.';
PH.B7.ctx='Drag or use W A S D to turn the finished cube, Q / E to zoom.';
/* "Show solution": each fold step as a list of moves, played one after another; the step is then checked as usual */
const CANON_CORNERS=[7,6,2,3,7,5,1,0,4,5];
PH.B1.solve=()=>[()=>{ S.trail=[]; S.tStart=S.tEnd=null; S.mirror=false; }, ...CANON_TRAIL.map((k,j)=>()=>{ S.trail=CANON_TRAIL.slice(0,j+1); S.reveal={stage:"last"}; S.tStart=7; S.tEnd=CANON_CORNERS[j+1]; })];
PH.B2.solve=()=>{ const cells=canonBack().map(p=>{ const t=tp(p); return [t[0],t[1]]; }), o=[()=>{ S.back=[]; }]; for(let k=5;k<=cells.length;k+=5) o.push(()=>{ S.backPrev=k-5; S.back=cells.slice(0,k); S.reveal={stage:"last"}; }); return o; };
PH.B2.solveDelay=260;
PH.B3.solve=()=>[()=>{ S.door=[]; }, ()=>{ S.door=[doorT()[0]]; }, ()=>{ S.door=doorT(); }];
PH.B3.solveDelay=500;
PH.B4.solve=()=>{ const rows=[...WALL_ROWS].sort((a,b)=>b-a), o=[];
  if(S.wsub===1){ o.push(()=>{ S.rows=[]; }); rows.forEach((y,j)=>o.push(()=>{ S.rows=rows.slice(0,j+1); })); o.push(()=>{ runCheck(true); }); }
  o.push(()=>{ S.spec=[]; }); SPECIAL_Y.forEach((y,j)=>o.push(()=>{ S.spec=SPECIAL_Y.slice(0,j+1).map(yy=>[mx(L),yy,0]); })); return o; };
PH.B4.solveDelay=450;
PH.B5.solve=()=>{ const a=solvePacking(S.lv.items,S.lv.K,lvB(S.lv)), items=S.tail.filter(b=>b.kind==='item');
  if(!a) return [()=>{ items.forEach(b=>S.asg[b.id]=-1); say('No way to fill every bin exactly: try every split and some bin always ends short or over.','info'); }, ()=>{ b5None(true); }];
  return [()=>{ items.forEach(b=>S.asg[b.id]=-1); S.selBlock=null; }, ...items.map(b=>()=>{ S.asg[b.id]=a[b.u]; })]; };
PH.B5.solveDelay=600;
PH.B6.solve=()=>[()=>{ S.conns.forEach(c=>{ c.layer=null; c.path=[]; c.full=null; c.segs=[]; }); S.selConn=0; }, ...S.conns.map(()=>()=>{ PH.B6.auto(); })];
PH.B6.solveDelay=550;
PH.B7.solve=()=>[()=>{}];
let playTimer=0;
function playSolution(){ const i=S.ph, P=PH[PH_IDS[i]]; if(!P.solve || S.playing || S.done[i]) return;
  const moves=P.solve(), me=S; S.autos++; S.playing=true; say('Playing the solution…','info'); let k=0;
  const tick=()=>{ if(S!==me || S.ph!==i){ me.playing=false; return; }
    if(k<moves.length){ moves[k++](); if(S.finished){ S.playing=false; return; } refreshAll(); playTimer=setTimeout(tick, P.solveDelay||300); return; }
    S.playing=false; say(null); if(!S.done[i] && !S.finished) runCheck(true); else refreshAll(); };
  tick(); }

function fullCheck(){ const {res}=buildResidues(9), N=res.length, letters=sbLetters(sbBlocks(toyP(S.lv)));
  let lettersOK=letters.length===N; for(let i=0;lettersOK&&i<N;i++) if(letters[i]!==res[i].h) lettersOK=false;
  let adjOK=true; for(let i=1;i<N;i++) if(!adj(res[i].p,res[i-1].p)){ adjOK=false; break; }
  const seen=new Set(); let inj=true; for(const r of res){ const k=K3(r.p); if(seen.has(k)){ inj=false; break; } seen.add(k); }
  const occ=new Set(); let Hc=0, bad=0; for(const r of res){ if(r.h){ Hc++; if(inCube(r.p)) occ.add(K3(r.p)); else bad++; } else if(inCube(r.p)) bad++; }
  let sc=0; for(const k of occ){ const [x,y,z]=k.split(',').map(Number); if(occ.has(K3([x+1,y,z]))) sc++; if(occ.has(K3([x,y+1,z]))) sc++; if(occ.has(K3([x,y,z+1]))) sc++; }
  const cube=Hc===N3&&bad===0&&occ.size===N3;
  const items=[[lettersOK,`${fmt(N)} residues, and their letters spell ${SB} exactly`],[adjOK,'consecutive residues sit on neighbouring sites'],[inj,'no site is used twice'],[cube,`the H's are exactly the ${fmt(N3)} sites of the cube, and every P is outside it`],[sc===SCORE,`score ${fmt(sc)} = 3n²(n − 1), the threshold of card 3`]];
  return {ok:items.every(x=>x[0]), items}; }

/* ---------------- rendering ---------------- */
function statusDefault(P){ return P.pick? 'Click a highlighted site in the view.' : 'Fill in the panel, then press Check.'; }
function say(text,cls){ S.msg = text? {text,cls:cls||'info'} : null; const m=elBrief.querySelector('.fg-status'); if(m){ m.className='fg-status is-'+(S.msg?({ok:'good',bad:'warn',info:'info'}[S.msg.cls]||'info'):'info'); m.innerHTML=S.msg?S.msg.text:''; m.hidden=!S.msg; } }
function stars(){ const a=S.autos, h=S.hintTotal; return a===0&&h<=3?3: a<=3?2:1; }
function renderLevels(){ elLevels.innerHTML=LEVELS.map((lv,i)=>`<button type="button" class="${i===S.li?'is-on':''}" data-lv="${i}" title="Level ${i+1}: ${lv.name}" aria-pressed="${i===S.li}">${i+1}${saved.stars[i]?'<span class="fg-chip-done" aria-label="solved"></span>':''}</button>`).join(''); }
elLevels.addEventListener('click',e=>{ const b=e.target.closest('[data-lv]'); if(!b) return; const li=+b.dataset.lv; if(li===S.li && !S.finished) return; S=newState(li); renderAll(); });
function renderRail(){ const reach=i=> i<=3 || S.done[i-1] || S.done[i];   // the three reading steps never block the game
  elRail.innerHTML=PH_IDS.map((id,i)=>`${i===0?'<span class="grp">The string</span>':i===3?'<span class="grp">The fold</span>':''}<button type="button" data-ph="${i}" class="${i===S.ph?'on':''} ${S.done[i]?'done':''}"${reach(i)?'':' disabled'}><b>${i+1}</b><span>${PH[id].short.replace('S_B','S<sub>B</sub>')}</span></button>`).join(''); }
elRail.addEventListener('click',e=>{ const b=e.target.closest('[data-ph]'); if(!b||b.disabled||S.playing) return; S.ph=+b.dataset.ph; if(S.ph>=3) for(let k=0;k<3;k++) S.done[k]=true; S.msg=null; renderAll(); });
function refreshLeft(keepFocus){
  const P=PH[PH_IDS[S.ph]], i=S.ph, ex=!!P.explainer, done=S.done[i]&&!ex, fin=S.finished && (i===9 || S.impossible);
  if(keepFocus){ const box=elLeft.querySelector('.g-ui'); if(box && P===PH.A1){ const f=document.activeElement, k=f&&f.dataset&&f.dataset.k, pos=f&&f.selectionStart; const ui=document.createElement('div'); ui.className='g-ui'; P.ui(ui); box.replaceWith(ui); if(k){ const g=ui.querySelector(`[data-k="${k}"]`); if(g){ g.focus(); try{ g.setSelectionRange(pos,pos); }catch(_){} } } return; } }
  const hl=P.hints?P.hints():[], hints=hl.slice(0,S.hints[i]);
  const fgEl=root.querySelector('.fg'); fgEl.classList.toggle('is-part1', i<=1); fgEl.classList.toggle('is-playing', !!S.playing); fgEl.classList.toggle('side-first', [2,8].includes(i));
  elBrief.innerHTML=`<p class="fg-kicker">Level ${S.li+1} of ${LEVELS.length} · ${S.lv.name} · step ${i+1} of ${PH_IDS.length}, ${P.part===1?'from the puzzle to the string':'folding the string into the cube'}</p><p class="fg-title">${P.title}</p><p class="fg-goal">${P.task()}</p>
    ${fin? finishHTML() : done? `<div class="g-done"><span>${S.doneMsg&&S.doneMsg[i]||'Done.'}</span><div class="g-actions"><button type="button" class="btn primary" data-act="cont">Continue to step ${i+2} →</button></div></div>`
      : `<div class="g-move"><b>Your move</b><span>${P.move()}</span></div><p class="fg-status is-${S.msg?({ok:'good',bad:'warn',info:'info'}[S.msg.cls]||'info'):'info'}" role="status"${S.msg?'':' hidden'}>${S.msg?S.msg.text:''}</p>`}
    ${hints.length?`<div class="g-hints">${hints.map((h,j)=>`<p><b>Hint ${j+1}</b>${h}</p>`).join('')}</div>`:''}
    ${(done||fin||ex||S.playing)? '' : S.hints[i]<hl.length? `<p><button type="button" class="g-hintlink" data-act="hint">${S.hints[i]?'Another hint':'Stuck? Get a hint'}</button></p>`
      : P.solve? `<p><button type="button" class="btn g-solve" data-act="solve"><svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 12h3l3-7 4 14 3-7h3"/></svg>Show solution</button></p>` : ''}`;
  // the step's main button, repeated under the 3D view so the way forward is always in sight
  const mainBtn = fin? (S.li<LEVELS.length-1?`<button type="button" class="btn primary" data-act="next">Next level →</button>`:`<button type="button" class="btn" data-act="replay">Replay</button>`)
    : done? `<button type="button" class="btn primary" data-act="cont">Continue to step ${i+2} →</button>`
    : i===2? (S.strIdx<SLOTS.length?`<button type="button" class="btn primary" data-act="nextblock">Next block →</button>`:`<button type="button" class="btn primary" data-act="cont">Start folding →</button>`)
    : ex? `<button type="button" class="btn primary" data-act="cont">Continue →</button>`
    : S.playing? '' : `<button type="button" class="btn primary" data-act="check">Check</button>`;
  const ctxText = i===2? 'This view only shows where the block goes (blue). Drag or use W A S D to turn it.' : ex? 'Drag or use W A S D to turn the view.' : (P.ctx&&!done)? P.ctx : P.pick&&!done? 'Click a blue site to play. Drag or use W A S D to turn the view, scroll or Q / E to zoom.' : 'Drag or use W A S D to turn the view, scroll or Q / E to zoom.';
  elCtx.innerHTML = `<p class="fg-context-text">${ctxText}</p><div class="fg-context-actions">${mainBtn}</div>`;
  const pr=progress(i), pct=pr&&pr.of? Math.round(100*Math.min(1,pr.num/pr.of)) : 0;
  elLeft.innerHTML=(pr?`<div class="fg-score"><p class="fg-score-head">${pr.label}</p><p class="fg-score-row"><span class="fg-score-num">${fmt(pr.num)}</span><span class="fg-score-of">of ${fmt(pr.of)}</span></p><div class="fg-meter is-bar" aria-hidden="true"><span style="width:${pct}%"></span></div></div>`:'')+`
    <div class="g-ui"></div>
    ${ex? (i===2? '' : `<div class="fg-actions"><button type="button" class="btn primary fg-wide" data-act="cont">Continue →</button></div>`) : fin||done? '' : `<div class="fg-actions"><div class="fg-actions-row"><button type="button" class="btn primary" data-act="check">Check</button><button type="button" class="btn" data-act="auto" title="Let the game do this step"><svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 12h3l3-7 4 14 3-7h3"/></svg>Next step</button></div><p class="g-note">${S.hintTotal} hint${S.hintTotal===1?'':'s'} · ${S.autos} step${S.autos===1?'':'s'} done for you</p></div>`}
    <details class="g-explain"><summary>Explanation</summary>${P.explain()}<div class="g-refs">${refsHTML(P.refs)}</div></details>
    <dl class="fg-facts"><div><dt>Items</dt><dd>${S.lv.items.join(', ')}</dd></div><div><dt>Bins K · size B</dt><dd>${S.lv.K} · ${lvB(S.lv)}</dd></div>${S.lv.layers?`<div><dt>Routing layers</dt><dd>${S.lv.layers}</dd></div>`:''}<div><dt>Scale model</dt><dd>n = ${n}, q = ${q}</dd></div></dl>
    <p class="g-note">${S.lv.blurb}</p>`;
  const ui=elLeft.querySelector('.g-ui'); if(done && i!==9){ ui.style.pointerEvents='none'; ui.style.opacity='0.7'; } P.ui(ui);
}
root.addEventListener('click',e=>{ const a=e.target.closest('[data-act]'); if(!a||!elBrief.parentNode.contains(a)) return; const act=a.dataset.act, i=S.ph, P=PH[PH_IDS[i]];
  if(S.playing && act!=='howto') return;
  if(act==='solve'){ playSolution(); return; }
  if(act==='nextblock'){ S.strIdx=Math.min(SLOTS.length,S.strIdx+1); refreshAll(); view.setView(camFor(SLOTS[Math.min(S.strIdx,SLOTS.length-1)].id),true); return; }
  if(act==='check') runCheck(); else if(act==='hint'){ S.hints[i]++; S.hintTotal++; refreshAll(); }
  else if(act==='auto'){ S.autos++; P.auto(); if(S.impossible) return; refreshAll(); if(!S.done[i]) runCheck(true); }
  else if(act==='cont'){ S.done[i]=true; S.ph=Math.min(9,i+1); S.msg=null; renderAll(); }
  else if(act==='next'){ S=newState(Math.min(LEVELS.length-1,S.li+1)); renderAll(); }
  else if(act==='replay'){ S=newState(S.li); renderAll(); }
  else if(act==='howto'){ introOpen=true; showIntro(); }
  else if(act==='start'){ introOpen=false; try{ localStorage.setItem(STORE+'-intro','1'); }catch(_){} showIntro(); renderAll(); } });
/* the How to play screen: shown on the first visit, and from the button by the levels */
let introOpen=(()=>{ try{ return !localStorage.getItem(STORE+'-intro'); }catch(_){ return true; } })();
function showIntro(){ root.querySelector('#g-howto').hidden=!introOpen; elBrief.hidden=introOpen; root.querySelector('.fg-body').hidden=introOpen; elRail.hidden=introOpen; if(!introOpen) view.resize(); }
function progress(i){
  switch(i){ case 0: case 1: return null; case 2: return {label:'Blocks read', num:Math.min(S.strIdx+1,SLOTS.length), of:SLOTS.length}; case 3: return {label:'Edges of X₁', num:S.trail.length, of:9}; case 4: return {label:'Back-face sites', num:S.back.length, of:(n-2)**2};
    case 5: return {label:'Door sites', num:S.door.length, of:2}; case 6: return S.wsub===1? {label:'Wall lines', num:S.rows.length, of:2*q} : {label:'Spaced-rod H’s', num:S.spec.length, of:q};
    case 7: return {label:'Blocks placed', num:S.tail.filter(b=>S.asg[b.id]>=0).length, of:S.tail.length}; case 8: return {label:'Linkers routed', num:S.conns.filter(c=>c.full).length, of:S.conns.length};
    default: { S._check=S._check||fullCheck(); return {label:'Score', num:S._check.ok?SCORE:0, of:SCORE}; } } }
function finishHTML(){ const st=stars(), last=S.li===LEVELS.length-1;
  return `<div class="g-done"><b>Level ${S.li+1} complete ${'★'.repeat(st)}${'☆'.repeat(3-st)}</b><span>${S.impossible
    ? `Right: no packing exists. Each bin of size ${lvB(S.lv)} must be filled exactly, and no choice of items does it. By card 9 a perfect fold of ${SB} would give a packing, so this string has <em>no</em> perfect fold. The reduction sends a no-instance to a no-instance.`
    : `You built a perfect fold of ${SB} from your own packing: a ${n}×${n}×${n} cube of H's. ${S.autos?`The game did ${S.autos} step${S.autos>1?'s':''} for you.`:'You did every step yourself.'}`}</span>
    <div class="g-actions">${last?'':`<button type="button" class="btn primary" data-act="next">Next level →</button>`}<button type="button" class="btn" data-act="replay">Replay</button></div></div>`; }
function finishLevel(){ S.finished=true; const st=stars(); if(!saved.stars[S.li]||saved.stars[S.li]<st){ saved.stars[S.li]=st; persist(); } S.ph = S.impossible? 7 : 9; renderAll(); }
function runCheck(fromAuto){ const i=S.ph, P=PH[PH_IDS[i]], r=P.check();
  if(r.ok==='level'){ S.done[i]=true; finishLevel(); return; }
  if(r.ok==='sub'){ S.reveal={stage:'W'}; say(r.msg,'ok'); refreshAll(); return; }
  if(r.ok){ S.done[i]=true; (S.doneMsg=S.doneMsg||{})[i]=r.msg; S.msg=null; S.reveal={stage:{3:'X1',4:'X2',5:'X4',6:'S',7:'tail',8:'tail'}[i]};
    if(i===8||i===7) S.reveal=null; renderAll(); return; }
  if(!fromAuto) say(r.msg,'bad'); refreshAll(); }
function refreshTop(){
  const P=PH[PH_IDS[S.ph]];
  if(P.top==='map'){ if(!mapView || !elTop.contains(mapView.box)){ elTop.innerHTML=`<span class="g-striph">Routing map: layer <span id="g-mlayer"></span>, seen from the front</span><div class="g-map" id="g-map"></div><p class="g-note">Dots: where a linker starts (the end of the previous block). Squares: where it must arrive. Small dark dots: shafts that pass through this layer. Faint dashed lines: paths on other layers.</p>`; mapView=new MapView(elTop.querySelector('#g-map')); mapView.onCell=routeClick; }
    elTop.querySelector('#g-mlayer').textContent = S.conns[S.selConn].layer || '—'; mapView.resize(); return; }
  mapView=null;
  if(P.top==='bins'){ elTop.innerHTML=`<span class="g-striph">The bins on the front face, ${T} sites each</span>${binsBoard()}`; return; }
  const hot=new Set(S.ph===2? (S.strIdx<SLOTS.length?[SLOTS[S.strIdx].id]:[]) : (P.blocks||[])), placed=new Set(), have=()=>true;
  [[3,['X1']],[4,['X2','X3']],[5,['X4','X5']],[6,['W','S']],[7,['F','D','I']]].forEach(([k,ids])=>{ if(S.done[k]) ids.forEach(x=>placed.add(x)); });
  const lens=sbBlocks(toyP(S.lv)).map(blockLen);
  elTop.innerHTML=`<span class="g-striph">The string ${SB}${S.ph>=3?' · blocks folded so far are solid':''}</span><div class="g-ribbon">${SLOTS.map((s,j)=>{ const on= S.ph>=3? placed.has(s.id) : have(s.id);
    return `<div class="${on?'have':''} ${hot.has(s.id)?'hot':''}" style="flex-grow:${Math.max(0.6,Math.log10(1+lens[j]))};${on?`background:${C[s.col]||s.col}`:''}" title="${s.role}">${s.nm}</div>`; }).join('')}</div><div class="g-rcap"><span>start</span><span>${fmt(lens.reduce((a,b)=>a+b,0))} letters · widths on a log scale</span><span>end</span></div>`;
}
/* clicks on the packing board: pick up an item, then click a bin (or the items row to take it back out) */
elTop.addEventListener('click',e=>{ if(PH_IDS[S.ph]!=='B5' || S.done[7] || S.finished || S.playing) return;
  const it=e.target.closest('[data-bb]'), bn=e.target.closest('[data-bbin]');
  if(S.selBlock && bn && +bn.dataset.bbin!==S.asg[S.selBlock]){ b5Move(S.selBlock,+bn.dataset.bbin); return; }
  if(it){
    const id=it.dataset.bb; S.selBlock = S.selBlock===id? null : id;
    if(S.selBlock){ const b=S.tail.find(x=>x.id===id), loads=binLoads(), f=[...Array(q).keys()].filter(k=>S.asg[id]!==k && b.size<=T-loads[k]).map(k=>k+1);
      say(`The ${b.size} is picked up. ${f.length?`It fits in bin ${f.join(' and ')}.`:'It fits in no other bin: take something out first.'}${S.asg[id]>=0?' Click the items row to take it out.':''}`,'info'); } else say(null);
    refreshAll(); return; }
  if(bn && S.selBlock){ b5Move(S.selBlock,+bn.dataset.bbin); } });
function sceneNow(){
  const i=S.ph, P=PH[PH_IDS[i]], {res,marks}=buildResidues(i), sc={balls:[],bonds:[],ghosts:[],lines:[],marks:[],labels:[]};
  const occH=new Set();
  res.forEach((r,j)=>{ const {hc,bc}=resColors(r), inner=r.h&&isInt(r.p); const fo=!P.focus||S.done[i]||P.focus(r.p); sc.balls.push({p:r.p,h:r.h,col:hc,al:(r.h?1:0.95)*(fo?1:0.1),i:j,inner}); if(r.h) occH.add(K3(r.p));
    const nx=res[j+1]; if(nx && adj(r.p,nx.p) && !nx.gap){ sc.bonds.push({a:r.p,b:nx.p,col:bc,i:j+1,hasP:!r.h||!nx.h,inner:inner&&nx.h&&isInt(nx.p),w:(r.st==='route'||nx.st==='route')?0.1:0.09,al:fo?0.75:0.08}); } });
  const ghostAll = P.part===1 || i>=3;
  if(ghostAll && i!==2) for(let x=0;x<n;x++) for(let y=0;y<n;y++) for(let z=0;z<n;z++){ const p=[x,y,z]; if(!isInt(p) && !occH.has(K3(p))) sc.ghosts.push(p); }
  if(i===2){ // where the current block of the string goes
    for(let x=0;x<n;x++) for(let y=0;y<n;y++) for(let z=0;z<n;z++){ const p=[x,y,z]; if(!isInt(p)) sc.ghosts.push(p); }
    if(S.strIdx<SLOTS.length){ const s=SLOTS[S.strIdx], col=s.id==='I'?itemCol(0):(C[s.col]||s.col), big=s.id==='X5';
      for(const p of regionFor(s.id)) sc.marks.push({p,col:C.sel,ring:true,ghost:true}); }
    else view.xray=false; }
  // phase overlays
  if(i===3){ const fr=new Set(S.hints[3]>=2? ['0-2','1-3','4-6'] : []);
    EDGES.forEach(e=>{ const ix=S.trail.indexOf(e.key), a=CORNER(e.a), b=CORNER(e.b); if(ix>=0) return; sc.lines.push({a,b,col: fr.has(e.key)?C.note:'#aab0ba', w: fr.has(e.key)?2.5:5, al:fr.has(e.key)?1:0.55, dash: fr.has(e.key)?[7,6]:null}); });
    if(!S.done[3]) S.trail.forEach((k,ix)=>{ const e=EDGES.find(x=>x.key===k), a=CORNER(e.a), b=CORNER(e.b); sc.labels.push({p:[(a[0]+b[0])/2,(a[1]+b[1])/2,(a[2]+b[2])/2],text:String(ix+1),col:'#fff',bg:C.sel}); });
    if(S.tEnd!=null && !S.done[3]) sc.marks.push({p:CORNER(S.tEnd),col:C.sel,ring:true,r:0.7,lw:2.5});
    for(let c=0;c<8;c++) sc.marks.push({p:CORNER(c),col:C.muted,r:0.14}); }
  if(i===4 && !S.done[4]){ const st=backStart(), en=backEnd(), P3=S.back.map(c=>[c[0],c[1],L]);
    { const occ=new Set(S.back.map(c=>c[0]+','+c[1])), last=S.back[S.back.length-1]; if(!last) sc.marks.push({p:st,col:C.sel,ring:true,ghost:true});
      else for(const [dx,dy] of [[1,0],[-1,0],[0,1],[0,-1]]){ let x=last[0]+dx, y=last[1]+dy; while(x>=1&&x<=n-2&&y>=1&&y<=n-2&&!occ.has(x+','+y)){ sc.marks.push({p:[x,y,L],col:C.sel,ring:true,ghost:true}); x+=dx; y+=dy; } } }
    sc.marks.push({p:st,col:C.ok,ring:true,r:0.62,lw:2.5}); sc.marks.push({p:en,col:C.sel,ring:true,r:0.62,lw:2.5});
    if(S.hints[4]>=2){ const g=canonBack().map(tp); for(let j=1;j<g.length;j++) sc.lines.push({a:g[j-1],b:g[j],col:C.note,w:1.5,dash:[4,4],al:0.8}); } }
  if(i===5 && !S.done[5]){ const top=sideFaces().top.map(tp); for(let j=1;j<2*(n-2);j++) sc.lines.push({a:top[j-1],b:top[j],col:C.note,w:3,dash:[6,4]});
    for(let x=1;x<=n-2;x++) for(let z=1;z<=n-2;z++){ const p=tp([x,L,z]); if(!S.door.some(c=>same(c,p))) sc.marks.push({p,col:C.sel,ring:true,ghost:true,r:0.24,lw:1}); }
    sc.marks.push({p:top[0],col:C.note,ring:true,r:0.6}); sc.labels.push({p:top[0],text:'X₄ starts the top face here',dy:-26});
    S.door.forEach(p=>sc.marks.push({p,col:C.sel,r:0.32}));
    if(S.hints[5]>=2) for(let x=1;x<=n-2;x++) sc.marks.push({p:tp([x,L,1]),col:C.note,ring:true,r:0.45,dash:true,lw:1.5}); }
  if(i===7 && !S.done[7] && S.selBlock) BIN_CELLS.forEach(cs=>cs.forEach(c=>sc.marks.push({p:tp(c),col:C.sel,ring:true,ghost:true})));
  if(i===6 && !S.done[6]){ if(S.wsub===1){ for(let x=1;x<=n-2;x++) for(let y=1;y<=n-2;y++) sc.marks.push({p:[x,y,0],col:C.sel,ring:true,ghost:true,r:0.24,lw:1}); S.rows.forEach(y=>{ sc.lines.push({a:[1,y,0],b:[n-2,y,0],col:C.sel,w:7,al:0.85}); }); }
    else { S.spec.forEach(p=>sc.marks.push({p,col:C.H,r:0.36})); if(S.hints[6]>=1) SPECIAL_Y.forEach(y=>sc.marks.push({p:[mx(L),y,0],col:C.note,ring:true,r:0.6,dash:true})); } }
  // reveal
  if(S.reveal){ const from=marks[S.reveal.stage]; if(from!=null){ sc.reveal={from,to:res.length,t0:performance.now(),dur:Math.min(2200,300+(res.length-from)*1.2)}; } S.reveal=null; }
  view.c = i===8? [L/2,L/2,-1] : [L/2,L/2,L/2]; view.span = i===8? n+8 : n+2;
  view.sc=sc; view.request();
  // legend
  const lg=[['H','H','var(--h)'],['P','P','P']]; if(i>=7||S.done[7]) S.tail.forEach(b=>lg.push([b.id,b.id+' ('+b.size+')',b.col]));
  elLegend.innerHTML= i===2 ? (S.strIdx<SLOTS.length? `<span><i style="background:color-mix(in srgb,var(--accent) 30%,transparent);border:1.5px solid var(--accent)"></i>where ${SLOTS[S.strIdx].nm.replace(/<sub>(\d)<\/sub>/,(m,d)=>'₀₁₂₃₄₅₆₇₈₉'[d])} goes: ${SLOTS[S.strIdx].role}</span>` : '<span>The whole cube: every site gets exactly one H.</span>')
    : lg.map(([k,t,c])=>`<span><i style="${c==='P'?`background:var(--bg-elev);border:1.5px solid var(--p)`:`background:${c}`}"></i>${t}</span>`).join('') + (i>=3?`<span><i style="background:${C.ghost}"></i>empty surface site</span>`:'');
  elPill.textContent = i===9? `${fmt(N3)} H's · ${n}×${n}×${n} cube` : '';
  view.onPick = (!S.done[i] && P.pick && !S.playing)? P.pick : null; view.box.classList.toggle('pick', !!view.onPick);
}
function refreshAll(){ refreshLeft(); refreshTop(); sceneNow(); renderRail(); showIntro(); }
function renderAll(){ renderLevels(); refreshAll(); const P=PH[PH_IDS[S.ph]]; view.zoom=1; view.setView(S.ph===2&&S.strIdx<SLOTS.length? camFor(SLOTS[S.strIdx].id) : (P.cam||VIEWS.iso),true); }

/* ---------------- start ---------------- */
let shown=false, hovered=false;
function setShown(on){ shown=on; if(on){ readTheme(); view.cache={}; view.themeChanged&&view.themeChanged(); view.start(); renderAll(); } else view.stop(); }
document.documentElement.addEventListener('themechange',()=>{ readTheme(); view.cache={}; view.themeChanged&&view.themeChanged(); if(shown) refreshAll(); });
root.addEventListener('pointerenter',()=>{ hovered=true; }); root.addEventListener('pointerleave',()=>{ hovered=false; keysDown.clear(); });
setShown(true);
/* keyboard: W A S D or the arrow keys turn the cube (hold to keep turning), Q / E or − / + zoom, R resets the view.
   Ignored while typing in a box; the arrow keys are only taken over while the board is on screen. */
const keysDown=new Set(); let keyRaf=0, keyT=0;
const KEYMAP={a:'left',arrowleft:'left',d:'right',arrowright:'right',w:'up',arrowup:'up',s:'down',arrowdown:'down',q:'out','-':'out','_':'out',e:'in','+':'in','=':'in'};
const typing=e=>{ const t=e.target; return !!t && (t.isContentEditable || /^(INPUT|TEXTAREA|SELECT)$/.test(t.tagName)); };
const boardOnScreen=()=>{ const st=root.querySelector('.fg-stage'); if(!st||st.offsetParent===null) return false; const r=st.getBoundingClientRect(); return r.bottom>40 && r.top<innerHeight-40; };
function resetView(){ view.zoom=1; const P=PH[PH_IDS[S.ph]]; view.setView(S.ph===2&&S.strIdx<SLOTS.length? camFor(SLOTS[S.strIdx].id) : (P.cam||VIEWS.iso),true); }
document.addEventListener('keydown',e=>{ if(!shown||introOpen||typing(e)||e.ctrlKey||e.metaKey||e.altKey) return; const k=e.key.toLowerCase();
  if(!boardOnScreen() || !(hovered || root.contains(document.activeElement))) return;
  if(k==='r'){ e.preventDefault(); resetView(); return; }
  const a=KEYMAP[k]; if(!a) return; e.preventDefault(); keysDown.add(a);
  if(!keyRaf){ keyT=performance.now(); keyRaf=requestAnimationFrame(keyLoop); } });
document.addEventListener('keyup',e=>{ const a=KEYMAP[e.key.toLowerCase()]; if(a) keysDown.delete(a); });
window.addEventListener('blur',()=>keysDown.clear());
function keyLoop(t){ const dt=Math.min(0.05,(t-keyT)/1000); keyT=t; if(!keysDown.size||!shown){ keyRaf=0; return; }
  const sp=1.7*dt; view.tw=null;
  if(keysDown.has('left')) view.yaw-=sp; if(keysDown.has('right')) view.yaw+=sp;
  if(keysDown.has('up')) view.pitch=Math.min(1.45,view.pitch+sp); if(keysDown.has('down')) view.pitch=Math.max(-1.45,view.pitch-sp);
  if(view.zoom!=null){ if(keysDown.has('in')) view.zoom=Math.max(0.6,view.zoom*(1-dt*1.3)); if(keysDown.has('out')) view.zoom=Math.min(2,view.zoom*(1+dt*1.3)); }
  view.request(); keyRaf=requestAnimationFrame(keyLoop); }

}
