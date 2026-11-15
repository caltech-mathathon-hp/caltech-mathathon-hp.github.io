// Bounded randomized depth-first threading of an enumerated periodic H core.
// Success is a coordinate certificate. Failure is not an infeasibility proof.
const fs=require('fs'),path=require('path');
const cores=JSON.parse(fs.readFileSync(path.join(__dirname,'layer_enumeration.json'))).sheared_survivors;
const ci=Number(process.argv[2]||2),seconds=Number(process.argv[3]||300),program=process.argv[4]||'00',core=cores[ci];
const cellOnly=process.argv[5]==='cell';
const fixedPorts=process.argv[6]==='ports';
const universalPorts=process.argv[6]==='universal';
const U=['PHP'.repeat(2)+'PHH'+'PHP'.repeat(3),'HHP'+'PHP'.repeat(5)];
const markers=program.startsWith('m')?program.slice(1).split('_').map(Number):null;
function marked(i){let chars=[...'PHP'.repeat(6)];if(chars[i]!=='P')throw Error('not a P position');chars[i]='H';return chars.join('')}
const word=markers?markers.map(marked).join(''):[...program].map(x=>U[Number(x)]).join('');
if(word.length!==36)throw Error('two modules required');
const T=[2,...core.shear],add=(a,b)=>a.map((v,i)=>v+b[i]),sub=(a,b)=>a.map((v,i)=>v-b[i]),scale=(p,t)=>p.map(v=>v*t);
const aux=([x,y,z])=>{let r=(x-y-z)/2;return[r,y+r,x-r]},phys=([r,s,k])=>[r+k,-r+s,-s+k];
const dirs=[];for(let x=-1;x<=1;x++)for(let y=-1;y<=1;y++)for(let z=-1;z<=1;z++)if(x*x+y*y+z*z===2)dirs.push(aux([x,y,z]));
function normalize(p){let t=Math.floor(p[0]/2);return[sub(p,scale(T,t)),t]}
const key=p=>normalize(p)[0].join(',');
const H=core.A.map(p=>[0,...p]).concat(core.B.map(p=>[1,...p]));
const hmap=new Map(H.map((p,i)=>[key(p),i]));let P=new Map();
for(let p of H)for(let d of dirs){let q=add(p,d),k=key(q);if(!hmap.has(k)&&!P.has(k))P.set(k,P.size)}
const options=Array.from({length:14},()=>[[],[],[],[]]);
for(let i=0;i<14;i++){
 function grow(points,pids){let cur=points[points.length-1],g=points.length;
  if(g>3)return;
  for(let d of dirs){let q=add(cur,d),k=key(q),j=hmap.get(k);
   if(j!==undefined){if(j!==i)options[i][g].push({j,shift:normalize(q)[1],points:points.slice(1).concat([q]),pids:pids.slice()});continue}
   let pid=P.get(k);if(pid===undefined||pids.includes(pid))continue;
   grow(points.concat([q]),pids.concat([pid]));
  }
 }grow([H[i]],[])
}
let state=619;const rand=()=>{state^=state<<13;state^=state>>>17;state^=state<<5;return(state>>>0)/4294967296};
function shuffle(a){for(let i=a.length-1;i>0;i--){let j=Math.floor(rand()*(i+1));[a[i],a[j]]=[a[j],a[i]]}return a}
const hindices=[...word].flatMap((c,i)=>c==='H'?[i]:[]),first=hindices[0];
const gaps=hindices.map((i,j)=>(j+1<hindices.length?hindices[j+1]:hindices[0]+36)-i);
const startTime=Date.now();let visited=0,attempts=0,solution=null,startH;
while(Date.now()-startTime<seconds*1000&&!solution){startH=(fixedPorts||universalPorts)?1:attempts%14;attempts++;let local=0,usedP=new Set(),walk=[H[startH]];
 function dfs(depth,h,shift,mask){visited++;local++;if(local>200000||(visited%10000===0&&Date.now()-startTime>seconds*1000))return false;
  let opts=shuffle(options[h][gaps[depth]].slice());
  for(let o of opts){let ns=shift+o.shift;
   if(depth===13){if(o.j!==startH||ns!==1)continue}
   else if((mask&(1<<o.j))||(cellOnly&&ns!==0))continue;
   if(cellOnly&&o.points.slice(0,-1).some(p=>p[0]+shift*T[0]<0||p[0]+shift*T[0]>1))continue;
   if(fixedPorts&&depth===13&&add(o.points[o.points.length-2],scale(T,shift)).join(',')!=='1,1,2')continue;
   if(universalPorts){let pp=o.points.slice(0,-1).map(p=>add(p,scale(T,shift)).join(','));
    if(pp.some((p,i)=>p==='1,1,2'&&!(depth===13&&first===1&&i===pp.length-1)))continue;
    if(depth===13){let finished=walk.concat(o.points.map(p=>add(p,scale(T,shift))));
     if(finished[35-first].join(',')!==(word[35]==='H'?'1,1,1':'1,0,1'))continue;
     if(first===1&&finished[35].join(',')!=='1,1,2')continue;
    }
   }
   if(o.pids.some(p=>usedP.has(p)))continue;
   const remain=gaps.slice(depth+1).reduce((a,b)=>a+b,0),dd=phys(sub(add(H[o.j],scale(T,ns)),add(H[startH],T))).map(Math.abs);
   if(Math.max(...dd)>remain||dd.reduce((a,b)=>a+b,0)>2*remain)continue;
   let oldlen=walk.length;walk.push(...o.points.map(p=>add(p,scale(T,shift))));o.pids.forEach(p=>usedP.add(p));
   if(depth===13||dfs(depth+1,o.j,ns,mask|(1<<o.j))){solution=walk.slice();return true}
   walk.length=oldlen;o.pids.forEach(p=>usedP.delete(p));
  }return false;
 }dfs(0,startH,0,1<<startH);
 if(attempts%100===0)console.log(JSON.stringify({attempts,visited,elapsed:(Date.now()-startTime)/1000}));
}
if(solution){let q=solution.slice(0,-1),positions=first?[...q.slice(-first).map(p=>sub(p,T)),...q.slice(0,-first)]:q;
 const hh=[...word].filter((c,i)=>c==='H'&&word[(i+1)%36]==='H').length;
 const result={kind:'periodic core threading certificate',core_index:ci,L:2,mode:'program',program,markers,cellOnly,word,translation_aux:T,positions_aux:positions,score_per_period:53-hh,baseline:50,attempts,visited};
 const filename=markers?`marker_${markers.join('_')}.json`:`periodic_threaded_${ci}${program==='00'?'':'_'+program}${cellOnly?'_cell':''}${fixedPorts?'_ports':''}${universalPorts?'_universal':''}.json`;
 fs.writeFileSync(path.join(__dirname,filename),JSON.stringify(result,null,2));
 console.log(JSON.stringify({found:true,attempts,visited,seconds:(Date.now()-startTime)/1000}));
}else console.log(JSON.stringify({found:false,attempts,visited,seconds:(Date.now()-startTime)/1000}));
