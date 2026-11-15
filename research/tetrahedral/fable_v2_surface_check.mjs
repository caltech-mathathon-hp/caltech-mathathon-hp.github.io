// Apply the independent coordinate checker to the revised explicit routes,
// the two finite representatives, a three-item layout, and K>8 actual inputs.
import fs from 'node:fs';
import assert from 'node:assert/strict';
const manuscript=fs.readFileSync(new URL('./fable_review_v2_2026_11_14/HP_tetrahedral_review/HP_tetrahedral_proof.md',import.meta.url),'utf8');
const prior=fs.readFileSync(new URL('../../background/HP_tetrahedral_proof_Astra.md',import.meta.url),'utf8');
assert.deepEqual(manuscript.split(/\r?\n/).filter(l=>l.startsWith('* Vertex ')),prior.split(/\r?\n/).filter(l=>l.startsWith('* Vertex ')));
let source=fs.readFileSync(new URL('./fable_surface_generated.mjs',import.meta.url),'utf8');
source=source.replace('function surface(m,K,B,unitItems=false) {','function surface(m,K,B,unitItems=false,layout=null) {');
const old='const Sigma=18*K+40,C=(Sigma+8)*B,J=C+Sigma+8,Rfill=C+Sigma+9;';
assert(source.includes(old));
source=source.replace(old,'const Sigma=layout?layout.lambda-8:18*K+40,C=layout?layout.C:(Sigma+8)*B,J=layout?layout.J:C+Sigma+8,Rfill=layout?layout.R:C+Sigma+9;');
const index=source.indexOf('const results=[];\nfor(const [K,B,unitItems]');assert(index>=0);
source=source.slice(0,index)+`const results=[];
for(const [m,K,C,Rfill] of [[80,8,4,15],[80,2,8,43],[80,1,12,49]]) {
 const result=surface(m,K,C/4,true,{lambda:4,C,J:14,R:Rfill});results.push({...result,layout:'finite-family'});console.log(JSON.stringify(results.at(-1)));
}
for(const [K,B] of [[1,1],[12,1]]) {
 const m=(K+2)*(18*K+48)*B+38*K+100;
 const result=surface(m,K,B,true);results.push({...result,layout:'actual-reduction'});console.log(JSON.stringify(results.at(-1)));
}
fs.writeFileSync(new URL('./fable_v2_surface_results.json',import.meta.url),JSON.stringify(results,null,2)+'\\n');
`;
const path=new URL('./fable_v2_surface_generated.mjs',import.meta.url);fs.writeFileSync(path,source);await import(path.href);
