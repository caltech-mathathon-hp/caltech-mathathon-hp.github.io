// Adapt the independent raw-coordinate near-field checker to the exact Appendix C
// borrowed column and the explicit entry route of Fable's review manuscript.
import fs from 'node:fs';
const source=fs.readFileSync(new URL('./astra_surface_check.mjs',import.meta.url),'utf8');
let revised=source.replace("const start=[m-2-3*k+j,3*k+j-1,1]","const start=[m-3-3*k+j,3*k+j,1]")
 .replace('3+10*k:','3+10*k+2:')
 .replace("(c.name==='left-filler'?-1:1)","(c.name==='left-filler'||c.name.endsWith('-b')?-1:1)")
 .replace("'./astra_surface_results.json'","'./fable_surface_results.json'");
if(revised===source)throw Error('Failed to adapt source');
// This generated module is saved next to its relative imports for reproducibility.
const path=new URL('./fable_surface_generated.mjs',import.meta.url);
fs.writeFileSync(path,revised);
await import(path.href);
