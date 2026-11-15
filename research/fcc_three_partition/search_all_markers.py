"""Bounded search for all one-marker word pairs on the common H core."""
import itertools as it, json, subprocess, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
markers=[i for i,c in enumerate('PHP'*6) if c=='P']
start=time.time(); results=[]
for a,b in it.product(markers,repeat=2):
    before=time.time()
    run=subprocess.run(['node',str(ROOT/'thread_core.js'),'2','5',f'm{a}_{b}','cell','universal'],
                       capture_output=True,text=True,timeout=15,cwd=ROOT)
    result=dict(markers=[a,b],returncode=run.returncode,seconds=round(time.time()-before,3),output=run.stdout.strip())
    results.append(result)
    (ROOT/'marker_search_log.json').write_text(json.dumps(results,indent=2)+'\n')
    if len(results)%12==0:
        print(json.dumps(dict(completed=len(results),certificates=len(list(ROOT.glob('marker_[0-9]*.json'))),
                              elapsed=round(time.time()-start,1))),flush=True)
