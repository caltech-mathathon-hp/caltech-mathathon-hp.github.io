"""Second bounded search pass; an unsuccessful run proves nothing."""
import json, subprocess, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
first=json.loads((ROOT/'marker_search_log.json').read_text())
results=[];start=time.time()
for record in first:
    a,b=record['markers']
    if (ROOT/f'marker_{a}_{b}.json').exists():continue
    before=time.time()
    run=subprocess.run(['node',str(ROOT/'thread_core.js'),'2','20',f'm{a}_{b}','cell','universal'],
                       capture_output=True,text=True,timeout=30,cwd=ROOT)
    results.append(dict(markers=[a,b],returncode=run.returncode,seconds=round(time.time()-before,3),output=run.stdout.strip()))
    (ROOT/'marker_retry_log.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(dict(markers=[a,b],found=(ROOT/f'marker_{a}_{b}.json').exists(),elapsed=round(time.time()-start,1))),flush=True)
