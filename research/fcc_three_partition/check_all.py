"""Run all deterministic certificate checks; heuristic searches are excluded."""
import hashlib, json, subprocess, sys, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
scripts=['verify.py','cap_theorem.py','verify_periodic.py','universal_competitor.py',
         'robust_checks.py','routing.py','enumerate_layers.py','marker_family_bound.py','verify_markers.py']
result=[]
for name in scripts:
    start=time.monotonic()
    run=subprocess.run([sys.executable,str(ROOT/name)],cwd=ROOT,capture_output=True,text=True)
    result.append(dict(script=name,exit_code=run.returncode,seconds=round(time.monotonic()-start,3),
                       stdout=run.stdout,stderr=run.stderr))
    print(name,'PASS' if run.returncode==0 else 'FAIL',flush=True)
    if run.returncode:break
manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in ROOT.glob('*.json')
          if p.name not in ('check_results.json','certificate_hashes.json')}
(ROOT/'check_results.json').write_text(json.dumps(result,indent=2)+'\n')
(ROOT/'certificate_hashes.json').write_text(json.dumps(manifest,indent=2)+'\n')
if len(result)!=len(scripts) or any(r['exit_code'] for r in result):raise SystemExit(1)
