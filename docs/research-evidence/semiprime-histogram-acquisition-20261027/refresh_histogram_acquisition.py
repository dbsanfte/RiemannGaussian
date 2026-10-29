#!/usr/bin/env python3
"""Refresh only this packet's new modules in recorded dependency order."""
from pathlib import Path
import hashlib,json,subprocess,time
ROOT=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-histogram-acquisition-20261027')
LAKE='/home/dbsanfte/.elan/bin/lake'
mods=json.loads((WORK/'all-modules.json').read_text())
rows=[]
for m in mods:
 src=ROOT/'RiemannGaussian'/(m+'.lean')
 obj=ROOT/'.lake/build/lib/lean/RiemannGaussian'/(m+'.olean')
 log=WORK/'canonical-refresh'/(m+'.log');log.parent.mkdir(exist_ok=True)
 t=time.monotonic()
 with log.open('w') as f:
  p=subprocess.run([LAKE,'env','lean','-DautoImplicit=false','-DwarningAsError=true','-o',str(obj),str(src.relative_to(ROOT))],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
 rows.append({'module':m,'exit_code':p.returncode,'seconds':time.monotonic()-t,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest() if obj.exists() else None})
 (WORK/'canonical-refresh/results.json').write_text(json.dumps(rows,indent=2)+'\n')
 print(m,p.returncode,flush=True)
 if p.returncode:raise SystemExit(p.returncode)
print('CANONICAL_REFRESH_PASS',len(rows),flush=True)
