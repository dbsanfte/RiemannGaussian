#!/usr/bin/env python3
"""Isolated strict check of only the two new physical modules; no dependency writes."""
from pathlib import Path
import hashlib,json,subprocess,time
r=Path('/home/dbsanfte/riemann/formal');s=Path('/tmp/semiprime-bit-execution-20261027');rows=[]
def h(x):return hashlib.sha256(x.read_bytes()).hexdigest()
for m in ['SemiprimeJetBits','SemiprimePolynomialCodeBits']:
 p=r/'RiemannGaussian'/(m+'.lean');o=s/(m+'.olean');before=h(p);t=time.monotonic()
 with (s/(m+'-isolated.log')).open('w') as f:
  q=subprocess.run(['/home/dbsanfte/.elan/bin/lake','env','lean','-DautoImplicit=false','-DwarningAsError=true','-o',str(o),str(p.relative_to(r))],cwd=r,stdout=f,stderr=subprocess.STDOUT)
 row={'module':m,'exit_code':q.returncode,'source_sha256':h(p),'source_unchanged':h(p)==before,'isolated_sha256':h(o) if o.exists() else None,'canonical_sha256':h(r/'.lake/build/lib/lean/RiemannGaussian'/(m+'.olean')),'seconds':time.monotonic()-t};row['object_identical']=row['isolated_sha256']==row['canonical_sha256'];rows.append(row)
 (s/'physical-compiler-isolated.json').write_text(json.dumps(rows,indent=2)+'\n')
 assert row['exit_code']==0 and row['source_unchanged'] and row['object_identical']
print('2 isolated strict/object-identity checks PASS')
