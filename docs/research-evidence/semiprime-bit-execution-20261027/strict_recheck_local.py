#!/usr/bin/env python3
"""Isolated strict elaboration; never modifies dependency objects."""
import hashlib,json,pathlib,subprocess,time
repo=pathlib.Path('/home/dbsanfte/riemann/formal')
out=pathlib.Path('/tmp/semiprime-bit-execution-20261027')
mods=['SemiprimeLocalBits','SemiprimeLocalBitsCorrectness','SemiprimeLocalBitsBounds']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for m in mods:
 src=repo/'RiemannGaussian'/f'{m}.lean'; root=repo/'.lake/build/lib/lean/RiemannGaussian'/f'{m}.olean'; obj=out/f'{m}.olean'; log=out/f'{m}-isolated.log'; before=sha(src); t=time.monotonic()
 with log.open('w') as f:
  p=subprocess.run(['/home/dbsanfte/.elan/bin/lake','env','lean','-DautoImplicit=false','-DwarningAsError=true','-o',str(obj),str(src.relative_to(repo))],cwd=repo,stdout=f,stderr=subprocess.STDOUT)
 row=dict(module=m,source_sha256=sha(src),source_unchanged=before==sha(src),exit_code=p.returncode,isolated_sha256=sha(obj) if obj.exists() else None,dependency_sha256=sha(root),seconds=time.monotonic()-t)
 row['identical_object']=row['isolated_sha256']==row['dependency_sha256'];rows.append(row)
 if p.returncode:break
(out/'strict-recheck.json').write_text(json.dumps(rows,indent=2)+'\n')
assert len(rows)==len(mods) and all(r['exit_code']==0 and r['source_unchanged'] and r['identical_object'] for r in rows)
