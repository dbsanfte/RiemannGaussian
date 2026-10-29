from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib,json,subprocess
root=Path('/home/dbsanfte/riemann/formal');work=Path('/tmp/semiprime-counter-compose-20261026')
names=['SemiprimeCounterNative','SemiprimeCounterSeparation','SemiprimeCounterCompose','SemiprimeCounterTail','SemiprimeJetRecurrence','SemiprimeBooleanNetwork','SemiprimeCounterSearch','SemiprimeMacroBitNetwork']
objects=work/'strict-objects';objects.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def build(name):
 src=root/'RiemannGaussian'/(name+'.lean');obj=objects/(name+'.olean');log=work/(name+'-strict.log')
 before=sha(src)
 cmd=['/home/dbsanfte/.elan/bin/lake','env','lean','-DautoImplicit=false','-DwarningAsError=true','-o',str(obj),str(src.relative_to(root))]
 with log.open('w') as out:r=subprocess.run(cmd,cwd=root,stdout=out,stderr=subprocess.STDOUT)
 assert sha(src)==before,name+' source changed'
 item={'command':cmd,'exit_code':r.returncode,'source_sha256':before,'log_sha256':sha(log)}
 if r.returncode==0:item['olean_sha256']=sha(obj)
 print(json.dumps({'module':name,'exit_code':r.returncode}),flush=True)
 return name,item
with ThreadPoolExecutor(max_workers=4) as pool:items=dict(pool.map(build,names))
(work/'strict-recheck.json').write_text(json.dumps(items,indent=2)+'\n')
assert all(item['exit_code']==0 for item in items.values()),'Strict source check failed; see module log'
