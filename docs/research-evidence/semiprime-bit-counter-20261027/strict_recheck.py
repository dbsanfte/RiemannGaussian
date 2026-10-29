"""Independent strict source recompilation; root imports remain untouched."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib,json,subprocess,sys,re,time
ROOT=Path('/home/dbsanfte/riemann/formal');WORK=Path('/tmp/semiprime-bit-counter-20261027')
NAMES=json.loads((WORK/'new-modules.json').read_text());selected=sys.argv[1:] or NAMES
assert set(selected)<=set(NAMES)
OBJECTS=WORK/'strict-objects';OBJECTS.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def source(name):return ROOT/(name.replace('.','/')+'.lean')
def obj(name):return ROOT/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean')
def local_closure(name,seen=None):
 seen=set() if seen is None else seen
 if name in seen:return seen
 seen.add(name)
 p=source(name)
 assert p.is_file(),str(p)
 for dep in re.findall(r'^import\s+(RiemannGaussian(?:\.[A-Za-z0-9_]+)*)\s*$',p.read_text(),re.M):local_closure(dep,seen)
 return seen
closure=set()
for n in selected:closure |=local_closure('RiemannGaussian.'+n)
snapshot={n:{'source_sha256':sha(source(n)),'olean_sha256':sha(obj(n))} for n in sorted(closure)}
(WORK/'strict-dependency-snapshot.json').write_text(json.dumps(snapshot,indent=2)+'\n')
def build(name):
 full='RiemannGaussian.'+name;src=source(full);out=OBJECTS/(name+'.olean');log=WORK/(name+'-strict.log')
 before=sha(src);root_before=sha(obj(full));started=time.monotonic()
 cmd=['/home/dbsanfte/.elan/bin/lake','env','lean','-DautoImplicit=false','-DwarningAsError=true','-o',str(out),str(src.relative_to(ROOT))]
 with log.open('w') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
 item={'command':cmd,'exit_code':r.returncode,'source_sha256':before,'source_unchanged':sha(src)==before,
       'root_olean_sha256':root_before,'root_olean_unchanged':sha(obj(full))==root_before,
       'log_sha256':sha(log),'elapsed_seconds':round(time.monotonic()-started,3)}
 if r.returncode==0:
  item['olean_sha256']=sha(out);item['isolated_matches_root_olean']=item['olean_sha256']==root_before
 print(json.dumps({'module':name,'exit_code':r.returncode,'isolated_matches_root':item.get('isolated_matches_root_olean')}),flush=True)
 return name,item
with ThreadPoolExecutor(max_workers=2) as pool:items=dict(pool.map(build,selected))
if set(selected)!=set(NAMES):
 prior=json.loads((WORK/'strict-recheck.json').read_text()) if (WORK/'strict-recheck.json').exists() else {};prior.update(items);items=prior
stable=all(sha(source(n))==v['source_sha256'] and sha(obj(n))==v['olean_sha256'] for n,v in snapshot.items())
(WORK/'strict-recheck.json').write_text(json.dumps({'modules':items,'local_dependency_count':len(snapshot),
 'dependency_sources_objects_unchanged':stable,'isolated_objects_not_used_to_overwrite_root':True},indent=2)+'\n')
assert stable,'Local source/dependency objects changed during recheck'
assert all(v['exit_code']==0 and v['source_unchanged'] and v['root_olean_unchanged'] and v['isolated_matches_root_olean'] for v in items.values()),'Strict check or exact root-object match failed'
