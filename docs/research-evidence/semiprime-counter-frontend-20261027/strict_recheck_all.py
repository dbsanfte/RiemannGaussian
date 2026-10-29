#!/usr/bin/env python3
"""Independent strict compilation and complete local-dependency stability check."""
from pathlib import Path
import hashlib,json,re,subprocess,time
ROOT=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-counter-frontend-20261027')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,v): p.write_text(json.dumps(v,indent=2)+'\n')
def snapshot(modules):
    seen=set();out={}
    def visit(name):
        if name in seen:return
        seen.add(name);rel=Path(*name.split('.'));src=ROOT/rel.with_suffix('.lean')
        if not src.exists():return
        obj=ROOT/'.lake/build/lib/lean'/rel.with_suffix('.olean')
        out[name]={'source_sha256':sha(src),'olean_sha256':sha(obj)}
        for dep in re.findall(r'^import\s+(\S+)',src.read_text(),re.M):visit(dep)
    for m in modules:visit('RiemannGaussian.'+m)
    return out
mods=json.loads((WORK/'all-modules.json').read_text());(WORK/'strict-objects').mkdir(exist_ok=True)
olddeps=json.loads((WORK/'strict-dependency-snapshot.json').read_text())
old=json.loads((WORK/'all-strict-recheck.json').read_text())['modules']
for r in json.loads((WORK/'strict-recheck.json').read_text()):
    m=r['module']
    old[m]={'exit_code':r['exit_code'],'seconds':r['seconds'],'source_sha256':r['source_sha256'],
        'root_olean_sha256':r['dependency_sha256'],'olean_sha256':r['isolated_sha256'],
        'log_sha256':sha(WORK/(m+'-isolated.log')),'isolated_matches_root_olean':r['identical_object'],
        'prior_object':str(WORK/(m+'.olean')),'prior_log':str(WORK/(m+'-isolated.log'))}
before=snapshot(mods);dump(WORK/'strict-dependency-snapshot.json',before)
result={}
import shutil
for name in mods:
    source=ROOT/'RiemannGaussian'/f'{name}.lean';obj=WORK/'strict-objects'/f'{name}.olean'
    rootobj=ROOT/'.lake/build/lib/lean/RiemannGaussian'/f'{name}.olean';log=WORK/f'{name}-strict.log'
    prev=old.get(name);closure=snapshot([name])
    reusable=prev and prev['exit_code']==0 and prev['source_sha256']==sha(source) and prev['root_olean_sha256']==sha(rootobj) and prev['isolated_matches_root_olean'] and all(olddeps.get(k)==v for k,v in closure.items())
    if reusable:
        p_obj=Path(prev.get('prior_object',str(obj)));p_log=Path(prev.get('prior_log',str(log)))
        assert sha(p_obj)==prev['olean_sha256'] and sha(p_log)==prev['log_sha256']
        if p_obj!=obj:shutil.copyfile(p_obj,obj)
        if p_log!=log:shutil.copyfile(p_log,log)
        result[name]={k:v for k,v in prev.items() if not k.startswith('prior_')}
        result[name]['reused_unchanged_source_object_dependency_check']=True
    else:
        start=time.monotonic()
        with log.open('w') as out:
            p=subprocess.run(['/home/dbsanfte/.elan/bin/lake','env','lean','-DautoImplicit=false','-DwarningAsError=true','-o',str(obj),str(source.relative_to(ROOT))],cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
        result[name]={'exit_code':p.returncode,'seconds':time.monotonic()-start,'source_sha256':sha(source),'root_olean_sha256':sha(rootobj),'olean_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log)}
        result[name]['isolated_matches_root_olean']=result[name]['olean_sha256']==result[name]['root_olean_sha256']
    dump(WORK/'all-strict-recheck.json',{'modules':result,'complete':len(result)==len(mods)})
    print(name,result[name]['exit_code'],result[name]['isolated_matches_root_olean'],'reused' if reusable else 'rebuilt',flush=True)
    assert result[name]['exit_code']==0 and result[name]['isolated_matches_root_olean'],name
assert snapshot(mods)==before,'Dependencies changed during strict audit'
print('PASS',len(result),'independently strict modules;',len(before),'stable local dependencies',flush=True)
