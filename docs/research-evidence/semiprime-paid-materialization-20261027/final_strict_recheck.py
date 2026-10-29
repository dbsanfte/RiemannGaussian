#!/usr/bin/env python3
"""Opt-in original-OAI branch: pin dependencies and recompile only new leaves."""
import hashlib,json,pathlib,re,subprocess,time
repo=pathlib.Path('/home/dbsanfte/riemann/formal')
work=pathlib.Path('/tmp/semiprime-ternary-machine-20261027')
out=work/'final-isolated';out.mkdir(exist_ok=True)
upstream=pathlib.Path('/tmp/semiprime-d1-audit-20261026/openai-math/lean')
original=pathlib.Path('/tmp/semiprime-d1-audit-20261026/lean-build')
names=['SemiprimeTernaryFactor','SemiprimeTernaryPublicFactor','SemiprimeTernaryLocal','SemiprimeTernaryLocalPaid','SemiprimeBooleanRingFactor','SemiprimeParametricFactorLoop','SemiprimeParametricFactorFrame']
mods=['RiemannGaussian.'+m for m in names]
lake='/home/dbsanfte/.elan/bin/lake'
paths=[work/'original-imports',*[pathlib.Path(p) for p in subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=repo,text=True).strip().split(':')]]
roots=[repo,upstream,repo/'vendor/openai-quasi-rh',*sorted((repo/'.lake/packages').glob('*')),pathlib.Path('/home/dbsanfte/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean')]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def source(m):
 r=pathlib.Path(*m.split('.')).with_suffix('.lean')
 return next((p/r for p in roots if (p/r).is_file()),None)
def obj(m):
 r=pathlib.Path(*m.split('.')).with_suffix('.olean')
 return next((p/r for p in paths if (p/r).is_file()),None)
seen=set();order=[]
def visit(m):
 if m in seen:return
 assert not m.startswith('OpenAISemiprime'), 'mixed original/vendor namespace'
 seen.add(m);s=source(m)
 if s:
  for line in s.read_text().splitlines():
   if re.match(r'^(?:public |private )?import ',line):
    for dep in line.split('import ',1)[1].split('--',1)[0].split():visit(dep)
 order.append(m)
for m in ['RiemannGaussian',*mods]:visit(m)
def checkpoint():
 rows={}
 for m in sorted(seen):
  s,o=source(m),obj(m)
  rows[m]={'source':str(s) if s else None,'source_sha256':sha(s) if s else None,'object':str(o) if o else None,'object_sha256':sha(o) if o else None}
 return {'modules':rows,'no_OpenAISemiprime':True,'toolchain':subprocess.check_output([lake,'env','lean','--version'],cwd=repo,text=True).strip()}
# Verify original sources AND compiled objects against the previously sealed full build.
state=json.loads(pathlib.Path('/tmp/semiprime-d1-audit-20261026/lean-build-state.json').read_text())
assert state['status']=='complete' and state['commit']=='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a'
for m,x in state['completed'].items():
 rel=pathlib.Path(*m.split('.'))
 assert sha(upstream/rel.with_suffix('.lean'))==x['source_sha256'],m
 assert sha(original/rel.with_suffix('.olean'))==x['olean_sha256'],m
(out/'original-closure-check.json').write_text(json.dumps({'status':'PASS','modules':len(state['completed']),'commit':state['commit'],'rebuilt':False},indent=2)+'\n')
before=checkpoint();(out/'dependencies-before.json').write_text(json.dumps(before,indent=2)+'\n')
results=[]
for m in order:
 if m not in mods:continue
 s=source(m);o=out/(m.split('.')[-1]+'.olean');log=out/(m.split('.')[-1]+'.log');t=time.monotonic()
 with log.open('w') as f:
  p=subprocess.run(['python3',str(work/'run_with_upstream.py'),'-o',str(o),str(s.relative_to(repo))],cwd=repo,stdout=f,stderr=subprocess.STDOUT)
 row={'module':m,'exit_code':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(s),'isolated_sha256':sha(o) if o.exists() else None,'canonical_sha256':sha(obj(m)) if obj(m) else None}
 row['object_matches']=row['isolated_sha256']==row['canonical_sha256'];results.append(row)
 (out/'results.json').write_text(json.dumps(results,indent=2)+'\n');print(m,p.returncode,row['object_matches'],flush=True)
 if p.returncode:break
after=checkpoint();(out/'dependencies-after.json').write_text(json.dumps(after,indent=2)+'\n')
summary={'complete':len(results)==len(mods),'strict_pass':all(x['exit_code']==0 for x in results),'all_objects_match':all(x['object_matches'] for x in results),'dependency_snapshot_unchanged':before==after,'count':len(results),'dependency_modules':len(seen)}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
assert all(summary[k] for k in ('complete','strict_pass','all_objects_match','dependency_snapshot_unchanged'))
