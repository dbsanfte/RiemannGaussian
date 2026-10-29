#!/usr/bin/env python3
"""Strict final checks for frozen acquisition/controller/selector modules; opt-in only."""
from pathlib import Path
import hashlib,json,subprocess,time,re
REPO=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-hermite-words-20261027')
LAKE='/home/dbsanfte/.elan/bin/lake'
OUT=WORK/'final-isolated'
OUT.mkdir(exist_ok=True)
mods=json.loads((WORK/'all-modules.json').read_text())
assert len(mods)==len(set(mods))
names=['RiemannGaussian.'+m for m in mods]
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base=(REPO/'docs/research-evidence/semiprime-paid-materialization-20261027/CombinedMaterializationAudit.lean').read_text()
body=base[base.index('run_cmd do'):]
a=body.index('  let expected : List Name :=');b=body.index('\n',a)
body=body[:a]+'  let expected : List Name := ['+', '.join('`'+m for m in names)+']'+body[b:]
body+='  liftIO <| IO.FS.writeFile '+json.dumps(str(WORK/'compiler-imports.json'))+' (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty\n'
audit=WORK/'CombinedHermiteWordsAudit.lean'
audit.write_text('import RiemannGaussian\n'+''.join('import '+m+'\n' for m in names)+'import Lean.Util.CollectAxioms\nimport Mathlib.Tactic.Linter\nopen Lean Elab Command\n'+''.join('#lint+ in '+m+'\n' for m in names)+body)
with (WORK/'CombinedHermiteWordsAudit.log').open('w') as f:
 p=subprocess.run([LAKE,'env','lean','-DautoImplicit=false','-DwarningAsError=true',str(audit)],cwd=REPO,stdout=f,stderr=subprocess.STDOUT)
assert p.returncode==0, 'combined root audit failed'
text=(WORK/'CombinedHermiteWordsAudit.log').read_text()
assert text.count('-- All linting checks passed!')==len(mods)
actual=json.loads((WORK/'compiler-imports.json').read_text())
assert set(names)<=set(actual)
assert len(actual)==len(set(actual))
assert not any(n.startswith('OAI.Algorithms.SubexponentialSAT') for n in actual), 'mixed original and vendored SAT branches'
paths=[Path(p) if Path(p).is_absolute() else REPO/p for p in subprocess.check_output([LAKE,'env','printenv','LEAN_PATH'],cwd=REPO,text=True).strip().split(':')]
paths.append(Path('/home/dbsanfte/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean'))
roots=[REPO,REPO/'vendor/openai-semiprime',REPO/'vendor/openai-quasi-rh',REPO/'vendor/zeta23',*sorted((REPO/'.lake/packages').glob('*')),Path('/home/dbsanfte/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean'),Path('/home/dbsanfte/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/lake')]
def resolve(m,roots,suffix):
 rel=Path(*m.split('.')).with_suffix(suffix)
 return next((root/rel for root in roots if (root/rel).is_file()),None)
def snapshot():
 rows={}
 for m in sorted(actual):
  s=resolve(m,roots,'.lean');o=resolve(m,paths,'.olean')
  assert o is not None, ('missing imported object',m)
  assert s is not None, ('missing imported source',m)
  rows[m]={'source':str(s) if s else None,'source_sha256':sha(s) if s else None,'object':str(o),'object_sha256':sha(o)}
 return {'provenance':'Lean environment header actual transitive imported module names; no source-text import scanner','modules':rows,'toolchain':subprocess.check_output([LAKE,'env','lean','--version'],cwd=REPO,text=True).strip()}
before=snapshot();dump(OUT/'dependencies-before.json',before)
results=[]
for m in actual:
 if m not in names:continue
 src=resolve(m,roots,'.lean');canonical=resolve(m,paths,'.olean')
 obj=OUT/(m.split('.')[-1]+'.olean');log=OUT/(m.split('.')[-1]+'.log');t=time.monotonic()
 with log.open('w') as f:
  p=subprocess.run([LAKE,'env','lean','-DautoImplicit=false','-DwarningAsError=true','-o',str(obj),str(src.relative_to(REPO))],cwd=REPO,stdout=f,stderr=subprocess.STDOUT)
 row={'module':m,'exit_code':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(src),'isolated_sha256':sha(obj) if obj.exists() else None,'canonical_sha256':sha(canonical)}
 row['object_matches']=row['isolated_sha256']==row['canonical_sha256'];results.append(row)
 dump(OUT/'results.json',results);print(m,p.returncode,row['object_matches'],flush=True)
 if p.returncode:raise SystemExit(p.returncode)
after=snapshot();dump(OUT/'dependencies-after.json',after)
summary={'complete':len(results)==len(mods),'strict_pass':all(x['exit_code']==0 for x in results),'all_objects_match':all(x['object_matches'] for x in results),'dependency_snapshot_unchanged':before==after,'count':len(results),'actual_compiler_imported_modules':len(actual),'resolved_sources':sum(x['source'] is not None for x in before['modules'].values()),'source_of_module_list':'Lean environment header'}
dump(OUT/'summary.json',summary);print(summary,flush=True)
assert all(summary[k] for k in ('complete','strict_pass','all_objects_match','dependency_snapshot_unchanged'))
