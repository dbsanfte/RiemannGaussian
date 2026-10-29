#!/usr/bin/env python3
"""Read-only source/dependency checkpoint and isolated strict builds of this slice.
Run --snapshot before freeze; default rechecks each source once in topological order.
No repository object is written. Dependency snapshots include all repository objects,
all imported external objects reachable through available source, and toolchain version.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess, time
repo=pathlib.Path('/home/dbsanfte/riemann/formal'); out=pathlib.Path('/tmp/semiprime-bit-execution-20261027/final-isolated');out.mkdir(exist_ok=True)
mods=['RiemannGaussian.SemiprimeJetBits', 'RiemannGaussian.SemiprimePolynomialCodeBits', 'RiemannGaussian.SemiprimeLocalBits', 'RiemannGaussian.SemiprimeLocalBitsCorrectness', 'RiemannGaussian.SemiprimeLocalBitsBounds', 'RiemannGaussian.SemiprimeMeasurementBits', 'RiemannGaussian.SemiprimeSupportRate', 'RiemannGaussian.SemiprimeScheduledSupportRate', 'RiemannGaussian.SemiprimeAcquiredPrefixSearch', 'RiemannGaussian.SemiprimePublicAcquiredExecution', 'RiemannGaussian.SemiprimeScheduledFactorExecution']
lake='/home/dbsanfte/.elan/bin/lake'
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=repo,text=True).strip().split(':')
source_roots=[repo,repo/'vendor/openai-semiprime',*sorted((repo/'.lake/packages').glob('*')),*sorted((repo/'vendor').glob('*')),pathlib.Path('/home/dbsanfte/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean')]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def source(m):
 rel=pathlib.Path(*m.split('.')).with_suffix('.lean')
 return next((p/rel for p in source_roots if (p/rel).is_file()),None)
def obj(m):
 rel=pathlib.Path(*m.split('.')).with_suffix('.olean')
 return next((pathlib.Path(p)/rel for p in paths if (pathlib.Path(p)/rel).is_file()),None)
def imports(m):
 p=source(m)
 if not p:return []
 return [x for line in p.read_text().splitlines() if re.match(r'^(?:public |private )?import ',line) for x in line.split('import ',1)[1].split('--',1)[0].split()]
seen=set();ordered=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 for d in imports(m):visit(d)
 ordered.append(m)
for m in mods:visit(m)
order=[m for m in ordered if m in mods]
def checkpoint():
 rows={}
 for m in sorted(seen):
  s,o=source(m),obj(m)
  rows[m]={'source':str(s) if s else None,'source_sha256':sha(s) if s else None,'object':str(o) if o else None,'object_sha256':sha(o) if o else None}
 return {'modules':rows,'toolchain':subprocess.check_output([lake,'env','lean','--version'],cwd=repo,text=True).strip()}
a=argparse.ArgumentParser();a.add_argument('--snapshot',action='store_true');args=a.parse_args()
before=checkpoint();(out/'dependencies-before.json').write_text(json.dumps(before,indent=2)+'\n')
if args.snapshot:
 print('snapshot',len(seen),'dependency modules; planned builds',len(order));raise SystemExit
results=[]
for m in order:
 s=source(m);o=out/(m.split('.')[-1]+'.olean');log=out/(m.split('.')[-1]+'.log');t=time.monotonic()
 with log.open('w') as f:p=subprocess.run([lake,'env','lean','-DautoImplicit=false','-DwarningAsError=true','-o',str(o),str(s.relative_to(repo))],cwd=repo,stdout=f,stderr=subprocess.STDOUT)
 row={'module':m,'exit_code':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(s),'isolated_sha256':sha(o) if o.exists() else None,'canonical_sha256':sha(obj(m)) if obj(m) else None}
 row['object_matches']=row['isolated_sha256']==row['canonical_sha256'];results.append(row)
 (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
 print(m,p.returncode,row['object_matches'],flush=True)
 if p.returncode:break
after=checkpoint();(out/'dependencies-after.json').write_text(json.dumps(after,indent=2)+'\n')
summary={'complete':len(results)==len(mods),'strict_pass':all(r['exit_code']==0 for r in results),'all_objects_match':all(r['object_matches'] for r in results),'dependency_snapshot_unchanged':before==after,'count':len(results)}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
assert all(summary[k] for k in ('complete','strict_pass','all_objects_match','dependency_snapshot_unchanged'))
