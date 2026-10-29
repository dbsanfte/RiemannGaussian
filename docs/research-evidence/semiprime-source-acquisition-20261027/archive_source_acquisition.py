#!/usr/bin/env python3
"""Archive the verified source acquisition slice, preserving all previous work."""
from pathlib import Path
import hashlib,json,re,shutil,subprocess
ROOT=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-source-acquisition-20261027')
PACKET=ROOT/'docs/research-evidence/semiprime-source-acquisition-20261027'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def preserve(base):
 for k in ['protected','concurrent']:
  for rel,digest in base[k].items():assert sha(ROOT/rel)==digest,(k,rel)
 for rel,x in base['prefixes'].items():
  assert hashlib.sha256((ROOT/rel).read_bytes()[:x['bytes']]).hexdigest()==x['sha256'],rel
base=json.loads((WORK/'preservation-before.json').read_text());preserve(base)
assert not PACKET.exists(),'Existing archive must be inspected, not overwritten'
mods=json.loads((WORK/'all-modules.json').read_text());assert len(mods)==len(set(mods))==20
log=(WORK/'CombinedSourceAcquisitionAudit.log').read_text()
assert log.count('-- All linting checks passed!')==20 and 'error:' not in log and 'sorryAx' not in log
au={m:{'declarations':int(d),'theorem_constants':int(t)} for m,d,t in re.findall(r'^AUDIT RiemannGaussian\.(\w+): declarations=(\d+), theorems=(\d+), standard_axioms_only=true$',log,re.M)}
assert set(au)==set(mods)
assert sum(x['declarations'] for x in au.values())==573 and sum(x['theorem_constants'] for x in au.values())==361
isolated=WORK/'final-isolated';summary=json.loads((isolated/'summary.json').read_text())
assert all(summary[k] for k in ['complete','strict_pass','all_objects_match','dependency_snapshot_unchanged'])
results=json.loads((isolated/'results.json').read_text());assert {x['module'] for x in results}=={'RiemannGaussian.'+m for m in mods}
before=json.loads((isolated/'dependencies-before.json').read_text());after=json.loads((isolated/'dependencies-after.json').read_text());assert before==after
moduleinfo={}
for x in results:
 name=x['module'].split('.')[-1];source=ROOT/'RiemannGaussian'/(name+'.lean');obj=ROOT/'.lake/build/lib/lean/RiemannGaussian'/(name+'.olean')
 assert x['exit_code']==0 and x['object_matches']
 assert sha(source)==x['source_sha256']
 assert sha(obj)==x['canonical_sha256']==x['isolated_sha256']==sha(isolated/(name+'.olean'))
 clean=re.sub(r'/-.*?-/', '',source.read_text(),flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|admit|sorryAx|native_decide)\b',clean),name
 moduleinfo[name]={'source':str(source.relative_to(ROOT)),'source_sha256':sha(source),'olean_sha256':sha(obj),**au[name]}
# Check every recorded local review hash, including proof/diagnostic references.
def checkpins(x):
 if not isinstance(x,dict):return
 for k,v in x.items():
  if isinstance(v,dict):checkpins(v)
  elif isinstance(v,str) and re.fullmatch('[0-9a-f]{64}',v):
   if k.startswith('/'):p=Path(k)
   elif k.startswith('RiemannGaussian/'):p=ROOT/k
   else:p=WORK/k
   if p.is_file():assert sha(p)==v,('review pin',str(p))
for p in WORK.glob('*hash*.json'):checkpins(json.loads(p.read_text()))
assert (WORK/'acquired-source-smoke.log').read_text().strip()=='1\n2\n0'
assert (WORK/'original-source-array-smoke.log').read_text().strip()=='#[#[#[1, 0], #[0, 0]], #[#[0, 0], #[1, 0]]]\n#[1, 0]\n#[0, 0]\n#[1, 0]'
assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
selected={p.relative_to(WORK):p for p in WORK.iterdir() if p.is_file() and p.suffix in ['.md','.json']}
for pat in ['*-build.log','*-audit.log','*-smoke.log','*-root-audit.lean','*-isolated.log']:
 for p in WORK.glob(pat):selected[p.relative_to(WORK)]=p
for name in ['CombinedSourceAcquisitionAudit.lean','CombinedSourceAcquisitionAudit.log','CombinedUniversalSourceAudit.lean','RootSourceAudit.lean','CheckSourceSuppliers.lean',
 'AcquiredSourceCounterSmoke.lean','BinomialSmoke.lean','OriginalSourceArraySmoke.lean','RuntimeRawSmoke.lean','SourceArraySmoke.lean','SourceConstraintSmoke.lean',
 'final_strict_recheck.py','strict_recheck_universal.py','archive_source_acquisition.py']:
 selected[Path(name)]=WORK/name
for p in isolated.iterdir():
 if p.suffix in ['.json','.log']:selected[p.relative_to(WORK)]=p
for name in mods:selected[Path(name+'.lean')]=ROOT/'RiemannGaussian'/(name+'.lean')
for rel,p in selected.items():
 assert p.is_file(),p
 if p.suffix=='.log':assert 'error:' not in p.read_text() and 'Traceback' not in p.read_text(),rel
PACKET.mkdir();prov={}
for rel,p in sorted(selected.items(),key=lambda x:str(x[0])):
 dest=PACKET/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
 prov[str(rel)]={'source':str(p),'sha256':sha(p)}
dump(PACKET/'archive-provenance.json',prov)
note='''

## Actual source acquisition and source-to-scalar counter, 2026-10-27

Packet: docs/research-evidence/semiprime-source-acquisition-20261027.
Goal ACTIVE; slice PROGRESS. Guaranteed all-input factoring bit-time OPEN.

20 new modules strict+ordinary-root15lint PASS; every573 generated declaration/
361 theorem constant has only standard3 transitive axioms. All20 independent
isolated objects byte-identical; full source-resolved dependency checkpoint
unchanged. Prior1913 files,24 concurrent files and2 append-only prefixes preserved.
No commit/push. Published external SAT audit remains frozen.

BinomialExecution computes integer parity coefficients by cached Pascal rows,
explicit lower solution and reverse unitriangular solve. B=L*U and uniqueness
prove literal source equality; no inverse/vector oracle. Tracked arithmetic
A(R+1)+A+R+R², reads2A(R+1)+R², all-prefix integer height polynomial in A,R.
Core convenience wrapper still repeats ordinary target powers; pay them.

UniversalNumerator uses sorted commuting differences; SourceInterpolation/CodeArrays
compute actual universal coefficient arrays. SourceArrayAcquisition searches
packing, assembles complete blocks and leftover identities, pulls back to original
variables and caches M*n arrays. SourceExpressionBound proves actual syntax nodes
<=6Q²+8Q+3 and explicit array arithmetic/read bounds. Source constants/finite
search/packing/index work is NOT included in those array reports.

PaddedBlock/Constraint acquisition uses explicit (block×universal)⊕incidence
indices, at most2M rows. Every old source row appears; every padded row is zero
or literally old. Kernels/row spaces/rank preserved. RuntimeDesignAcquisition
executes original-row selection and caches selected entries without runtime
Layout/Polynomial indices. SourceRuntimeDesignBridge derives native locality
and exact selected source rank from actual row covers.

AcquiredSourceCounter.count_correct now constructs ALL source arrays, integer
constraints and node designs internally and returns originalContraction from
original indexed network/table inputs. Only owner bound, Q/interval, positiveJ
and precision guards remain; no coeff/constraint/locality/Taylor/count answer
premise. Actual whole-source Lean controls1/2/0 PASS (executability, not rate).

LocalExecutionHeight/BitBounds attach source Horner, corrected-port prefixes,
restricted truth branches/tail ports, products and all convolution subtotals to
common-denominator bounds; polynomial binary Fits derived without cancellation.

Independent source-preprocessing review gives fixed polynomial overhead under
scheduled D=r^(2Q),r>=2: subset difference leaves<=3^Q<=D. Repeated lazy word/
packing/selection calls are explicitly paid; let-records are NOT global caches.
AST occurrence-denominator and matrix-minor/scratch bounds support polynomial
bits. Aggregate preprocessing runtime is PAPER-level, no numerical polynomial
exponent asserted. Counter .work still omits source/design preprocessing;
not even a complete formal scalar-operation clock for the new wrapper yet.

NEXT: attach all source/design and counter arithmetic/read/control/storage to
actual bit primitives in one executed run; public equality-subdivided graph and
paid entries; original Boolean/prefix recovery; guard+finitefallback+schedule
in ONE all-input factoring bit theorem. CandidateN^o1 remains unproved here.
Older native longquery softK^1.25 unchanged; no new softK acquisition theorem.
'''
for rel in base['prefixes']:
 with (ROOT/rel).open('a') as f:f.write(note)
preserve(base)
verification={'status':'PASS','goal':'ACTIVE','slice':'PROGRESS','whole_input_factoring_bit_theorem':'OPEN',
 'module_count':20,'generated_declarations':573,'theorem_constants':361,'strict_options':['autoImplicit=false','warningAsError=true'],
 'ordinary_root_import':True,'scoped_linters_per_module':15,'all_generated_transitive_standard_axioms_only':True,
 'isolated_objects_identical':True,'dependency_checkpoint_unchanged':True,'source_resolved_dependency_modules':len(before['modules']),
 'preserved_prior_files':len(base['protected']),'preserved_concurrent_files':len(base['concurrent']),'preserved_append_only_prefixes':len(base['prefixes']),
 'actual_full_source_execution_controls':[1,2,0],'complete_primitive_runtime_claimed':False,'complete_scalar_clock_claimed':False,'commit_or_push':False,'modules':moduleinfo}
dump(PACKET/'verification.json',verification)
links=0
for p in PACKET.glob('*.md'):
 clean=re.sub(r'```.*?```','',p.read_text(),flags=re.S);clean=re.sub(r'`[^`]*`','',clean)
 for target in re.findall(r'\]\(([^)]+)\)',clean):
  if target.startswith(('http://','https://','#')):continue
  assert (p.parent/target.split('#')[0]).exists(),(p.name,target);links+=1
files={str(p.relative_to(PACKET)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(PACKET.rglob('*')) if p.is_file()}
dump(PACKET/'manifest.json',{'status':'PASS','files':files})
for rel,x in files.items():assert sha(PACKET/rel)==x['sha256']
assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
print(json.dumps({'packet':str(PACKET),'files':len(files)+1,'manifest_entries':len(files),'links_checked':links,'verification':{k:v for k,v in verification.items() if k!='modules'}},indent=2))
