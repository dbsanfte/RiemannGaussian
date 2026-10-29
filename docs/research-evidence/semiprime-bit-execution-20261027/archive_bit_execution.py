#!/usr/bin/env python3
"""Seal the verified physical-bit/public-factor slice without touching old evidence."""
from pathlib import Path
import hashlib,json,re,shutil,subprocess
ROOT=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-bit-execution-20261027')
PACKET=ROOT/'docs/research-evidence/semiprime-bit-execution-20261027'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def preserve(base):
 for k in ['protected','concurrent']:
  for rel,digest in base[k].items():assert sha(ROOT/rel)==digest,(k,rel)
 for rel,x in base['prefixes'].items():
  assert hashlib.sha256((ROOT/rel).read_bytes()[:x['bytes']]).hexdigest()==x['sha256'],rel
base=json.loads((WORK/'preservation-before.json').read_text());preserve(base)
assert not PACKET.exists(),'Existing archive must be inspected, not overwritten'
mods=json.loads((WORK/'all-modules.json').read_text());assert len(mods)==len(set(mods))==11
log=(WORK/'CombinedBitExecutionAudit.log').read_text()
assert log.count('-- All linting checks passed!')==11 and 'error:' not in log and 'sorryAx' not in log
au={m:{'declarations':int(d),'theorem_constants':int(t)} for m,d,t in re.findall(r'^AUDIT RiemannGaussian\.(\w+): declarations=(\d+), theorems=(\d+), standard_axioms_only=true$',log,re.M)}
assert set(au)==set(mods)
decls=sum(x['declarations'] for x in au.values());thms=sum(x['theorem_constants'] for x in au.values())
isolated=WORK/'final-isolated';summary=json.loads((isolated/'summary.json').read_text())
assert all(summary[k] for k in ['complete','strict_pass','all_objects_match','dependency_snapshot_unchanged'])
results=json.loads((isolated/'results.json').read_text());assert {x['module'] for x in results}=={'RiemannGaussian.'+m for m in mods}
before=json.loads((isolated/'dependencies-before.json').read_text());after=json.loads((isolated/'dependencies-after.json').read_text());assert before==after
moduleinfo={}
for x in results:
 name=x['module'].split('.')[-1];source=ROOT/'RiemannGaussian'/(name+'.lean');obj=ROOT/'.lake/build/lib/lean/RiemannGaussian'/(name+'.olean')
 assert x['exit_code']==0 and x['object_matches'] and sha(source)==x['source_sha256']
 assert sha(obj)==x['canonical_sha256']==x['isolated_sha256']==sha(isolated/(name+'.olean'))
 clean=re.sub(r'/-.*?-/', '',source.read_text(),flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|admit|sorryAx|native_decide)\b',clean),name
 moduleinfo[name]={'source':str(source.relative_to(ROOT)),'source_sha256':sha(source),'olean_sha256':sha(obj),**au[name]}
def checkpins(x):
 if isinstance(x,list):
  for v in x:checkpins(v)
  return
 if not isinstance(x,dict):return
 if isinstance(x.get('source'),str) and isinstance(x.get('source_sha256'),str):
  p=Path(x['source']);p=p if p.is_absolute() else ROOT/p
  assert sha(p)==x['source_sha256'],('structured source pin',str(p))
 for k,v in x.items():
  if isinstance(v,dict):checkpins(v)
  elif isinstance(v,str) and re.fullmatch('[0-9a-f]{64}',v):
   p=Path(k) if k.startswith('/') else ROOT/k if k.startswith('RiemannGaussian/') else ROOT/'RiemannGaussian'/(k+'.lean') if k in mods else WORK/k
   if p.is_file():assert sha(p)==v,('review pin',str(p))
for p in WORK.glob('*hash*.json'):checkpins(json.loads(p.read_text()))
upstream=Path('/tmp/semiprime-d1-audit-20261026/openai-math')
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=upstream,text=True).strip()=='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a'
for rel,digest in json.loads((WORK/'upstream-source-reuse-hashes.json').read_text()).items():
 assert sha(upstream/'lean/OAI/Algorithms/SubexponentialSAT'/rel)==digest,('upstream source',rel)
assert (WORK/'measurement-physical-smoke.log').read_text().strip()=='true\n2\ntrue\nfalse\nsome [false, false, true]\nnone'
assert (WORK/'acquired-prefix-smoke.log').read_text().strip()=='1\n0\n1\n0\n(some [(0, true)], 2)\n(some [(0, false)], 2)\n(none, 1)'
assert (WORK/'local-physical-smoke.log').read_text().strip()=='([1 / 6, -1 / 6, -1], 4543524)'
assert (WORK/'scheduled-factor-smoke.log').read_text().strip()=='(true, 5)\n(false, 5)\ntrue\n(none, none, none, some 3, some 3)\n(false, false, false)'
assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
selected={p.relative_to(WORK):p for p in WORK.iterdir() if p.is_file() and p.suffix in ['.md','.json']}
for name in ['CombinedBitExecutionAudit.lean','CombinedBitExecutionAudit.log',
 'MeasurementPhysicalSmoke.lean','measurement-physical-smoke.log',
 'AcquiredPrefixSmoke.lean','acquired-prefix-smoke.log',
 'PhysicalCompilerSmoke.lean','physical-compiler-smoke.log',
 'CheckPhysicalCompiler.lean','physical-compiler-audit.log','strict_recheck_physical.py',
 'SemiprimeJetBits-isolated.log','SemiprimePolynomialCodeBits-isolated.log',
 'LocalPhysicalSmoke.lean','local-physical-smoke.log',
 'CombinedLocalBitAudit.lean','combined-local-bit-audit.log','strict_recheck_local.py',
 'SemiprimeLocalBits-isolated.log','SemiprimeLocalBitsCorrectness-isolated.log','SemiprimeLocalBitsBounds-isolated.log',
 'ScheduledFactorSmoke.lean','scheduled-factor-smoke.log',
 'final_strict_recheck.py','archive_bit_execution.py']:
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
note=f'''

## Physical local execution and original-input factor recovery, 2026-10-27

Packet: docs/research-evidence/semiprime-bit-execution-20261027.
Goal ACTIVE; slice PROGRESS. Whole-input guaranteed factoring bit-time OPEN.

11 new modules strict+ordinary-root15lint PASS; all{decls} generated declarations/
{thms} theorem constants standard3-only. All11 isolated strict objects identical;
full source-resolved dependency checkpoint unchanged. Prior2066 files,
24 concurrent files and2 append-only prefixes preserved. No commit/push.

JetBits executes rational-word add/scale/convolution; PolynomialCodeBits compiles
actual physical-constant expressions. Structural budgets derive intermediate
capacity and initialized width from original constant words; no output-Fits
oracle. Source constants and width/template acquisition remain separate.

LocalBits executes actual bounded integer callbacks and BOTH restricted truth
branches with cached lo/hi and physical word arithmetic. Correctness derives
all intermediate representations from initial ports. Wbits=(2b+3)(w+1)+3
suffices from J,d,B<=2^b. Actual local clock<=2^w*(E+(w+1)*nodeBudget(J,Wbits)).
This is a scoped Boolean arithmetic/flat-cell ledger, not a complete tape clock.

MeasurementBits executes signed-word dots, subtraction and zero scans, including
signed zero, and preserves the EXACT previous false-first representative.
Each test costs polynomial(m,n,W); matrix/target generation, callback listing
and outer traversal/control/physical addressing remain to compose.

SupportRate proves actual inclusive weightedCount=sum2^j*choose(n,j) is
subexponential whenever cutoff/n->0. ScheduledSupportRate proves this for
floor(2nR/Q), retaining rounded R/Q and without unpinned constant16435.
This is literal callback count, not a global execution clock.

AcquiredPrefixSearch uses actual source counter for each every-occurrence
restriction. PublicAcquiredExecution preserves exact B=2, reindexes actual
ordered graph, and proves original proper-factor count and common-witness
binary recovery. <=wireCount+1 actual acquired queries; every query repeats
source/design acquisition unless future caching is explicitly implemented.

ScheduledFactorExecution supplies N-only run with computed parameters,
decidable numerical guard and complete finite trial fallback. All-input
soundness/completeness includes zero, one, primes and squares. Actual fast
guard passes eventually and runtime eventually uses the same source-counter
branch. These are correctness/branch theorems, NOT whole-run bit complexity.

Read-only upstream reuse audit located arbitrary-scope primitive packing with
fixed-polynomial scalarSize clock, actual integer parity cache/numerator, and
generic opaque-byte row emitter. scalarEntry_eq_entry supplies the semantic
numerator identity. Need exact tolerance/order/serialization/word adapters;
finite fixed-width represented ring is not an unconditional rational backend.
An alternative remains viable: upstream unramified ring over Z/(3^t), t=n+1,
exact count decoding and residue-distinct unit nodes in d=O(logQ). Rebuild the
source/interpolation directly in that ring; no unrestricted rational reduction.
This may reuse more existing machine code; growing-scope callback/controller
and input/setup/rate joins remain unproved for our factor network.
Published SAT closure audit remains frozen; no new external rebuild claimed.

NEXT: reuse upstream packing/cache/numerator via exact adapters, acquire
physical source/corrected-port words, join group/fibre/support/Hermite bits and
all preprocessing/control/storage to SAME public run, then prove its rate.
Candidate N^o1 and original all-semiprime sixth goal remain OPEN; native long
query still softK^1.25, no new softK acquisition theorem.
'''
for rel in base['prefixes']:
 with (ROOT/rel).open('a') as f:f.write(note)
preserve(base)
verification={'status':'PASS','goal':'ACTIVE','slice':'PROGRESS','whole_input_factoring_bit_theorem':'OPEN',
 'module_count':11,'generated_declarations':decls,'theorem_constants':thms,
 'strict_options':['autoImplicit=false','warningAsError=true'],'ordinary_root_import':True,
 'scoped_linters_per_module':15,'all_generated_transitive_standard_axioms_only':True,
 'isolated_objects_identical':True,'dependency_checkpoint_unchanged':True,
 'source_resolved_dependency_modules':len(before['modules']),
 'preserved_prior_files':len(base['protected']),'preserved_concurrent_files':len(base['concurrent']),
 'preserved_append_only_prefixes':len(base['prefixes']),
 'all_input_algorithm_semantics':True,'eventual_actual_fast_branch':True,
 'complete_primitive_runtime_claimed':False,'whole_run_clock_claimed':False,
 'commit_or_push':False,'modules':moduleinfo}
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
print(json.dumps({'packet':str(PACKET),'files':len(files)+1,'manifest_entries':len(files),'links_checked':links,
 'verification':{k:v for k,v in verification.items() if k!='modules'}},indent=2))
