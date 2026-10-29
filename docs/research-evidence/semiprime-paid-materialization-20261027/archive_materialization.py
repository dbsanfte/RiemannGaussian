#!/usr/bin/env python3
"""Seal paper-time algorithm and strictly checked supporting modules."""
from pathlib import Path
import hashlib,json,re,shutil,subprocess
ROOT=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-ternary-machine-20261027')
PACKET=ROOT/'docs/research-evidence/semiprime-paid-materialization-20261027'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def preserve(base):
 for key in ['protected','concurrent']:
  for rel,h in base[key].items():assert sha(ROOT/rel)==h,(key,rel)
 for rel,x in base['prefixes'].items():
  assert hashlib.sha256((ROOT/rel).read_bytes()[:x['bytes']]).hexdigest()==x['sha256'],rel
base=json.loads((WORK/'preservation-before.json').read_text());preserve(base)
assert not PACKET.exists(),'Do not overwrite sealed evidence'
mods=json.loads((WORK/'all-modules.json').read_text());assert len(mods)==len(set(mods))==7
log=(WORK/'CombinedMaterializationAudit.log').read_text()
assert log.count('-- All linting checks passed!')==7 and 'error:' not in log and 'sorryAx' not in log
au={m:{'declarations':int(d),'theorem_constants':int(t)} for m,d,t in re.findall(r'^AUDIT RiemannGaussian\.(\w+): declarations=(\d+), theorems=(\d+), standard_axioms_only=true$',log,re.M)}
assert set(au)==set(mods)
isolated=WORK/'final-isolated';summary=json.loads((isolated/'summary.json').read_text())
assert all(summary[k] for k in ['complete','strict_pass','all_objects_match','dependency_snapshot_unchanged'])
assert (isolated/'dependencies-before.json').read_bytes()==(isolated/'dependencies-after.json').read_bytes()
results=json.loads((isolated/'results.json').read_text());assert len(results)==7
moduleinfo={}
for x in results:
 name=x['module'].split('.')[-1];s=ROOT/'RiemannGaussian'/(name+'.lean');o=ROOT/'.lake/build/lib/lean/RiemannGaussian'/(name+'.olean')
 assert x['exit_code']==0 and x['object_matches'] and sha(s)==x['source_sha256']
 assert sha(o)==x['canonical_sha256']==x['isolated_sha256']==sha(isolated/(name+'.olean'))
 clean=re.sub(r'/-.*?-/', '',s.read_text(),flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|admit|sorryAx|native_decide)\b',clean),name
 moduleinfo[name]={'source':str(s.relative_to(ROOT)),'source_sha256':sha(s),'olean_sha256':sha(o),**au[name]}
for name in ['review-paid-integer-counter-hashes.json','review-paid-materialization-hashes.json','parametric-frame-pins.json']:
 for path,h in json.loads((WORK/name).read_text()).items():assert sha(Path(path))==h,(name,path)
assert 'Ran 7 tests' in (WORK/'paid-integer-tests.log').read_text()
assert (WORK/'paid-integer-tests.log').read_text().rstrip().endswith('OK')
assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
runtime=['semiprime-executable-counter-20261027/source_parameters.py','semiprime-executable-counter-20261027/source_layout.py','semiprime-executable-counter-20261027/source_factor_search.py','semiprime-shared-counter-20261026/shared_counter.py','semiprime-shared-counter-20261026/shared_parameters.py','semiprime-shared-counter-20261026/factor_solver.py','semiprime-shared-counter-20261026/factor_network.py']
dump(WORK/'runtime-dependencies.json',{str(ROOT/'docs/research-evidence'/p):sha(ROOT/'docs/research-evidence'/p) for p in runtime})
selected={p.name:p for p in WORK.iterdir() if p.is_file() and p.suffix in ['.md','.json'] and p.name!='archive-result.json'}
for name in ['paid_integer_counter.py','test_paid_integer_counter.py','paid-integer-tests.log',
 'CombinedMaterializationAudit.lean','CombinedMaterializationAudit.log','run_with_upstream.py',
 'final_strict_recheck.py','archive_materialization.py','LocalInterpreterSmoke.lean','local-interpreter-smoke.log',
 'OriginalBranchAudit.lean','original-branch-audit.log','ImportBranchAudit.lean','import-branch-audit.log']:
 selected[name]=WORK/name
for p in isolated.iterdir():
 if p.suffix in ['.json','.log']:selected[str(p.relative_to(WORK))]=p
for name in mods:selected[name+'.lean']=ROOT/'RiemannGaussian'/(name+'.lean')
for rel,p in selected.items():
 assert p.is_file(),p
 if p.suffix=='.log':assert 'error:' not in p.read_text() and 'Traceback' not in p.read_text(),rel
PACKET.mkdir();provenance={}
for rel,p in sorted(selected.items()):
 dest=PACKET/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
 provenance[rel]={'source':str(p),'sha256':sha(p)}
dump(PACKET/'archive-provenance.json',provenance)
verification={
 'status':'PASS','goal':'ACTIVE','slice':'SUBSTANTIVE_PAPER_TIME_RESULT',
 'paper_factoring_bit_time':'N^o(1), using subexponential storage',
 'complete_Lean_whole_machine_bit_clock':'OPEN','practical_speedup_claimed':False,
 'original_native_long_query_bound':'unchanged soft K^1.25',
 'module_count':7,'generated_declarations':sum(x['declarations'] for x in au.values()),
 'theorem_constants':sum(x['theorem_constants'] for x in au.values()),
 'strict_options':['autoImplicit=false','warningAsError=true'],
 'ordinary_root_import':True,'scoped_linters_per_module':15,
 'all_generated_transitive_standard_axioms_only':True,
 'isolated_objects_identical':True,'dependency_checkpoint_unchanged':True,
 'source_resolved_dependency_modules':summary['dependency_modules'],
 'original_upstream_closure':json.loads((isolated/'original-closure-check.json').read_text()),
 'independent_paper_review':'PASS','independent_implementation_review':'PASS',
 'focused_python_tests':7,'python_tests_pass':True,'tests_are_scaling_evidence':False,
 'preserved_prior_files':len(base['protected']),'preserved_concurrent_files':len(base['concurrent']),
 'preserved_append_only_prefixes':len(base['prefixes']),'commit_or_push':False,'modules':moduleinfo}
dump(PACKET/'verification.json',verification)
note='''

## Paid materialization gives a paper bit-time result, 2026-10-27

Packet: docs/research-evidence/semiprime-paid-materialization-20261027.
Goal ACTIVE. Substantive positive paper-level result: explicit deterministic
factoring algorithm with N^o(1) ordinary bit time and subexponential storage.
Complete Lean whole-program machine-clock refinement remains OPEN. Current
schedule crossover is enormous; no practical timing improvement is asserted.

NEW paid_integer_counter.py acquires source/layout from N via frozen compiler
and source constructor, then keeps original scopes through prefix recovery.
Caches each original Boolean truth table once per query and all head assignment
measurement fibres per node; product ranges over attained summary KEYS <=Y.
Head sums are multiplied without enumerating their global assignment product.
Homogeneous integer jets carry acquired common denominator Delta to declared
port-incidence degree, at most M=2n. Addition requires same degree. Actual LCM
of finite source denominators divides the proved source delta. Known rational
source elimination and Hermite remain; their actual intermediate minor/common-
denominator bounds, not the diagnostic Meter, prove polynomial bit lengths.

Independent paper and actual-code reviews PASS. Fixed-depth source search,
3^Q<=r^(2Q) difference expansion, polynomial matrix elimination, explicit
Cq/Y/2^h/2^w loops, all indexing/copies and even full-tape scans give fixed
polynomial time in S=poly(n)+Cq+Y+2^h+2^w. Scheduled logS=o(n), n=Theta(logN)
therefore gives paper N^o1. No unpinned numerical polynomial exponent. Finite
guard-failure lengths use explicit trial division. No count/source oracle,
optional cap, silent no-result branch, or polynomial-space claim. Seven focused
algebra/control tests PASS; small N-only smoke exercises fallback only, not rate.

Seven NEW Lean modules strict+ordinary-root15 lint PASS; all409 generated
declarations/202 theorem constants standard3-only. All7 isolated strict objects
identical; source-resolved18156-module dependency checkpoint unchanged; original
2569-module SAT source/object pins verified without rebuilding that closure.
Pure and original-OAI branches do not mix the renamed vendored SAT namespace.
Prior2157 files,24 concurrent files,2 append-only prefixes preserved. No push.

TernaryFactor/PublicFactor give original and prefix count-preserving reject2
encoding; TernaryLocal gives exact3point interpolant. TernaryLocalPaid supplies
actual finite neg/add/mul interpreter and cached Boolean extension with2^w
checker calls and2w+3(2^w-1) scalar calls; physical backend remains a contract.
BooleanRingFactor uses original Bool directly, proves graph-count/ring decoding
at t=n+1; restoring rows and ring setup are still explicit future construction.
ParametricFactorLoop/Frame execute generic callback iteration/setup/cleanup and
preserve upper registers; no macro Cmd40 callback is silently supplied.

The rational materialization result does NOT require completing the alternative
finite-ring source/controller route. Next priority is one simple verified
finite-list/integer controller for the ACTUAL materialized algorithm and its
whole bit-cost refinement, using the already proved semantic identities and
height bounds. Do not restart broader representation searches or insist on
polynomial space unless separately requested. Native longquery remains soft
K^1.25; paper factoring-time improvement follows the factor-count detour.
'''
for rel in base['prefixes']:
 with (ROOT/rel).open('a') as f:f.write(note)
preserve(base)
links=0
for p in PACKET.glob('*.md'):
 clean=re.sub(r'```.*?```','',p.read_text(),flags=re.S);clean=re.sub(r'`[^`]*`','',clean)
 for target in re.findall(r'\]\(([^)]+)\)',clean):
  if target.startswith(('http://','https://','#')) or target=='manifest.json':continue
  assert (p.parent/target.split('#')[0]).exists(),(p.name,target);links+=1
files={str(p.relative_to(PACKET)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(PACKET.rglob('*')) if p.is_file()}
dump(PACKET/'manifest.json',{'status':'PASS','files':files})
assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
print(json.dumps({'packet':str(PACKET),'files':len(files)+1,'manifest_entries':len(files),'links_checked':links,'verification':{k:v for k,v in verification.items() if k!='modules'}},indent=2))
