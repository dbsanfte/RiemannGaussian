#!/usr/bin/env python3
"""Independent READ-ONLY final seal check. Run only after Root's seal notice.
All output stays under scratch final-archive-review names. No Lean invocation.
Each distinct dependency path is freshly hashed once; every current/prior pin
is checked against that hash, including paths outside the current closure.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import unquote
import hashlib,json,re,subprocess,time,traceback
ROOT=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-histogram-acquisition-20261027')
PACK=ROOT/'docs/research-evidence/semiprime-histogram-acquisition-20261027'
OUT=WORK/'final-archive-review.json'
PRIOR={
 'constraint-count':17657,'word-bank':17646,'score-count':17628,
 'source-lowering':17634,'source-machine':17608,'source-state':17610,
 'hermite-report-rate':17661,
}
REVIEWS=['review-query-original.md','review-query-resources.md','review-source-selection.md']
SHA=re.compile(r'[0-9a-f]{64}')
def digest(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as f:
  while chunk:=f.read(1<<20):h.update(chunk)
 return h.hexdigest()
def read_json(path):return json.loads(Path(path).read_text())
def load(rel):return read_json(PACK/rel)
def check(test,*info):
 if not test:raise AssertionError(info)
def verify_live_pin(path,wanted,context):
 p=Path(path)
 if not p.is_absolute():p=ROOT/p
 check(p.is_file(),'missing live pin',context,str(p))
 check(digest(p)==wanted,'live pin mismatch',context,str(p))
 return str(p)

def main():
 start=time.monotonic();res={'packet':str(PACK),'read_only':True}
 check(PACK.is_dir(),'packet not sealed/present',str(PACK))
 manifest=load('manifest.json')['files']
 actual={str(p.relative_to(PACK)):p for p in PACK.rglob('*') if p.is_file()}
 check(set(actual)-{'manifest.json'}==set(manifest),'manifest exact file set')
 for rel,pin in manifest.items():
  p=actual[rel]
  check(p.stat().st_size==pin['bytes'],'manifest size',rel)
  check(digest(p)==pin['sha256'],'manifest hash',rel)
 res.update(archive_files=len(actual),manifest_entries=len(manifest),manifest='PASS')
 prov=load('archive-provenance.json')
 for rel,pin in prov.items():
  check(rel in actual,'provenance target missing',rel)
  check(digest(PACK/rel)==pin['sha256'],'archived provenance hash',rel)
  verify_live_pin(pin['source'],pin['sha256'],('provenance',rel))
 res['live_provenance_origins_checked']=len(prov)

 v=load('verification.json');mods=load('all-modules.json')
 check(len(mods)==42==len(set(mods)),'42 unique final modules',len(mods))
 check(set(mods)==set(v['modules']),'verification module set')
 check(v['module_count']==len(mods),'verification module count')
 results=load('final-isolated/results.json')
 check({x['module'] for x in results}=={'RiemannGaussian.'+m for m in mods},'isolated module set')
 for m,pin in v['modules'].items():
  source=ROOT/pin['source'];obj=ROOT/'.lake/build/lib/lean/RiemannGaussian'/f'{m}.olean'
  check(digest(source)==pin['source_sha256']==digest(PACK/f'{m}.lean'),'source archive/live pin',m)
  check(digest(obj)==pin['object_sha256'],'canonical object',m)
  row=next(x for x in results if x['module']=='RiemannGaussian.'+m)
  check(row['exit_code']==0 and row['object_matches'],'isolated strict pass',m)
  check(row['source_sha256']==pin['source_sha256'],'isolated source',m)
  check(row['canonical_sha256']==row['isolated_sha256']==pin['object_sha256'],'isolated object pins',m)
  iso=WORK/'final-isolated'/f'{m}.olean'
  check(digest(iso)==pin['object_sha256'],'live isolated bytes',m)
  log=(PACK/'final-isolated'/f'{m}.log').read_text()
  check('error:' not in log,'isolated error log',m)
 res['canonical_and_live_isolated_modules']=len(mods)
 decl=sum(p['declarations'] for p in v['modules'].values())
 thm=sum(p['theorem_constants'] for p in v['modules'].values())
 check(decl==v['generated_declarations'] and thm==v['theorem_constants'],'dynamic generated totals')
 audit=(PACK/'CombinedHistogramAcquisitionAudit.log').read_text()
 check(audit.count('-- All linting checks passed!')==42 and 'error:' not in audit,'combined namespace lints')
 rows=re.findall(r'^AUDIT RiemannGaussian\.(\w+): declarations=(\d+), theorems=(\d+), standard_axioms_only=true$',audit,re.M)
 check(len(rows)==42,'combined all-generated audit rows')
 check({m:(int(d),int(t)) for m,d,t in rows}=={
  m:(p['declarations'],p['theorem_constants']) for m,p in v['modules'].items()},'audit exact generated metadata')
 audit_source=(PACK/'CombinedHistogramAcquisitionAudit.lean').read_text()
 check(audit_source.startswith('import RiemannGaussian\n'),'ordinary root import')
 lint_names=re.findall(r'^#lint\+ in (RiemannGaussian\.\w+)$',audit_source,re.M)
 check(set(lint_names)=={'RiemannGaussian.'+m for m in mods} and len(lint_names)==42,'exact namespace lint source')
 check('Lean.collectAxioms' in audit_source and 'ci.isAxiom' in audit_source,'all-generated transitive axioms source')
 strict_source=(PACK/'verify_histogram_acquisition.py').read_text()
 check("'-DautoImplicit=false'" in strict_source and "'-DwarningAsError=true'" in strict_source,'strict flags in producer')
 res.update(generated_declarations=decl,theorem_constants=thm,combined_root15_standard_axioms='PASS')

 summary=load('final-isolated/summary.json')
 check(all(summary[k] for k in ['complete','strict_pass','all_objects_match','dependency_snapshot_unchanged']),'isolated summary')
 before=load('final-isolated/dependencies-before.json');after=load('final-isolated/dependencies-after.json')
 check(before==after,'current compiler closure before/after unchanged')
 imports=load('compiler-imports.json');deps=before['modules']
 check(len(imports)==len(set(imports))==len(deps)==v['actual_compiler_imported_modules'],'actual compiler import count')
 check(set(imports)==set(deps),'exact actual compiler header set')
 check(not any(m.startswith('OAI.Algorithms.SubexponentialSAT') for m in imports),'disjoint original/vendored branches')
 all_pins={};closure_counts={}
 def add_closure(label,snapshot,expected=None):
  module_pins=snapshot['modules']
  if expected is not None:check(len(module_pins)==expected,'prior closure exact count',label,len(module_pins))
  records=0;outside=0
  for name,pin in module_pins.items():
   if name not in deps:outside+=1
   for kind in ['source','object']:
    p=pin[kind];wanted=pin[kind+'_sha256']
    check(p and wanted and SHA.fullmatch(wanted),'resolved dependency pin',label,name,kind)
    check(p not in all_pins or all_pins[p]==wanted,'conflicting dependency snapshots',label,p)
    all_pins[p]=wanted;records+=1
  closure_counts[label]={'modules':len(module_pins),'source_object_path_pins':records,'modules_outside_new_closure':outside}
 add_closure('current',before)
 for label,count in PRIOR.items():
  path=ROOT/f'docs/research-evidence/semiprime-{label}-20261027/final-isolated/dependencies-after.json'
  add_closure(label,read_json(path),count)
 def fresh(item):
  p,wanted=item
  check(digest(p)==wanted,'fresh dependency source/object hash',p)
  return True
 with ThreadPoolExecutor(max_workers=8) as pool:check(all(pool.map(fresh,all_pins.items())),'fresh complete union rehash')
 res.update(actual_compiler_imports=len(imports),dependency_closures=closure_counts,
  fresh_unique_dependency_paths_rehashed=len(all_pins),
  logical_dependency_source_object_pins_checked=sum(x['source_object_path_pins'] for x in closure_counts.values()),
  dependency_rehash_scope='Fresh one-pass hash of every distinct path; every current and all seven prior pin validated, including paths outside current closure')

 pres=load('preservation-before.json')
 for group,expected in [('protected',3683),('concurrent',24)]:
  check(len(pres[group])==expected,'baseline count',group,len(pres[group]))
  for rel,wanted in pres[group].items():verify_live_pin(rel,wanted,('preservation',group))
  res[group+'_files_rehashed']=len(pres[group])
 check(len(pres['prefixes'])==2,'two exact append-only prefixes')
 note=(PACK/'journal-append.md').read_bytes();suffixes=[];prefixes={}
 for rel,pin in pres['prefixes'].items():
  data=(ROOT/rel).read_bytes()
  check(len(data)>=pin['bytes'],'prefix unexpectedly truncated',rel)
  check(hashlib.sha256(data[:pin['bytes']]).hexdigest()==pin['sha256'],'original full prefix',rel)
  suffix=data[pin['bytes']:];check(suffix==note,'exactly one appended journal note',rel)
  suffixes.append(suffix);prefixes[rel]={'original_bytes':pin['bytes'],'appended_bytes':len(suffix),'exactly_one_note':True}
 check(suffixes[0]==suffixes[1],'same note appended both prefixes')
 check(len(pres['protected'])==v['preserved_prior_files'] and len(pres['concurrent'])==v['preserved_concurrent_files'],'preservation metadata')
 res.update(append_only_prefixes=prefixes,journal_append_bytes=len(note))

 review_pins=[]
 def collect(obj):
  if isinstance(obj,list):
   for x in obj:collect(x)
  elif isinstance(obj,dict):
   for key,value in obj.items():
    if isinstance(key,str) and key.startswith('/') and isinstance(value,str) and SHA.fullmatch(value):
     review_pins.append((key,value))
   for label in ['source','object','canonical','isolated','path','review']:
    hashkey='sha256' if label=='path' else label+'_sha256'
    if isinstance(obj.get(label),str) and isinstance(obj.get(hashkey),str) and SHA.fullmatch(obj[hashkey]):
     p=obj[label]
     if label=='review' and not Path(p).is_absolute():p=str(PACK/p)
     review_pins.append((p,obj[hashkey]))
   for x in obj.values():collect(x)
 for name in REVIEWS:
  check((PACK/name).is_file() and 'PASS' in (PACK/name).read_text(),'independent scope review PASS',name)
  pinpath=PACK/(name.removesuffix('.md')+'-pins.json')
  check(pinpath.is_file(),'independent review pins',str(pinpath));obj=read_json(pinpath)
  if isinstance(obj,dict) and 'status' in obj:check(obj['status']=='PASS','review pin status',name)
  collect(obj)
 check(review_pins,'nonempty live independent review pin set')
 for p,wanted in review_pins:verify_live_pin(p,wanted,'independent review')
 res.update(independent_pass_reviews=len(REVIEWS),independent_review_live_pins_checked=len(review_pins))

 links=[]
 for md in PACK.rglob('*.md'):
  clean=re.sub(r'```.*?```','',md.read_text(),flags=re.S);clean=re.sub(r'`[^`]*`','',clean)
  for raw in re.findall(r'\]\(([^)]+)\)',clean):
   raw_target=raw.strip()
   target=(raw_target[1:raw_target.index('>')] if raw_target.startswith('<') and '>' in raw_target
     else raw_target.split(' ',1)[0])
   if target.startswith(('http://','https://','mailto:','#')):continue
   target=unquote(target.split('#',1)[0].split('?',1)[0])
   if not target:continue
   p=Path(target) if Path(target).is_absolute() else md.parent/target
   if not p.exists() and re.search(r':\d+(?:-\d+)?$',str(p)):
    p=Path(re.sub(r':\d+(?:-\d+)?$','',str(p)))
   check(p.exists(),'recursive Markdown local link',str(md.relative_to(PACK)),raw)
   links.append((str(md.relative_to(PACK)),raw))
 res['recursive_local_markdown_links_checked']=len(links)
 git=subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True,text=True)
 check(git.returncode==0,'git diff --check',git.stdout,git.stderr);res['git_diff_check']='PASS'

 # Written only after independent manual READ-ONLY review of sealed scope docs.
 scope_path=WORK/'final-archive-review-scope.json'
 check(scope_path.is_file(),'manual final read-only sealed scope review pending')
 scope=read_json(scope_path);check(scope['status']=='PASS','manual scope review verdict')
 for rel,wanted in scope['sealed_inputs'].items():
  check(digest(PACK/rel)==wanted,'manual scope inputs changed',rel)
 required={'goal_active':True,'whole_primitive_bit_clock':'OPEN',
  'exact_original_selector_labels_and_ties':'PROVED',
  'quadratic_T_constructor_in_new_query_runtime':False,
  'uniform_family_mixed_report':'PROVED_FIXED_POLYNOMIAL',
  'existing_public_caller_changed':False,'whole_machine_exponent_claimed':False,
  'native_tokens_length_host_join':'OPEN'}
 check(all(scope['conclusions'].get(k)==value for k,value in required.items()),'manual scope conclusions')
 res['scope_checks']=scope
 res['status']='PASS';res['seconds']=time.monotonic()-start
 return res

if __name__=='__main__':
 try: result=main()
 except BaseException as exc:
  result={'status':'FAIL','packet':str(PACK),'error':str(exc),'traceback':traceback.format_exc()}
 OUT.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
 raise SystemExit(0 if result['status']=='PASS' else 1)
