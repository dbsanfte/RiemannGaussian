#!/usr/bin/env python3
"""Seal verified original-source state proofs; never rewrite earlier evidence."""
from pathlib import Path
import hashlib,json,re,shutil,subprocess
ROOT=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-score-count-20261027')
PACK=ROOT/'docs/research-evidence/semiprime-score-count-20261027'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
base=load(WORK/'preservation-before.json')
def preserve():
 for section in ['protected','concurrent']:
  for rel,h in base[section].items():assert sha(ROOT/rel)==h,(section,rel)
 for rel,v in base['prefixes'].items():
  assert hashlib.sha256((ROOT/rel).read_bytes()[:v['bytes']]).hexdigest()==v['sha256'],rel
preserve()
assert not PACK.exists(),'Refuse overwrite of sealed packet'
mods=load(WORK/'all-modules.json');assert len(mods)==20
log=(WORK/'CombinedScoreCountAudit.log').read_text()
au={m:{'declarations':int(d),'theorem_constants':int(t)} for m,d,t in re.findall(r'^AUDIT RiemannGaussian\.(\w+): declarations=(\d+), theorems=(\d+), standard_axioms_only=true$',log,re.M)}
assert set(au)==set(mods)
assert sum(x['declarations'] for x in au.values())==652
assert sum(x['theorem_constants'] for x in au.values())==423
assert log.count('-- All linting checks passed!')==len(mods) and 'error:' not in log
isolated=WORK/'final-isolated';summary=load(isolated/'summary.json')
assert all(summary[k] for k in ['complete','strict_pass','all_objects_match','dependency_snapshot_unchanged'])
assert (isolated/'dependencies-before.json').read_bytes()==(isolated/'dependencies-after.json').read_bytes()
info={}
for row in load(isolated/'results.json'):
 name=row['module'].split('.')[-1];src=ROOT/'RiemannGaussian'/(name+'.lean');obj=ROOT/'.lake/build/lib/lean/RiemannGaussian'/(name+'.olean')
 assert row['exit_code']==0 and row['object_matches']
 assert sha(src)==row['source_sha256'] and sha(obj)==row['canonical_sha256']==row['isolated_sha256']==sha(isolated/(name+'.olean'))
 info[name]={'source':str(src.relative_to(ROOT)),'source_sha256':sha(src),'object_sha256':sha(obj),**au[name]}
assert set(info)==set(mods)
for stem in ['review-count-identity','review-physical-predicate','review-physical-count-score','review-physical-score-search']:
 assert 'PASS' in (WORK/(stem+'.md')).read_text(),stem
# Recursively check review records in any documented path/hash layout.
def pins(x):
 if isinstance(x,dict):
  if 'path' in x and 'sha256' in x:assert sha(x['path'])==x['sha256'],x['path']
  if 'source' in x and 'source_sha256' in x:assert sha(x['source'])==x['source_sha256'],x['source']
  if 'object' in x and 'object_sha256' in x:assert sha(x['object'])==x['object_sha256'],x['object']
  for k,v in x.items():
   if k.startswith('/') and isinstance(v,str) and len(v)==64:assert sha(k)==v,k
   elif k.startswith('/') and isinstance(v,dict) and 'sha256' in v:assert sha(k)==v['sha256'],k
   pins(v)
 elif isinstance(x,list):
  for v in x:pins(v)
for p in WORK.glob('review-*.json'):pins(load(p))
selected={p.name:p for p in WORK.glob('*.md') if not p.name.startswith('final-archive-review')}
for p in WORK.glob('*.json'):
 if p.name not in ['isolated-status.json'] and not p.name.startswith(('final-archive-review','archive-seal-result')):selected[p.name]=p
for name in ['CombinedScoreCountAudit.lean','CombinedScoreCountAudit.log','verify_score_count.py','archive_score_count.py']:selected[name]=WORK/name
for p in isolated.iterdir():
 if p.suffix in ['.json','.log']:selected[str(p.relative_to(WORK))]=p
for m in mods:selected[m+'.lean']=ROOT/'RiemannGaussian'/(m+'.lean')
for rel,p in selected.items():
 assert p.is_file(),p
 if p.suffix=='.log':assert 'error:' not in p.read_text() and 'Traceback' not in p.read_text(),rel
assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
PACK.mkdir();provenance={}
for rel,p in sorted(selected.items()):
 dest=PACK/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
 provenance[rel]={'source':str(p),'sha256':sha(p)}
dump(PACK/'archive-provenance.json',provenance)
v={'status':'PASS','goal':'ACTIVE','slice':'PHYSICAL_INTEGER_COUNT_SCORE_AND_ORIGINAL_LABEL_PRODUCER',
 'complete_Lean_whole_program_bit_clock':'OPEN',
 'new_controller_public_report_subpower':'PREVIOUSLY_PROVED_ACTUAL_RETAINED_REPORT',
 'actual_original_count_identity':'PROVED_ALL_PREFIXES_NO_COUNT_ADVICE',
 'scheduled_score_cancellation':'PROVED_POSITIVE_AFFINE_ORDER_AND_TIES',
 'physical_terminal_count_padding_weight_pipeline':'PROVED_CONCRETE_ORIGINAL_INPUTS',
 'original_score_acquisition_and_labels':'PROVED_PHYSICAL_DATA_NATIVE_METADATA',
 'original_score_producer_compiler':'PROVED_STATED_HOST_METADATA_SCOPE',
 'original_source_descriptor_acquisition':'PROVED_EXECUTED_NATIVE_INDEX_SCANS',
 'new_search_rational_scales_offset_and_GCD_arithmetic':'ELIMINATED_FROM_RUNTIME',
 'actual_original_family_report':'PROVED_UNIFORM_FIXED_POLYNOMIAL_ORIGINAL_RESOURCES',
 'physical_candidate_word_ID_bank':'OPEN_COMPLETE_CALLER_ADAPTER',
 'source_Nat_Word_descriptor_label_metadata_bit_refinement':'OPEN',
 'original_parity_prescription_AST_construction_bit_refinement':'OPEN',
 'source_cache_packing_pullback_public_composition':'OPEN',
 'primitive_internal_report_erasure':'OPEN','complete_auxiliary_heap_and_pointer_encoding':'OPEN',
 'source_all_reachable_machine_state':'OPEN','full_bit_simulation_join':'OPEN',
 'new_simulator_functions':True,'existing_public_caller_changed':False,
 'whole_program_machine_rate_claimed':False,'new_native_long_query_bound':False,
 'subexponential_storage_allowed':True,'practical_speedup_claimed':False,'commit_or_push':False,
 'module_count':len(mods),'generated_declarations':sum(x['declarations'] for x in au.values()),
 'theorem_constants':sum(x['theorem_constants'] for x in au.values()),
 'strict_options':['autoImplicit=false','warningAsError=true'],'ordinary_root_import':True,
 'scoped_linters_per_module':15,'all_generated_transitive_standard_axioms_only':True,
 'isolated_objects_identical':True,'dependency_checkpoint_unchanged':True,
 'actual_compiler_imported_modules':summary['actual_compiler_imported_modules'],
 'dependency_list_provenance':'Lean environment header; no source-text import scanner',
 'preserved_prior_files':len(base['protected']),'preserved_concurrent_files':len(base['concurrent']),
 'preserved_append_only_prefixes':len(base['prefixes']),'modules':info}
dump(PACK/'verification.json',v)
note=(WORK/'journal-append.md').read_bytes()
for rel,pin in base['prefixes'].items():
 assert (ROOT/rel).stat().st_size==pin['bytes'],('unexpected journal append',rel)
 with (ROOT/rel).open('ab') as f:f.write(note)
preserve()
files={str(p.relative_to(PACK)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(PACK.rglob('*')) if p.is_file()}
dump(PACK/'manifest.json',{'status':'PASS','files':files})
links=0
for p in PACK.glob('*.md'):
 clean=re.sub(r'```.*?```','',p.read_text(),flags=re.S);clean=re.sub(r'`[^`]*`','',clean)
 for target in re.findall(r'\]\(([^)]+)\)',clean):
  if target.startswith(('http://','https://','#')):continue
  assert (p.parent/target.split('#')[0]).exists(),(p.name,target);links+=1
assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
print(json.dumps({'status':'PASS','files':len(files)+1,'manifest_entries':len(files),'links_checked':links,'modules':len(mods),'declarations':v['generated_declarations'],'theorems':v['theorem_constants'],'actual_compiler_imports':v['actual_compiler_imported_modules']},indent=2))
