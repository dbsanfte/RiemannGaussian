#!/usr/bin/env python3
"""Seal the verified original-source histogram query and selector once."""
from pathlib import Path
import hashlib,json,re,shutil,subprocess
ROOT=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-histogram-acquisition-20261027')
PACK=ROOT/'docs/research-evidence/semiprime-histogram-acquisition-20261027'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def lean_code(s):
 out=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:i+=1
  else:out.append(s[i]);i+=1
 assert depth==0,'unterminated Lean comment'
 return ''.join(out)
base=load(WORK/'preservation-before.json')
def preserve():
 for group in ['protected','concurrent']:
  for rel,h in base[group].items():assert sha(ROOT/rel)==h,(group,rel)
 for rel,pin in base['prefixes'].items():
  assert hashlib.sha256((ROOT/rel).read_bytes()[:pin['bytes']]).hexdigest()==pin['sha256'],rel
preserve()
assert not PACK.exists(),'Refuse overwrite of sealed packet'
mods=load(WORK/'all-modules.json');assert len(mods)==42 and len(set(mods))==42
log=(WORK/'CombinedHistogramAcquisitionAudit.log').read_text()
au={m:{'declarations':int(d),'theorem_constants':int(t)} for m,d,t in re.findall(r'^AUDIT RiemannGaussian\.(\w+): declarations=(\d+), theorems=(\d+), standard_axioms_only=true$',log,re.M)}
assert set(au)==set(mods)
assert all(p['declarations']>0 and p['theorem_constants']>0 for p in au.values())
assert log.count('-- All linting checks passed!')==len(mods) and 'error:' not in log
isolated=WORK/'final-isolated';summary=load(isolated/'summary.json')
assert all(summary[k] for k in ['complete','strict_pass','all_objects_match','dependency_snapshot_unchanged'])
assert (isolated/'dependencies-before.json').read_bytes()==(isolated/'dependencies-after.json').read_bytes()
info={}
for row in load(isolated/'results.json'):
 m=row['module'].split('.')[-1];src=ROOT/'RiemannGaussian'/(m+'.lean');obj=ROOT/'.lake/build/lib/lean/RiemannGaussian'/(m+'.olean')
 assert row['exit_code']==0 and row['object_matches']
 assert sha(src)==row['source_sha256'] and sha(obj)==row['canonical_sha256']==row['isolated_sha256']==sha(isolated/(m+'.olean'))
 info[m]={'source':str(src.relative_to(ROOT)),'source_sha256':sha(src),'object_sha256':sha(obj),**au[m]}
 assert not re.search(r'\b(sorry|admit|sorryAx|native_decide)\b',lean_code(src.read_text())),m
assert set(info)==set(mods)
reviews=['review-query-original','review-source-selection','review-query-resources']
for name in reviews:assert 'PASS' in (WORK/(name+'.md')).read_text(),name
def pins(x):
 if isinstance(x,dict):
  if 'path' in x and 'sha256' in x:assert sha(x['path'])==x['sha256'],x['path']
  for label in ['source','object']:
   if label in x and label+'_sha256' in x:assert sha(x[label])==x[label+'_sha256'],x[label]
  for k,v in x.items():
   if k.startswith('/') and isinstance(v,str) and re.fullmatch('[0-9a-f]{64}',v):assert sha(k)==v,k
   elif k.startswith('/') and isinstance(v,dict) and 'sha256' in v:assert sha(k)==v['sha256'],k
   pins(v)
 elif isinstance(x,list):
  for v in x:pins(v)
for name in reviews:pins(load(WORK/(name+'-pins.json')))
for p in (WORK/'next').glob('*-pins.json'):pins(load(p))
selected={p.name:p for p in WORK.glob('*.md') if not p.name.startswith('final-archive-review')}
for p in WORK.glob('*.json'):
 if not p.name.startswith(('final-archive-review','archive-seal-result')):selected[p.name]=p
for name in ['CombinedHistogramAcquisitionAudit.lean','CombinedHistogramAcquisitionAudit.log','verify_histogram_acquisition.py','refresh_histogram_acquisition.py','archive_histogram_acquisition.py','final-archive-review-check.py','HistogramModuleInventory.lean','histogram-inventory.log','canonical-refresh-run.log']:
 selected[name]=WORK/name
# Retain successful component audits and smoke programs/logs as supporting checks.
for p in WORK.glob('*.lean'):
 if 'Audit' in p.name or 'Smoke' in p.name:selected[p.name]=p
for p in WORK.glob('*.log'):
 if any(tag in p.name for tag in ['audit','smoke']) and 'error:' not in p.read_text() and 'Traceback' not in p.read_text():selected[p.name]=p
for folder in [isolated,WORK/'canonical-refresh']:
 for p in folder.iterdir():
  if p.suffix in ['.json','.log']:selected[str(p.relative_to(WORK))]=p
for m in mods:selected[m+'.lean']=ROOT/'RiemannGaussian'/(m+'.lean')
for p in (WORK/'next').iterdir():
 if p.suffix in ['.md','.json']:selected[str(p.relative_to(WORK))]=p
for rel,p in selected.items():
 assert p.is_file(),p
 if p.suffix=='.log':assert 'error:' not in p.read_text() and 'Traceback' not in p.read_text(),rel
# Resolve every Markdown link before creating the packet or appending journals.
available=set(selected)|{'archive-provenance.json','verification.json','manifest.json'}
for rel,p in selected.items():
 if p.suffix!='.md':continue
 clean=re.sub(r'```.*?```','',p.read_text(),flags=re.S);clean=re.sub(r'`[^`]*`','',clean)
 for target in re.findall(r'\]\(([^)]+)\)',clean):
  if target.startswith(('http://','https://','#')):continue
  resolved=(PACK/rel).parent.joinpath(target.split('#')[0]).resolve()
  if resolved.is_relative_to(PACK.resolve()):assert str(resolved.relative_to(PACK.resolve())) in available,(rel,target)
  else:assert resolved.exists(),(rel,target)
assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
note=(WORK/'journal-append.md').read_bytes()
assert note.startswith(b'\n\n') and note.endswith(b'\n') and not note.endswith(b'\n\n')
for rel,pin in base['prefixes'].items():assert (ROOT/rel).stat().st_size==pin['bytes'],('unexpected journal append',rel)
PACK.mkdir();provenance={}
for rel,p in sorted(selected.items()):
 dest=PACK/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
 provenance[rel]={'source':str(p),'sha256':sha(p)}
dump(PACK/'archive-provenance.json',provenance)
v={'status':'PASS','goal':'ACTIVE','slice':'EXACT_ORIGINAL_HISTOGRAM_QUERY_AND_ACQUIRED_SOURCE_SELECTOR',
 'current_user_goal':'EXPLICIT_PAPER_RATE_COMPLETE_ORIGINAL_INPUT_BIT_RUNTIME',
 'current_rate_target':'2^(C*ell/sqrt(log(ell+2)))*(ell+1)^d; fixed C,d; ell=ceil(log2(N+1))',
 'full_runtime_subpower_status':'MILESTONE_NOT_COMPLETION_OF_EXPLICIT_RATE_GOAL',
 'complete_Lean_whole_program_bit_clock':'OPEN',
 'new_controller_public_report_subpower':'PREVIOUSLY_PROVED_ACTUAL_RETAINED_REPORT',
 'actual_original_incidence_padded_counts':'PROVED_SIXTEEN_SPARSE_FEATURE_HISTOGRAMS_ALL_PREFIXES',
 'actual_original_head_padded_counts':'PROVED_ONE_JOINT_COORDINATE_COLOUR_HISTOGRAM_ALL_PREFIXES',
 'physical_histogram_acquisition':'ACTUAL_TRIE_COUNTER_UPDATE_AND_SQUARE_INCREMENT_TWO_K_PLUS_ONE',
 'actual_compact_word_ids':'PROVED_DIRECT_COMPACT_ACQUISITION_EXACT_ORIGINAL_MENU_ORDER',
 'actual_prefix_and_row_dictionary':'PROVED_ORIGINAL_KEYS_LABELS_AND_LOGARITHMIC_QUERY_PAYLOADS',
 'actual_original_counts_and_score':'PROVED_EXACT_BOTH_LANES_AND_ORIGINAL_SCHEDULED_INTEGER_OBJECTIVE',
 'original_indexed_source_labels_and_ties':'PROVED_EXACT_SELECTED_IDS_WITH_PROOF_ONLY_DECODING',
 'source_metadata_term_list':'ELIMINATED_FROM_NEW_HISTOGRAM_SOURCE_RUNTIME',
 'local_completion_and_unary_count_padding':'ABSENT_FROM_NEW_HISTOGRAM_SOURCE_RUNTIME',
 'actual_original_setup_report':'PROVED_PAID_CONSERVATIVE_ORIGINAL_RESOURCE_POLYNOMIAL',
 'actual_original_family_report':'PROVED_UNIFORM_FIXED_POLYNOMIAL_SEVEN_ORIGINAL_MATERIALIZED_RESOURCES',
 'original_resource_dimensions':['n','F','r','Q','lambda','M=sum arity','L=r^Q'],
 'separate_next_research_supplement':'UNPROVED_ID_PAIR_PACKING_WITH_DISTINCT_BIN_CARDINALITY_GUARD',
 'research_supplement_in_canonical_declaration_totals':False,
 'streaming_histogram_report':'LINEAR_IN_OCCURRENCE_COUNT_TIMES_KEY_WIDTH_PLUS_LOG_COUNT_WIDTH',
 'whole_family_near_linear_bit_acquisition':'OPEN','complete_primitive_query_bit_complexity':'OPEN',
 'selected_id_and_colour_reads_inside_query':'PROVED_ACTUALLY_ACQUIRED',
 'selected_incidence_labels_for_packing':'OPEN','packing_universal_cache_pullback_public_composition':'OPEN',
 'native_Word_cacheWord_runtime':'ABSENT_FROM_NEW_HISTOGRAM_SOURCE_SELECTOR',
 'native_callback_tokens_length_argument_lowering':'OPEN',
 'arity_owner_index_support_native_control_bit_refinement':'OPEN',
 'original_parity_prescription_AST_construction_bit_refinement':'OPEN',
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
 'preserved_append_only_prefixes':len(base['prefixes']),'journal_append_bytes':len(note),
 'independent_reviews':reviews,'modules':info}
dump(PACK/'verification.json',v)
for rel,pin in base['prefixes'].items():
 assert (ROOT/rel).stat().st_size==pin['bytes'],('unexpected journal append',rel)
 with (ROOT/rel).open('ab') as f:f.write(note)
preserve()
files={str(p.relative_to(PACK)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(PACK.rglob('*')) if p.is_file()}
dump(PACK/'manifest.json',{'status':'PASS','files':files})
links=0
for p in PACK.rglob('*.md'):
 clean=re.sub(r'```.*?```','',p.read_text(),flags=re.S);clean=re.sub(r'`[^`]*`','',clean)
 for target in re.findall(r'\]\(([^)]+)\)',clean):
  if target.startswith(('http://','https://','#')):continue
  assert (p.parent/target.split('#')[0]).exists(),(p.name,target);links+=1
assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
print(json.dumps({'status':'PASS','files':len(files)+1,'manifest_entries':len(files),'provenance_origins':len(provenance),'links_checked':links,'modules':len(mods),'declarations':v['generated_declarations'],'theorems':v['theorem_constants'],'actual_compiler_imports':v['actual_compiler_imported_modules'],'journal_append_bytes':len(note)},indent=2))
