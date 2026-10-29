#!/usr/bin/env python3
"""Seal only the verified native-bit execution join; preserve all earlier work."""
from pathlib import Path
import hashlib,json,re,shutil,subprocess
ROOT=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-native-bit-join-20261027')
PACKET=ROOT/'docs/research-evidence/semiprime-native-bit-join-20261027'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
base=json.loads((WORK/'preservation-before.json').read_text())
def preserve():
 for section in ['protected','concurrent']:
  for rel,h in base[section].items():assert sha(ROOT/rel)==h,(section,rel)
 for rel,v in base['prefixes'].items():
  assert hashlib.sha256((ROOT/rel).read_bytes()[:v['bytes']]).hexdigest()==v['sha256'],rel
preserve()
assert not PACKET.exists(),'Refuse to overwrite a sealed research packet'
mods=json.loads((WORK/'all-modules.json').read_text());assert len(mods)==16
log=(WORK/'CombinedNativeBitJoinAudit.log').read_text()
au={m:{'declarations':int(d),'theorem_constants':int(t)} for m,d,t in re.findall(r'^AUDIT RiemannGaussian\.(\w+): declarations=(\d+), theorems=(\d+), standard_axioms_only=true$',log,re.M)}
assert set(au)==set(mods)
assert log.count('-- All linting checks passed!')==len(mods) and 'error:' not in log
assert sum(x['declarations'] for x in au.values())==493
assert sum(x['theorem_constants'] for x in au.values())==331
isolated=WORK/'final-isolated';summary=json.loads((isolated/'summary.json').read_text())
assert all(summary[k] for k in ['complete','strict_pass','all_objects_match','dependency_snapshot_unchanged'])
assert (isolated/'dependencies-before.json').read_bytes()==(isolated/'dependencies-after.json').read_bytes()
results=json.loads((isolated/'results.json').read_text());assert len(results)==len(mods)
info={}
for row in results:
 name=row['module'].split('.')[-1];src=ROOT/'RiemannGaussian'/(name+'.lean');obj=ROOT/'.lake/build/lib/lean/RiemannGaussian'/(name+'.olean')
 assert row['exit_code']==0 and row['object_matches']
 assert sha(src)==row['source_sha256'] and sha(obj)==row['canonical_sha256']==row['isolated_sha256']==sha(isolated/(name+'.olean'))
 info[name]={'source':str(src.relative_to(ROOT)),'source_sha256':sha(src),'object_sha256':sha(obj),**au[name]}
for stem in ['review-native-bit-callpath','review-native-bit-costs']:
 assert 'PASS' in (WORK/(stem+'.md')).read_text()
 for p,h in json.loads((WORK/(stem+'.json')).read_text()).items():assert sha(Path(p))==h,p
# Only final notes, pins, audits, runtime controls and reproducible verification tools.
selected={p.name:p for p in WORK.glob('*.md') if p.name not in {'review-native-counter-path.md','final-archive-review.md'}}
for p in WORK.glob('*.json'):
 if not p.name.startswith('final-archive-review'):selected[p.name]=p
excluded={'ArrayProbe.lean','Checks.lean','GroupBudgetDiagnostic.lean'}
for p in WORK.glob('*.lean'):
 if p.name not in excluded:selected[p.name]=p
for p in WORK.glob('*.log'):
 if p.name not in {'group-budget-diagnostic.log','final-archive-review.log'}:selected[p.name]=p
for name in ['verify_native_bit_join.py','archive_native_bit_join.py']:selected[name]=WORK/name
for p in isolated.iterdir():
 if p.suffix in ['.json','.log']:selected[str(p.relative_to(WORK))]=p
for name in mods:selected[name+'.lean']=ROOT/'RiemannGaussian'/(name+'.lean')
for rel,p in selected.items():
 assert p.is_file(),p
 if p.suffix=='.log':assert 'error:' not in p.read_text() and 'Traceback' not in p.read_text(),rel
assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
PACKET.mkdir();provenance={}
for rel,p in sorted(selected.items()):
 dest=PACKET/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
 provenance[rel]={'source':str(p),'sha256':sha(p)}
dump(PACKET/'archive-provenance.json',provenance)
verification={'status':'PASS','goal':'ACTIVE','slice':'EXECUTED_PHYSICAL_NATIVE_PATH_AND_ORIGINAL_SOURCE_COST_JOIN',
 'prior_paper_factoring_bit_time':'N^o(1), permitting subexponential storage',
 'complete_Lean_whole_program_bit_clock':'OPEN','prior_controller_mixed_report_subpower':'FROZEN_PROVED',
 'new_controller_public_report_subpower':'OPEN','new_controller_all_input_correctness':True,
 'physical_corrected_port_local_group_on_actual_path':True,'source_and_encoding_work_retained':True,
 'arbitrary_group_work_assumption_discharged':True,'original_source_width_guards_derived':True,
 'outer_arithmetic_and_Hermite':'SCALAR_REFINEMENT_OPEN','source_production_and_encoding':'SCALAR_BOUNDARIES_OPEN',
 'finite_address_control_clock':'OPEN','new_native_long_query_bound':False,'practical_speedup_claimed':False,
 'module_count':len(mods),'generated_declarations':sum(x['declarations'] for x in au.values()),
 'theorem_constants':sum(x['theorem_constants'] for x in au.values()),
 'strict_options':['autoImplicit=false','warningAsError=true'],'ordinary_root_import':True,'scoped_linters_per_module':15,
 'all_generated_transitive_standard_axioms_only':True,'isolated_objects_identical':True,
 'dependency_checkpoint_unchanged':True,'actual_compiler_imported_modules':summary['actual_compiler_imported_modules'],
 'dependency_list_provenance':'Lean environment header; no source-text import scanner',
 'preserved_prior_files':len(base['protected']),'preserved_concurrent_files':len(base['concurrent']),
 'preserved_append_only_prefixes':len(base['prefixes']),'commit_or_push':False,'modules':info}
dump(PACKET/'verification.json',verification)
note=(WORK/'journal-append.md').read_bytes()
for rel,pin in base['prefixes'].items():
 assert (ROOT/rel).stat().st_size==pin['bytes'],('unexpected extra journal text',rel)
 with (ROOT/rel).open('ab') as f:f.write(note)
preserve()
files={str(p.relative_to(PACKET)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(PACKET.rglob('*')) if p.is_file()}
dump(PACKET/'manifest.json',{'status':'PASS','files':files})
links=0
for p in PACKET.glob('*.md'):
 clean=re.sub(r'```.*?```','',p.read_text(),flags=re.S);clean=re.sub(r'`[^`]*`','',clean)
 for target in re.findall(r'\]\(([^)]+)\)',clean):
  if target.startswith(('http://','https://','#')):continue
  assert (p.parent/target.split('#')[0]).exists(),(p.name,target);links+=1
assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
print(json.dumps({'status':'PASS','packet':str(PACKET),'files':len(files)+1,'manifest_entries':len(files),'links_checked':links,'modules':len(mods),'declarations':verification['generated_declarations'],'theorems':verification['theorem_constants'],'actual_compiler_imports':verification['actual_compiler_imported_modules']},indent=2))
