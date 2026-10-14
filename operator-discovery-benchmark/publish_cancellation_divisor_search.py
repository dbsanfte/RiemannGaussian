"""Publication004 integrity loader. Publication requires all independent audits.
Only invocation of publish writes output; importing this module performs no work.
"""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
FLAGS=dict(global_bound_proved=False,RH_proved=False)
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v):
 with p.open('x')as f:json.dump(v,f,sort_keys=True,indent=2,allow_nan=False);f.write('\n')
def bound_path(directory,name):
 p=ROOT/name
 if p.is_file():return p
 p=directory/name
 if p.is_file():return p
 p=directory/(name+'.json')
 if p.is_file():return p
 raise FileNotFoundError('bound input '+name)
def check_bindings(directory,receipt):
 for field in ('input_sha256','source_sha256'):
  for name,h in receipt.get(field,{}).items():
   if sha(bound_path(directory,name))!=h:raise ValueError('receipt binding changed: '+name)
def check_manifest(path,relative_root):
 m=read(path)
 for name,h in m['files'].items():
  if sha(relative_root/name)!=h:raise ValueError('manifest changed: '+name)
 return m

def load_inputs():
 old=BASE/'publication-003';resource=ROOT/'detector-performance-results/publication-001'
 check_manifest(old/'manifest.json',ROOT);check_manifest(resource/'manifest.json',ROOT)
 pilots={name:BASE/name for name in ('divisor-localizer-probe-001','divisor-cell-probe-001')}
 receipts={}
 for name,d in pilots.items():
  r=read(d/'independent_verification.json')
  if r.get('all_passed')is not True:raise ValueError('independent whole audit required: '+name)
  check_bindings(d,r);receipts[name]=r
  seal=read(d/'source_seal.json');hashes=seal.get('hashes',seal)
  for n,h in hashes.items():
   if sha(ROOT/n)!=h or sha(d/'frozen_source'/n)!=h:raise ValueError('pilot source changed: '+n)
  if not (d/'receipt.json').is_file():raise FileNotFoundError('terminal receipt required')
  receipt=read(d/'receipt.json')
  if type(receipt.get('files_sha256'))is not dict or not receipt['files_sha256']:
   raise ValueError('terminal nested artifact bindings required')
  for n,h in receipt['files_sha256'].items():
   if sha(d/n)!=h:raise ValueError('terminal artifact changed: '+name+'/'+n)
 scope_dir=BASE/'divisor-localizer-scope-001'
 scope=read(scope_dir/'uniform_scope_independent_review.json')
 if scope.get('all_passed')is not True or scope.get('constant_coordinates')!=['0']*5 or scope.get('lhs_dot_y')!='-1':
  raise ValueError('localizer uniform scope admission')
 check_bindings(pilots['divisor-localizer-probe-001'],scope)
 calibration=BASE/'divisor-coupling-calibration-001'
 check_manifest(calibration/'manifest.json',calibration)
 r=read(calibration/'independent_verification.json');check_bindings(calibration,r)
 root=read(calibration/'root_verification.json');check_bindings(calibration,root)
 if r.get('all_passed')is not True or root.get('all_passed')is not True or root['manifest_sha256']!=sha(calibration/'manifest.json'):
  raise ValueError('calibration root/independent admission')
 # Calibration binds its exact dependency closure separately.
 spec=read(calibration/'spec.json')
 for n,h in spec['source_sha256'].items():
  if sha(ROOT/n)!=h or sha(calibration/'frozen_source'/n)!=h:raise ValueError('coupling source changed: '+n)
 gram=BASE/'divisor-cell-gram-probe-001'
 gr=read(gram/'independent_verification.json');check_bindings(gram,gr)
 if gr.get('all_passed')is not True or gr.get('contexts_verified')!=18 or gr.get('full_2x2_failures')!=10 or gr.get('unsupported_coordinates')!=0:
  raise ValueError('complete independently checked Gram diagnostic required')
 if gr['dual_sha256']!=sha(pilots['divisor-cell-probe-001']/'jobs/dual-000.json') or gr['verifier_sha256']!=sha(ROOT/'check_divisor_cell_gram_probe.py'):
  raise ValueError('Gram dual/checker binding changed')
 protocol=read(gram/'protocol.json');seal=read(gram/'seal.json');result=read(gram/'results.json')
 if seal!=dict(protocol_sha256=sha(gram/'protocol.json'),code_sha256=protocol['code_sha256']) or protocol['parent_protocol_sha256']!=sha(pilots['divisor-cell-probe-001']/'protocol.json') or result['dual_input_sha256']!=gr['dual_sha256'] or result['protocol_sha256']!=sha(gram/'protocol.json'):
  raise ValueError('Gram protocol/result/parent binding changed')
 for n,h in protocol['code_sha256'].items():
  if sha(ROOT/n)!=h or sha(gram/'frozen_source'/n)!=h:raise ValueError('Gram source changed: '+n)
 from check_divisor_cell_gram_probe import audit
 if audit(gram)!=gr:raise ValueError('Gram independent diagnostic replay changed')
 return dict(old=old,resource=resource,pilots=pilots,receipts=receipts,calibration=calibration,scope_dir=scope_dir,scope=scope,gram=gram,gram_receipt=gr)

def publish():
 inputs=load_inputs();handoff=ROOT/'CANCELLATION_DIVISOR_SEARCH_HANDOFF.txt'
 if not handoff.is_file():raise FileNotFoundError('final handoff required')
 out=BASE/'publication-004'
 if out.exists():raise FileExistsError('exclusive publication required')
 notes=['publish_cancellation_divisor_search.py','CANCELLATION_DIVISOR_SEARCH_HANDOFF.txt',
  'cancellation_divisor_localizer_uniform_review.txt','cancellation_divisor_coupling_budget_scope.txt',
  'cancellation_cross_divisor_search_design.txt','cancellation_divisor_cell_language_scope.txt',
  'divisor_localizer_training_adjudication.json','divisor_localizer_training_adjudication.txt',
  'divisor_cell_training_adjudication.json','divisor_cell_training_adjudication.txt',
  'cancellation_gcd_closure_probe.py','cancellation_gcd_separator_probe.py',
  'cancellation_gcd_closure_analytical_review.txt','check_divisor_cell_gram_probe.py']
 files={ROOT/n for n in notes}
 for d in (inputs['scope_dir'],BASE/'gcd-closure-probe-001',BASE/'gcd-separator-probe-001'):
  files.update(p for p in d.rglob('*')if p.is_file()and '__pycache__'not in p.parts)
 # Earlier PNT note is auxiliary arithmetic scope only, not evidence for this cone.
 auxiliary=ROOT/'factor_region_filtered_prime_review.txt'
 if auxiliary.is_file():files.add(auxiliary)
 for d in [*inputs['pilots'].values(),inputs['calibration'],inputs['gram']]:
  files.update(p for p in d.rglob('*')if p.is_file()and '__pycache__'not in p.parts)
 for d in inputs['pilots'].values():
  s=read(d/'source_seal.json');files.update(ROOT/n for n in s.get('hashes',s))
 files.update(ROOT/n for n in read(inputs['calibration']/'spec.json')['source_sha256'])
 files.update(ROOT/n for n in read(inputs['gram']/'protocol.json')['code_sha256'])
 for d in (inputs['old'],inputs['resource']):files.update([d/'manifest.json',d/'report.json'])
 report=dict(schema=4,prior_research_publication='publication-003',prior_resource_publication='publication-001',
  previous_research_manifest_sha256=sha(inputs['old']/'manifest.json'),previous_resource_manifest_sha256=sha(inputs['resource']/'manifest.json'),
  pilots={name:dict(independent_receipt_sha256=sha(d/'independent_verification.json'),
     training_statuses=inputs['receipts'][name].get('training_statuses'),
     followup_statuses=inputs['receipts'][name].get('followup_statuses'),
     original_failures_preserved=True)for name,d in inputs['pilots'].items()},
  localizer_uniform_scope=dict(receipt_sha256=sha(inputs['scope_dir']/'uniform_scope_independent_review.json'),scope=inputs['scope']['scope']),
  coupling_calibration=dict(supplied_identity_not_discovery=True,root_receipt_sha256=sha(inputs['calibration']/'root_verification.json')),
  cell_gram_diagnostic=dict(independent_receipt_sha256=sha(inputs['gram']/'independent_verification.json'),protocol_sha256=sha(inputs['gram']/'protocol.json'),results_sha256=sha(inputs['gram']/'results.json'),dual_sha256=inputs['gram_receipt']['dual_sha256'],contexts_verified=18,non_PSD_contexts=10,unsupported_coordinates=0,old_witness_separates_expanded_cell_gram_cone=False,feasibility_proved=False,simple_direction=inputs['gram_receipt']['simple_direction']),
  scope='finite declared shared proof cones and supplied exact identities; every missing/failed state retained; no actual bound refutation',
  next_action='preregister expanded cell Gram interactions, search independently, and prove full accepted templates uniformly',**FLAGS)
 # Verify every input before any publication mutation.
 hashes={str(p.relative_to(ROOT)):sha(p)for p in sorted(files)}
 out.mkdir()
 snapshot=out/'frozen_source';snapshot.mkdir()
 for n in ['check_divisor_cell_gram_probe.py','publish_cancellation_divisor_search.py']:
  target=snapshot/n
  with target.open('xb')as f:f.write((ROOT/n).read_bytes())
  hashes[str(target.relative_to(ROOT))]=sha(target)
 with (out/handoff.name).open('xb')as f:f.write(handoff.read_bytes())
 hashes[str((out/handoff.name).relative_to(ROOT))]=sha(out/handoff.name)
 write(out/'report.json',report);hashes[str((out/'report.json').relative_to(ROOT))]=sha(out/'report.json')
 write(out/'manifest.json',dict(schema=1,files=hashes,**FLAGS));check_manifest(out/'manifest.json',ROOT)
 # Final integrity replay, preserving old snapshots.
 load_inputs()
 check_manifest(out/'manifest.json',ROOT)
 pointer=dict(publication='publication-004',report_sha256=sha(out/'report.json'),manifest_sha256=sha(out/'manifest.json'),**FLAGS)
 tmp=BASE/'latest-004.tmp';write(tmp,pointer);tmp.replace(BASE/'latest.json')
 return dict(publication='publication-004',bound_files=len(hashes),**FLAGS)
if __name__=='__main__':print(json.dumps(publish()))
