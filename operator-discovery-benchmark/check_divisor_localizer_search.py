"""Independent whole-run divisor-localizer finite-cone audit."""
import ast,json,re,sys
from collections import OrderedDict
from pathlib import Path
from fractions import Fraction as F
import check_cancellation_arithmetic_run as I
import check_cancellation_divisor_localizer as B
import check_grouped_arithmetic_sparse as S
import check_cancellation_gram as G
ROOT=Path(__file__).resolve().parent
TESTS=['test_cancellation_divisor_localizer_language','test_check_cancellation_divisor_localizer','test_cancellation_native_gram_dual','test_run_divisor_localizer_search']
LIMITS=dict(max_columns=1024,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=80,max_degree=12,max_denominator=1000000,time_limit=180)
DUAL_LIMITS=dict(time_limit=180,max_rows=1500,max_variables=60000,max_work=400000000,max_cells=2000000,max_denominator=2**4096,max_coefficient_bits=4096,max_columns=1024,max_monomials=30000,max_operations=200000000,max_horizon=80,max_degree=12)
PROGRAMS=[dict(target='mu',q=6,C=32,claim='critical',constraint='zero_cubic',dictionary_mode='extended',allow_constant_slack=True),dict(target='mu',q=2,C=1,claim='unsigned_calibration',constraint='none',dictionary_mode='extended',allow_constant_slack=True)]
def source_names():
 pending=['run_divisor_localizer_search','check_divisor_localizer_search',*TESTS];seen=set()
 while pending:
  name=pending.pop();f=ROOT/(name+'.py')
  if name in seen or not f.is_file():continue
  seen.add(name)
  for node in ast.walk(ast.parse(f.read_text())):
   if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
   elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
 return sorted(x+'.py'for x in seen)
def audit(directory):
 d=Path(directory).resolve();protocol=I.read(d/'protocol.json');source=I.read(d/'source_seal.json');input_value=I.read(d/'input.json');receipt=I.read(d/'receipt.json');start={n:I.sha(d/n)for n in ['protocol.json','source_seal.json','seal.json','input.json','tests.json','training.json','candidate_seal.json','followup.json','receipt.json']}
 def bindings():
  I.require(set(source)==set(source_names()),'complete executed source closure')
  I.require(I.read(d/'seal.json')==dict(protocol_sha256=I.sha(d/'protocol.json'),source_seal_sha256=I.sha(d/'source_seal.json'),input_sha256=I.sha(d/'input.json')),'protocol/source/input seal')
  for name,h in source.items():I.require(I.sha(ROOT/name)==h and I.sha(d/'frozen_source'/name)==h,'source '+name)
  for name,h in input_value['input_sha256'].items():I.require(I.sha(ROOT/name)==h,'prior bound input '+name)
  for path in ['cancellation-arithmetic-results/publication-003/manifest.json','detector-performance-results/publication-001/manifest.json']:
   for name,h in I.read(ROOT/path)['files'].items():I.require(I.sha(ROOT/name)==h,'prior publication '+name)
 bindings();I.require(protocol['schema']==1 and protocol['language']==B.SPEC and protocol['dictionary']==B.descriptors() and protocol['programs']==PROGRAMS and protocol['training_scales']==[1,2,3,5] and protocol['final_scales']==[8,13] and protocol['limits']==LIMITS and protocol['dual_limits']==DUAL_LIMITS and protocol['tests']==TESTS,'known frozen grammar/grid/limits');I.require(protocol['audit_seconds']==180 and protocol['final_refit'] is False and protocol['no_actual_signed_response_inputs'] is True,'independence/no refit');I.require(protocol['parallel']==dict(workers=2,worker_memory_bytes=2*1024**3,memory_budget_bytes=4*1024**3,timeout_seconds=600,max_jobs=64,max_result_bytes=65536),'parallel contract')
 test=I.read(d/'tests.json');I.require(test['returncode']==0 and re.search(r'Ran \d+ tests? in .*\n\s*OK\s*$',test['stdout']+test['stderr']),'calibration tests');training=I.read(d/'training.json');plan=I.read(d/'candidate_seal.json');follow=I.read(d/'followup.json');I.require(plan['training_sha256']==start['training.json'],'training selection seal')
 built_cache=OrderedDict();loaded_jobs=[]
 def build(program,X):
  key=(I.digest(program),X)
  if X>5:return B.build(program,X)
  if key not in built_cache:
   built_cache[key]=B.build(program,X)
   if len(built_cache)>4:built_cache.popitem(last=False)
  built_cache.move_to_end(key)
  return built_cache[key]
 def check_record(record,program,scales,phase):
  I.require(record['phase']==phase and record['refitted'] is False,'phase/no refit')
  built=[build(program,X)for X in scales];ordinary=[v['instance']for v in built];instances=ordinary+([B.auxiliary()['instance']]if phase in ['train','dual']and program['constraint']=='zero_cubic'else[])
  if 'case_hashes'in record:
   I.require(record['program']==program and record['scales']==scales and record['ordinary_case_hashes']==list(map(I.digest,ordinary)) and record['case_hashes']==list(map(I.digest,instances)) and record['factor_archive_hashes']==[I.digest(v['factor_archive'])for v in built] and record['divisor_archive_hashes']==[I.digest(v['divisor_archive'])for v in built] and record['dictionary_sha256']==I.digest(B.descriptors()),'complete source/archive/target metadata')
  status=record['status']
  if status in ['finite_certificate','exact_separator']:I.require('case_hashes'in record,'accepted result needs complete source metadata')
  if status=='finite_certificate':
   I.require(phase!='dual' and record['synthesis']['status']==status,'finite type');S.verify_joint_result(instances,record['synthesis'],allow_constant_slack=program['allow_constant_slack'],expected_instance_sha256=list(map(I.digest,instances)),time_limit=180,max_operations=200000000);I.require(record['independent_check']['verified'] is True,'accepted independent receipt')
  elif phase=='dual'and record.get('synthesis',{}).get('certified'):I.require(status=='exact_separator','certified dual status');G.verify_dual(instances,scales,record['synthesis'])
  else:I.require(status in ['missing_resource','rejected','no_certificate_found','uncertified'],'explicit retained nonadmission')
  return built
 def row(receipt,phase,index):
  I.require(receipt['index']==index and receipt['status']in ['available','missing_resource','error'],'ordered process receipt')
  if receipt['status']!='available':I.require('value'not in receipt,'process failure has no result');return None
  val=receipt['value'];expected=f'jobs/{phase}-{index:03d}.json';I.require(val['file']==expected and val['sha256']==I.sha(d/expected),'isolated job hash');record=I.read(d/expected);loaded_jobs.append(record);I.require(record['index']==index and record['status']==val['status'] and record['cost']==val['cost'],'job receipt');return record
 I.require(len(training['results'])==2,'all training attempts');expected_jobs=[];statuses=[]
 for j,program in enumerate(PROGRAMS):
  record=row(training['results'][j],'train',j)
  if record is not None:check_record(record,program,[1,2,3,5],'train')
  status=record['status']if record is not None else training['results'][j]['status'];statuses.append(status)
  if status=='finite_certificate':
   val=training['results'][j]['value'];expected_jobs.extend(dict(phase='final',program=program,X=X,attempt_file=val['file'],attempt_sha256=val['sha256'])for X in [8,13])
  elif program['claim']=='critical':expected_jobs.append(dict(phase='dual',program=program))
 I.require(plan['jobs']==expected_jobs and len(follow['results'])==len(expected_jobs),'complete deterministic followup plan');follow_status=[]
 for j,job in enumerate(expected_jobs):
  record=row(follow['results'][j],job['phase'],j);follow_status.append(record['status']if record is not None else follow['results'][j]['status'])
  if record is None:continue
  check_record(record,job['program'],[job['X']]if job['phase']=='final'else [1,2,3,5],job['phase'])
  if job['phase']=='final'and record['status']=='finite_certificate':
   attempt=I.read(d/job['attempt_file']);weights=attempt['synthesis']['weights'];I.require(record['synthesis']['weights']==weights and record['weights_sha256']==I.digest(weights),'fixed unchanged weights')
 actual=[]
 for program in PROGRAMS:
  for X in [1,2,3,5,8,13]:
   N=4*X-1
   D=F(program['C'])*X*X*I.B.rootceil(X,program['q']) if program['claim']=='critical' else sum(sum(n for n in range(2*X,4*X)if n>=i)*int(all(e==1 for e in I.B.P.factor(i).values()))for i in range(1,N+1))
   actual.append(I.B.truth(dict(X=X,D=str(D),instance={'target':program['target']})))
 files={str(p.relative_to(d)):I.sha(p)for p in sorted(d.rglob('*.json'))if p.name not in ['receipt.json','independent_verification.json']}
 I.require(receipt['files_sha256']==files and receipt['source_count']==len(source) and receipt['refitted'] is False,'complete run receipt')
 def flags(v):
  if isinstance(v,dict):
   for k,x in v.items():
    if k in ['global_bound_proved','RH_proved']:I.require(x is False,'global promotion')
    flags(x)
  elif isinstance(v,list):
   for x in v:flags(x)
 for v in [protocol,training,follow,receipt,*loaded_jobs]:flags(v)
 bindings();I.require(start=={n:I.sha(d/n)for n in start},'end input hashes')
 return dict(all_passed=True,input_sha256=start,training_statuses=statuses,followup_statuses=follow_status,actual_truth_after_search=actual,construction_shared_with_calibrated_checker_builder=True,independent_certificate_algebra_verified=True,global_bound_proved=False,RH_proved=False)
if __name__=='__main__':
 d=Path(sys.argv[1]);r=audit(d)
 with (d/'independent_verification.json').open('x')as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
 print(json.dumps(r))
