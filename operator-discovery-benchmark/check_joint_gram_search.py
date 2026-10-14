"""Independent whole-run shared joint-divisor Gram finite-cone audit."""
import ast,json,re,sys,math
from collections import OrderedDict
from pathlib import Path
from fractions import Fraction as F
import check_cancellation_arithmetic_run as I
import check_cancellation_joint_gram_program as B
import check_cancellation_shared_gram as G
import check_cancellation_divisor_cells as SCALAR
ROOT=Path(__file__).resolve().parent
TESTS=['test_cancellation_shared_gram_synthesis_v2','test_check_cancellation_shared_gram','test_cancellation_shared_gram_dual','test_check_cancellation_joint_gram_program','test_run_joint_gram_search']
LIMITS=dict(max_columns=2048,max_monomials=100000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=80,max_degree=12,max_denominator=1000000,time_limit=180)
SOLVER_LIMITS=dict(LIMITS,max_exact_cells=4000000,max_exact_work=450000000,max_checkpoint_bytes=8388608,row_normalization=True)
DUAL_LIMITS=dict(time_limit=180,max_rows=2500,max_variables=60000,max_work=450000000,max_cells=4000000,max_denominator=2**4096,max_coefficient_bits=4096,max_columns=2048,max_monomials=100000,max_operations=200000000,max_horizon=80,max_degree=12)
PROGRAMS=[dict(target='mu',q=6,C=32,claim='critical',constraint='zero_cubic',dictionary_mode='extended',allow_constant_slack=True),dict(target='mu',q=2,C=1,claim='unsigned_calibration',constraint='none',dictionary_mode='extended',allow_constant_slack=True)]
def source_names():
 pending=['run_joint_gram_search','check_joint_gram_search',*TESTS];seen=set()
 while pending:
  name=pending.pop();f=ROOT/(name+'.py')
  if name in seen or not f.is_file():continue
  seen.add(name)
  for node in ast.walk(ast.parse(f.read_text())):
   if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
   elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
 return sorted(x+'.py'for x in seen)

def checkpoint_columns(instances,blocks,specs):
 """Independent complete scalar and shared-Gram expansion for checkpoint hashes."""
 parsed=[G.G.columns(v)for v in instances];ns=len(parsed[0][1]);nr=len(parsed[0][2])
 I.require(all(len(s)==ns and len(r)==nr for _,s,r in parsed),'same scalar checkpoint groups')
 lhs={(k,)+m:q for k,(p,_,_)in enumerate(parsed)for m,q in p.items()}
 columns=[]
 for j in range(ns):columns.append({(k,)+m:q for k,(_,sq,_)in enumerate(parsed)for m,q in sq[j].items()})
 for j in range(nr):
  col={(k,)+m:q for k,(_,_,rel)in enumerate(parsed)for m,q in rel[j].items()}
  columns.extend([col,{m:-q for m,q in col.items()}])
 columns.extend({(k,):F(1)}for k in range(len(instances)));offset=len(columns)
 layout=[dict(index=i,kind='scalar')for i in range(offset)]
 for name,n in sorted(specs.items()):
  for a in range(n):
   for b in range(a,n):
    col={}
    for k,(instance,row)in enumerate(zip(instances,blocks)):
     for atoms in row[name]:
      p=G.P.multiply(G.P.parse(atoms[a],instance['horizon']),G.P.parse(atoms[b],instance['horizon']))
      for m,q in p.items():
       key=(k,)+m;col[key]=col.get(key,F(0))+q*(1 if a==b else 2)
    columns.append({m:q for m,q in col.items()if q});layout.append(dict(index=len(layout),kind='Gram',group=name,i=a,j=b))
 ms=sorted(set(lhs)|{m for col in columns for m in col})
 return columns,lhs,ms,[ns,nr],offset,layout


def verify_checkpoint(checkpoint,instances,blocks,specs):
 I.require(checkpoint['schema']=='shared-Gram-SDP-proposal-v2' and checkpoint['proposal_only']is True and checkpoint['certified']is False,'proposal-only checkpoint')
 I.require(len(json.dumps(checkpoint,sort_keys=True,separators=(',',':'),allow_nan=False).encode())<=SOLVER_LIMITS['max_checkpoint_bytes'],'bounded checkpoint')
 I.require(checkpoint['source_hashes']==list(map(I.digest,instances)) and checkpoint['gram_block_hashes']==list(map(I.digest,blocks)) and checkpoint['gram_specs']==specs,'checkpoint source binding')
 columns,lhs,ms,shape,offset,layout=checkpoint_columns(instances,blocks,specs)
 monomials=[dict(instance=m[0],m=list(m[1:]))for m in ms]
 I.require(checkpoint['scalar_shape']==shape and checkpoint['scalar_offset']==offset and checkpoint['column_layout']==layout and checkpoint['layout_hash']==I.digest(layout),'complete checkpoint column order')
 I.require(checkpoint['monomials']==monomials and checkpoint['row_order_hash']==I.digest(monomials),'complete checkpoint row order')
 I.require(checkpoint['exact_columns_hash']==I.digest([[[list(m),str(q)]for m,q in sorted(col.items())]for col in columns]) and checkpoint['exact_target_hash']==I.digest([[list(m),str(q)]for m,q in sorted(lhs.items())]),'independent checkpoint exact coefficient hashes')
 vector=checkpoint['float_vector']
 I.require(type(vector)is list and len(vector)==len(columns) and all(type(v)in(int,float)and math.isfinite(v)for v in vector),'complete finite proposal vector')
 I.require(checkpoint['active_threshold']==1e-7 and checkpoint['active_support']==[i for i in range(offset)if vector[i]>1e-7]+list(range(offset,len(columns))),'saved declared active face')
 I.require(checkpoint['numerical_options']==dict(solver='CLARABEL',max_threads=1,row_normalization=True),'known numerical options')
 I.require(checkpoint['float_objective']is None or type(checkpoint['float_objective'])in(int,float)and math.isfinite(checkpoint['float_objective']),'finite proposal objective')
 expected=dict(max_exact_work=450000000,max_exact_cells=4000000,max_denominator=1000000,max_coefficient_bits=4096,max_operations=200000000,time_limit=180)
 I.require(checkpoint['reconstruction_limits']==expected and type(checkpoint['reconstruction_attempts'])is list,'checkpoint declared exact limits/attempts')
 return dict(verified=True,exact_coefficient_hashes_independently_verified=True,proposal_only=True)

def audit(directory):
 d=Path(directory).resolve();protocol=I.read(d/'protocol.json');source=I.read(d/'source_seal.json');input_value=I.read(d/'input.json');receipt=I.read(d/'receipt.json');start={n:I.sha(d/n)for n in ['protocol.json','source_seal.json','seal.json','input.json','tests.json','training.json','candidate_seal.json','followup.json','receipt.json']}
 def bindings():
  I.require(set(source)==set(source_names()),'complete executed source closure')
  I.require(I.read(d/'seal.json')==dict(protocol_sha256=I.sha(d/'protocol.json'),source_seal_sha256=I.sha(d/'source_seal.json'),input_sha256=I.sha(d/'input.json')),'protocol/source/input seal')
  for name,h in source.items():I.require(I.sha(ROOT/name)==h and I.sha(d/'frozen_source'/name)==h,'source '+name)
  mandatory={'cancellation-arithmetic-results/publication-005/manifest.json','detector-performance-results/publication-001/manifest.json','cancellation-arithmetic-results/cell-joint-gram-probe-001/independent_verification.json','detector_resource_search.json','cancellation-arithmetic-results/divisor-cell-probe-001/jobs/train-001.json'}
  I.require(mandatory<=set(input_value['input_sha256']),'complete prior evidence input binding')
  for name,h in input_value['input_sha256'].items():I.require(I.sha(ROOT/name)==h,'prior bound input '+name)
  for path in ['cancellation-arithmetic-results/publication-005/manifest.json','detector-performance-results/publication-001/manifest.json']:
   for name,h in I.read(ROOT/path)['files'].items():I.require(I.sha(ROOT/name)==h,'prior publication '+name)
 bindings();I.require(protocol['schema']==1 and protocol['language']==B.SPEC and protocol['dictionary']==SCALAR.descriptors() and protocol['gram_groups']==B.group_descriptors() and protocol['gram_specs']==B.gram_specs() and protocol['programs']==PROGRAMS and protocol['training_scales']==[1,2,3,5] and protocol['final_scales']==[8,13] and protocol['limits']==LIMITS and protocol['solver_limits']==SOLVER_LIMITS and protocol['dual_limits']==DUAL_LIMITS and protocol['tests']==TESTS,'known frozen grammar/grid/limits');I.require(protocol['final_refit'] is False and protocol['no_actual_signed_response_inputs'] is True,'independence/no refit');I.require(protocol['parallel']==dict(workers=2,worker_memory_bytes=2*1024**3,memory_budget_bytes=4*1024**3,timeout_seconds=600,max_jobs=64,max_result_bytes=65536),'parallel contract')
 test=I.read(d/'tests.json');I.require(test['returncode']==0 and re.search(r'Ran \d+ tests? in .*\n\s*OK\s*$',test['stdout']+test['stderr']),'calibration tests');training=I.read(d/'training.json');plan=I.read(d/'candidate_seal.json');follow=I.read(d/'followup.json');I.require(plan['training_sha256']==start['training.json'],'training selection seal')
 built_cache=OrderedDict();loaded_jobs=[];checkpoints_verified=[];supplied_calibrations_verified=0
 def build(program,X):
  key=(I.digest(program),X)
  if X>5:return B.build(program,X)
  if key not in built_cache:
   built_cache[key]=B.build(program,X)
   if len(built_cache)>4:built_cache.popitem(last=False)
  built_cache.move_to_end(key)
  return built_cache[key]
 def check_record(record,program,scales,phase):
  nonlocal supplied_calibrations_verified
  I.require(record['phase']==phase and record['refitted'] is False,'phase/no refit')
  built=[build(program,X)for X in scales];ordinary=[v['instance']for v in built];instances=ordinary+([B.auxiliary()['instance']]if phase in ['train','dual']and program['constraint']=='zero_cubic'else[])
  blocks=[v['gram_blocks']for v in built]+([B.auxiliary()['gram_blocks']]if phase in ['train','dual']and program['constraint']=='zero_cubic'else[])
  if 'case_hashes'in record:
   I.require(record['program']==program and record['scales']==scales and record['ordinary_case_hashes']==list(map(I.digest,ordinary)) and record['case_hashes']==list(map(I.digest,instances)) and record['factor_archive_hashes']==[I.digest(v['factor_archive'])for v in built] and record['divisor_archive_hashes']==[I.digest(v['divisor_archive'])for v in built] and record['cell_archive_hashes']==[I.digest(v['cell_archive'])for v in built] and record['dictionary_sha256']==I.digest(SCALAR.descriptors()) and record['gram_block_hashes']==list(map(I.digest,blocks)) and record['gram_archive_hashes']==[I.digest(v['gram_archive'])for v in built] and record['gram_specs']==B.gram_specs(),'complete source/archive/target metadata')
  if phase=='train'and program['claim']=='unsigned_calibration'and record.get('synthesis',{}).get('status')=='finite_PSD_certificate':
   baseline=ROOT/'cancellation-arithmetic-results/divisor-cell-probe-001/jobs/train-001.json'
   result=record['synthesis']
   I.require(record['proposal_origin']=='supplied_archived_unsigned_calibration' and result['calibration_source_sha256']==I.sha(baseline) and result['weights']==I.read(baseline)['synthesis']['weights'],'supplied unchanged archived calibration')
   I.require(result['grams']=={name:[['0']*n for _ in range(n)]for name,n in B.gram_specs().items()},'calibration four zero Grams')
   supplied_calibrations_verified+=1
  if phase=='train'and program['claim']=='critical':
   filename='jobs/train-000-proposal.json';path=d/filename
   saved=I.read(path)if path.is_file()else None;returned=record.get('synthesis',{}).get('proposal_checkpoint')
   if saved is not None:
    I.require(record.get('proposal_checkpoint')==dict(file=filename,sha256=I.sha(path)),'persisted checkpoint receipt binding')
    verify_checkpoint(saved,instances,blocks,B.gram_specs());checkpoints_verified.append(filename)
    if returned is not None:
     core=set(saved)-{'reconstruction_attempts','failure'}
     I.require(all(returned[k]==saved[k]for k in core),'same immutable numerical proposal')
     attempts=saved['reconstruction_attempts'];I.require(returned['reconstruction_attempts'][:len(attempts)]==attempts,'persisted reconstruction attempt prefix')
   else:I.require(returned is None and 'proposal_checkpoint'not in record,'no hidden or dropped numerical checkpoint')
  status=record['status']
  if status in ['finite_PSD_certificate','exact_separator']:I.require('case_hashes'in record,'accepted result needs complete source metadata')
  if status=='finite_PSD_certificate':
   I.require(phase!='dual' and record['synthesis']['status']==status,'finite type')
   G.verify_primal(instances,blocks,B.gram_specs(),record['synthesis'])
   I.require(record['independent_check']['verified'] is True,'accepted independent receipt')
  elif phase=='dual'and record.get('synthesis',{}).get('certified'):
   I.require(status=='exact_separator','certified dual status')
   G.verify_dual(instances,blocks,B.gram_specs(),record['synthesis'])
   I.require(record['independent_check']['verified'] is True,'accepted independent dual receipt')
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
  if record is None and j==0 and (d/'jobs/train-000-proposal.json').is_file():
   built=[build(program,X)for X in [1,2,3,5]];aux=B.auxiliary()
   verify_checkpoint(I.read(d/'jobs/train-000-proposal.json'),[v['instance']for v in built]+[aux['instance']],[v['gram_blocks']for v in built]+[aux['gram_blocks']],B.gram_specs());checkpoints_verified.append('jobs/train-000-proposal.json')
  status=record['status']if record is not None else training['results'][j]['status'];statuses.append(status)
  if status=='finite_PSD_certificate':
   val=training['results'][j]['value'];expected_jobs.extend(dict(phase='final',program=program,X=X,attempt_file=val['file'],attempt_sha256=val['sha256'])for X in [8,13])
  elif program['claim']=='critical':expected_jobs.append(dict(phase='dual',program=program))
 I.require(plan['jobs']==expected_jobs and len(follow['results'])==len(expected_jobs),'complete deterministic followup plan');follow_status=[];transfer_certificates_verified=0
 for j,job in enumerate(expected_jobs):
  record=row(follow['results'][j],job['phase'],j);follow_status.append(record['status']if record is not None else follow['results'][j]['status'])
  if record is None:continue
  check_record(record,job['program'],[job['X']]if job['phase']=='final'else [1,2,3,5],job['phase'])
  if job['phase']=='final'and record['status']=='finite_PSD_certificate':
   attempt=I.read(d/job['attempt_file']);weights=attempt['synthesis']['weights'];I.require(record['synthesis']['weights']==weights and record['weights_sha256']==I.digest(weights) and record['synthesis']['grams']==attempt['synthesis']['grams'] and record['grams_sha256']==I.digest(attempt['synthesis']['grams']),'fixed unchanged weights and Gram matrices')
   transfer_certificates_verified+=1
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
 for v in [protocol,input_value,training,plan,follow,receipt,*loaded_jobs]:flags(v)
 bindings();I.require(start=={n:I.sha(d/n)for n in start},'end input hashes')
 return dict(all_passed=True,input_sha256=start,training_statuses=statuses,followup_statuses=follow_status,actual_truth_after_search=actual,construction_shared_with_calibrated_checker_builder=True,independent_certificate_algebra_verified=True,complete_shared_Gram_sources_verified=True,gram_group_count=len(B.gram_specs()),proposal_checkpoints_verified=checkpoints_verified,supplied_archived_calibrations_verified=supplied_calibrations_verified,transfer_certificates_verified=transfer_certificates_verified,frozen_weights_and_Gram_transfer_verified=transfer_certificates_verified>0,global_bound_proved=False,RH_proved=False)
if __name__=='__main__':
 d=Path(sys.argv[1]);r=audit(d)
 with (d/'independent_verification.json').open('x')as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
 print(json.dumps(r))
