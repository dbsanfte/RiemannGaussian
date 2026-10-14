"""Whole-run integrity and independent exact replay of full14 completion probe."""
import ast
import json
import re
import sys
from pathlib import Path
import check_cancellation_arithmetic_run as H
import check_complete_gram_moment_probe_v2 as M
import check_cancellation_complete_gram_program as B

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
PARENT=BASE/'joint-gram-compressed-replay-001'
TESTS=['test_check_cancellation_complete_gram_program','test_check_complete_gram_moment_probe_v2','test_run_complete_gram_moment_probe_v2','test_check_complete_gram_probe_run_v2']
INPUTS=['cancellation-arithmetic-results/publication-006/manifest.json','cancellation-arithmetic-results/publication-006/report.json','cancellation-arithmetic-results/joint-gram-compressed-replay-001/result.json','cancellation-arithmetic-results/joint-gram-compressed-replay-001/receipt.json','cancellation-arithmetic-results/joint-gram-compressed-replay-001/independent_verification.json','cancellation-arithmetic-results/joint-shared-gram-probe-001/protocol.json']
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=600,max_jobs=1,max_result_bytes=65536)
FLAGS=dict(global_bound_proved=False,RH_proved=False)


INPUTS += ['cancellation-arithmetic-results/complete-gram-moment-probe-001/' + n for n in ['protocol.json','result.json','receipt.json','independent_verification.json']]


def source_names():
 pending=['run_complete_gram_moment_probe_v2','check_complete_gram_probe_run_v2',*TESTS];seen=set()
 while pending:
  name=pending.pop();p=ROOT/(name+'.py')
  if name in seen or not p.is_file():continue
  seen.add(name)
  for node in ast.walk(ast.parse(p.read_text())):
   if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
   elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
 return sorted(n+'.py'for n in seen)


def finite_flags(value):
 if isinstance(value,dict):
  for k,v in value.items():
   if k in ('global_bound_proved','RH_proved','larger_cone_feasibility_proved'):H.require(v is False,'diagnostic scope promotion')
   finite_flags(v)
 elif isinstance(value,list):
  for v in value:finite_flags(v)


def verify_probe(observed,expected):
 H.require(H.digest(observed)==H.digest(expected),'complete independent moment replay')
 H.require(observed['larger_cone_feasibility_proved']is False and set(observed['regions'])==set(B.gram_specs()),'both complete regional outcomes')
 outcomes={};missing=0
 for name,n in B.gram_specs().items():
  row=observed['regions'][name];status=row['status'];outcomes[name]=status
  H.require(status in ['unknown_missing_coordinates','PSD_extension','witness_invalid_for_complete_cone'],'explicit moment admission state')
  if status=='unknown_missing_coordinates':
   H.require(row['missing'] and 'matrix'not in row and 'PSD_proof'not in row,'missing coordinates not zero-extended')
   missing+=len(row['missing'])
  else:
   H.require(row['missing']==[] and len(row['matrix'])==n and all(len(r)==n for r in row['matrix']),'complete supported matrix')
   if status=='PSD_extension':M.I.verify_psd(row['matrix'])
   else:H.require(row['full_polynomial_matching_verified']is True and M.F(row['quadratic_value'])<0 and row['quadratic_value']==row['full_square_polynomial_dot'],'negative direction full polynomial admission')
 finite_flags(observed)
 return dict(region_statuses=outcomes,missing_coordinate_occurrences=missing,independent_full_moment_replay_passed=True)


def verify_execution(execution,record,result_hash):
 cost=execution['cost'];expected=dict(workers=1,requested_workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False)
 for k,v in expected.items():H.require(type(cost.get(k))is type(v) and cost[k]==v,'actual isolated resource profile '+k)
 rows=execution['results'];H.require(type(rows)is list and len(rows)==1 and rows[0]['index']==0 and rows[0]['status']in ['available','missing_resource','error'],'one ordered process receipt')
 row=rows[0]
 if row['status']!='available':
  H.require(record is None and 'value'not in row,'process failure retained without result');return dict(process_status=row['status'],record_status=None)
 H.require(record is not None,'available process result exists');value=row['value']
 H.require(value['file']=='result.json'and value['sha256']==result_hash and value['status']==record['status']and value['cost']==record['cost'],'result hash/status/cost execution binding')
 finite_flags(execution);finite_flags(record)
 return dict(process_status='available',record_status=record['status'])


def audit(directory):
 d=Path(directory).resolve();names=['protocol.json','source_seal.json','input.json','seal.json','tests.json','execution.json','receipt.json']
 if(d/'result.json').is_file():names.append('result.json')
 start={n:H.sha(d/n)for n in names};protocol=H.read(d/'protocol.json');source=H.read(d/'source_seal.json');inputs=H.read(d/'input.json');receipt=H.read(d/'receipt.json')
 def bindings():
  H.require(set(source)==set(source_names()),'complete executed probe closure')
  H.require(H.read(d/'seal.json')==dict(protocol_sha256=H.sha(d/'protocol.json'),source_seal_sha256=H.sha(d/'source_seal.json'),input_sha256=H.sha(d/'input.json')),'protocol/source/input seal')
  for n,h in source.items():H.require(H.sha(ROOT/n)==h and H.sha(d/'frozen_source'/n)==h,'frozen source '+n)
  H.require(set(inputs['input_sha256'])==set(INPUTS),'all prior evidence inputs')
  for n,h in inputs['input_sha256'].items():H.require(H.sha(ROOT/n)==h,'prior bound evidence '+n)
  manifest=H.read(BASE/'publication-006/manifest.json');H.require(len(manifest['files'])==319,'publication006 count')
  for n,h in manifest['files'].items():H.require(H.sha(ROOT/n)==h,'immutable published evidence '+n)
  prior=H.read(PARENT/'independent_verification.json');H.require(prior['all_passed']is True,'admitted prior exact separator')
  for n,h in prior['input_sha256'].items():H.require(H.sha(PARENT/n)==h,'original independent admission '+n)
 bindings();original=H.read(PARENT/'result.json')
 H.require(original['status']=='exact_separator'and original['synthesis']['certified']is True,'exact original witness')
 H.require(protocol['schema']==1 and protocol['program']==original['program']and protocol['scales']==original['scales']==[1,2,3,5]and protocol['language']==B.SPEC and protocol['gram_specs']==B.gram_specs()and protocol['gram_groups']==B.group_descriptors(),'complete frozen fourteen atom program')
 H.require(protocol['tests']==TESTS and protocol['parallel']==PARALLEL and protocol['no_new_float_search']is True and protocol['numerical_response_inputs']is False and protocol['missing_policy']=='unknown; no implicit zero moments','preregistered exact diagnostic/resource contract')
 finite_flags(protocol);tests=H.read(d/'tests.json');match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests['stdout']+tests['stderr']);H.require(tests['returncode']==0 and match is not None,'prescore exact calibrations')
 record=H.read(d/'result.json')if(d/'result.json').is_file()else None
 process=verify_execution(H.read(d/'execution.json'),record,H.sha(d/'result.json')if record is not None else None)
 outcomes=dict(region_statuses={},missing_coordinate_occurrences=None,independent_full_moment_replay_passed=False)
 if record is not None:
  H.require(record['no_new_float_search']is True,'no new optimizer')
  if record['status']=='complete':
   expected=M.audit_existing_separator(protocol['program'],protocol['scales'],original['synthesis'])
   outcomes=verify_probe(record['probe'],expected)
  else:H.require(record['status']in ['missing_resource','rejected']and 'probe'not in record,'explicit diagnostic failure retained')
 files={str(p.relative_to(d)):H.sha(p)for p in d.rglob('*.json')if p.name not in ['receipt.json','independent_verification.json']}
 H.require(receipt['files_sha256']==files and receipt['source_count']==len(source),'complete terminal artifact receipt')
 finite_flags(receipt);bindings();H.require(start=={n:H.sha(d/n)for n in start},'end input hash replay')
 return dict(all_passed=True,input_sha256=start,source_count=len(source),tests_passed=int(match.group(1)),original_dual_sha256=H.sha(PARENT/'result.json'),protocol_and_all_prior_bindings_verified=True,actual_6GiB_single_worker_receipts_verified=True,**process,**outcomes,**FLAGS)


if __name__=='__main__':
 d=Path(sys.argv[1]);result=audit(d)
 with(d/'independent_verification.json').open('x')as f:json.dump(result,f,sort_keys=True,indent=2,allow_nan=False);f.write('\n')
 print(json.dumps(result))
