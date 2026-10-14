"""Publication006 loader: only explicit publish writes a publication archive."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
FLAGS=dict(global_bound_proved=False,RH_proved=False)


def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v):
 with p.open('x')as f:json.dump(v,f,sort_keys=True,indent=2,allow_nan=False);f.write('\n')
def require(condition,message):
 if not condition:raise ValueError(message)
def manifest(path,expected):
 m=read(path);require(len(m['files'])==expected,'prior manifest file count')
 for n,h in m['files'].items():require(sha(ROOT/n)==h,'prior file changed '+n)
 return m


def load_inputs():
 import check_joint_gram_search as C
 d=BASE/'joint-shared-gram-probe-001';old=BASE/'publication-005';resource=ROOT/'detector-performance-results/publication-001'
 for path,count in [(old/'manifest.json',263),(BASE/'publication-004/manifest.json',343),(BASE/'publication-003/manifest.json',259),(resource/'manifest.json',244)]:manifest(path,count)
 review=read(d/'independent_verification.json');require(review.get('all_passed')is True,'whole-run independent admission required')
 for n,h in review['input_sha256'].items():require(sha(d/n)==h,'independent receipt input '+n)
 require(read(d/'seal.json')==dict(protocol_sha256=sha(d/'protocol.json'),source_seal_sha256=sha(d/'source_seal.json'),input_sha256=sha(d/'input.json')),'stage protocol/source/input seal')
 for n,h in read(d/'input.json')['input_sha256'].items():require(sha(ROOT/n)==h,'stage bound prior input '+n)
 source=read(d/'source_seal.json');require(set(source)==set(C.source_names()),'complete frozen executed closure')
 for n,h in source.items():require(sha(ROOT/n)==h and sha(d/'frozen_source'/n)==h,'root/frozen source binding '+n)
 protocol=read(d/'protocol.json')
 require(protocol['language']==C.B.SPEC and protocol['gram_specs']==C.B.gram_specs() and protocol['gram_groups']==C.B.group_descriptors() and protocol['dictionary']==C.SCALAR.descriptors(),'known complete joint grammar')
 require(protocol['programs']==C.PROGRAMS and protocol['training_scales']==[1,2,3,5] and protocol['final_scales']==[8,13] and protocol['limits']==C.LIMITS and protocol['solver_limits']==C.SOLVER_LIMITS and protocol['dual_limits']==C.DUAL_LIMITS and protocol['tests']==C.TESTS,'known programs/grid/resources')
 require(protocol['final_refit']is False and protocol['no_actual_signed_response_inputs']is True and len(protocol['gram_specs'])==4 and sorted(protocol['gram_specs'].values())==[5,5,10,10],'four full shared matrices/no refit')
 tests=read(d/'tests.json');match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests['stdout']+tests['stderr']);require(tests['returncode']==0 and match is not None,'frozen prescore calibrations')
 receipt=read(d/'receipt.json')
 files={str(p.relative_to(d)):sha(p)for p in d.rglob('*.json')if p.name not in ['receipt.json','independent_verification.json']}
 require(receipt['files_sha256']==files and receipt['source_count']==len(source) and receipt['refitted']is False,'complete terminal artifact closure')
 records=[]
 for p in sorted((d/'jobs').glob('*.json')):
  if p.name.endswith('-proposal.json'):continue
  record=read(p);require(record['phase']in ['train','dual','final'] and record['refitted']is False,'retained known job state')
  if record['status']in ['finite_PSD_certificate','exact_separator']:require(record['independent_check']['verified']is True,'accepted independent job check')
  records.append((p,record))
 require(any(r['phase']=='final'and r['status']=='finite_PSD_certificate'and r.get('scales')==[8]and r.get('program',{}).get('claim')=='unsigned_calibration'for _,r in records),'original unsigned X8 exact transfer')
 require(any(r['phase']=='final'and r['status']=='missing_resource'and r.get('scales')==[13]and r.get('reason')=='MemoryError'for _,r in records),'original X13 memory failure retained')
 require(review['gram_group_count']==4 and review['complete_shared_Gram_sources_verified']is True,'whole grammar replay admission')
 finals=sum(r['phase']=='final'and r['status']=='finite_PSD_certificate'for _,r in records)
 require(review['transfer_certificates_verified']==finals and review['frozen_weights_and_Gram_transfer_verified']is(finals>0),'accurate accepted transfer count')
 checkpoints=[]
 for n in review['proposal_checkpoints_verified']:
  p=d/n;require(p.is_file(),'verified checkpoint artifact');cp=read(p)
  require(cp['proposal_only']is True and cp['certified']is False,'checkpoint not certificate')
  checkpoints.append(dict(file=n,sha256=sha(p),bytes=p.stat().st_size,monomials=len(cp['monomials']),columns=len(cp['column_layout']),active_support=len(cp['active_support']),solver_status=cp['solver_status'],float_objective=cp['float_objective'],row_order_sha256=cp['row_order_hash'],exact_columns_sha256=cp['exact_columns_hash']))
 require((ROOT/'joint_gram_scalar_scope.txt').is_file(),'scalar scope handoff evidence')
 compressed=BASE/'joint-gram-compressed-replay-001'
 import run_joint_gram_compressed_replay as K
 K.validate(compressed)
 cr=read(compressed/'independent_verification.json');require(cr.get('all_passed')is True,'compressed independent replay admission')
 for n,h in cr['input_sha256'].items():require(sha(compressed/n)==h,'compressed independent input '+n)
 cs=read(compressed/'source_seal.json');require(set(cs)==set(K.sources()),'complete compressed executed closure')
 for n,h in cs.items():require(sha(ROOT/n)==h and sha(compressed/'frozen_source'/n)==h,'compressed frozen source '+n)
 terminal=read(compressed/'receipt.json')
 for n,h in terminal['files_sha256'].items():require(sha(compressed/n)==h,'compressed terminal artifact '+n)
 require(terminal['source_count']==len(cs),'compressed terminal source count')
 cp=read(compressed/'protocol.json');ct=read(compressed/'tests.json');testmatch=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',ct['stdout']+ct['stderr'])
 require(ct['returncode']==0 and testmatch is not None and int(testmatch.group(1))==15,'15 frozen compression calibrations')
 require(cp['limits']==K.LIMITS and cp['limits']['max_work']==450000000 and cp['prepare_limits']==K.PREPARE_LIMITS and cp['parallel']==K.PARALLEL and cp['no_new_float_search']is True and cp['same_cone']is True,'same450m compressed protocol')
 recovered=read(compressed/'result.json');rd=recovered['synthesis'];saved=read(compressed/'support.json')['indices'];failed=read(d/'jobs/dual-000.json')
 require(saved==failed['synthesis']['proposal_diagnostics']['support']==rd['saved_support'] and len(saved)==632,'same632 saved support')
 require(recovered['status']=='exact_separator' and rd['certified']is True and cr['same_support_verified']is True and cr['unchanged_450m_gate_verified']is True and cr['original_solution']['all_original_equations_verified']is True and cr['full_Gram_dual_check']['verified']is True,'exact compression/equivalence/full-cone independent admission')
 require(recovered['case_hashes']==failed['case_hashes'] and recovered['gram_block_hashes']==failed['gram_block_hashes'] and recovered['gram_archive_hashes']==failed['gram_archive_hashes'],'identical compressed retry cone')
 compression=rd['diagnostics']['row_compression'];require(compression['original_rows']==1296 and compression['original_work_proxy']==1296*632**2==517653504 and compression['total_work_proxy']<=450000000 and cr['compression']['total_work_proxy']==compression['total_work_proxy'],'raw versus compressed charged work')
 require(rd['constant_coordinates']==['0']*5 and rd['lhs_dot_y']=='-1','compressed scalar-budget scope')
 memory=BASE/'joint-gram-transfer-memory-retry-001'
 import run_joint_gram_transfer_retry as M
 M.validate(memory)
 mr=read(memory/'independent_verification.json');require(mr.get('all_passed')is True,'memory-only transfer independent admission')
 for n,h in mr['input_sha256'].items():require(sha(memory/n)==h,'memory retry independent input '+n)
 msource=read(memory/'source_seal.json');require(set(msource)==set(M.sources()),'complete memory retry source closure')
 for n,h in msource.items():require(sha(ROOT/n)==h and sha(memory/'frozen_source'/n)==h,'memory retry frozen source '+n)
 mt=read(memory/'receipt.json')
 for n,h in mt['files_sha256'].items():require(sha(memory/n)==h,'memory retry terminal artifact '+n)
 require(mt['source_count']==len(msource),'memory retry source count')
 mp=read(memory/'protocol.json');memory_result=read(memory/'result.json');ms=memory_result['synthesis'];candidate=read(memory/'candidate.json')
 runtime=read(memory/'execution.json')['cost'];require(runtime['workers']==1 and runtime['worker_memory_bytes']==6*1024**3 and runtime['memory_budget_bytes']==6*1024**3 and runtime['worker_memory_limit_enforced']is True,'runtime enforced6GiB singleton policy')
 require(mp['parallel']==M.PARALLEL and mp['parallel']['workers']==1 and mp['parallel']['worker_memory_bytes']==6*1024**3 and mp['parallel']['memory_budget_bytes']==6*1024**3 and mp['limits']==protocol['limits'],'authorized memory-only retry resources')
 require(memory_result['status']=='finite_PSD_certificate' and memory_result['scales']==[13] and memory_result['refitted']is False and ms['weights']==candidate['weights'] and ms['grams']==candidate['grams'] and mr['transfer']['fixed_training_weights_verified']is True and mr['transfer']['four_zero_Grams_verified']is True and mr['resources']['one_worker_6GiB_verified']is True,'fixed candidate exact X13 retry')
 mtests=read(memory/'tests.json');mmatch=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',mtests['stdout']+mtests['stderr']);require(mtests['returncode']==0 and mmatch is not None,'memory retry prescore calibrations')
 return dict(directory=d,old=old,resource=resource,review=review,records=records,source=source,tests_passed=int(match.group(1)),checkpoints=checkpoints,compressed=compressed,compressed_review=cr,compressed_result=recovered,compressed_sources=cs,compression=compression,memory=memory,memory_result=memory_result,memory_review=mr,memory_sources=msource,memory_tests_passed=int(mmatch.group(1)))


def outcome_report(inputs):
 jobs=[]
 for path,r in inputs['records']:
  s=r.get('synthesis',{});entry=dict(file=str(path.relative_to(inputs['directory'])),sha256=sha(path),phase=r['phase'],status=r['status'],reason=s.get('reason',r.get('reason')),cost=r['cost'])
  if r.get('proposal_origin'):entry['proposal_origin']=r['proposal_origin']
  if s.get('weights'):entry['weights_sha256']=hashlib.sha256(json.dumps(s['weights'],sort_keys=True,separators=(',',':')).encode()).hexdigest()
  if s.get('grams'):entry['nonzero_Gram_matrices']=sum(any(v!='0'for row in matrix for v in row)for matrix in s['grams'].values())
  if s.get('constant_coordinates')is not None:entry['constant_coordinates']=s['constant_coordinates']
  if s.get('saved_support')is not None:entry['saved_support_size']=len(s['saved_support'])
  jobs.append(entry)
 critical=[r for _,r in inputs['records']if r.get('program',{}).get('claim')=='critical']
 critical_accepted=any(r['status']=='finite_PSD_certificate'for r in critical)
 raw_separator=any(r['status']=='exact_separator'for r in critical)
 separator=raw_separator or inputs['compressed_result']['status']=='exact_separator'
 if critical_accepted:next_action='prove accepted full templates and charged scalar budgets uniformly; retain finite scope until such a proof is independently verified'
 elif separator:next_action='preregister coherent full14atom regional Grams mixing all five legacy atoms and all nine complete divisor contrasts; inspect the admitted witness against that larger cone without claiming feasibility or an actual bound'
 else:next_action='inspect retained numerical checkpoints and deterministic resource requirements, then preregister a bounded same-proposal retry or a new complete arithmetic grammar'
 return dict(schema=6,prior_research_publication='publication-005',previous_research_manifest_sha256=sha(inputs['old']/'manifest.json'),previous_research_bound_files=263,previous_resource_manifest_sha256=sha(inputs['resource']/'manifest.json'),previous_resource_bound_files=244,
  independent_receipt_sha256=sha(inputs['directory']/'independent_verification.json'),tests_passed=inputs['tests_passed'],source_count=len(inputs['source']),training_statuses=inputs['review']['training_statuses'],followup_statuses=inputs['review']['followup_statuses'],
  gram_group_dimensions=dict(joint_parent=10,joint_child=10,old_parent=5,old_child=5),complete_original_defect_and_all_channels_preserved=True,
  supplied_archived_calibrations_verified=inputs['review']['supplied_archived_calibrations_verified'],supplied_calibration_is_discovery=False,transfer_certificates_verified=inputs['review']['transfer_certificates_verified'],historical_transfer_scales_reused=True,
  compressed_recovery=dict(status=inputs['compressed_result']['status'],result_sha256=sha(inputs['compressed']/'result.json'),independent_receipt_sha256=sha(inputs['compressed']/'independent_verification.json'),source_count=len(inputs['compressed_sources']),tests_passed=15,same_saved_support_count=632,new_floating_search=False,higher_resource_ceiling=False,unchanged_work_ceiling=450000000,original_rows=inputs['compression']['original_rows'],reduced_rows=inputs['compression']['reduced_rows'],full_equation_rows=1318,full_system_work_upper_proxy=526440832,actual_selected_support_raw_work_proxy=517653504,native_work_proxy=inputs['compression']['native_work_proxy'],preprocessing_work=inputs['compression']['preprocessing_work'],total_work_proxy=inputs['compression']['total_work_proxy'],all_original_equations_independently_verified=True,constant_coordinates=['0']*5,scope='arbitrary scalar budget shifts in the exact fixed four-group shared gamma-zero cone; no actual bound refutation'),
  memory_transfer_recovery=dict(result_sha256=sha(inputs['memory']/'result.json'),independent_receipt_sha256=sha(inputs['memory']/'independent_verification.json'),status=inputs['memory_result']['status'],cost=inputs['memory_result']['cost'],X=13,source_count=len(inputs['memory_sources']),tests_passed=inputs['memory_tests_passed'],same_fixed_weights_and_four_zero_Grams=True,new_floating_search=False,refitted=False,worker_memory_bytes=6*1024**3,total_memory_bytes=6*1024**3,workers=1,original_2GiB_MemoryError_preserved=True),
  admitted_unsigned_transfer_scales_across_separate_archives=[8,13],original_stage_transfer_count=inputs['review']['transfer_certificates_verified'],separate_memory_retry_transfer_count=1,future_memory_policy=dict(worker_memory_bytes=6*1024**3,total_concurrent_memory_bytes=6*1024**3,full_memory_workers=1,authorization_persists=True,old_frozen_resources_preserved=True),
  proposal_checkpoints=inputs['checkpoints'],proposal_checkpoints_are_certificates=False,all_missing_failed_and_accepted_states_preserved=True,jobs=jobs,
  scope='finite complete joint-divisor shared proof cone with supplied calibration and exact admission; gamma-zero necessity uses the recorded q>1 fixed-template scalar asymptotic assumptions; no actual all-scale bound',
  scalar_scope_sha256=sha(ROOT/'joint_gram_scalar_scope.txt'),critical_finite_certificate_found=critical_accepted,joint_exact_separator_found=separator,raw_stage_exact_separator_found=raw_separator,next_action=next_action,**FLAGS)


def publish():
 inputs=load_inputs();out=BASE/'publication-006';require(not out.exists(),'exclusive publication006')
 notes=['publish_cancellation_joint_gram.py','JOINT_GRAM_SEARCH_HANDOFF.txt','joint_gram_scalar_scope.txt']
 files={ROOT/n for n in notes};d=inputs['directory'];files.update(p for p in d.rglob('*')if p.is_file()and '__pycache__'not in p.parts);files.update(ROOT/n for n in inputs['source'])
 compressed=inputs['compressed'];files.update(p for p in compressed.rglob('*')if p.is_file()and '__pycache__'not in p.parts);files.update(ROOT/n for n in inputs['compressed_sources'])
 memory=inputs['memory'];files.update(p for p in memory.rglob('*')if p.is_file()and '__pycache__'not in p.parts);files.update(ROOT/n for n in inputs['memory_sources'])
 for key in ['old','resource']:files.update([inputs[key]/'manifest.json',inputs[key]/'report.json'])
 hashes={str(p.relative_to(ROOT)):sha(p)for p in sorted(files)};report=outcome_report(inputs)
 out.mkdir();(out/'frozen_source').mkdir()
 for n in ['publish_cancellation_joint_gram.py']:
  p=out/'frozen_source'/n;p.write_bytes((ROOT/n).read_bytes());hashes[str(p.relative_to(ROOT))]=sha(p)
 for n in ['JOINT_GRAM_SEARCH_HANDOFF.txt','joint_gram_scalar_scope.txt']:
  p=out/n;p.write_bytes((ROOT/n).read_bytes());hashes[str(p.relative_to(ROOT))]=sha(p)
 write(out/'report.json',report);hashes[str((out/'report.json').relative_to(ROOT))]=sha(out/'report.json')
 write(out/'manifest.json',dict(schema=1,files=hashes,**FLAGS));manifest(out/'manifest.json',len(hashes))
 load_inputs();manifest(out/'manifest.json',len(hashes))
 pointer=dict(publication='publication-006',report_sha256=sha(out/'report.json'),manifest_sha256=sha(out/'manifest.json'),**FLAGS)
 write(BASE/'latest-006.tmp',pointer);(BASE/'latest-006.tmp').replace(BASE/'latest.json')
 return dict(publication='publication-006',bound_files=len(hashes),**FLAGS)


if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('action',choices=['validate','publish']);args=parser.parse_args()
 if args.action=='publish':print(json.dumps(publish()))
 else:print(json.dumps(dict(all_passed=True,publication_written=False,report=outcome_report(load_inputs()))))
