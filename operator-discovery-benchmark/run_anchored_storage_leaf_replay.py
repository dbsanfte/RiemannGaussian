"""Frozen same-support native reconstruction retry; no new LP or SDP search."""
import argparse
import ast
import json
import os
import resource
import subprocess
import sys
import time
from fractions import Fraction as F
from pathlib import Path
import run_detector as R
from detector_parallel import run_jobs
from detector_workflow_guard import require_verified_runtime
import check_cancellation_anchored_storage as B
import cancellation_anchored_storage_synthesis as S
import cancellation_anchored_storage_dual as D
import native_exact_support_leaf as N
import check_cancellation_shared_gram as I

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'cancellation-arithmetic-results/anchored-storage-search-001'
FLAGS=dict(global_bound_proved=False,RH_proved=False)
LIMITS=dict(time_limit=360,max_rows=2500,max_variables=60000,max_work=450000000,
 max_cells=4000000,max_preprocessing_operations=200000000,max_preprocessing_cells=4000000,max_denominator=2**4096,max_coefficient_bits=4096,max_receipt_bytes=8388608)
PREPARE_LIMITS=dict(max_columns=2048,max_monomials=100000,max_operations=200000000,
 max_coefficient_bits=4096,max_horizon=80,max_degree=12)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,
 timeout_seconds=1200,max_jobs=1,max_result_bytes=65536)


def sources():
 pending=['run_anchored_storage_leaf_replay','test_anchored_storage_leaf_replay','check_anchored_storage_leaf_replay','test_check_anchored_storage_leaf_replay','test_native_exact_support_leaf','test_check_native_exact_support_leaf'];seen=set()
 while pending:
  name=pending.pop();p=ROOT/(name+'.py')
  if name in seen or not p.is_file():continue
  seen.add(name)
  for node in ast.walk(ast.parse(p.read_text())):
   if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
   elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
 return sorted(n+'.py'for n in seen)


def parent_bindings():
 source=R.read(PARENT/'source_seal.json')
 for n,h in source.items():
  if R.sha(ROOT/n)!=h or R.sha(PARENT/'frozen_source'/n)!=h:raise ValueError('frozen parent source '+n)
 for n,h in R.read(PARENT/'receipt.json')['files_sha256'].items():
  if R.sha(PARENT/n)!=h:raise ValueError('parent terminal artifact '+n)
 review=R.read(PARENT/'independent_verification.json')
 if review.get('all_passed')is not True:raise ValueError('independent parent admission')
 for n,h in review['input_sha256'].items():
  if R.sha(PARENT/n)!=h:raise ValueError('parent audit binding '+n)


def freeze(directory):
 require_verified_runtime();parent_bindings()
 original=R.read(PARENT/'jobs/dual-000.json')
 checkpoint=R.read(PARENT/'jobs/dual-000-proposal.json');indices=checkpoint['support']
 if original['status']!='missing_resource' or original['synthesis']['reason']!='total charged anchored reconstruction work cap' or len(indices)!=703:
  raise ValueError('exact declared failed support required')
 protocol=dict(schema=1,program=original['program'],scales=original['scales'],gram_specs=B.gram_specs(),
  limits=LIMITS,prepare_limits=PREPARE_LIMITS,parallel=PARALLEL,
  support_count=703,tests=['test_anchored_storage_leaf_replay','test_check_anchored_storage_leaf_replay','test_native_exact_support_leaf','test_check_native_exact_support_leaf'],no_new_float_search=True,same_cone=True,
  conditioning='same complete 703 support and equations; exact singleton-column elimination and back-substitution, then proportional augmented-row compression; unchanged 450-million total work proxy cap',**FLAGS)
 inputs={str(p.relative_to(ROOT)):R.sha(p)for p in [PARENT/'jobs/dual-000.json',PARENT/'jobs/dual-000-proposal.json',PARENT/'protocol.json',PARENT/'source_seal.json',PARENT/'receipt.json',PARENT/'independent_verification.json']}
 inputs['anchored_storage_resource_authorization.txt']=R.sha(ROOT/'anchored_storage_resource_authorization.txt')
 d=Path(directory).resolve();d.mkdir(parents=True,exist_ok=False);(d/'frozen_source').mkdir()
 hashes={}
 for n in sources():
  (d/'frozen_source'/n).write_bytes((ROOT/n).read_bytes());hashes[n]=R.sha(ROOT/n)
 test=subprocess.run([sys.executable,'-B','-m','unittest',*protocol['tests']],cwd=ROOT,capture_output=True,text=True,timeout=120)
 if test.returncode:raise ValueError('saved-support calibration failed')
 R.write(d/'tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr))
 R.write(d/'protocol.json',protocol);R.write(d/'source_seal.json',hashes);R.write(d/'input.json',dict(input_sha256=inputs))
 R.write(d/'support.json',dict(indices=indices,original_dual_sha256=R.sha(PARENT/'jobs/dual-000.json'),proposal_sha256=R.sha(PARENT/'jobs/dual-000-proposal.json')))
 R.write(d/'seal.json',dict(protocol_sha256=R.sha(d/'protocol.json'),source_seal_sha256=R.sha(d/'source_seal.json'),input_sha256=R.sha(d/'input.json'),support_sha256=R.sha(d/'support.json')))
 return d


def validate(directory):
 d=Path(directory);seal=R.read(d/'seal.json')
 for n in ['protocol','source_seal','input','support']:
  if seal[n+'_sha256']!=R.sha(d/(n+'.json')):raise ValueError('replay seal changed '+n)
 source=R.read(d/'source_seal.json')
 if set(source)!=set(sources()):raise ValueError('complete replay source closure')
 for n,h in source.items():
  if R.sha(ROOT/n)!=h or R.sha(d/'frozen_source'/n)!=h:raise ValueError('replay source changed '+n)
 for n,h in R.read(d/'input.json')['input_sha256'].items():
  if R.sha(ROOT/n)!=h:raise ValueError('original input changed '+n)
 parent_bindings()
 support=R.read(d/'support.json');original=R.read(PARENT/'jobs/dual-000.json')
 if support!=dict(indices=R.read(PARENT/'jobs/dual-000-proposal.json')['support'],original_dual_sha256=R.sha(PARENT/'jobs/dual-000.json'),proposal_sha256=R.sha(PARENT/'jobs/dual-000-proposal.json')):raise ValueError('same saved support only')


def replay(instances,blocks,storage,specs,support,on_checkpoint=None):
 start=time.monotonic();deadline=start+360
 columns,lhs,ms,shape,offset,_,prepared_specs=S.prepare(instances,blocks,storage,gram_specs=specs,deadline=deadline,**PREPARE_LIMITS)
 nonnegative,relations,layout=D.classify(columns,shape,offset,prepared_specs)
 restricted,rnn,rrr,keep,redundancy=D.restricted_columns(columns,offset,nonnegative,relations,layout)
 compilation=S.compilation_charge(instances,blocks,columns)+sum(map(len,columns))+1
 result=N.reconstruct_dual_fixed_support(restricted,lhs,ms,rnn,rrr,support,
  compilation_work_reserve=compilation,on_checkpoint=on_checkpoint,**dict(LIMITS,time_limit=max(0.001,deadline-time.monotonic())))
 result['saved_support_sha256']=R.digest(support)
 if not result.get('certified'):return result
 y=dict(zip(ms,map(F,result['weights'])));grams={}
 for name,n,entries in layout:
  matrix=[[F(0)for _ in range(n)]for _ in range(n)]
  for pos,a,b in entries:
   value=sum((F(q)*y[m]for m,q in columns[pos].items()),F(0))
   if a!=b and value:raise ValueError('restricted cross moment nonzero')
   if a==b and value<0:raise ValueError('negative diagonal')
   matrix[a][b]=matrix[b][a]=value if a==b else value/2
  matrix=[[str(q)for q in row]for row in matrix]
  grams[name]=dict(matrix=matrix,PSD_certificate=I.verify_psd(matrix))
 restricted_dots=result['columns_dot_y'];dots=[str(sum((q*y[m] for m,q in col.items()),F(0))) for col in columns]
 if [dots[i] for i in keep]!=restricted_dots:raise ValueError('same full/restricted dual dots')
 constants=[str(y.get((k,),F(0)))for k in range(len(instances))]
 result.update(monomials=[dict(instance=m[0],m=list(m[1:]))for m in ms],columns_dot_y=dots[:offset],
  gram_columns_dot_y=dots[offset:],gram_duals=grams,gram_specs=specs,
  source_hashes=list(map(R.digest,instances)),gram_block_hashes=list(map(R.digest,blocks)),storage_block_hashes=list(map(R.digest,storage)),grammar_hash=R.digest(B.SPEC),
  restricted_columns_dot_y=restricted_dots,restricted_column_indices=keep,storage_cross_redundancy=redundancy,
  constant_coordinates=constants,all_C_q_extension_requires_zero_constant_coordinates=all(F(q)==0 for q in constants),
  restricted_dual_search='same saved support; all offdiagonal moments zero',**FLAGS)
 result['independent_check']=B.verify_dual(instances,blocks,storage,specs,result)
 result['independent_full_Gram_check_passed']=True
 result['diagnostics']['elapsed_total_seconds']=time.monotonic()-start
 if time.monotonic()>deadline:raise TimeoutError('compressed replay independent verification deadline')
 return result


def worker(job):
 require_verified_runtime();d=Path(job['directory']);validate(d)
 if (d/'result.json').exists():raise FileExistsError('exclusive replay result')
 spec=R.read(d/'protocol.json');original=R.read(PARENT/'jobs/dual-000.json');start=time.monotonic();cpu=time.process_time()
 built=[B.build(spec['program'],X)for X in spec['scales']]
 instances=[b['instance']for b in built];blocks=[b['gram_blocks']for b in built];storage=[b['storage_blocks'] for b in built]
 if spec['program']['constraint']=='zero_cubic':
  aux=B.auxiliary();instances.append(aux['instance']);blocks.append(aux['gram_blocks']);storage.append(aux['storage_blocks'])
 metadata=dict(case_hashes=list(map(R.digest,instances)),gram_block_hashes=list(map(R.digest,blocks)),storage_block_hashes=list(map(R.digest,storage)),
  gram_archive_hashes=[R.digest(b['gram_archive'])for b in built])
 for key,value in metadata.items():
  if value!=original[key]:raise ValueError('same cone '+key)
 checkpoint={}
 def save_checkpoint(value):
  path=d/'leaf-checkpoint.json';temporary=d/'leaf-checkpoint.tmp'
  R.write(temporary,value);os.replace(temporary,path)
  checkpoint.update(file=path.name,sha256=R.sha(path))
 result=replay(instances,blocks,storage,spec['gram_specs'],R.read(d/'support.json')['indices'],save_checkpoint)
 output=dict(status=result['status'],synthesis=result,program=spec['program'],scales=spec['scales'],
  gram_specs=spec['gram_specs'],no_new_float_search=True,same_cone=True,**metadata,**FLAGS)
 if checkpoint:output['leaf_checkpoint']=checkpoint
 output['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,
  peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,pid=os.getpid(),
  observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())))
 validate(d);R.write(d/'result.json',output)
 return dict(file='result.json',sha256=R.sha(d/'result.json'),status=output['status'],cost=output['cost'],**FLAGS)


def run(directory):
 require_verified_runtime();d=Path(directory).resolve();validate(d)
 if (d/'execution.json').exists():raise FileExistsError('replay already run')
 execution=run_jobs([dict(directory=str(d))],worker='run_anchored_storage_leaf_replay:worker',**PARALLEL)
 R.write(d/'execution.json',execution);validate(d)
 R.write(d/'receipt.json',dict(files_sha256={str(p.relative_to(d)):R.sha(p)for p in sorted(d.rglob('*.json'))},source_count=len(R.read(d/'source_seal.json')),no_new_float_search=True,**FLAGS))
 print(json.dumps(dict(process_status=execution['results'][0]['status'],result=execution['results'][0].get('value'))))


if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');args=parser.parse_args()
 (freeze if args.command=='freeze'else run)(args.directory)
