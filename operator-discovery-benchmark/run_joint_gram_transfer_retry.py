"""Memory-only retry of the unchanged X13 unsigned shared-Gram certificate."""
import argparse,ast,json,os,resource,subprocess,sys,time
from pathlib import Path
import run_detector as R
from detector_parallel import run_jobs
from detector_workflow_guard import require_verified_runtime
import check_cancellation_joint_gram_program as B
from cancellation_shared_gram_synthesis_v2 import instantiate_certificate
import check_cancellation_shared_gram as I

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'cancellation-arithmetic-results/joint-shared-gram-probe-001'
FLAGS=dict(global_bound_proved=False,RH_proved=False)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=600,max_jobs=1,max_result_bytes=65536)
TESTS=['test_joint_gram_transfer_retry','test_check_joint_gram_transfer_retry']
METADATA_KEYS=['ordinary_case_hashes','case_hashes','factor_archive_hashes','divisor_archive_hashes','cell_archive_hashes','gram_archive_hashes','gram_block_hashes','dictionary_sha256','gram_specs']

def sources():
 pending=['run_joint_gram_transfer_retry','check_joint_gram_transfer_retry',*TESTS];seen=set()
 while pending:
  name=pending.pop();p=ROOT/(name+'.py')
  if name in seen or not p.is_file():continue
  seen.add(name)
  for node in ast.walk(ast.parse(p.read_text())):
   if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
   elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
 return sorted(n+'.py'for n in seen)

def parent_bindings():
 for n,h in R.read(PARENT/'source_seal.json').items():
  if R.sha(ROOT/n)!=h or R.sha(PARENT/'frozen_source'/n)!=h:raise ValueError('frozen parent source '+n)
 for n,h in R.read(PARENT/'receipt.json')['files_sha256'].items():
  if R.sha(PARENT/n)!=h:raise ValueError('parent receipt artifact '+n)
 audit=R.read(PARENT/'independent_verification.json')
 if audit.get('all_passed')is not True:raise ValueError('parent audit failed')
 for n,h in audit['input_sha256'].items():
  if R.sha(PARENT/n)!=h:raise ValueError('parent audit binding '+n)


def parent_candidate():
 parent_bindings();failed=R.read(PARENT/'jobs/final-002.json');train=R.read(PARENT/'jobs/train-001.json');spec=R.read(PARENT/'protocol.json')
 if failed.get('status')!='missing_resource' or failed.get('reason')!='MemoryError' or failed.get('scales')!=[13] or failed.get('phase')!='final' or failed.get('index')!=2:raise ValueError('only original failed X13 transfer')
 if train.get('status')!='finite_PSD_certificate' or train.get('independent_check',{}).get('verified')is not True:raise ValueError('accepted original training candidate')
 if failed['program']!=train['program']or failed['program']['claim']!='unsigned_calibration':raise ValueError('same supplied unsigned program')
 plan=R.read(PARENT/'candidate_seal.json')
 if plan['training_sha256']!=R.sha(PARENT/'training.json'):raise ValueError('parent training seal')
 follow=plan['jobs'][2]
 if follow!=dict(phase='final',program=train['program'],X=13,attempt_file='jobs/train-001.json',attempt_sha256=R.sha(PARENT/'jobs/train-001.json')):raise ValueError('same final candidate plan')
 weights=train['synthesis']['weights'];grams=train['synthesis']['grams']
 if set(grams)!=set(spec['gram_specs'])or len(grams)!=4:raise ValueError('four same Gram groups')
 for name,n in spec['gram_specs'].items():
  if grams[name]!=[['0']*n for _ in range(n)]:raise ValueError('same four zero Gram matrices')
 if spec['limits']['time_limit']!=180:raise ValueError('same cooperative time limit')
 return spec,failed,dict(weights=weights,grams=grams,training_sha256=R.sha(PARENT/'jobs/train-001.json'))


def freeze(directory):
 require_verified_runtime();spec,failed,candidate=parent_candidate()
 for name in ['check_joint_gram_transfer_retry',*TESTS]:
  if not(ROOT/(name+'.py')).is_file():raise FileNotFoundError(name)
 protocol=dict(schema=1,program=failed['program'],scales=[13],gram_specs=spec['gram_specs'],limits=spec['limits'],parallel=PARALLEL,
  tests=TESTS,training_file='jobs/train-001.json',failed_file='jobs/final-002.json',weights_sha256=R.digest(candidate['weights']),grams_sha256=R.digest(candidate['grams']),
  no_new_float_search=True,same_candidate=True,refitted=False,conditioning='memory-only retry; unchanged source builder, deep-copy instantiation, scalar weights and four zero Grams',**FLAGS)
 names=['protocol.json','source_seal.json','receipt.json','independent_verification.json','jobs/train-001.json','jobs/final-002.json','candidate_seal.json','training.json']
 inputs={str((PARENT/n).relative_to(ROOT)):R.sha(PARENT/n)for n in names}
 d=Path(directory).resolve();d.mkdir(parents=True,exist_ok=False);(d/'frozen_source').mkdir()
 hashes={}
 for name in sources():
  (d/'frozen_source'/name).write_bytes((ROOT/name).read_bytes());hashes[name]=R.sha(ROOT/name)
 test=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=180)
 if test.returncode:raise ValueError('memory retry calibration failed: '+test.stderr)
 R.write(d/'tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr))
 R.write(d/'protocol.json',protocol);R.write(d/'source_seal.json',hashes);R.write(d/'input.json',dict(input_sha256=inputs));R.write(d/'candidate.json',candidate)
 R.write(d/'seal.json',dict(protocol_sha256=R.sha(d/'protocol.json'),source_seal_sha256=R.sha(d/'source_seal.json'),input_sha256=R.sha(d/'input.json'),candidate_sha256=R.sha(d/'candidate.json')))
 return d


def validate(directory):
 d=Path(directory);seal=R.read(d/'seal.json')
 for name in ['protocol','source_seal','input','candidate']:
  if seal[name+'_sha256']!=R.sha(d/(name+'.json')):raise ValueError('retry seal '+name)
 hashes=R.read(d/'source_seal.json')
 if set(hashes)!=set(sources()):raise ValueError('complete retry source closure')
 for name,h in hashes.items():
  if R.sha(ROOT/name)!=h or R.sha(d/'frozen_source'/name)!=h:raise ValueError('retry source '+name)
 for name,h in R.read(d/'input.json')['input_sha256'].items():
  if R.sha(ROOT/name)!=h:raise ValueError('bound parent input '+name)
 parent,failed,candidate=parent_candidate();spec=R.read(d/'protocol.json')
 if R.read(d/'candidate.json')!=candidate:raise ValueError('unchanged training weights and Grams')
 if spec['program']!=failed['program']or spec['scales']!=[13]or spec['gram_specs']!=parent['gram_specs']or spec['limits']!=parent['limits']or spec['parallel']!=PARALLEL:raise ValueError('memory-only computation policy')
 if spec['weights_sha256']!=R.digest(candidate['weights'])or spec['grams_sha256']!=R.digest(candidate['grams']):raise ValueError('candidate hashes')


def transfer(instance,blocks,specs,candidate,limits):
 record=instantiate_certificate(instance,candidate['weights'],candidate['grams'],blocks,**limits)
 result=dict(status='finite_PSD_certificate',weights=candidate['weights'],grams=candidate['grams'],gram_specs=specs,
  source_hashes=[R.digest(instance)],gram_block_hashes=[R.digest(blocks)],certificates=[record],constant_slacks=[record['constant_slack']],**FLAGS)
 result['independent_check']=I.verify_primal([instance],[blocks],specs,result)
 return result


def worker(job):
 require_verified_runtime();d=Path(job['directory']);validate(d)
 if(d/'result.json').exists()or(d/'receipt.json').exists():raise FileExistsError('exclusive memory retry')
 spec=R.read(d/'protocol.json');candidate=R.read(d/'candidate.json');failed=R.read(PARENT/'jobs/final-002.json');parent=R.read(PARENT/'protocol.json');start=time.monotonic();cpu=time.process_time()
 output=dict(phase='final',index=2,program=spec['program'],scales=[13],gram_specs=spec['gram_specs'],weights_sha256=spec['weights_sha256'],grams_sha256=spec['grams_sha256'],no_new_float_search=True,same_candidate=True,refitted=False,**FLAGS)
 try:
  built=B.build(spec['program'],13);instance=built['instance'];blocks=built['gram_blocks']
  metadata=dict(ordinary_case_hashes=[R.digest(instance)],case_hashes=[R.digest(instance)],gram_block_hashes=[R.digest(blocks)],
   factor_archive_hashes=[R.digest(built['factor_archive'])],divisor_archive_hashes=[R.digest(built['divisor_archive'])],cell_archive_hashes=[R.digest(built['cell_archive'])],gram_archive_hashes=[R.digest(built['gram_archive'])],dictionary_sha256=R.digest(parent['dictionary']),gram_specs=B.gram_specs())
  for name in METADATA_KEYS:
   if metadata[name]!=failed[name]:raise ValueError('same complete source '+name)
  output.update(metadata)
  result=transfer(instance,blocks,spec['gram_specs'],candidate,spec['limits'])
  output.update(status=result['status'],synthesis=result,independent_check=result['independent_check'])
 except(OverflowError,TimeoutError,MemoryError,ImportError)as e:output.update(status='missing_resource',reason=str(e)or type(e).__name__)
 except(ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError)as e:output.update(status='rejected',reason=str(e)or type(e).__name__)
 output['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,pid=os.getpid(),observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())))
 validate(d);R.write(d/'result.json',output)
 return dict(file='result.json',sha256=R.sha(d/'result.json'),status=output['status'],cost=output['cost'],**FLAGS)


def run(directory):
 require_verified_runtime();d=Path(directory).resolve();validate(d)
 if(d/'execution.json').exists():raise FileExistsError('retry already run')
 execution=run_jobs([dict(directory=str(d))],worker='run_joint_gram_transfer_retry:worker',**PARALLEL)
 R.write(d/'execution.json',execution);validate(d)
 R.write(d/'receipt.json',dict(files_sha256={str(p.relative_to(d)):R.sha(p)for p in sorted(d.rglob('*.json'))},source_count=len(R.read(d/'source_seal.json')),no_new_float_search=True,same_candidate=True,refitted=False,**FLAGS))
 print(json.dumps(execution))

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');args=parser.parse_args()
 (freeze if args.command=='freeze'else run)(args.directory)
