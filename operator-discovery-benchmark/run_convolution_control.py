#!/usr/bin/env python3
"""Frozen-protocol orchestration for complete actual convolution potentials.
No actual dataset is generated at import or in tests. Python file guard is a
read/write dataflow check, not operating-system isolation.
"""
import argparse,builtins,hashlib,io,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
from fractions import Fraction as F
import convolution_control_arithmetic as arithmetic
import convolution_control_search as search
from detector_workflow_guard import require_verified_runtime
BASE=Path(__file__).resolve().parent
OUTPUTS=['candidate_batch.json','validation.json','proof_queue.json']
INPUTS=['training.json','validation_data.json']
CODE=['convolution_control_arithmetic.py','test_convolution_control_arithmetic.py','convolution_control_search.py','test_convolution_control_search.py','run_convolution_control.py','test_run_convolution_control.py','check_convolution_control_run.py','test_convolution_control_run.py','convolution_control_checks.py','test_convolution_control_checks.py','convolution_control_proof.txt','convolution_control_analytic.py','test_convolution_control_analytic.py','detector_safe_evaluation.py','inverse_prefix_grammar.py','detector_workflow_guard.py']
CLAIM='There exists an integer q0>=1 such that for every integer q>=q0 there exists finite Cq>=0 independent of X such that for every dyadic integer X>=1, E(2X)+V(2X)-E(X)-V(X)<=Cq ceil(X^(1/q)), where E(X)=A_C(X)/X^2, C is the complete prefix of actual mu*lambda, and V is the exact nonnegative potential specified by the frozen terms, with every cutoff recomputed at its own scale.'
def digest(x):return search.digest(x)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def write(p,x):
 with Path(p).open('x') as f:json.dump(x,f,sort_keys=True,indent=2);f.write('\n')
def rank(c,score):
 values=list(c['program']['constants'].values());missing_constants=sum(x is None for x in values)
 return (score['missing_cases']+missing_constants,score['finite_failures'],max([F(x) for x in values if x is not None] or [F(0)]),sum(F(t['weight']) for t in c['program']['terms']),len(c['program']['terms']),c['program_id'])
def rank_json(r):return [str(x) if isinstance(x,F) else x for x in r]
def select(factory,results):
 scores={r['program_id']:r['score'] for r in results};queue={};decisions=[]
 for group in ['baseline','gram','fixed','root','three','all']:
  eligible=[]
  for c in factory['candidates']:
   origins=c['origins'];match=False
   for o in origins:
    if group=='baseline' and o['kind']=='baseline':match=True
    elif o['kind']=='lp' and o['group']==group:match=True
    elif o['kind']=='singleton' and group!='baseline':
     f=next(f for f in search.FEATURE_DICTIONARY if f['feature_id']==o['feature_id'])
     if group==f['kind']:match=True
   if match:eligible.append(c)
  if not eligible:decisions.append(dict(group=group,eligible_ids=[],selected_id=None,rank=None));continue
  chosen=min(eligible,key=lambda c:rank(c,scores[c['program_id']]))
  pid=chosen['program_id'];decisions.append(dict(group=group,eligible_ids=sorted(c['program_id'] for c in eligible),selected_id=pid,rank=rank_json(rank(chosen,scores[pid]))))
  if pid not in queue:
   queue[pid]=dict(program_id=pid,exact_program=chosen['program'],exact_program_sha256=digest(chosen['program']),global_claim=CLAIM,precise_claim_sha256=digest(CLAIM),selection_origins=[],validation_score=scores[pid],global_bound_proved=False)
  queue[pid]['selection_origins'].append(group)
 return sorted(queue.values(),key=lambda x:x['program_id']),decisions

def worker(directory):
 require_verified_runtime();d=Path(directory).resolve();spec=read(d/'protocol.json')
 if any((d/n).exists() for n in OUTPUTS+['seal.json','verification.json','failure.json']):raise FileExistsError('worker requires unused output destination')
 for name,expected in spec.get('code_sha256',{}).items():
  if sha(BASE/name)!=expected:raise ValueError('worker source differs from frozen protocol')
 # Load numerical backend before enabling the declared dataflow guard.
 try:import scipy.optimize
 except ImportError:pass
 allowed={d/'protocol.json'}|{d/n for n in INPUTS+OUTPUTS}
 old=builtins.open;oldio=io.open;oldpath=Path.open
 def guarded(file,*args,**kwargs):
  if isinstance(file,(str,bytes,os.PathLike)) and Path(file).resolve() not in allowed:raise PermissionError('outside discovery dataflow')
  return old(file,*args,**kwargs)
 def guardedio(file,*args,**kwargs):
  if isinstance(file,(str,bytes,os.PathLike)) and Path(file).resolve() not in allowed:raise PermissionError('outside discovery dataflow')
  return oldio(file,*args,**kwargs)
 def guardedpath(path,*args,**kwargs):
  if path.resolve() not in allowed:raise PermissionError('outside discovery dataflow')
  return oldpath(path,*args,**kwargs)
 builtins.open=guarded;io.open=guardedio;Path.open=guardedpath
 try:
  denied={}
  for label,path in [('proof',BASE/'convolution_control_proof.txt'),('final_cases',d/'final_cases.json'),('final_evaluation',d/'final_evaluation.json'),('historical_report',BASE/'root-results/report.txt')]:
   try:read(path);denied[label]=False
   except PermissionError:denied[label]=True
  training=read(d/'training.json');validation=read(d/'validation_data.json')
  for data,name in ((training,'training_scales'),(validation,'validation_scales')):
   if data['protocol_sha256']!=digest(spec) or data['base_scales']!=spec[name]:raise ValueError('input protocol binding mismatch')
  factory=search.candidate_factory(training['table'],spec['training_scales'],spec['levels'],bit_budget=spec['budgets']['bit'])
  write(d/'candidate_batch.json',dict(protocol_sha256=digest(spec),training_data_sha256=sha(d/'training.json'),access_denials=denied,factory=factory))
  results=[dict(program_id=c['program_id'],score=search.score(c['program'],validation['table'],spec['validation_scales'],spec['levels'],bit_budget=spec['budgets']['bit'])) for c in factory['candidates']]
  write(d/'validation.json',dict(protocol_sha256=digest(spec),validation_data_sha256=sha(d/'validation_data.json'),results=results))
  queue,decisions=select(factory,results)
  write(d/'proof_queue.json',dict(protocol_sha256=digest(spec),queue=queue,selection_decisions=decisions,candidate_ids_frozen_before_final=True,final_used_for_selection=False))
 finally:builtins.open=old;io.open=oldio;Path.open=oldpath

def specification():
 try:
  import scipy
  scipy_version=scipy.__version__
 except ImportError:scipy_version=None
 try:
  import numpy
  numpy_version=numpy.__version__
 except ImportError:numpy_version=None
 prior=BASE/'signed-arithmetic-results/pilot-001/proof_queue.json'
 return dict(target_provenance=dict(path=str(prior.relative_to(BASE)),sha256=sha(prior),ast_program_id='43bc2c2518395be27e340edb652a8a3f7574d337d35f994f8f89a951165bcb78',scope='unshifted convolution target motivated by frozen AST; no bound transferred'),runtime=dict(python=sys.version,numpy_version=numpy_version,scipy_version=scipy_version,scipy_role='proposal only; exact rationalized refits authoritative'),version='convolution-control-v1',code_sha256={n:sha(BASE/n) for n in CODE},training_scales=[1,2,4,8,16,32,64,128,256,512,1024,2048],validation_scales=[1535,3072,4096,6144],levels=[2,3,6,12],final_levels=[3,12,13,17],budgets=dict(arithmetic_work=30000000,max_n=1048575,feature_work=200000000,bit=1000000),feature_dictionary=search.FEATURE_DICTIONARY,feature_dictionary_sha256=search.FEATURE_DICTIONARY_SHA256,selection_groups=['baseline','gram','fixed','root','three','all'],selection_rank=['missing_observations_plus_missing_constants','finite_failures','max_exact_training_constant','sum_nonnegative_weights','term_count','program_id'],lp_groups=search.LP_GROUPS,lp_penalties=search.LP_PENALTIES,singleton_weights=search.SINGLETON_WEIGHTS,global_claim=CLAIM,provenance=dict(actual_coefficients='complete prime sieve and complete generic convolution mu*lambda',prime_coefficients_new_holdout=False,historical_coefficient_overlap=True,scope='new finite scale/candidate evaluation only; no all-scale bound'),final_generation=dict(odd_min=9001,odd_count=1500,formula='9001+2*(int(seal_sha256[:16],16)%1500)',fixed=[8192,16384]))
def dataset(spec,scales):
 b=spec['budgets'];p=arithmetic.arithmetic_profile(scales,control='actual_h',return_tau_profile=True,work_budget=b['arithmetic_work'],max_n=b['max_n'])
 table=search.featuretable(p,sorted(set(scales)|{2*x for x in scales}),work_budget=b['feature_work'],bit_budget=b['bit'])
 return dict(protocol_sha256=digest(spec),base_scales=list(scales),profile=p,table=table)
def final_cases(spec,seal_hash):
 odd=9001+2*(int(seal_hash[:16],16)%1500)
 return dict(protocol_sha256=digest(spec),seal_sha256=seal_hash,base_scales=sorted([odd,8192,16384]),levels=spec['final_levels'],generated_after_seal=True)
def replay_worker(d):
 with tempfile.TemporaryDirectory(prefix='convolution-control-replay-') as tmp:
  r=Path(tmp)
  for n in ['protocol.json']+INPUTS:shutil.copyfile(d/n,r/n)
  subprocess.run([sys.executable,'-B',str(BASE/'run_convolution_control.py'),'worker',str(r)],check=True,cwd=BASE)
  matches={n:sha(d/n)==sha(r/n) for n in OUTPUTS}
  if not all(matches.values()):raise ValueError('isolated worker byte replay mismatch')
  return dict(files_match=matches,isolated_subprocess=True,python_guard_not_os_sandbox=True)
def run(directory):
 require_verified_runtime();d=Path(directory).resolve()
 d.mkdir(parents=True,exist_ok=False)
 spec=specification(); frozen=d/'frozen_source';frozen.mkdir()
 for n in CODE:shutil.copyfile(BASE/n,frozen/n)
 write(d/'protocol.json',spec)
 tests=['test_convolution_control_arithmetic','test_convolution_control_search','test_run_convolution_control','test_convolution_control_checks','test_convolution_control_run','test_convolution_control_analytic']
 result=subprocess.run([sys.executable,'-B','-m','unittest',*tests],capture_output=True,text=True,cwd=BASE)
 with (d/'contract_tests.txt').open('x') as f:f.write(result.stdout+result.stderr)
 if result.returncode:raise RuntimeError('contract tests failed; evidence retained')
 if any(sha(BASE/n)!=h for n,h in spec['code_sha256'].items()):raise ValueError('source changed after protocol freeze')
 write(d/'source_seal.json',dict(protocol_sha256=digest(spec),code_sha256=spec['code_sha256'],source_frozen_before_actual_data=True,contract_tests_sha256=sha(d/'contract_tests.txt'),development_tests=tests,tests_passed=True))
 for name,scales in [('training.json',spec['training_scales']),('validation_data.json',spec['validation_scales'])]:write(d/name,dataset(spec,scales))
 subprocess.run([sys.executable,'-B',str(BASE/'run_convolution_control.py'),'worker',str(d)],check=True,cwd=BASE)
 replay=replay_worker(d)
 write(d/'worker_replay.json',replay)
 write(d/'seal.json',dict(protocol_sha256=digest(spec),files={n:sha(d/n) for n in ['protocol.json','contract_tests.txt','source_seal.json','worker_replay.json']+INPUTS+OUTPUTS},selection_closed=True,final_cases_exist=False))
 if any(sha(BASE/n)!=h for n,h in spec['code_sha256'].items()):raise ValueError('source changed before postseal evaluation')
 cases=final_cases(spec,sha(d/'seal.json'));write(d/'final_cases.json',cases)
 data=dataset(spec,cases['base_scales']);queue=read(d/'proof_queue.json')['queue']
 results=[dict(program_id=c['program_id'],score=search.score(c['exact_program'],data['table'],cases['base_scales'],cases['levels'],bit_budget=spec['budgets']['bit'])) for c in queue]
 write(d/'final_evaluation.json',dict(protocol_sha256=digest(spec),cases_sha256=sha(d/'final_cases.json'),data=data,results=results,global_bound_proved=False))
 subprocess.run([sys.executable,'-B',str(BASE/'check_convolution_control_run.py'),str(d)],check=True,cwd=BASE)
 return d
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('command',choices=['run','worker']);parser.add_argument('directory');args=parser.parse_args()
 (run if args.command=='run' else worker)(args.directory)
