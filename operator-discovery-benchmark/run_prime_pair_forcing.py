#!/usr/bin/env python3
"""Freeze-before-data runner for complete signed prime-pair-forcing potentials.
Python file-access guard enforces declared discovery dataflow; it is not an OS
sandbox. Replay checks implementation determinism, not independent mathematics.
"""
import argparse,builtins,hashlib,io,json,os,shutil,subprocess,sys,tempfile
from fractions import Fraction as F
from pathlib import Path
import prime_pair_forcing as arithmetic
import prime_pair_forcing_search as search
from arithmetic_filter_pole_budget import certify
from detector_workflow_guard import require_verified_runtime
BASE=Path(__file__).resolve().parent
CODE=['run_prime_pair_forcing.py','test_run_prime_pair_forcing.py','prime_pair_forcing.py','test_prime_pair_forcing.py','prime_pair_forcing_proof.txt','prime_pair_forcing_search.py','test_prime_pair_forcing_search.py','prime_pair_forcing_checks.py','test_prime_pair_forcing_checks.py','check_prime_pair_forcing_run.py','test_check_prime_pair_forcing_run.py','arithmetic_filter_pole_budget.py','arithmetic_filter_pole_budget_proof.txt','test_arithmetic_filter_pole_budget.py','detector_safe_evaluation.py','inverse_prefix_grammar.py','detector_workflow_guard.py','prime_pair_forcing_review.txt']
INPUTS=['training.json','validation_data.json']
OUTPUTS=['candidate_batch.json','validation.json','proof_queue.json']
TARGETS=['mu','c']
CUTOFFS=search.CUTOFFS
CLAIM='For the exact actual target f=mu or c=mu*lambda and cutoff B(X) in this program, there exists integer q0>=1 such that every integer q>=q0 admits finite Cq>=0 independent of X, and every dyadic integer X>=1 satisfies -R_B(X)<=Cq X^2 ceil(X^(1/q)). R_B is the COMPLETE prime-pair forcing sum over prime powers k=p^e with ka,b<=4X-1 and max(a,b)/gcd(a,b)>B(X), weighted by log(p)*f(a)*f(b)*J_X(max(ka,b))/log(kab). All e>=1 occur for mu; only odd e occur for c. J_X(t)=K_2X(t)-4K_X(t), K_X(t)=max(0,2X-max(X,t)). The exact full identity is Delta_f(X)=J_X(1)-2*kappa*(S_B(X)+R_B(X)), with kappa=1 for mu and2 for c. The selected cutoff has a supplied uniform cofinal critical bound on |S_B|; this recovers the full original signed defect before the ordinary-zeta argument. Stored constants are finite conservative fits, not assertions about unknown existential constants. Interval or finite success is never a uniform proof.'
def digest(x):return search.digest(x)
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())
def write(path,x):
 with Path(path).open('x') as f:json.dump(x,f,sort_keys=True,indent=2);f.write('\n')
def rank(c,score):
 values=list(c['program']['constants'].values())
 observed={o['X']:F(o['normalized_upper_plus_auxiliary']) for o in score['observations'] if o['normalized_upper_plus_auxiliary'] is not None}
 return (score['missing_cases']+sum(v is None for v in values),score['unresolved_intervals'],score['finite_failures'],sum(observed.values(),F(0)),max([F(v) for v in values if v is not None] or [F(0)]),c['program_id'])
def select(factories,results):
 scores={r['program_id']:r['score'] for r in results};queue={};decisions=[]
 for factory in factories:
  target=factory['target'];candidates=factory['candidates']
  for group in ('baseline','fixed','bit_length_power','all_admitted'):
   eligible=[c for c in candidates if c['conditional_auxiliary']['auxiliary_bound_admitted'] and (group=='all_admitted' or (group=='baseline' and c['program']['cutoff']==dict(kind='fixed',value=0)) or (group=='fixed' and c['program']['cutoff']['kind']=='fixed' and c['program']['cutoff']['value']>0) or (group=='bit_length_power' and c['program']['cutoff']['kind']=='bit_length_power'))]
   chosen=min(eligible,key=lambda c:rank(c,scores[c['program_id']])) if eligible else None
   decisions.append(dict(target=target,group=group,eligible_ids=sorted(c['program_id'] for c in eligible),selected_id=None if chosen is None else chosen['program_id'],rank=None if chosen is None else [str(x) if isinstance(x,F) else x for x in rank(chosen,scores[chosen['program_id']])]))
   if chosen is None:continue
   pid=chosen['program_id']
   if pid not in queue:
    queue[pid]=dict(program_id=pid,exact_program=chosen['program'],exact_program_sha256=digest(chosen['program']),global_claim=CLAIM,precise_claim_sha256=digest(CLAIM),selection_origins=[],validation_score=scores[pid],conditional_admission=certify(1,int(target=='c'),[dict(divisor=1,weight='1')]),prefix_certificate=chosen['component_certificate'],kappa=1 if target=='mu' else 2,recovery='Delta=J1-2*kappa*(S_prefix+R); J1=-2X; a lower bound on R and the proved absolute prefix bound imply the original full upper defect bound',global_bound_proved=False)
   queue[pid]['selection_origins'].append(group)
 return sorted(queue.values(),key=lambda q:q['program_id']),decisions

def specification():
 versions={}
 for name in ('numpy','scipy'):
  try:module=__import__(name);versions[name]=module.__version__
  except ImportError:versions[name]=None
 previous='critical-core-results/pilot-001/verification.json'
 return dict(schema=1,version='prime-pair-forcing-v1',code_sha256={n:sha(BASE/n) for n in CODE},targets=TARGETS,cutoffs=CUTOFFS,dictionary_sha256=digest(CUTOFFS),training_scales=[2**j for j in range(7)],validation_scales=[96,128,192],levels=[2,3,6,12],final_levels=[3,12,17,29],budgets=dict(arithmetic_work=2000000000,max_n=4095,bits=80,bit=1000000),selection_groups=['baseline','fixed','bit_length_power','all_admitted'],selection_rank=['missing_observations_plus_missing_constants','unresolved_intervals','validation_failures','sum_normalized_remainder_upper_plus_uniform_auxiliary_cost','max_training_constant','program_id'],final_generation=dict(fixed=[512,1024],odd_min=769,odd_count=50,formula='769+2*(int(seal_sha256[:16],16)%50)'),global_claim=CLAIM,runtime=dict(python=sys.version,**versions),provenance=dict(prior_verifications={previous:sha(BASE/previous)},complete_actual_prime_source=True,historical_coefficient_overlap=True,unseen_prime_holdout=False,supplied_bias='exact prime-log pair forcing, primitive-core partition and harmonic envelope rules; finite cutoff dictionary supplied before scores; only numerical cutoff choice learned',full_signed_bound_proved=False,global_bound_proved=False))
def dataset(spec,bases):
 b=spec['budgets'];p=arithmetic.profile(bases,spec['targets'],spec['cutoffs'],work_budget=b['arithmetic_work'],max_n=b['max_n'],bits=b['bits'])
 return dict(protocol_sha256=digest(spec),base_scales=list(bases),scales=list(bases),profile=p)
def worker(directory):
 require_verified_runtime();d=Path(directory).resolve()
 if any((d/n).exists() for n in OUTPUTS+['seal.json','verification.json','failure.json']):raise FileExistsError('worker requires unused outputs')
 spec=read(d/'protocol.json')
 for n,h in spec['code_sha256'].items():
  if sha(BASE/n)!=h:raise ValueError('worker source mismatch: '+n)
 # Preload optional numerical dependencies before enforcing file dataflow.
 try:import numpy
 except ImportError:pass
 try:import scipy.optimize
 except ImportError:pass
 allowed={d/n for n in ['protocol.json']+INPUTS+OUTPUTS};old,oldio,oldpath=builtins.open,io.open,Path.open
 def check(path):
  if isinstance(path,(str,bytes,os.PathLike)) and Path(path).resolve() not in allowed:raise PermissionError('outside frozen discovery dataflow')
 def guarded(path,*a,**kw):check(path);return old(path,*a,**kw)
 def guardedio(path,*a,**kw):check(path);return oldio(path,*a,**kw)
 def guardedpath(path,*a,**kw):check(path);return oldpath(path,*a,**kw)
 builtins.open,io.open,Path.open=guarded,guardedio,guardedpath
 try:
  denied={}
  for label,path in [('proof',BASE/'prime_pair_forcing_proof.txt'),('final_cases',d/'final_cases.json'),('final_evaluation',d/'final_evaluation.json'),('prior_results',BASE/'critical-core-results/pilot-001/report.json')]:
   try:read(path);denied[label]=False
   except PermissionError:denied[label]=True
  training,validation_data=[read(d/n) for n in INPUTS]
  for data,field in ((training,'training_scales'),(validation_data,'validation_scales')):
   if data['protocol_sha256']!=digest(spec) or data['base_scales']!=spec[field] or data['scales']!=spec[field]:raise ValueError('input protocol/domain binding mismatch')
  factories=[search.candidate_factory(training['profile'],target,spec['training_scales'],spec['levels'],cutoffs=spec['cutoffs'],bit_budget=spec['budgets']['bit']) for target in spec['targets']]
  write(d/'candidate_batch.json',dict(protocol_sha256=digest(spec),training_sha256=sha(d/'training.json'),access_denials=denied,factories=factories))
  results=[dict(program_id=c['program_id'],score=search.score(c['program'],validation_data['profile'],spec['validation_scales'],spec['levels'],bit_budget=spec['budgets']['bit'])) for f in factories for c in f['candidates']]
  write(d/'validation.json',dict(protocol_sha256=digest(spec),validation_sha256=sha(d/'validation_data.json'),results=results))
  queue,decisions=select(factories,results)
  write(d/'proof_queue.json',dict(protocol_sha256=digest(spec),queue=queue,selection_decisions=decisions,candidate_ids_frozen_before_final=True,final_used_for_selection=False))
 finally:builtins.open,io.open,Path.open=old,oldio,oldpath

def replay(directory):
 directory=Path(directory)
 with tempfile.TemporaryDirectory(prefix='prime-pair-forcing-replay-') as tmp:
  d=Path(tmp)
  for n in ['protocol.json']+INPUTS:shutil.copyfile(directory/n,d/n)
  subprocess.run([sys.executable,'-B',str(BASE/'run_prime_pair_forcing.py'),'worker',str(d)],check=True,cwd=BASE)
  matches={n:sha(directory/n)==sha(d/n) for n in OUTPUTS}
  if not all(matches.values()):raise ValueError('worker byte replay mismatch')
  return dict(files_match=matches,isolated_subprocess=True,independent_implementation=False,python_guard_is_OS_sandbox=False)
def final_cases(spec,seal_hash):
 f=spec['final_generation'];odd=f['odd_min']+2*(int(seal_hash[:16],16)%f['odd_count'])
 return dict(protocol_sha256=digest(spec),seal_sha256=seal_hash,base_scales=sorted(f['fixed']+[odd]),levels=spec['final_levels'],generated_after_seal=True)
def run(directory):
 require_verified_runtime();d=Path(directory).resolve();d.mkdir(parents=True,exist_ok=False);spec=specification();(d/'frozen_source').mkdir()
 for n in CODE:shutil.copyfile(BASE/n,d/'frozen_source'/n)
 write(d/'protocol.json',spec);tests=[Path(n).stem for n in CODE if n.startswith('test_')]
 result=subprocess.run([sys.executable,'-B','-m','unittest',*tests],cwd=BASE,capture_output=True,text=True)
 with (d/'contract_tests.txt').open('x') as f:f.write(result.stdout+result.stderr)
 if result.returncode:raise RuntimeError('contract failure evidence retained')
 if any(sha(BASE/n)!=h for n,h in spec['code_sha256'].items()):raise ValueError('source changed during contract tests')
 write(d/'source_seal.json',dict(protocol_sha256=digest(spec),code_sha256=spec['code_sha256'],tests=tests,tests_passed=True,contract_tests_sha256=sha(d/'contract_tests.txt'),source_frozen_before_data=True))
 for n,bases in [('training.json',spec['training_scales']),('validation_data.json',spec['validation_scales'])]:
  if any(sha(BASE/n)!=h for n,h in spec['code_sha256'].items()):raise ValueError('source changed before data')
  write(d/n,dataset(spec,bases))
 subprocess.run([sys.executable,'-B',str(BASE/'run_prime_pair_forcing.py'),'worker',str(d)],check=True,cwd=BASE);write(d/'worker_replay.json',replay(d))
 names=['protocol.json','contract_tests.txt','source_seal.json','worker_replay.json']+INPUTS+OUTPUTS
 write(d/'seal.json',dict(protocol_sha256=digest(spec),files={n:sha(d/n) for n in names},selection_closed=True,final_cases_exist=False))
 if any(sha(BASE/n)!=h for n,h in spec['code_sha256'].items()):raise ValueError('source changed before final')
 cases=final_cases(spec,sha(d/'seal.json'));write(d/'final_cases.json',cases);data=dataset(spec,cases['base_scales'])
 results=[dict(program_id=c['program_id'],score=search.score(c['exact_program'],data['profile'],cases['base_scales'],cases['levels'],bit_budget=spec['budgets']['bit'])) for c in read(d/'proof_queue.json')['queue']]
 write(d/'final_evaluation.json',dict(protocol_sha256=digest(spec),cases_sha256=sha(d/'final_cases.json'),data=data,results=results,global_bound_proved=False))
 subprocess.run([sys.executable,'-B',str(BASE/'check_prime_pair_forcing_run.py'),str(d)],check=True,cwd=BASE)
 return d
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('command',choices=['run','worker']);parser.add_argument('directory');args=parser.parse_args();(run if args.command=='run' else worker)(args.directory)
