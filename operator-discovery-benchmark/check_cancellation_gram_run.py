"""Independent complete shared-Gram posthoc run audit; no producer imports."""
import sys,json,re
from pathlib import Path
from fractions import Fraction as F
import check_cancellation_arithmetic_run as B
import check_cancellation_gram as G
EXTRA=['run_cancellation_gram_probe.py','check_cancellation_gram_run.py','cancellation_gram_synthesis.py','test_cancellation_gram_synthesis.py','cancellation_gram_language.py','test_cancellation_gram_language.py','cancellation_gram_diagonal_dual.py','test_cancellation_gram_diagonal_dual.py','check_cancellation_gram.py','test_check_cancellation_gram.py','test_check_cancellation_gram_run.py','test_run_cancellation_gram_probe.py','cancellation_gram_independent_review.txt','exact_dual_support_reconstruction.py','cancellation_dual_column_search.py']
TESTS=['test_cancellation_gram_language','test_cancellation_gram_synthesis','test_cancellation_gram_diagonal_dual','test_check_cancellation_gram','test_check_cancellation_gram_run','test_run_cancellation_gram_probe']
LIMITS=dict(B.LIMITS,time_limit=120,max_coefficient_bits=4096,max_horizon=80)
DUAL_LIMITS=dict(time_limit=60,max_denominator=2**4096,max_rows=1200,max_variables=40000,max_work=30000000,max_horizon=80)
def audit(parent):
 parent=Path(parent);d=parent/'gram-probe-001';names=['protocol','source_seal','seal','tests','training','candidate_seal','final','dual','producer_receipt'];hashes={n:B.sha(d/(n+'.json')) for n in names};spec=B.read(d/'protocol.json');source=B.read(d/'source_seal.json');training=B.read(d/'training.json');final=B.read(d/'final.json');dual=B.read(d/'dual.json')
 def binding():
  B.require(set(source['hashes'])==set(EXTRA),'exact extra source set')
  B.require(B.read(d/'seal.json')==dict(protocol_sha256=B.sha(d/'protocol.json'),source_seal_sha256=B.sha(d/'source_seal.json')),'source/protocol seal')
  for n,h in source['hashes'].items():B.require(B.sha(d/'frozen_source'/n)==h and B.sha(Path(__file__).parent/n)==h,'source '+n)
  for n,h in B.read(parent/'source_seal.json')['hashes'].items():B.require(B.sha(parent/'frozen_source'/n)==h and B.sha(Path(__file__).parent/n)==h,'parent source '+n)
  for n in ['training','verification','source_seal']:
   p=parent/('independent_verification.json' if n=='verification' else n+'.json');B.require(spec['parent_'+n+'_sha256']==B.sha(p),'parent input '+n)
 binding();B.require(B.read(parent/'independent_verification.json')['all_passed'],'verified parent');old=B.read(parent/'training.json')['attempts'];programs=[dict(old[j]['program'],allow_constant_slack=True) for j in [26,28]]
 B.require(spec['programs']==programs and spec['training_scales']==[1,2,3,5] and spec['final_scales']==[11,13] and spec['limits']==LIMITS and spec['dual_limits']==DUAL_LIMITS and spec['tests']==TESTS and spec['atoms']==['prefix','half','even','mod3one','prime'] and spec['regions']==['parent','child'],'known contract')
 B.require(spec['historical_coefficient_overlap'] is True and spec['unseen_prime_holdout'] is False and spec['solver_byte_replay_guaranteed'] is False,'provenance');test=B.read(d/'tests.json');B.require(test['returncode']==0 and re.search(r'Ran \d+ tests? in .*\n\s*OK\s*$',test['stdout']+test['stderr']),'tests')
 ats=training['attempts'];fs=final['results'];B.require(len(ats)==len(fs)==2 and training['no_actual_signed_responses'] is True and final['refitted'] is False,'complete attempts/no responses/refit');B.require(B.read(d/'candidate_seal.json')==dict(training_sha256=hashes['training'],protocol_sha256=hashes['protocol']),'candidate seal');diagnostics=[];allinstances=[]
 for j,(program,a,f) in enumerate(zip(programs,ats,fs)):
  B.require(a==B.read(d/'attempts'/f'{j:03d}.json') and a['program']==program,'checkpoint/program');ordinary=[B.build(program,X)['instance'] for X in [1,2,3,5]];aux=[B.auxiliary_constraint(B.descriptors())['instance']] if program['constraint']=='zero_cubic' else [];instances=ordinary+aux;allinstances.append(instances);r=a['synthesis'];accepted=r['status']=='finite_PSD_certificate'
  if a.get('external_resource_failure'):B.require(r['status']=='missing_resource' and a['independent_check'] is None and a['gamma'] is None and a['budgets']==[],'external missing')
  else:B.require(a['case_hashes']==list(map(B.digest,instances)),'full training instances')
  if accepted:
   G.verify_primal(instances,[1,2,3,5],r);gamma=sum((F(c)*F(w) for c,w in zip(B.auxiliary_constraint(B.descriptors())['gamma_coefficients'],r['weights']['relation_weights'])),F(0));B.require(a['gamma']==str(gamma) and (program['constraint']!='zero_cubic' or gamma==0),'gamma');B.require(a['budgets']==[B.budget(i,r['weights']) for i in ordinary],'budgets')
  else:B.require(r['status'] in ['missing_resource','uncertified'] and a['gamma'] is None and a['budgets']==[] and a['independent_check'] is None,'no false admission')
  B.require(f['refitted'] is False and f['status']==('evaluated' if accepted else 'no_candidate') and [o['X'] for o in f['observations']]==([11,13] if accepted else []),'fixed final coverage')
  if accepted:B.require(f['weights_sha256']==B.digest(r['weights']) and f['grams_sha256']==B.digest(r['grams']),'fixed weights/Grams')
  for o in f['observations']:
   b=B.build(program,o['X']);i=b['instance']
   if o['case_sha256'] is None:B.require(o['status']=='missing_resource' and o['scalar_budget'] is None and bool(o['reason']),'preparation missing');continue
   B.require(o['case_sha256']==B.digest(i) and o['scalar_budget']==B.budget(i,r['weights']),'final target/budget')
   residue=B.B.residual(i,r['weights'])
   for reg in ['parent','child']:residue=B.P.add(residue,G.gram_polynomial(r['grams'][reg],G.atom_blocks(o['X'])[reg],i['horizon']),F(-1))
   valid=all(not m for m in residue) and residue.get((),F(0))>=0
   if o['status']=='finite_PSD_certificate':G.verify_primal([i],[o['X']],dict(status='finite_PSD_certificate',weights=r['weights'],grams=r['grams'],certificates=[o['certificate']],constant_slacks=[o['scalar_budget']['scalar_slack']]))
   elif o['status']=='template_mismatch':B.require(not valid,'exact mismatch')
   else:B.require(o['status']=='missing_resource' and bool(o['reason']),'missing retained')
  diagnostics.extend(B.B.truth(B.build(program,X)) for X in [1,2,3,5,11,13])
 dr=dual['result'];critical=ats[0]['synthesis']['status']=='finite_PSD_certificate'
 if critical:B.require(dr['status']=='not_requested' and not dr['certified'] and dual['independent_check'] is None,'dual trigger')
 elif dr.get('certified'):G.verify_dual(allinstances[0],[1,2,3,5],dr)
 else:B.require(dr['status'] in ['missing_resource','uncertified'] and dual['independent_check'] is None,'unproved dual')
 receipt=B.read(d/'producer_receipt.json')
 for n in ['training','final','dual','tests','candidate_seal','source_seal']:B.require(receipt[n+'_sha256']==hashes[n],'receipt '+n)
 def flags(v):
  if isinstance(v,dict):
   for k,x in v.items():
    if k in ['global_bound_proved','RH_proved']:B.require(x is False,'global promotion')
    flags(x)
  elif isinstance(v,list):
   for x in v:flags(x)
 for v in [spec,training,final,dual,receipt]:flags(v)
 binding();B.require(hashes=={n:B.sha(d/(n+'.json')) for n in names},'end hashes')
 return dict(all_passed=True,input_sha256=hashes,training_statuses=[a['synthesis']['status'] for a in ats],final_statuses=[[o['status'] for o in f['observations']] for f in fs],dual_status=dr['status'],actual_truth_after_search=diagnostics,global_bound_proved=False,RH_proved=False)
if __name__=='__main__':
 p=Path(sys.argv[1]);r=audit(p)
 with (p/'gram-probe-001/independent_verification.json').open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
 print(json.dumps(r))
