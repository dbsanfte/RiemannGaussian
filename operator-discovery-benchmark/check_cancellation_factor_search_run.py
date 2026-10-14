"""Independent complete shared-Gram posthoc run audit; no producer imports."""
import sys,json,re
from pathlib import Path
from fractions import Fraction as F
import check_cancellation_arithmetic_run as B
import check_cancellation_gram as G
import check_cancellation_factor_search as Z
import check_cancellation_gram_run as OLD
NEW=['run_cancellation_factor_search.py','test_run_cancellation_factor_search.py','cancellation_factor_search_language.py','test_cancellation_factor_search_language.py','check_cancellation_factor_search.py','test_check_cancellation_factor_search.py','check_cancellation_factor_search_run.py','cancellation_factor_closure_scope.txt','cancellation_factor_search_prefreeze_review.txt']
CALIB=['cancellation_factor_blocks.py','test_cancellation_factor_blocks.py','check_cancellation_factor_blocks.py','test_check_cancellation_factor_blocks.py','cancellation_factor_block_groups.py','test_cancellation_factor_block_groups.py','run_cancellation_factor_calibration.py']
EXTRA=sorted(set(B.CODE+OLD.EXTRA+CALIB+NEW))
TESTS=['test_cancellation_factor_search_language','test_check_cancellation_factor_search','test_run_cancellation_factor_search']
LIMITS=dict(OLD.LIMITS,time_limit=180)
DUAL_LIMITS=dict(OLD.DUAL_LIMITS,time_limit=120,max_rows=1400,max_variables=60000,max_work=200000000)
def audit(parent):
 parent=Path(parent);d=parent/'factor-probe-001';names=['protocol','source_seal','seal','tests','training','candidate_seal','final','dual','producer_receipt'];hashes={n:B.sha(d/(n+'.json')) for n in names};spec=B.read(d/'protocol.json');source=B.read(d/'source_seal.json');training=B.read(d/'training.json');final=B.read(d/'final.json');dual=B.read(d/'dual.json')
 def binding():
  B.require(set(source['hashes'])==set(EXTRA),'exact extra source set')
  B.require(B.read(d/'seal.json')==dict(protocol_sha256=B.sha(d/'protocol.json'),source_seal_sha256=B.sha(d/'source_seal.json')),'source/protocol seal')
  for n,h in source['hashes'].items():B.require(B.sha(d/'frozen_source'/n)==h and B.sha(Path(__file__).parent/n)==h,'source '+n)
  for n,h in B.read(parent/'source_seal.json')['hashes'].items():B.require(B.sha(parent/'frozen_source'/n)==h and B.sha(Path(__file__).parent/n)==h,'parent source '+n)
  inputs=dict(parent_gram_verification=parent/'gram-probe-001/independent_verification.json',parent_gram_uniform=parent/'gram-probe-001/uniform_scope_independent_review.json',factor_calibration=parent.parent/'factor-calibration-001/root_verification.json',previous_manifest=parent.parent/'publication-002/manifest.json')
  B.require(spec['inputs_sha256']=={k:B.sha(p) for k,p in inputs.items()},'verified prior bindings')
  for key in ['parent_gram_verification','factor_calibration']:B.require(B.read(inputs[key])['all_passed'],'prior verified '+key)
  for n,h in B.read(inputs['previous_manifest'])['files'].items():B.require(B.sha(Path(__file__).parent/n)==h,'prior publication '+n)
 binding();programs=B.read(parent/'gram-probe-001/protocol.json')['programs']
 B.require(spec['programs']==programs and spec['training_scales']==[1,2,3,5] and spec['final_scales']==[7,11] and spec['limits']==LIMITS and spec['dual_limits']==DUAL_LIMITS and spec['tests']==TESTS and spec['factor_catalog']==Z.catalog() and spec['dictionary']==Z.descriptors(),'known contract')
 B.require(spec['historical_coefficient_overlap'] is True and spec['unseen_prime_holdout'] is False and spec['solver_byte_replay_guaranteed'] is False,'provenance');test=B.read(d/'tests.json');B.require(test['returncode']==0 and re.search(r'Ran \d+ tests? in .*\n\s*OK\s*$',test['stdout']+test['stderr']),'tests')
 ats=training['attempts'];fs=final['results'];B.require(len(ats)==len(fs)==2 and training['no_actual_signed_responses'] is True and final['refitted'] is False,'complete attempts/no responses/refit');B.require(B.read(d/'candidate_seal.json')==dict(training_sha256=hashes['training'],protocol_sha256=hashes['protocol']),'candidate seal');diagnostics=[];allinstances=[]
 for j,(program,a,f) in enumerate(zip(programs,ats,fs)):
  B.require(a==B.read(d/'attempts'/f'{j:03d}.json') and a['program']==program,'checkpoint/program');ordinary=[Z.build(program,X)['instance'] for X in [1,2,3,5]];aux=[Z.auxiliary()['instance']] if program['constraint']=='zero_cubic' else [];instances=ordinary+aux;allinstances.append(instances);r=a['synthesis'];accepted=r['status']=='finite_PSD_certificate'
  if a.get('external_resource_failure'):B.require(r['status']=='missing_resource' and a['independent_check'] is None and a['gamma'] is None and a['budgets']==[],'external missing')
  else:
   B.require(a['case_hashes']==list(map(B.digest,instances)),'full training instances')
   B.require(a['factor_archive_hashes']==[B.digest(Z.build(program,X)['factor_archive']) for X in [1,2,3,5]],'factor archives')
   B.require(a['scalar_audits']==[B.scalar_audit(i) for i in ordinary],'zero scalar audit')
  B.require(a['dictionary_sha256']==B.digest(Z.descriptors()),'dictionary binding')
  if accepted:
   G.verify_primal(instances,[1,2,3,5],r);gamma=sum((F(c)*F(w) for c,w in zip(Z.auxiliary()['gamma_coefficients'],r['weights']['relation_weights'])),F(0));B.require(a['gamma']==str(gamma) and (program['constraint']!='zero_cubic' or gamma==0),'gamma');B.require(a['budgets']==[B.budget(i,r['weights']) for i in ordinary],'budgets')
  else:B.require(r['status'] in ['missing_resource','uncertified'] and a['gamma'] is None and a['budgets']==[] and a['independent_check'] is None,'no false admission')
  B.require(f['refitted'] is False and f['status']==('evaluated' if accepted else 'no_candidate') and [o['X'] for o in f['observations']]==([7,11] if accepted else []),'fixed final coverage')
  if accepted:B.require(f['weights_sha256']==B.digest(r['weights']) and f['grams_sha256']==B.digest(r['grams']),'fixed weights/Grams')
  for o in f['observations']:
   b=Z.build(program,o['X']);i=b['instance'];B.require(o['dictionary_sha256']==B.digest(Z.descriptors()),'final dictionary')
   if o['case_sha256'] is None:B.require(o['status']=='missing_resource' and o['scalar_budget'] is None and o['factor_archive_sha256'] is None and bool(o['reason']),'preparation missing');continue
   B.require(o['case_sha256']==B.digest(i) and o['scalar_budget']==B.budget(i,r['weights']) and o['factor_archive_sha256']==B.digest(b['factor_archive']) and o['dictionary_sha256']==B.digest(Z.descriptors()),'final target/budget/archive')
   residue=B.B.residual(i,r['weights'])
   for reg in ['parent','child']:residue=B.P.add(residue,G.gram_polynomial(r['grams'][reg],G.atom_blocks(o['X'])[reg],i['horizon']),F(-1))
   valid=all(not m for m in residue) and residue.get((),F(0))>=0
   if o['status']=='finite_PSD_certificate':G.verify_primal([i],[o['X']],dict(status='finite_PSD_certificate',weights=r['weights'],grams=r['grams'],certificates=[o['certificate']],constant_slacks=[o['scalar_budget']['scalar_slack']]))
   elif o['status']=='template_mismatch':B.require(not valid,'exact mismatch')
   else:B.require(o['status']=='missing_resource' and bool(o['reason']),'missing retained')
  diagnostics.extend(B.B.truth(Z.build(program,X)) for X in [1,2,3,5,7,11])
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
 with (p/'factor-probe-001/independent_verification.json').open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
 print(json.dumps(r))
