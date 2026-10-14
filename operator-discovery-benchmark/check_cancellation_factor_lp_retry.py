"""Independent fixed-zero-Gram factor LP retry audit."""
import json,sys,re
from pathlib import Path
from fractions import Fraction as F
import check_cancellation_arithmetic_run as I
import check_cancellation_factor_search as Z
import check_cancellation_factor_search_run as PREV
import check_grouped_arithmetic as G
OWN=['run_cancellation_factor_lp_retry.py','test_run_cancellation_factor_lp_retry.py','check_cancellation_factor_lp_retry.py','test_check_cancellation_factor_lp_retry.py']
TESTS=['test_run_cancellation_factor_lp_retry','test_check_cancellation_factor_lp_retry']
def verify_attempt(a,program,scales):
 I.require(a['program']==program and a['dictionary_sha256']==I.digest(Z.descriptors()) and a['grams_fixed_zero'] is True,'fixed program/dictionary/subcone')
 built=[Z.build(program,X) for X in scales];instances=[b['instance'] for b in built]+([Z.auxiliary()['instance']] if program['constraint']=='zero_cubic' else [])
 if a['case_hashes']:I.require(a['case_hashes']==list(map(I.digest,instances)) and a['factor_archive_hashes']==[I.digest(b['factor_archive']) for b in built],'complete cases/archive')
 else:I.require(a['factor_archive_hashes']==[] and a['synthesis']['status']!='finite_certificate','preparation failure')
 r=a['synthesis'];G.verify_joint_result(instances,r,allow_constant_slack=True)
 if r['status']=='finite_certificate':
  I.require(a.get('proposed_synthesis')==r,'accepted original proposal');gamma=sum((F(c)*F(w)for c,w in zip(Z.auxiliary()['gamma_coefficients'],r['weights']['relation_weights'])),F(0));I.require(a['gamma']==str(gamma) and (program['constraint']!='zero_cubic' or gamma==0),'gamma')
 else:I.require(a['gamma'] is None,'no false gamma')
 return instances

def audit(parent):
 parent=Path(parent);d=parent/'lp-retry-001';names=['protocol','source_seal','seal','tests','training','candidate_seal','final','producer_receipt'];hashes={n:I.sha(d/(n+'.json')) for n in names};p=I.read(d/'protocol.json');source=I.read(d/'source_seal.json');expected_sources=sorted(set(PREV.EXTRA+OWN));previous=I.read(parent/'protocol.json')
 def binding():
  I.require(p['source_names']==expected_sources and set(source['hashes'])==set(expected_sources),'complete frozen sources')
  I.require(I.read(d/'seal.json')==dict(protocol_sha256=I.sha(d/'protocol.json'),source_seal_sha256=I.sha(d/'source_seal.json')),'source/protocol seal')
  for n,h in source['hashes'].items():I.require(I.sha(d/'frozen_source'/n)==h and I.sha(Path(__file__).parent/n)==h,'source '+n)
  inputs={n:parent/n for n in ['protocol.json','seal.json','source_seal.json','training.json','independent_verification.json']};inputs['supplied_embedding_audit']=Path(__file__).parent/'cancellation_factor_unsigned_embedding_audit.json';I.require(p['inputs_sha256']=={n:I.sha(v) for n,v in inputs.items()},'parent inputs');I.require(I.read(parent/'independent_verification.json')['all_passed'] is True,'verified parent')
 binding();I.require(p['programs']==previous['programs'] and p['training_scales']==[1,2,3,5] and p['final_scales']==[7,11] and p['limits']==dict(previous['limits'],time_limit=180) and p['tests']==TESTS and p['dictionary_sha256']==I.digest(Z.descriptors()) and p['runtime']==previous['runtime'],'known contract')
 for flag in ['grams_fixed_zero','constant_slack_allowed','original_results_preserved','no_actual_signed_responses']:I.require(p[flag] is True,'protocol '+flag)
 I.require(p['final_refit'] is False,'no refit');test=I.read(d/'tests.json');I.require(test['returncode']==0 and re.search(r'Ran \d+ tests? in .*\n\s*OK\s*$',test['stdout']+test['stderr']),'tests passed')
 training=I.read(d/'training.json');final=I.read(d/'final.json');ats=training['attempts'];fs=final['results'];I.require(len(ats)==len(fs)==2 and final['refitted'] is False,'full attempts');I.require(I.read(d/'candidate_seal.json')==dict(training_sha256=hashes['training'],protocol_sha256=hashes['protocol']),'candidate seal');truth=[]
 for j,(program,a,f) in enumerate(zip(p['programs'],ats,fs)):
  I.require(a==I.read(d/'attempts'/f'{j:03d}.json'),'checkpoint');verify_attempt(a,program,p['training_scales']);r=a['synthesis'];accepted=r['status']=='finite_certificate';I.require(f['refitted'] is False and f['status']==('evaluated'if accepted else 'no_candidate') and [o['X']for o in f['observations']]==([7,11]if accepted else []),'complete no-refit finals')
  if accepted:I.require(f['weights_sha256']==I.digest(r['weights']),'fixed learned weights')
  for o in f['observations']:
   b=Z.build(program,o['X']);instance=b['instance']
   if o['case_sha256'] is None:I.require(o['factor_archive_sha256'] is None and o['status']=='missing_resource' and bool(o['reason']) and 'certificate'not in o,'preparation missing');continue
   I.require(o['case_sha256']==I.digest(instance) and o['factor_archive_sha256']==I.digest(b['factor_archive']) and o['scalar_budget']==I.budget(instance,r['weights']),'final complete bindings');res=I.B.residual(instance,r['weights']);valid=all(not m for m in res) and res.get((),F(0))>=0
   if o['status']=='finite_certificate':G.verify_joint_result([instance],dict(status='finite_certificate',weights=r['weights'],certificates=[o['certificate']],constant_slacks=[o['scalar_budget']['scalar_slack']]),allow_constant_slack=True)
   elif o['status']=='template_mismatch':I.require(not valid,'exact mismatch witness')
   else:I.require(o['status']=='missing_resource' and bool(o['reason']),'resource missing')
  truth.extend(I.B.truth(Z.build(program,X)) for X in [1,2,3,5,7,11])
 receipt=I.read(d/'producer_receipt.json');I.require(receipt['files_sha256']=={n+'.json':hashes[n] for n in names if n!='producer_receipt'},'receipt files')
 def flags(v):
  if isinstance(v,dict):
   for k,x in v.items():
    if k in ['global_bound_proved','RH_proved']:I.require(x is False,'global promotion')
    flags(x)
  elif isinstance(v,list):
   for x in v:flags(x)
 for v in [p,training,final,receipt]:flags(v)
 binding();I.require(hashes=={n:I.sha(d/(n+'.json'))for n in names},'end input hashes')
 return dict(all_passed=True,input_sha256=hashes,training_statuses=[a['synthesis']['status']for a in ats],final_statuses=[[o['status']for o in f['observations']]for f in fs],grams_fixed_zero=True,actual_truth_after_search=truth,original_resource_results_preserved=True,global_bound_proved=False,RH_proved=False)
if __name__=='__main__':
 p=Path(sys.argv[1]);r=audit(p)
 with (p/'lp-retry-001/independent_verification.json').open('x')as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
 print(json.dumps(r))
