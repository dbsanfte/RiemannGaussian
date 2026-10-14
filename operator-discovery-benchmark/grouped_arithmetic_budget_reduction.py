"""Posthoc universal removal of nonnegative scalar padding; no RH claim."""
from fractions import Fraction as F
import json,hashlib,pathlib
import grouped_arithmetic_templates as T
import grouped_arithmetic_budget as B

def reduce_weights(weights,*,square_ids=None,relation_ids=None):
 d=T.descriptors()
 if square_ids is not None and square_ids!=[x['id'] for x in d['square']]:raise ValueError('square dictionary IDs')
 if relation_ids is not None and relation_ids!=[x['id'] for x in d['relation']]:raise ValueError('relation dictionary IDs')
 if type(weights)is not dict or set(weights)!={'square_weights','relation_weights'}:raise ValueError('weights schema')
 sw=weights['square_weights'];rw=weights['relation_weights']
 if type(sw)is not list or type(rw)is not list or len(sw)!=52 or len(rw)!=195 or any(type(v)is not str or str(F(v))!=v for v in sw+rw):raise ValueError('canonical weight shape')
 sw=list(map(F,sw));rw=list(map(F,rw))
 if any(v<0 for v in sw):raise ValueError('square weight sign')
 ledger=[]
 if sw[0]:ledger.append(dict(kind='constant_square',square_id=d['square'][0]['id'],alpha=str(sw[0]),removed_scalar='alpha*X^2*ceil(X^(1/q))'));sw[0]=F(0)
 for i,s in enumerate(d['square']):
  if s['family']!='coordinate' or s['weight'] not in ('one','X'):continue
  for j,r in enumerate(d['relation']):
   if r['family']=='norm' and r['multiplier']=='one' and r['region']==s['region'] and r['weight']==s['weight']:
    alpha=min(sw[i],max(F(0),-rw[j]))
    if alpha:
     sw[i]-=alpha;rw[j]+=alpha
     ledger.append(dict(kind='coordinate_norm',square_id=s['id'],relation_id=r['id'],alpha=str(alpha),region=s['region'],weight=s['weight'],removed_scalar='alpha*sum_region W(n)*h_n >= 0'))
 return dict(weights=dict(square_weights=list(map(str,sw)),relation_weights=list(map(str,rw))),ledger=ledger,nonconstant_coefficients_preserved_all_X=True,budget_nonincreasing_all_X=True,global_bound_proved=False,RH_proved=False,scope='supplied algebraic reduction rules; no all-scale sign estimate')

def run(pilot,output):
 from grouped_arithmetic_synthesis import instantiate_certificate
 from check_grouped_arithmetic import verify_joint
 pilot=pathlib.Path(pilot);output=pathlib.Path(output);output.mkdir(exist_ok=False)
 source=pathlib.Path(__file__).read_bytes();(output/'frozen_source.py').write_bytes(source)
 dependencies=['grouped_arithmetic_budget_reduction.py','test_grouped_arithmetic_budget_reduction.py','grouped_arithmetic_budget.py','grouped_arithmetic_templates.py','grouped_arithmetic_synthesis.py','grouped_arithmetic_language.py','check_grouped_arithmetic.py','arithmetic_cycle_synthesis.py','arithmetic_cycle_language.py','check_arithmetic_cycle_certificate.py']
 hashes={n:hashlib.sha256(pathlib.Path(n).read_bytes()).hexdigest() for n in dependencies}
 training=json.loads((pilot/'training.json').read_text());final=json.loads((pilot/'final.json').read_text())
 spec=dict(schema=1,label='posthoc known-outcome simplification',source_sha256=hashlib.sha256(source).hexdigest(),dependency_sha256=hashes,input_sha256={n:hashlib.sha256((pilot/n).read_bytes()).hexdigest() for n in ('training.json','final.json')},rule='remove constant square and matched coordinate/norm nonnegative padding; preserve all failures',global_bound_proved=False)
 with (output/'spec.json').open('x') as f:json.dump(spec,f,sort_keys=True)
 rows=[]
 for a in training['attempts']:
  result=a['synthesis']
  if result['status']!='finite_certificate':
   rows.append(dict(program=a['program'],original_status=result['status'],status='unchanged_nonfinite',observations=[]));continue
  reduction=reduce_weights(result['weights']);observations=[]
  builds=a['instances'][:]
  for f in final['results']:
   if f['program']==a['program']:builds.extend(o['instance'] for o in f['observations'])
  for build in builds:
   try:
    budget=B.extract_budget(build,reduction['weights'])
    cert=instantiate_certificate(build['instance'],reduction['weights'],allow_constant_slack=True,time_limit=30)
    verification=verify_joint([build['instance']],**reduction['weights'],allow_constant_slack=True)
    observations.append(dict(X=build['X'],status='finite_verified',budget=budget,certificate=cert,independent_verification=verification))
   except (ValueError,OverflowError,TimeoutError) as e:observations.append(dict(X=build['X'],status='rejected_or_missing',reason=str(e)))
  rows.append(dict(program=a['program'],original_weights=result['weights'],reduction=reduction,observations=observations))
 if any(hashlib.sha256(pathlib.Path(n).read_bytes()).hexdigest()!=h for n,h in hashes.items()):raise RuntimeError('runtime source changed')
 artifact=dict(spec_sha256=hashlib.sha256((output/'spec.json').read_bytes()).hexdigest(),rows=rows,global_bound_proved=False,RH_proved=False,original_evaluations_unchanged=True)
 with (output/'results.json').open('x') as f:json.dump(artifact,f,sort_keys=True)
 return artifact
if __name__=='__main__':
 import sys
 print(json.dumps({'accepted_programs':len(run(sys.argv[1],sys.argv[2])['rows'])}))
