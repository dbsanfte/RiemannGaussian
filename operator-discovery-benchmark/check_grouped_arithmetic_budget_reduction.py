"""Independent posthoc nonnegative-padding reduction audit."""
import json,hashlib
from pathlib import Path
from fractions import Fraction as F
from check_grouped_arithmetic_run import descriptors,residual
from check_grouped_arithmetic import verify_certificate,verify_joint_result

def require(x,msg):
 if not x:raise ValueError(msg)
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def reduce(weights):
 d=descriptors();sw=list(map(F,weights['square_weights']));rw=list(map(F,weights['relation_weights']));require(all(v>=0 for v in sw),'square weights');ledger=[]
 if sw[0]:ledger.append(dict(kind='constant_square',square_id=d['square'][0]['id'],alpha=str(sw[0]),removed_scalar='alpha*X^2*ceil(X^(1/q))'));sw[0]=F(0)
 for i,s in enumerate(d['square']):
  if s['family']!='coordinate' or s['weight'] not in ('one','X'):continue
  for j,r in enumerate(d['relation']):
   if r['family']=='norm' and r['multiplier']=='one' and r['region']==s['region'] and r['weight']==s['weight']:
    alpha=min(sw[i],max(F(0),-rw[j]))
    if alpha:
     sw[i]-=alpha;rw[j]+=alpha;ledger.append(dict(kind='coordinate_norm',square_id=s['id'],relation_id=r['id'],alpha=str(alpha),region=s['region'],weight=s['weight'],removed_scalar='alpha*sum_region W(n)*h_n >= 0'))
 return dict(square_weights=list(map(str,sw)),relation_weights=list(map(str,rw))),ledger

def audit(directory,pilot):
 d=Path(directory);pilot=Path(pilot);spec=read(d/'spec.json');out=read(d/'results.json');original={n:sha(d/n) for n in ('spec.json','results.json')};require(out['spec_sha256']==original['spec.json'],'reduction spec binding');require(sha(d/'frozen_source.py')==spec['source_sha256'],'utility source binding')
 for name,h in spec['input_sha256'].items():require(sha(pilot/name)==h,'pilot input binding')
 for name,h in spec['dependency_sha256'].items():require(sha(Path(__file__).parent/name)==h,'dependency binding')
 train=read(pilot/'training.json');final=read(pilot/'final.json');require([r['program'] for r in out['rows']]==[a['program'] for a in train['attempts']],'all statuses retained');summaries=[]
 for row,attempt in zip(out['rows'],train['attempts']):
  syn=attempt['synthesis']
  if syn['status']!='finite_certificate':require(row['status']=='unchanged_nonfinite' and row['original_status']==syn['status'],'unchanged failure');continue
  require(row['original_weights']==syn['weights'],'original weights');weights,ledger=reduce(syn['weights']);require(row['reduction']['weights']==weights and row['reduction']['ledger']==ledger,'exact reduction rules')
  builds=attempt['instances'][:]
  for f in final['results']:
   if f['program']==attempt['program']:builds.extend(o['instance'] for o in f['observations'])
  require([o['X'] for o in row['observations']]==[b['X'] for b in builds],'full observation coverage')
  verified=0
  for b,o in zip(builds,row['observations']):
   old=residual(b['instance'],syn['weights']);new=residual(b['instance'],weights);require({m:v for m,v in old.items() if m}=={m:v for m,v in new.items() if m},'nonconstant identity changed');reduction=new.get((),F(0))-old.get((),F(0));require(reduction>=0,'budget increased')
   if o['status']=='finite_verified':
    require(not any(m for m in new) and new.get((),F(0))>=0,'invalid reduced finite identity');verify_joint_result([b['instance']],dict(status='finite_certificate',weights=weights,certificates=[o['certificate']],constant_slacks=[str(new.get((),F(0)))]),allow_constant_slack=True);require(o['certificate']['lhs']==b['instance']['lhs'],'reduced full lhs');require(F(o['budget']['B'])==F(b['D'])-new.get((),F(0)) and F(o['budget']['scalar_slack'])==new.get((),F(0)),'scalar budget extraction');verified+=1
   else:require(o['status']=='rejected_or_missing' and isinstance(o.get('reason'),str),'explicit failure/missing')
  summaries.append(dict(program=row['program'],reduction_rules=len(ledger),finite_verified=verified,observations=len(builds),remaining_weights_sha256=digest(weights)))
 require({n:sha(d/n) for n in original}==original,'reduction artifacts changed')
 for name,h in spec['dependency_sha256'].items():require(sha(Path(__file__).parent/name)==h,'dependencies changed')
 return dict(verified=True,all_programs_retained=True,accepted_programs=summaries,universal_rule_scope='nonnegative scalar padding removal only; full signed critical estimate unproved',input_sha256=original,global_bound_proved=False,RH_proved=False)
