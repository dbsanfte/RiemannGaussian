"""Independent posthoc finite-cone audit; no producer mathematics imports."""
import json,hashlib,sys
from pathlib import Path
from fractions import Fraction as F
import check_cancellation_arithmetic_run as I
import check_grouped_arithmetic as G

def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(x,msg):
 if not x:raise ValueError(msg)
def audit(parent,probe):
 parent=Path(parent);d=parent/probe;spec=read(d/'spec.json');source=read(d/'source_seal.json');seal=read(d/'seal.json');result=read(d/'result.json');receipt=read(d/'producer_receipt.json')
 paths=[d/n for n in ['spec.json','source_seal.json','seal.json','result.json','producer_receipt.json']]+[parent/n for n in ['training.json','protocol.json','source_seal.json']]
 initial={str(p):sha(p) for p in paths}
 def bindings():
  require(seal==dict(spec_sha256=sha(d/'spec.json'),source_seal_sha256=sha(d/'source_seal.json')),'probe seal')
  for n,h in source['hashes'].items():require(sha(d/'frozen_source'/n)==h and sha(Path(__file__).parent/n)==h,'probe source '+n)
  for n,h in read(parent/'source_seal.json')['hashes'].items():require(sha(parent/'frozen_source'/n)==h and sha(Path(__file__).parent/n)==h,'parent source '+n)
  require(spec['parent_training_sha256']==sha(parent/'training.json') and spec['parent_source_seal_sha256']==sha(parent/'source_seal.json'),'parent inputs')
  require(receipt['result_sha256']==sha(d/'result.json') and receipt['spec_sha256']==sha(d/'spec.json'),'receipt')
 bindings();a=read(parent/'training.json')['attempts'][26];p=a['program'];scales=read(parent/'protocol.json')['training_scales'];require(spec['attempt_index']==26 and p['constraint']=='zero_cubic' and a['synthesis']['status']=='no_certificate_found','retained failed attempt')
 instances=[I.build(p,X)['instance'] for X in scales]+[I.auxiliary_constraint(I.descriptors())['instance']]
 require(list(map(I.digest,instances))==a['case_hashes']+a['auxiliary_hashes']==result['instance_hashes'],'complete independent instances')
 dual=result['dual'];affine=None
 if dual.get('certified'):
  checked=G.verify_joint_dual(instances,dual,allow_constant_slack=True)
  y={(v['instance'],tuple(v['m'])):F(w) for v,w in zip(dual['monomials'],dual['weights'])}
  slope=F(0)
  for j,X in enumerate(scales):
   # C enters only the original scalar bound C*X^2*ceil(X^(1/q)).
   unit=dict(p,C='0');zero=I.build(unit,X)['instance'];unit['C']='1';one=I.build(unit,X)['instance']
   z=G.columns(zero)[0];o=G.columns(one)[0]
   slope+=sum((v*y[j,m] for m,v in I.P.add(o,z,F(-1)).items()),F(0))
  bdot=F(dual['lhs_dot_y']);intercept=bdot-F(p['C'])*slope
  affine={'C_coefficient':str(slope),'constant':str(intercept),'at_selected_C':str(bdot),'scope':'same fixed-q shared cone, same scales, dictionary and zero-cubic auxiliary; not actual arithmetic'}
 else:
  require(dual['status'] in ['missing_resource','uncertified'] and result['independent_finite_check'] is None,'uncertified missingness');checked=None
 require(result['global_bound_proved'] is False and result['RH_proved'] is False,'no global promotion');bindings();require(initial=={str(q):sha(q) for q in paths},'end input hashes')
 return dict(all_passed=True,probe=probe,input_sha256=initial,certified=dual.get('certified',False),status=dual['status'],finite_check=checked,affine_C=affine,original_failure_retained=True,global_bound_proved=False,RH_proved=False)
if __name__=='__main__':
 parent=Path(sys.argv[1]);probe=sys.argv[2];r=audit(parent,probe)
 with (parent/probe/'independent_verification.json').open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
 print(json.dumps({'all_passed':r['all_passed'],'status':r['status'],'affine_C':r['affine_C']}))
