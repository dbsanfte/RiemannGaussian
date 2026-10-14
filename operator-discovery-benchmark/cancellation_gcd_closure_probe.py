"""Posthoc old-dual and DECLARED zero-extension pairings, no bound scores.
Zero extension chooses new unconstrained moments; it does not infer their values.
"""
from fractions import Fraction as F
import json,pathlib,hashlib,math
import grouped_arithmetic_language as L

def run(directory):
 directory=pathlib.Path(directory);directory.mkdir(exist_ok=False,parents=True)
 source=pathlib.Path('cancellation-arithmetic-results/pilot-001/factor-probe-001/native-dual-001/result.json');old=json.loads(source.read_text())['dual'];y={(m['instance'],tuple(m['m'])):F(v)for m,v in zip(old['monomials'],old['weights'])};scales=[1,2,3,5]
 spec=dict(scales=scales,contexts=['parent','child'],powers=[0,1],source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),probe_source_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),extension='Explicit new functional: original coordinates unchanged; ALL new monomial coordinates assigned0. No claim that every extension has these values.',no_actual_arithmetic_responses=True)
 with (directory/'spec.json').open('x')as f:json.dump(spec,f,sort_keys=True,indent=2)
 def dot(index,p):
  missing=[list(m)for m in p if (index,m)not in y];value=sum((q*y.get((index,m),F(0))for m,q in p.items()),F(0))
  return dict(original_domain_status='unsupported'if missing else 'exact',missing_coordinates=missing,original_dot=None if missing else str(value),declared_zero_extension_dot=str(value),zero_extension_sign=(value>0)-(value<0))
 def joint(parts):
  original=all(p['original_domain_status']=='exact'for p in parts);value=sum(F(p['declared_zero_extension_dot'])for p in parts)
  return dict(original_domain_status='exact'if original else 'unsupported',original_dot=str(value)if original else None,declared_zero_extension_dot=str(value),zero_extension_sign=(value>0)-(value<0))
 records=[]
 for context in spec['contexts']:
  for power in spec['powers']:
   rows={('inverse',mask):[]for mask in ('unit','nonunit')}
   rows.update({(kind,mask,sign):[]for kind in ('localizer','half_square','padding','norm_closure')for mask in ('unit','nonunit')for sign in (-1,1)})
   for index,X in enumerate(scales):
    H=4*X-1;polys={key:{}for key in rows};ts=range(X,2*X)if context=='parent'else range(2*X,4*X)
    for t in ts:
     # COMPLETE pair source, no product index or ab restriction.
     for a in range(1,t+1):
      for b in range(1,t+1):
       g=math.gcd(a,b);mask='unit'if g==1 else 'nonunit';weight=F(a*b,t*t)**power;rho=dict(kind='unit')if g==1 else dict(kind='inverse_row',n=g);p=L.mul(L.relation(rho,'mu',H),{tuple(sorted((a,b))):weight});polys['inverse',mask]=L.add(polys['inverse',mask],p)
     for d in range(1,t+1):
      mask='unit'if d==1 else 'nonunit';linear={(a,):F(a,t)**power for a in range(d,t+1,d)};square=L.mul(linear,linear);factors=L.factor_witness(d);h=int(all(e==1 for p,e in factors));norm=L.relation(dict(kind='norm',n=d,factors=factors),'mu',H);closure=L.mul(norm,square)
      for sign in (-1,1):
       localizer=L.add(square,L.scale(L.mul(L.variable(d),square),sign));form=L.mul(L.add(L.constant(1),L.scale(L.variable(d),sign)),linear);halfsquare=L.scale(L.mul(form,form),F(1,2));padding=L.scale(square,F(1-h,2));normpiece=L.scale(closure,F(-1,2))
       if localizer!=L.add(halfsquare,padding,normpiece):raise ValueError('exact localizer closure mismatch')
       for kind,p in [('localizer',localizer),('half_square',halfsquare),('padding',padding),('norm_closure',closure)]:polys[kind,mask,sign]=L.add(polys[kind,mask,sign],p)
    for key,p in polys.items():rows[key].append(dict(X=X,polynomial_sha256=hashlib.sha256(json.dumps(L.dump_poly(p),sort_keys=True,separators=(',',':')).encode()).hexdigest(),pairing=dot(index,p)))
   for key,parts in rows.items():records.append(dict(context=context,power=power,kind=key[0],mask=key[1],sign=key[2]if len(key)>2 else None,parts=parts,joint_pairing=joint([p['pairing']for p in parts])))
 summary=dict(records=len(records),original_supported_nonzero=sum(r['joint_pairing']['original_domain_status']=='exact'and r['joint_pairing']['zero_extension_sign']!=0 for r in records),zero_extension_nonzero_inverse=sum(r['kind']=='inverse'and r['joint_pairing']['zero_extension_sign']!=0 for r in records),zero_extension_negative_half_squares=sum(r['kind']=='half_square'and r['joint_pairing']['zero_extension_sign']<0 for r in records),unsupported_joint_columns=sum(r['joint_pairing']['original_domain_status']=='unsupported'for r in records))
 report=dict(spec=spec,records=records,summary=summary,closure_coefficient_identities_verified=True,all_scalar_contributions_zero=True,scope='old witness/one chosen extension only; neither feasibility nor all-extension obstruction is concluded',global_bound_proved=False,RH_proved=False)
 with (directory/'results.json').open('x')as f:json.dump(report,f,sort_keys=True,indent=2)
 return report
if __name__=='__main__':
 import sys
 print(json.dumps(run(sys.argv[1])['summary']))
