"""Scalar structural budget ledger. Does not certify nonconstant cancellation."""
from fractions import Fraction as F
import grouped_arithmetic_templates as T
import grouped_arithmetic_language as L

def extract_budget(build,weights):
 if type(build)is not dict or type(weights)is not dict or set(weights)!={'square_weights','relation_weights'}:raise ValueError('budget schema')
 d=T.descriptors();sw=weights['square_weights'];rw=weights['relation_weights']
 if type(sw)is not list or type(rw)is not list or len(sw)!=len(d['square']) or len(rw)!=len(d['relation']):raise ValueError('weight shape')
 if any(type(w)is not str or str(F(w))!=w for w in sw+rw):raise ValueError('canonical rational weights')
 sw=list(map(F,sw));rw=list(map(F,rw))
 if any(w<0 for w in sw):raise ValueError('nonnegative square weights')
 if build['square_ids']!=[v['id'] for v in d['square']] or build['relation_ids']!=[v['id'] for v in d['relation']]:raise ValueError('dictionary mismatch')
 target=build['instance']['target'];X=build['X'];q=build['q']
 if target not in ('mu','c') or type(X)is not int or X<1 or type(q)is not int or q<1:raise ValueError('domain')
 N=4*X-1
 if N>127:raise OverflowError('budget horizon cap')
 factors={n:L.factor_witness(n,max_n=127) for n in range(1,N+1)}
 def J(n):return max(0,4*X-max(2*X,n))-4*max(0,2*X-max(X,n))
 def rowmass(n):
  a=max(2*X,n);b=4*X-1
  return (a+b)*(b-a+1)//2 if a<=b else 0
 ledger=[];B=F(0)
 def record(group_id,family,coefficient,unweighted,origin):
  nonlocal B
  contribution=coefficient*unweighted;B+=contribution
  ledger.append(dict(group_id=group_id,family=family,shared_weight=str(coefficient),unweighted_constant=str(unweighted),contribution=str(contribution),provenance=origin))
 record(d['square'][0]['id'],'constant_square',sw[0],F(X*X*T._ceilroot(X,q)),'supplied rational normalizer; no sign responses')
 for desc,w in zip(d['relation'],rw):
  if desc['multiplier']!='one' or desc['family'] not in ('norm','prime_power','unit'):continue
  total=F(0)
  indices=[1] if desc['family']=='unit' else range(1,N+1)
  for n in indices:
   if desc['region']=='head' and n>2*X or desc['region']=='tail' and n<=2*X:continue
   f=factors[n]
   if desc['family']=='prime_power' and len(f)!=1:continue
   fixed=1 if desc['weight']=='one' else X if desc['weight']=='X' else J(n) if desc['weight']=='defect_kernel' else rowmass(n)
   if desc['family']=='norm':value=int(all(e==1 for p,e in f)) if target=='mu' else 4**len(f)
   elif desc['family']=='prime_power':value=(-1 if f[0][1]==1 else 0) if target=='mu' else 2*(-1)**f[0][1]
   else:value=1
   total-=fixed*value
  record(desc['id'],desc['family'],w,total,'complete factor witnesses / actual Euler local law; no signed coefficient table')
 return dict(B=str(B),D=build['D'],scalar_slack=str(F(build['D'])-B),ledger=ledger,finite_scalar_nonnegative=F(build['D'])>=B,nonconstant_identity_verified=False,global_bound_proved=False,RH_proved=False,scope='scalar coefficient only; full structural identity and all-scale budget inequality remain separate obligations')
