"""Supplied complete weighted inverse-row coupling; identities only, no bound search."""
from fractions import Fraction as F
import hashlib,json
import grouped_arithmetic_language as L

def digest(value):
 return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def build_coupling(horizon,weights,*,target='mu',max_horizon=128,max_operations=20000000,max_terms=10000,max_coefficient_bits=4096):
 for v in (horizon,max_horizon,max_operations,max_terms,max_coefficient_bits):
  if type(v)is not int or v<1:raise ValueError('positive strict limits')
 if target!='mu':raise ValueError('inverse-of-ones coupling is mu-specific')
 H=horizon
 if H>max_horizon or H*H>max_operations:raise OverflowError('complete source preflight')
 if type(weights)is not list or len(weights)!=H:raise ValueError('complete weights required')
 qs=[]
 for value in weights:
  if type(value)is not str or len(value)>2*max_coefficient_bits+3 or any(c not in '-0123456789/'for c in value):raise ValueError('canonical rational weights')
  q=F(value)
  if str(q)!=value:raise ValueError('canonical rational weights')
  if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('weight bits')
  qs.append(q)
 used=0
 def checked(p):
  if len(p)>max_terms:raise OverflowError('polynomial terms')
  if any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in p.values()):raise OverflowError('polynomial coefficient bits')
  return p
 def charge(n):
  nonlocal used
  used+=n
  if used>max_operations:raise OverflowError('coupling work')
 def add(*ps):
  charge(sum(map(len,ps)));return checked(L.add(*ps))
 def mul(p,q):
  charge(len(p)*len(q));return checked(L.mul(p,q,max_terms=max_terms,max_operations=max_operations))
 B={};pairs=[];blocks=[]
 for a,w in enumerate(qs,1):
  divisors=[]
  for d in range(1,a+1):
   charge(1)
   if a%d==0:
    pairs.append([a,d]);divisors.append(d)
    if w:B=add(B,{tuple(sorted((a,d))):w})
  blocks.append(dict(a=a,weight=str(w),divisors=divisors))
 c=qs[0];factor=add(B,L.constant(c))
 normalization=[];closure=[]
 for a,w in enumerate(qs,1):
  if a==1:
   spec=dict(kind='unit');mult=checked(L.scale(add(L.variable(1),L.constant(1)),w))
  else:
   spec=dict(kind='inverse_row',n=a);mult=checked(L.scale(L.variable(a),w))
  normalization.append(dict(spec=spec,multiplier=L.dump_poly(mult)))
  closure.append(dict(spec=spec,multiplier=L.dump_poly(mul(mult,factor))))
 normal_lhs=add(B,L.constant(-c));square=mul(B,B);scalar=checked(L.constant(-c*c));square_lhs=add(square,scalar)
 # Exact matching here; independently checkable flattened certificates retained.
 for lhs,rels in ((normal_lhs,normalization),(square_lhs,closure)):
  rebuilt={}
  for term in rels:
   rho=L.relation(term['spec'],'mu',H,max_operations=max_operations);rebuilt=add(rebuilt,mul(L.load_poly(term['multiplier']),rho))
  if rebuilt!=lhs:raise ValueError('complete coefficient identity mismatch')
 def cert(lhs,rels):return dict(target='mu',horizon=H,lhs=L.dump_poly(lhs),squares=[],relations=rels)
 return dict(target='mu',horizon=H,weights=weights.copy(),weights_sha256=digest(weights),
  B=L.dump_poly(B),c=str(c),square_polynomial=L.dump_poly(square),scalar_minus_c_squared=L.dump_poly(scalar),
  normalization_certificate=cert(normal_lhs,normalization),square_closure_certificate=cert(square_lhs,closure),
  source=dict(pairs=pairs,pairs_sha256=digest(pairs),pair_count=len(pairs),blocks=blocks,
              source_domain='all 1<=a<=H and d|a; zero weights retained',complete=True),
  formal_identities_verified=True,arithmetic_values_substituted=False,square_is_bound_certificate=False,
  cost=dict(operations=used,max_operations=max_operations,max_terms=max_terms,max_coefficient_bits=max_coefficient_bits),
  scope='supplied weighted Mobius inverse-row identity; cross-divisor square terms complete; no critical estimate',
  global_bound_proved=False,RH_proved=False)
