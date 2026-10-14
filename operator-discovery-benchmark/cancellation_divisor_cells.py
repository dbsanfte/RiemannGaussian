"""Complete structural divisor split and prefix coupling; no bound scores.
Weights are exact symbolic input, never actual sign-response arrays.
"""
from fractions import Fraction as F
import grouped_arithmetic_language as L
import cancellation_divisor_coupling as C
from cancellation_factor_blocks import floor_scaled_power

def build_cells(horizon,weights,partition,*,target='mu',max_horizon=128,max_operations=20000000,max_terms=10000,max_coefficient_bits=4096,max_exponent=64):
 if type(partition)is not dict or set(partition)!={'kind','coefficient','power'} or partition['kind']!='divisor_le':raise ValueError('structural divisor partition')
 if type(max_exponent)is not int or max_exponent<1:raise ValueError('positive exponent limit')
 base=C.build_coupling(horizon,weights,target=target,max_horizon=max_horizon,max_operations=max_operations,max_terms=max_terms,max_coefficient_bits=max_coefficient_bits)
 cutoff=floor_scaled_power(horizon,{k:partition[k]for k in ('coefficient','power')},max_exponent=max_exponent,max_bits=max_coefficient_bits)
 used=base['cost']['operations']
 def checked(p):
  if len(p)>max_terms:raise OverflowError('cell polynomial terms')
  if any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in p.values()):raise OverflowError('cell coefficient bits')
  return p
 def charge(n):
  nonlocal used
  used+=n
  if used>max_operations:raise OverflowError('cell expansion work')
 def add(*ps):charge(sum(map(len,ps)));return checked(L.add(*ps))
 def scale(p,q):charge(len(p));return checked(L.scale(p,q))
 def mul(p,q):charge(len(p)*len(q));return checked(L.mul(p,q,max_terms=max_terms,max_operations=max_operations))
 inside={};outside={};ip=[];op=[]
 for a,d in base['source']['pairs']:
  w=F(weights[a-1]);dest=inside if d<=cutoff else outside
  (ip if d<=cutoff else op).append([a,d])
  if w:
   p={tuple(sorted((a,d))):w};merged=add(dest,p);dest.clear();dest.update(merged)
 B=L.load_poly(base['B']);c=F(base['c']);P={(a,):F(1)for a in range(1,horizon+1)}
 if add(inside,outside)!=B:raise ValueError('cell complement mismatch')
 Z=add(B,L.constant(-c));D=scale(add(inside,scale(outside,-1),L.constant(-c)),F(1,2));Dprime=add(inside,L.constant(-c))
 if add(D,scale(Dprime,-1))!=scale(Z,F(-1,2)):raise ValueError('centered contrast identity')
 prim=base['normalization_certificate']['relations']
 def certificate(lhs,U):
  terms=[dict(spec=term['spec'],multiplier=L.dump_poly(mul(L.load_poly(term['multiplier']),U)))for term in prim]
  rebuilt={}
  for term in terms:
   rho=L.relation(term['spec'],'mu',horizon,max_operations=max_operations)
   rebuilt=add(rebuilt,mul(rho,L.load_poly(term['multiplier'])))
  if lhs!=rebuilt:raise ValueError('cell complete primitive closure mismatch')
  return dict(target='mu',horizon=horizon,lhs=L.dump_poly(lhs),squares=[],relations=terms)
 closures=[]
 for name,U in [('one',L.constant(1)),('prefix',P),('contrast',D),('normalization',Z)]:
  closures.append(dict(multiplier=name,certificate=certificate(mul(Z,U),U)))
 transports=[];squares=[]
 for sign in (-1,0,1):
  if sign==0:A=D;Aprime=Dprime;U=scale(add(D,Dprime),F(-1,2))
  else:
   A=add(P,scale(D,sign));Aprime=add(P,scale(Dprime,sign));U=scale(add(scale(P,2*sign),D,Dprime),F(-1,2))
  square=mul(A,A);difference=add(square,scale(mul(Aprime,Aprime),-1))
  transports.append(dict(sign=sign,certificate=certificate(difference,U)))
  squares.append(dict(sign=sign,poly=L.dump_poly(A),square_poly=L.dump_poly(square),formal_scalar=str(square.get((),F(0)))))
 return dict(target='mu',horizon=horizon,weights=weights.copy(),partition=partition.copy(),cutoff=cutoff,
  c=str(c),B=L.dump_poly(B),inside=L.dump_poly(inside),complement=L.dump_poly(outside),
  Z=L.dump_poly(Z),D=L.dump_poly(D),Dprime=L.dump_poly(Dprime),prefix=L.dump_poly(P),
  source=dict(full=base['source'],inside_pairs=ip,complement_pairs=op,inside_pairs_sha256=C.digest(ip),complement_pairs_sha256=C.digest(op),complete=True),
  normalization_certificate=base['normalization_certificate'],closures=closures,square_transports=transports,coupled_squares=squares,
  cost=dict(operations=used,max_operations=max_operations,max_terms=max_terms,max_coefficient_bits=max_coefficient_bits),
  formal_identities_verified=True,arithmetic_values_substituted=False,global_bound_proved=False,RH_proved=False,
  scope='supplied complete structural split; partial channels unknown; squares do not establish critical budget')
