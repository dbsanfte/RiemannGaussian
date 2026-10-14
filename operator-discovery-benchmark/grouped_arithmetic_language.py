"""Factor-certified norm/gcd relations; finite exact positivity only."""
from math import gcd,isqrt
import arithmetic_cycle_language as base
add=base.add
mul=base.mul
scale=base.scale
variable=base.variable
constant=base.constant
load_poly=base.load_poly
dump_poly=base.dump_poly
evaluate=base.evaluate
DEFAULT_OPERATIONS=1000000
DEFAULT_HORIZON=1000000

def integer(n,minimum=1):
 if type(n)is not int or n<minimum:raise ValueError('strict integer domain')
 return n

class Budget:
 def __init__(self,limit):self.limit=integer(limit);self.used=0
 def charge(self,n=1):
  self.used+=n
  if self.used>self.limit:raise OverflowError('factor/relation work budget')

def factor_witness(n,*,max_operations=DEFAULT_OPERATIONS,max_n=DEFAULT_HORIZON):
 integer(n);integer(max_n)
 if n>max_n:raise OverflowError('factor source horizon cap')
 b=Budget(max_operations);out=[];m=n;p=2
 while p*p<=m:
  b.charge();e=0
  while m%p==0:b.charge();m//=p;e+=1
  if e:out.append([p,e])
  p+=1
 if m>1:out.append([m,1])
 return out

def _factors(n,factors,b):
 if type(factors)is not list:raise ValueError('factor list')
 previous=1;product=1;out={}
 for item in factors:
  if type(item)is not list or len(item)!=2:raise ValueError('factor pair list')
  p,e=item;integer(p,2);integer(e)
  if p<=previous or p>n:raise ValueError('sorted unique factors in domain')
  previous=p
  if e>=n.bit_length():raise ValueError('factor exponent exceeds product')
  # Bound materialization before pow; exact product cannot exceed declared n.
  if e*p.bit_length()>b.limit:raise OverflowError('factor power bit/work budget')
  b.charge(e*p.bit_length())
  for d in range(2,isqrt(p)+1):
   b.charge()
   if p%d==0:raise ValueError('nonprime factor')
  power=pow(p,e)
  if power>n//product:raise ValueError('factor product exceeds n')
  product*=power;out[p]=e
 if product!=n:raise ValueError('incomplete factorization')
 return out

def _relation(spec,target,H,b):
 integer(H)
 if type(target)is not str or target not in ('mu','c') or type(spec)is not dict:raise ValueError('relation domain')
 kind=spec.get('kind')
 if kind=='norm' and set(spec)=={'kind','n','factors'}:
  n=integer(spec['n'])
  if n>H:raise ValueError('norm horizon')
  f=_factors(n,spec['factors'],b);value=int(all(e==1 for e in f.values())) if target=='mu' else 4**len(f)
  return add(mul(variable(n),variable(n)),constant(-value))
 if kind=='gcd_product' and set(spec)=={'kind','a','b','factors_a','factors_b'}:
  a=integer(spec['a']);c=integer(spec['b'])
  if max(a,c)>H:raise ValueError('gcd horizon')
  fa=_factors(a,spec['factors_a'],b);fb=_factors(c,spec['factors_b'],b);g=gcd(a,c);u=a//g;v=c//g
  fg={p:min(e,fb.get(p,0)) for p,e in fa.items() if p in fb};overlap=sum(1 for p,e in fg.items() if fa.get(p,0)!=fb.get(p,0));left=mul(variable(a),variable(c))
  if target=='mu':
   sq=all(e==1 for e in fg.values());compatible=overlap==0
   return add(left,scale(mul(variable(u),variable(v)),-int(sq and compatible)))
  right=mul(mul(variable(g),variable(g)),mul(variable(u),variable(v)))
  return add(scale(left,2**overlap),scale(right,-1))
 # Frozen old relations remain the only remaining admissions.
 kindwork=1
 if kind=='inverse_row':kindwork=integer(spec.get('n'))
 elif kind=='squarefree_zero':kindwork=isqrt(integer(spec.get('n')))+1
 elif kind=='prime_power':kindwork=isqrt(integer(spec.get('p')))+1
 b.charge(kindwork)
 return base.relation(spec,target,H,max_operations=b.limit)

def relation(spec,target,horizon,*,max_operations=DEFAULT_OPERATIONS,max_horizon=DEFAULT_HORIZON):
 integer(horizon);integer(max_horizon)
 if horizon>max_horizon:raise OverflowError('relation horizon cap')
 return _relation(spec,target,horizon,Budget(max_operations))

def compile_certificate(cert,*,max_terms=100000,max_operations=DEFAULT_OPERATIONS,max_horizon=DEFAULT_HORIZON):
 integer(max_terms);integer(max_horizon);budget=Budget(max_operations)
 if type(cert)is not dict or set(cert)!={'target','horizon','lhs','squares','relations'}:raise ValueError('certificate schema')
 H=integer(cert['horizon']);target=cert['target']
 if H>max_horizon:raise OverflowError('certificate horizon cap')
 if type(target)is not str or target not in ('mu','c') or type(cert['squares'])is not list or type(cert['relations'])is not list:raise ValueError('certificate domain')
 def parse(p):
  p=load_poly(p);budget.charge(len(p))
  if len(p)>max_terms:raise OverflowError('polynomial terms')
  if any(i>H for m in p for i in m):raise ValueError('polynomial horizon')
  return p
 lhs=parse(cert['lhs']);rhs={}
 def product(a,b):
  budget.charge(len(a)*len(b));return mul(a,b,max_terms=max_terms,max_operations=max_operations)
 def merge(p):
  nonlocal rhs
  budget.charge(len(rhs)+len(p));rhs=add(rhs,p)
  if len(rhs)>max_terms:raise OverflowError('expanded terms')
 for s in cert['squares']:
  if type(s)is not dict or set(s)!={'weight','poly'} or type(s['weight'])is not str:raise ValueError('square schema')
  w=base._q(s['weight'])
  if w<0 or str(w)!=s['weight']:raise ValueError('nonnegative canonical weight')
  p=parse(s['poly']);merge(scale(product(p,p),w))
 for r in cert['relations']:
  if type(r)is not dict or set(r)!={'spec','multiplier'}:raise ValueError('relation schema')
  p=parse(r['multiplier']);q=_relation(r['spec'],target,H,budget);merge(product(p,q))
 if lhs!=rhs:raise ValueError('coefficient identity mismatch')
 return dict(finite_identity_verified=True,conditional_finite_nonnegativity=True,target=target,horizon=H,coefficient_matching_exact=True,operations=budget.used,identity_terms=len(lhs),square_count=len(cert['squares']),relation_count=len(cert['relations']),actual_all_scale_signed_bound_proved=False,global_bound_proved=False,RH_proved=False,scope='finite factor-certified arithmetic identity; no uniform estimate')
