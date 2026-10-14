"""Conditional ordinary-zeta bridge for fixed sparse actual arithmetic filters.
No fitted data, zero-location assumption, or critical estimate is supplied.
"""
from fractions import Fraction
from math import comb

def _integer(n,minimum=0):
 if type(n) is not int or n<minimum:raise ValueError('integer outside domain')
 return n

def _rational(x):
 if isinstance(x,(bool,float)):raise ValueError('exact rational required; bool/float forbidden')
 if not isinstance(x,(int,str,Fraction)):raise ValueError('exact integer, rational string or Fraction required')
 return Fraction(x)

def canonical_filter(terms):
 """Terms {divisor:d,weight:w}, or (d,w); exact merge then delete zeros."""
 weights={}
 for t in terms:
  if isinstance(t,dict):
   if set(t)!={'divisor','weight'}:raise ValueError('only fixed divisor and exact weight fields supported')
   d,w=t['divisor'],t['weight']
  elif isinstance(t,(tuple,list)) and len(t)==2:d,w=t
  else:raise ValueError('fixed filter term required')
  _integer(d,1);weights[d]=weights.get(d,Fraction(0))+_rational(w)
 return [dict(divisor=d,weight=str(w)) for d,w in sorted(weights.items()) if w]

def certify(r,l,terms):
 """Certify implication ONLY for the complete actual mu^*r * lambda^*l target."""
 try:
  _integer(r);_integer(l);k=r+l
  if not k:raise ValueError('positive total convolution arity required')
  terms=list(terms)
  if any(isinstance(t,dict) and (set(t)!={'divisor','weight'} or isinstance(t.get('divisor'),(dict,list,tuple)) or callable(t.get('divisor'))) for t in terms):
   return dict(schema=1,status='unsupported',reason='only fixed integer divisor filters supported; moving/other semantics not certified',conditional_bridge_admitted=False,estimate_proved=False,RH_proved=False)
  normalized=canonical_filter(terms);m=len(normalized)
  result=dict(schema=1,target=dict(mu_arity=r,liouville_arity=l,total_arity=k,sequence='actual complete Dirichlet convolution mu^{*r}*lambda^{*l}',dirichlet_series='zeta(2s)^l/zeta(s)^(r+l)',prefix='A(x)=sum_(n<=x)a(n)'),filter=normalized,support_size=m,filter_semantics='G(x)=sum_j w_j A(floor(x/d_j)); fixed positive integer d_j',estimate_proved=False,RH_proved=False,conditional_bridge_admitted=False)
  if not m:return dict(result,status='unsupported',reason='zero filter has no pole information')
  if m>k:return dict(result,status='unsupported',reason='support exceeds sufficient pole budget; no mathematical refutation',maximum_filter_zero_multiplicity=m-1)
  return dict(result,status='admitted_conditional',reason=None,conditional_bridge_admitted=True,maximum_filter_zero_multiplicity=m-1,minimum_surviving_pole_order=k-m+1,
   premise='There exists integer q0>=1 such that every integer q>=q0 admits finite Kq>=0 independent of dyadic X>=1 with sum_(n=X)^(2X-1)|G(n)|^2<=Kq X^(2+1/q).',
   implication='The complete filtered critical-energy premise excludes ordinary zeta zeros with Re(s)>1/2 and implies RH.',
   proof_mechanism='Distinct real logarithms yield invertible derivative Vandermonde through order m-1; any zero of the nonzero filter multiplier has multiplicity at most m-1. Actual numerator zeta(2s)^l is zero-free in Re(s)>1/2.')
 except (ValueError,TypeError,ZeroDivisionError,KeyError) as e:return dict(schema=1,status='invalid',reason=str(e),conditional_bridge_admitted=False,estimate_proved=False,RH_proved=False)

def _convolution(a,b,N,charge):
 out=[0]*(N+1);charge(N+1)
 for i in range(1,N+1):
  if a[i]:
   for j in range(1,N//i+1):charge(1);out[i*j]+=a[i]*b[j]
 return out

def actual_coefficients(N,r,l,*,work_budget=10000000):
 """Complete actual primitives via prime sieve; no truncation on budget failure."""
 used=0
 try:
  _integer(N,1);_integer(r);_integer(l);_integer(work_budget)
  if r+l<1:raise ValueError('positive total arity required')
  def charge(n):
   nonlocal used
   if used+n>work_budget:raise OverflowError('work budget exceeded')
   used+=n
  charge(5*(N+1));mu=[0]+[1]*N;lam=[0]+[1]*N;prime=[True]*(N+1)
  for p in range(2,N+1):
   charge(1)
   if not prime[p]:continue
   for n in range(p,N+1,p):charge(1);mu[n]*=-1
   for n in range(2*p,N+1,p):charge(1);prime[n]=False
   for n in range(p*p,N+1,p*p):charge(1);mu[n]=0
   power=p
   while power<=N:
    for n in range(power,N+1,power):charge(1);lam[n]*=-1
    power*=p
  a=[0]*(N+1);a[1]=1
  for source,count in ((mu,r),(lam,l)):
   for _ in range(count):a=_convolution(a,source,N,charge)
  return dict(status='available',coefficients=a,cost=used,lookahead=N,cost_scope='scalar/list work proxy; not coefficient bit complexity',coefficient_bit_complexity_certified=False,provenance='complete prime sieve, complete product-loop Dirichlet convolution',estimate_proved=False,RH_proved=False)
 except OverflowError as e:return dict(status='missing',coefficients=None,cost=used,reason=str(e),estimate_proved=False,RH_proved=False)
 except (ValueError,TypeError) as e:return dict(status='invalid',coefficients=None,cost=used,reason=str(e),estimate_proved=False,RH_proved=False)

def filtered_prefix(coefficients,terms):
 """Evaluate every filtered prefix through the supplied complete horizon."""
 terms=canonical_filter(terms);a=[_rational(x) for x in coefficients]
 if not a or a[0]:raise ValueError('zero index sentinel required')
 P=[Fraction(0)]*len(a)
 for n in range(1,len(a)):P[n]=P[n-1]+a[n]
 return [sum((_rational(t['weight'])*P[n//t['divisor']] for t in terms),Fraction(0)) for n in range(len(a))]

def sharpness_filter(k,base=2,amplitude=1):
 """Multiplier (1-amplitude*base^-s)^k: k+1 terms, k-fold zeros."""
 _integer(k,1);_integer(base,2);_integer(amplitude,1)
 return [dict(divisor=base**j,weight=str((-amplitude)**j*comb(k,j))) for j in range(k+1)]
