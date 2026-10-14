"""Whitelisted finite arithmetic polynomial certificates; stdlib only.

No actual coefficient table is an axiom. A matched certificate establishes an
identity and positivity conditional on its declared arithmetic relations only.
"""
from fractions import Fraction
from math import gcd,isqrt

DEFAULT_TERMS=100000
DEFAULT_OPERATIONS=1000000

def _int(n,minimum=1):
 if type(n)is not int or n<minimum:raise ValueError('strict integer domain')
 return n

def _q(q):
 if type(q)not in (str,int,Fraction):raise ValueError('exact rational required')
 try:return Fraction(q)
 except (ValueError,ZeroDivisionError):raise ValueError('invalid rational') from None

def _poly(p):
 if type(p)is not dict:raise ValueError('internal polynomial dict required')
 out={}
 for m,c in p.items():
  if type(m)is not tuple or any(type(i)is not int or i<1 for i in m) or tuple(sorted(m))!=m:raise ValueError('canonical monomial required')
  c=_q(c)
  if c:out[m]=c
 return out

def constant(q):
 q=_q(q);return {():q} if q else {}
def variable(n):return {(_int(n),):Fraction(1)}
def add(*polys):
 out={}
 for p in polys:
  for m,c in _poly(p).items():out[m]=out.get(m,Fraction(0))+c
 return {m:c for m,c in out.items() if c}
def scale(poly,q):
 q=_q(q);return {m:q*c for m,c in _poly(poly).items() if q*c}
def mul(a,b,*,max_terms=DEFAULT_TERMS,max_operations=DEFAULT_OPERATIONS):
 _int(max_terms);_int(max_operations);a=_poly(a);b=_poly(b)
 if len(a)*len(b)>max_operations:raise OverflowError('polynomial multiplication work limit')
 out={}
 for ma,ca in a.items():
  for mb,cb in b.items():
   m=tuple(sorted(ma+mb));out[m]=out.get(m,Fraction(0))+ca*cb
   if not out[m]:del out[m]
   if len(out)>max_terms:raise OverflowError('polynomial term limit')
 return out

def dump_poly(poly):return [dict(m=list(m),c=str(c)) for m,c in sorted(_poly(poly).items())]
def load_poly(data):
 if type(data)is not list:raise ValueError('polynomial list required')
 out={};previous=None
 for t in data:
  if type(t)is not dict or set(t)!={'m','c'} or type(t['m'])is not list or type(t['c'])is not str:raise ValueError('serialized polynomial schema')
  m=tuple(t['m']);c=_q(t['c'])
  if any(type(i)is not int or i<1 for i in m) or tuple(sorted(m))!=m or not c or str(c)!=t['c']:raise ValueError('noncanonical polynomial term')
  if previous is not None and m<=previous:raise ValueError('duplicate or unordered polynomial')
  previous=m;out[m]=c
 return out

def evaluate(poly,values):
 if type(values)is not dict:raise ValueError('index-value dict required')
 for n,v in values.items():_int(n);_q(v)
 total=Fraction(0)
 for m,c in _poly(poly).items():
  for n in m:
   if n not in values:raise ValueError('missing coefficient')
   c*=_q(values[n])
  total+=c
 return total

def _prime(p):return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
def _squarefree(n):return all(n%(d*d) for d in range(2,isqrt(n)+1))
def _horizon(p,H):
 _int(H)
 if any(n>H for m in p for n in m):raise ValueError('product/index outside declared horizon')
 return p

def relation(spec,target,horizon,*,max_operations=DEFAULT_OPERATIONS):
 _int(horizon);_int(max_operations)
 if target not in ('mu','c') or type(target)is not str or type(spec)is not dict:raise ValueError('relation domain')
 kind=spec.get('kind')
 if kind=='unit' and set(spec)=={'kind'}:p=add(variable(1),constant(-1))
 elif kind=='coprime_product' and set(spec)=={'kind','a','b'}:
  a=_int(spec['a']);b=_int(spec['b'])
  if gcd(a,b)!=1:raise ValueError('false coprime premise')
  if a*b>horizon:raise ValueError('missing product horizon')
  p=add(mul(variable(a),variable(b)),scale(variable(a*b),-1))
 elif kind=='squarefree_zero' and set(spec)=={'kind','n'}:
  n=_int(spec['n'])
  if n>horizon:raise ValueError('index outside horizon')
  if isqrt(n)>max_operations:raise OverflowError('squarefree predicate work limit')
  if target!='mu' or _squarefree(n):raise ValueError('squarefree-zero premise false')
  p=variable(n)
 elif kind=='prime_power' and set(spec)=={'kind','p','e'}:
  prime=_int(spec['p']);e=_int(spec['e'])
  if prime>horizon:raise ValueError('prime outside horizon')
  if isqrt(prime)>max_operations:raise OverflowError('prime predicate work limit')
  if not _prime(prime):raise ValueError('prime premise false')
  # Preflight before pow: p^e >=2^e.
  if e>=horizon.bit_length():raise ValueError('prime power outside horizon')
  n=pow(prime,e)
  if n>horizon:raise ValueError('prime power outside horizon')
  value=(-1 if e==1 else 0) if target=='mu' else (2 if e%2==0 else -2)
  p=add(variable(n),constant(-value))
 elif kind=='inverse_row' and set(spec)=={'kind','n'}:
  n=_int(spec['n'])
  if target!='mu' or n>horizon:raise ValueError('inverse-row domain')
  if n>max_operations:raise OverflowError('inverse row work limit')
  p=add(*(variable(d) for d in range(1,n+1) if n%d==0),constant(-int(n==1)))
 else:raise ValueError('unknown relation or extra fields')
 return _horizon(p,horizon)

def _kernel(X,n):return max(0,2*X-max(X,n))
def complete_defect(X,*,max_terms=DEFAULT_TERMS,max_operations=DEFAULT_OPERATIONS):
 _int(X);_int(max_terms);_int(max_operations);N=4*X-1
 if N*(N+1)//2>max_operations:raise OverflowError('complete defect work limit')
 out={}
 for j in range(1,N+1):
  J=_kernel(2*X,j)-4*_kernel(X,j)
  if J:
   for i in range(1,j+1):
    out[i,j]=Fraction(J*(1 if i==j else 2))
    if len(out)>max_terms:raise OverflowError('complete defect term limit')
 return out

def cycle_domain(N,*,max_pairs=DEFAULT_OPERATIONS,max_horizon=1000000,include_diagonal=True):
 _int(N);_int(max_pairs);_int(max_horizon)
 if type(include_diagonal)is not bool:raise ValueError('boolean diagonal switch')
 H=N*N
 if H>max_horizon or H>max_pairs:raise OverflowError('complete cycle domain resource limit')
 specs=[dict(kind='coprime_product',a=a,b=b) for a in range(1,N+1) for b in range(1,N+1) if gcd(a,b)==1 and (include_diagonal or a!=b)]
 return dict(N=N,horizon=H,ordered=True,include_diagonal=include_diagonal,specs=specs,complete_coprime_domain=True)

def compile_certificate(cert,*,max_terms=DEFAULT_TERMS,max_operations=DEFAULT_OPERATIONS):
 _int(max_terms);_int(max_operations)
 if type(cert)is not dict or set(cert)!={'target','horizon','lhs','squares','relations'}:raise ValueError('certificate schema')
 target=cert['target'];H=_int(cert['horizon'])
 if type(target)is not str or target not in ('mu','c') or type(cert['squares'])is not list or type(cert['relations'])is not list:raise ValueError('certificate domain')
 lhs=_horizon(load_poly(cert['lhs']),H);rhs={};used=len(lhs)
 def charge(n):
  nonlocal used
  used+=n
  if used>max_operations:raise OverflowError('certificate total work limit')
 def merge(p):
  nonlocal rhs
  charge(len(rhs)+len(p));rhs=add(rhs,p)
  if len(rhs)>max_terms:raise OverflowError('certificate term limit')
 if len(lhs)>max_terms:raise OverflowError('lhs term limit')
 for s in cert['squares']:
  if type(s)is not dict or set(s)!={'weight','poly'} or type(s['weight'])is not str:raise ValueError('square schema')
  w=_q(s['weight'])
  if w<0 or str(w)!=s['weight']:raise ValueError('nonnegative canonical square weight required')
  p=_horizon(load_poly(s['poly']),H);charge(len(p)**2);merge(scale(mul(p,p,max_terms=max_terms,max_operations=max_operations),w))
 for r in cert['relations']:
  if type(r)is not dict or set(r)!={'spec','multiplier'}:raise ValueError('relation multiplier schema')
  p=_horizon(load_poly(r['multiplier']),H);spec=r['spec']
  if type(spec)is not dict:raise ValueError('relation spec dict')
  kind=spec.get('kind');work=1
  if kind=='inverse_row':work=_int(spec.get('n'))
  elif kind=='squarefree_zero':work=isqrt(_int(spec.get('n')))+1
  elif kind=='prime_power':work=isqrt(_int(spec.get('p')))+1
  charge(work);q=relation(spec,target,H,max_operations=max_operations);charge(len(p)*len(q));merge(mul(p,q,max_terms=max_terms,max_operations=max_operations))
 if lhs!=rhs:raise ValueError('coefficient identity mismatch')
 return dict(finite_identity_verified=True,conditional_finite_nonnegativity=True,target=target,horizon=H,coefficient_matching_exact=True,operations=used,identity_terms=len(lhs),relation_count=len(cert['relations']),square_count=len(cert['squares']),actual_all_scale_signed_bound_proved=False,global_bound_proved=False,RH_proved=False,scope='finite identity; nonnegativity conditional on whitelisted actual arithmetic relations, no global estimate')
