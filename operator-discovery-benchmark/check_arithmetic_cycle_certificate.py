"""Independent finite arithmetic SOS certificate checker. Standard library only."""
from fractions import Fraction as F
from math import gcd,isqrt

LIMITS=dict(horizon=100000,degree=12,terms=10000,coefficient_bits=4096,expansion_ops=1000000,factor_loops=1000000)
class ResourceLimit(OverflowError):pass
def guard(n,key):
 if n>LIMITS[key]:raise ResourceLimit(key+" resource limit")
def integer(x):
 if type(x)is not int or x<1:raise ValueError('positive exact integer required')
 return x
def rational(x):
 if type(x)is not str:raise ValueError('canonical rational string required')
 if len(x)>LIMITS["coefficient_bits"]:raise ResourceLimit("rational text resource limit")
 try:v=F(x)
 except (ValueError,ZeroDivisionError):raise ValueError('invalid rational')
 guard(max(abs(v.numerator).bit_length(),v.denominator.bit_length()),"coefficient_bits")
 if str(v)!=x:raise ValueError('noncanonical rational')
 return v
def factor(n):
 integer(n);guard(n,"horizon");result={};d=2;steps=0
 while d*d<=n:
  steps+=1;guard(steps,"factor_loops")
  while n%d==0:result[d]=result.get(d,0)+1;n//=d
  d+=1
 if n>1:result[n]=result.get(n,0)+1
 return result
def prime(n):return integer(n)>=2 and factor(n)=={n:1}
def canonical(p):return [{'m':list(m),'c':str(v)} for m,v in sorted(p.items()) if v]
def parse(poly,N):
 if type(poly)is not list:raise ValueError('polynomial list required')
 guard(len(poly),'terms');result={};previous=None
 for term in poly:
  if type(term)is not dict or set(term)!={'m','c'} or type(term['m'])is not list:raise ValueError('polynomial term schema')
  guard(len(term['m']),'degree');m=tuple(term['m'])
  if any(type(i)is not int or i<1 or i>N for i in m) or list(m)!=sorted(m):raise ValueError('monomial indices/horizon')
  if previous is not None and m<=previous:raise ValueError('monomial order/duplicate')
  v=rational(term['c'])
  if not v:raise ValueError('zero coefficient forbidden')
  result[m]=v;previous=m
 return result
def bounded(poly):
 guard(len(poly),"terms")
 for value in poly.values():guard(max(abs(value.numerator).bit_length(),value.denominator.bit_length()),"coefficient_bits")
 return poly
def add(a,b,scale=F(1)):
 out=dict(a)
 for m,v in b.items():out[m]=out.get(m,F(0))+scale*v
 return bounded({m:v for m,v in out.items() if v})
def multiply(a,b):
 guard(len(a)*len(b),"expansion_ops");out={}
 for m,v in a.items():
  for n,w in b.items():
   guard(len(m)+len(n),"degree");k=tuple(sorted(m+n));out[k]=out.get(k,F(0))+v*w
 return bounded({m:v for m,v in out.items() if v})
def relation(spec,target,N):
 if target not in ('mu','c'):raise ValueError('actual target')
 integer(N);guard(N,'horizon')
 if type(spec)is not dict:raise ValueError('relation dictionary required')
 kind=spec.get('kind')
 if kind=='unit' and set(spec)=={'kind'}:return {(1,):F(1),():F(-1)}
 if kind=='coprime_product' and set(spec)=={'kind','a','b'}:
  a,b=integer(spec['a']),integer(spec['b'])
  if a>N or b>N:raise ValueError('factor outside horizon')
  if a*b>N or gcd(a,b)!=1:raise ValueError('coprime product domain')
  return add({tuple(sorted((a,b))):F(1)},{(a*b,):F(-1)})
 if kind=='squarefree_zero' and set(spec)=={'kind','n'}:
  n=integer(spec['n'])
  if target!='mu' or n>N or not any(e>=2 for e in factor(n).values()):raise ValueError('squarefree zero domain')
  return {(n,):F(1)}
 if kind=='prime_power' and set(spec)=={'kind','p','e'}:
  p,e=integer(spec['p']),integer(spec['e'])
  if p>N:raise ValueError('prime outside horizon')
  if e>N.bit_length():raise ValueError('prime power outside horizon')
  if not prime(p):raise ValueError('actual prime required')
  n=1
  for _ in range(e):
   n*=p
   if n>N:raise ValueError('prime power outside horizon')
  value=(-1 if e==1 else 0) if target=='mu' else 2*(-1)**e
  return add({(n,):F(1)},{():F(-value)})
 if kind=='inverse_row' and set(spec)=={'kind','n'}:
  n=integer(spec['n'])
  if target!='mu' or n>N:raise ValueError('inverse row domain')
  out={}
  for d in range(1,isqrt(n)+1):
   if n%d==0:out[(d,)]=F(1);out[(n//d,)]=F(1)
  return add(out,{():F(-int(n==1))})
 raise ValueError('unsupported relation schema')
def verify_certificate(cert):
 if type(cert)is not dict or set(cert)!={'target','horizon','lhs','squares','relations'}:raise ValueError('certificate exact schema')
 target=cert['target'];N=integer(cert['horizon']);guard(N,'horizon')
 if target not in ('mu','c'):raise ValueError('actual target')
 lhs=parse(cert['lhs'],N);rhs={}
 if type(cert['squares'])is not list or type(cert['relations'])is not list:raise ValueError('certificate terms lists')
 guard(len(cert['squares'])+len(cert['relations']),'terms')
 operations=0
 for term in cert['squares']:
  if type(term)is not dict or set(term)!={'weight','poly'}:raise ValueError('square schema')
  w=rational(term['weight'])
  if w<0:raise ValueError('negative square weight')
  p=parse(term['poly'],N);operations+=len(p)**2;guard(operations,'expansion_ops');rhs=add(rhs,multiply(p,p),w)
 for term in cert['relations']:
  if type(term)is not dict or set(term)!={'spec','multiplier'}:raise ValueError('relation term schema')
  rel=relation(term['spec'],target,N);mult=parse(term['multiplier'],N);operations+=len(mult)*len(rel);guard(operations,'expansion_ops');rhs=add(rhs,multiply(mult,rel))
  guard(len(rhs),'terms')
 if lhs!=rhs:raise ValueError('exact polynomial identity fails')
 return dict(verified=True,horizon=N,target=target,finite_identity_verified=True,resource_scope='conservative per-certificate terms/degrees/bitlength/expansion/factor limits; ResourceLimit is missing not invalid; not a physical-memory certificate',actual_finite_nonnegative_evaluation=True,conditional_on_listed_actual_relations=True,global_bound_proved=False,RH_proved=False)
def complete_defect(X):
 integer(X);guard(4*X-1,'horizon');guard(sum(n*n for n in range(X,4*X)),'expansion_ops');out={}
 for lo,hi,weight in ((X,2*X,-4),(2*X,4*X,1)):
  for n in range(lo,hi):
   p={(i,):F(1) for i in range(1,n+1)};out=add(out,multiply(p,p),F(weight))
 return canonical(out)
def verify_defect_certificate(cert,X,D):
 integer(X);v=rational(D);N=4*X-1
 horizon=integer(cert.get('horizon'));guard(horizon,'horizon')
 if horizon<N:raise ValueError('defect horizon insufficient')
 expected=add({():v},parse(complete_defect(X),N),F(-1))
 if parse(cert.get('lhs'),horizon)!=expected:raise ValueError('lhs is not D minus complete defect')
 result=verify_certificate(cert);result.update(target_horizon=N,product_horizon=horizon,product_horizon_extra=horizon-N);return result
