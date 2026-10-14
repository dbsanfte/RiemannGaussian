"""Exact complete mu prime coboundary transport; no critical bound."""
from math import isqrt
import arithmetic_cycle_language as L

def _int(n):
 if type(n)is not int or n<1:raise ValueError('positive strict integer')
 return n

def kernel(X,t):return max(0,2*X-max(X,t))
def shell_kernel(X,p,a,b):
 for n in (X,p,a,b):_int(n)
 return max(0,min(2*X,p*a,p*b)-max(X,a,b))

def build_transport(X,p,*,max_n=127,max_operations=10000000,max_terms=100000):
 for n in (X,p,max_n,max_operations,max_terms):_int(n)
 N=4*X-1
 if N>max_n or p>max_n:raise OverflowError('transport source/prime cap')
 if p<2 or any(p%d==0 for d in range(2,isqrt(p)+1)):raise ValueError('prime required')
 if N**3*16>max_operations:raise OverflowError('complete transport work preflight')
 used=0
 def charge(n):
  nonlocal used
  used+=n
  if used>max_operations:raise OverflowError('transport expansion work')
 def product(a,b):
  charge(len(a)*len(b));return L.mul(a,b,max_terms=max_terms,max_operations=max_operations)
 def merged(a,b):
  charge(len(a)+len(b));r=L.add(a,b)
  if len(r)>max_terms:raise OverflowError('transport terms')
  return r
 prefixes=[{}];B=[{}];decompositions=[];counts=dict(p_free=0,valuation_one=0,valuation_at_least_two=0)
 for i in range(1,N+1):
  prefixes.append(merged(prefixes[-1],L.variable(i)));m=i;e=0
  while m%p==0:m//=p;e+=1
  if e==0:counts['p_free']+=1
  elif e==1:counts['valuation_one']+=1
  else:counts['valuation_at_least_two']+=1
  bt={};terms=[]
  for a in range(1,i+1):
   charge(1)
   if a%p:bt=merged(bt,L.variable(a))
  for a in range(1,i//p+1):
   charge(1)
   if a%p:bt=merged(bt,L.scale(L.variable(a),-1))
  B.append(bt)
  for j in range(1,i+1):
   charge(1);core=j;v=0
   while core%p==0:core//=p;v+=1
   if v==1:
    terms.append(dict(spec=dict(kind='coprime_product',a=p,b=core),multiplier=L.constant(-1)))
    terms.append(dict(spec=dict(kind='prime_power',p=p,e=1),multiplier=L.variable(core)))
   elif v>=2:terms.append(dict(spec=dict(kind='squarefree_zero',n=j),multiplier=L.constant(1)))
  decompositions.append(terms)
 original=L.complete_defect(X,max_terms=max_terms,max_operations=max_operations);transport={};relations=[]
 for t in range(X,4*X):
  w=-4 if t<2*X else 1
  transport=merged(transport,L.scale(product(B[t],B[t]),w));plus=merged(prefixes[t],B[t])
  for term in decompositions[t-1]:relations.append(dict(spec=term['spec'],multiplier=L.dump_poly(L.scale(product(term['multiplier'],plus),w))))
 lhs=merged(original,L.scale(transport,-1));cert=dict(target='mu',horizon=N,lhs=L.dump_poly(lhs),squares=[],relations=relations)
 # Independent finite compiler is also invoked by callers/checkers.
 validation=L.compile_certificate(cert,max_terms=max_terms,max_operations=max_operations)
 reverse=dict(target='mu',horizon=N,lhs=L.dump_poly(L.scale(lhs,-1)),squares=[],relations=[dict(spec=r['spec'],multiplier=L.dump_poly(L.scale(L.load_poly(r['multiplier']),-1))) for r in relations])
 L.compile_certificate(reverse,max_terms=max_terms,max_operations=max_operations)
 return dict(X=X,prime=p,horizon=N,original_defect=L.dump_poly(original),transported_defect=L.dump_poly(transport),equality_certificate=cert,reverse_equality_certificate=reverse,validation=validation,coverage=dict(source_indices=N,source_classes=counts,p_free_indices=[i for i in range(1,N+1) if i%p],all_prime_square_complement_retained=True,parent_domain=[X,2*X],child_domain=[2*X,4*X],endpoint_convention='integer half-open; shell a<=n<pa'),cost=used,scope='finite full equality; one-prime coboundary does not prove critical control',global_bound_proved=False,RH_proved=False)
