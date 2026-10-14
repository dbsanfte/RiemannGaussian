"""Complete prime-log pair forcing; rigorous rational intervals, no RH bound."""
from fractions import Fraction as F
from math import gcd
import hashlib,json
from detector_safe_evaluation import rational_ceiling
from arithmetic_filter_pole_budget import actual_coefficients

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def integer(x,minimum=0):
 if type(x)is not int or x<minimum:raise ValueError('integer domain')
 return x

def cutoff_descriptor(c):
 if not isinstance(c,dict):raise ValueError('cutoff dict')
 if c.get('kind')=='fixed' and set(c)=={'kind','value'}:return dict(kind='fixed',value=integer(c['value']))
 if c.get('kind') in ('power','bit_length_power') and set(c)=={'kind','power'}:
  if isinstance(c['power'],(float,bool)):raise ValueError('exact power')
  p=F(c['power'])
  if p<0:raise ValueError('nonnegative power')
  return dict(kind=c['kind'],power=str(p))
 raise ValueError('cutoff schema')

def cutoff_value(X,c):
 c=cutoff_descriptor(c)
 if c['kind']=='fixed':return c['value']
 n=X if c['kind']=='power' else X.bit_length();p=F(c['power']);result=rational_ceiling(n,str(p))
 if result.status!='available':raise OverflowError('cutoff power unavailable')
 v=result.value
 if n==1 or p==0:return 1
 if p.denominator*v.bit_length()>1000000 or p.numerator*n.bit_length()>1000000:raise OverflowError('floor equality bit budget exceeded')
 # Frozen helper returns exact ceiling; floor differs unless that ceiling is an exact root.
 return v if pow(v,p.denominator)==pow(n,p.numerator) else v-1

def log_interval(n,bits):
 integer(n,1);integer(bits,8)
 if n==1:return F(0),F(0)
 def series(z,T):
  s=F(0);term=z
  for j in range(T):s+=term/(2*j+1);term*=z*z
  return 2*s,2*s+2*term/((2*T+1)*(1-z*z))
 k=n.bit_length()-1;m=F(n,1<<k);T=bits+k.bit_length()+8
 l2,u2=series(F(1,3),T);lm,um=series((m-1)/(m+1),T)
 return k*l2+lm,k*u2+um

def kernel(X,t):return max(0,2*X-max(X,t))
def defect_kernel(X,t):return kernel(2*X,t)-4*kernel(X,t)
def _ceil(x):return -((-x.numerator)//x.denominator)
def _pair(lo,hi):return {'lo':lo,'hi':hi}

def prefix_certificate(target,c):
 if target not in ('mu','c'):raise ValueError('target')
 c=cutoff_descriptor(c);kind=c['kind'];gamma=F(c.get('power','0'));s,r=(1,1) if target=='mu' else (3,4)
 if kind=='fixed':
  B=c['value'];scalar=F(8*B*(1+B.bit_length())**s);degree=r;loss=F(0)
 elif kind=='bit_length_power':
  m=_ceil(gamma);scalar=8*2**m*(1+2*gamma)**s;degree=m+s+r;loss=F(0)
 else:scalar=8*(1+gamma)**s;degree=s+r;loss=gamma
 import math
 return dict(admitted_component_bound=True,cofinal_critical_component_bound=loss==0,scalar=str(scalar),ordinary_X_power=str(2+loss),log_4X_power=degree,cofinal_conversion=dict(log_definition='L=1+log(4X)',integer_degree=degree,outer=2**(degree-1),constant_term=3**degree,q_power=degree,q_coefficient=math.factorial(degree),inequality='L^d <= 2^(d-1)*(3^d+d!*q^d)*ceil(X^(1/q)), q integer>=1'),bound='|S_prefix| <= scalar*X^ordinary_X_power*(1+log(4X))^log_4X_power',full_signed_bound_proved=False,RH_proved=False)

def profile(scales,targets,cutoffs,*,work_budget,max_n,bits=80):
 integer(work_budget);integer(max_n,1);integer(bits,8);scales=list(scales);targets=list(targets);cutoffs=[cutoff_descriptor(c) for c in cutoffs]
 if not scales or any(type(x)is not int or x<1 for x in scales) or any(t not in ('mu','c') for t in targets):raise ValueError('domain')
 if len(set(scales))!=len(scales) or len(set(targets))!=len(targets) or len({digest(c) for c in cutoffs})!=len(cutoffs):raise ValueError('duplicates')
 used=0
 def charge(n):
  nonlocal used
  used+=n
  if used>work_budget:raise OverflowError('work budget exceeded')
 try:
  Nmax=4*max(scales)-1
  if Nmax>max_n:raise OverflowError('max_n exceeded')
  coeff={}
  for t in targets:
   src=actual_coefficients(Nmax,1,int(t=='c'),work_budget=max(0,work_budget-used));charge(src['cost'])
   if src['status']!='available':raise OverflowError(src.get('reason','source unavailable'))
   coeff[t]=src['coefficients']
  D=1<<bits;charge((Nmax+1)*(bits+Nmax.bit_length().bit_length()+8));logs=[None]
  for n in range(1,Nmax+1):
   l,u=log_interval(n,bits);logs.append([int((D*l).__floor__()),_ceil(D*u)])
  charge(Nmax*(__import__('math').isqrt(Nmax)+1));primes=[p for p in range(2,Nmax+1) if all(p%d for d in range(2,__import__('math').isqrt(p)+1))];rows=[];histograms={}
  for X in scales:
   N=4*X-1
   for t in targets:
    f=coeff[t];hist={};count=zero=0;prefix=[0]*(N+1)
    for n in range(1,N+1):prefix[n]=prefix[n-1]+f[n]
    delta=sum(prefix[n]**2 for n in range(2*X,4*X))-4*sum(prefix[n]**2 for n in range(X,2*X));kappa=1 if t=='mu' else 2
    for p in primes:
     if p>N:break
     k=p;e=1
     while k<=N:
      if t=='mu' or e%2:
       for a in range(1,N//k+1):
        for b in range(1,N+1):
         charge(1);count+=1;h=max(a,b)//gcd(a,b);q=f[a]*f[b]*defect_kernel(X,max(k*a,b));zero+=q==0
         row=hist.setdefault(h,dict(lo=0,hi=0,triples=0,zero_terms=0));row['triples']+=1;row['zero_terms']+=q==0
         if not q:continue
         l=logs[k*a][0]+logs[b][0];u=logs[k*a][1]+logs[b][1];lo=D*logs[p][0]//u;hi=(D*logs[p][1]+l-1)//l
         row['lo']+=q*(lo if q>0 else hi);row['hi']+=q*(hi if q>0 else lo)
      k*=p;e+=1
    full=_pair(sum(v['lo'] for v in hist.values()),sum(v['hi'] for v in hist.values()));exact=F(defect_kernel(X,1)-delta,2*kappa)
    if not F(full['lo'],D)<=exact<=F(full['hi'],D):raise ArithmeticError('full identity interval failure')
    hid=f'{t}:{X}';histograms[hid]={str(h):v for h,v in sorted(hist.items())};hh=digest(histograms[hid])
    for c in cutoffs:
     B=cutoff_value(X,c);pre=_pair(sum(v['lo'] for h,v in hist.items() if h<=B),sum(v['hi'] for h,v in hist.items() if h<=B));rem=_pair(sum(v['lo'] for h,v in hist.items() if h>B),sum(v['hi'] for h,v in hist.items() if h>B))
     rows.append(dict(normalized_negative_remainder=dict(lower=str(F(-rem['hi'],D*X*X)),upper=str(F(-rem['lo'],D*X*X))),coverage=dict(prefix_triples=sum(v['triples'] for h,v in hist.items() if h<=B),remainder_triples=sum(v['triples'] for h,v in hist.items() if h>B),all_triples=count,complete=True),original_energy=dict(A_X=sum(prefix[n]**2 for n in range(X,2*X)),A_2X=sum(prefix[n]**2 for n in range(2*X,4*X))),X=X,target=t,cutoff=c,cutoff_id=digest(c),B=B,N=N,D=D,bits=bits,kappa=kappa,S=full,prefix=pre,remainder=rem,Delta=delta,J1=defect_kernel(X,1),exact_full_S=str(exact),identity_interval_contains_exact=True,histogram_id=hid,histogram_sha256=hh,complete_triples=count,zero_terms=zero,coefficients_sha256=digest(f[:N+1]),prefix_sha256=digest(prefix),component_certificate=prefix_certificate(t,c),full_signed_bound_proved=False,RH_proved=False))
  return dict(status='available',value=dict(rows=rows,complete_horizon=Nmax,histograms=histograms,log_denominator=D,logs_sha256=digest(logs[1:]),log_bounds=logs[1:],log_method='binary range reduction; rational atanh; T=bits+bit_length(k)+8',full_signed_bound_proved=False,RH_proved=False),cost=used,cost_scope='scalar source/log-series/triple proxy, not full bit complexity or memory')
 except OverflowError as e:return dict(status='missing',value=None,reason=str(e),cost=used,full_signed_bound_proved=False,RH_proved=False)
