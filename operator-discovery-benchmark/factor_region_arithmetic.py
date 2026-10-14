"""Complete actual signed factor-region Gram; identities, not critical estimates."""
from fractions import Fraction as F
import hashlib,json,math
import arithmetic_filter_pole_budget as source
COMPONENTS=('unit',)+tuple(f'prime_{"small" if p else "large"}/core_{"small" if c else "large"}/{e}' for p in (True,False) for c in (True,False) for e in ('odd','even'))
def canonical_id(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def _int(x,low=0):
 if type(x) is not int or x<low:raise ValueError('integer domain')
 return x
def _rat(x):
 if not isinstance(x,str):raise ValueError('rational string required')
 return F(x)
def _target(t):
 if not isinstance(t,dict) or set(t)!={'r','l','filter'}:raise ValueError('target schema')
 _int(t['r']);_int(t['l'])
 if t['r']+t['l']<1:raise ValueError('positive arity')
 terms=source.canonical_filter(t['filter'])
 if not terms:raise ValueError('nonzero filter')
 return terms
def _cut(X,p,bits):
 q=_rat(p)
 if q<=0:raise ValueError('positive cutoff power')
 if X.bit_length()*q.numerator>bits or max(1,X.bit_length()*q.numerator)*q.denominator>bits:raise OverflowError('cutoff bit budget')
 goal=X**q.numerator;lo=0;hi=1<<((goal.bit_length()+q.denominator-1)//q.denominator)
 while hi-lo>1:
  m=(hi+lo)//2
  if m**q.denominator<=goal:lo=m
  else:hi=m
 return hi if hi**q.denominator<=goal else lo
class Meter:
 def __init__(self,budget,bits):self.cost=0;self.budget=budget;self.bits=bits
 def add(self,n=1):
  if self.cost+n>self.budget:raise OverflowError('work budget')
  self.cost+=n
 def check(self,n):
  if abs(n).bit_length()>self.bits:raise OverflowError('integer bit budget')
def _factor_table(N,meter):
 meter.add(2*(N+1));spf=list(range(N+1))
 for p in range(2,math.isqrt(N)+1):
  meter.add()
  if spf[p]==p:
   for n in range(p*p,N+1,p):
    meter.add()
    if spf[n]==n:spf[n]=p
 out=[(0,0,0)]*(N+1)
 for n in range(2,N+1):
  p=spf[n];m=n;e=0
  while m%p==0:meter.add();m//=p;e+=1
  out[n]=(p,e,m)
 return out

def profile(scales,targets,schemes,*,work_budget=100000000,max_n=262143,bit_budget=1000000,use_numpy=True):
 meter=Meter(work_budget,bit_budget)
 try:
  _int(work_budget);_int(max_n,1);_int(bit_budget,1)
  scales=list(scales);targets=list(targets);schemes=list(schemes)
  if not scales or not targets or not schemes:raise ValueError('nonempty dimensions')
  for X in scales:_int(X,1)
  if len(set(scales))!=len(scales):raise ValueError('duplicate scale')
  terms=[_target(t) for t in targets]
  for s in schemes:
   if not isinstance(s,dict) or set(s)!={'prime_power','core_power'}:raise ValueError('scheme schema')
   if _rat(s['prime_power'])<=0 or _rat(s['core_power'])<=0:raise ValueError('positive powers')
  if len({canonical_id(t) for t in targets})!=len(targets) or len({canonical_id(s) for s in schemes})!=len(schemes):raise ValueError('duplicate program')
  N=2*max(scales)-1
  if N>max_n:raise OverflowError('complete horizon exceeds max_n')
  factors=_factor_table(N,meter);coeff={};provenance=[]
  for t in targets:
   key=(t['r'],t['l'])
   if key not in coeff:
    res=source.actual_coefficients(N,*key,work_budget=work_budget-meter.cost);meter.add(res['cost'])
    if res['status']!='available':raise OverflowError(res.get('reason','source unavailable'))
    coeff[key]=res['coefficients'];provenance.append(dict(r=key[0],l=key[1],source_cost=res['cost'],source_sha256=canonical_id(res['coefficients'])))
    for a in coeff[key]:meter.check(a)
  rows=[]
  for X in scales:
   for t,ts in zip(targets,terms):
    a=coeff[t['r'],t['l']];Q=math.lcm(*(F(v['weight']).denominator for v in ts));weights=[(v['divisor'],int(F(v['weight'])*Q)) for v in ts]
    for scheme in schemes:
     z=_cut(X,scheme['prime_power'],bit_budget);u=_cut(X,scheme['core_power'],bit_budget);events=[[0]*9 for _ in range(2*X)];meter.add(18*X)
     coverage=[0]*9;classmap=[];source_max=(2*X-1)//min(d for d,w in weights)
     for m in range(1,source_max+1):
      meter.add();p,e,core=factors[m];i=0 if m==1 else 1+(0 if p<=z else 4)+(0 if core<=u else 2)+(0 if e%2 else 1)
      coverage[i]+=1;classmap.append(i)
      for d,w in weights:
       meter.add();n=d*m
       if n<2*X:events[n][i]+=w*a[m];meter.check(events[n][i])
     prefixes=[];running=[0]*9
     for n in range(1,2*X):
      meter.add(9)
      for i in range(9):running[i]+=events[n][i];meter.check(running[i])
      if n>=X:prefixes.append(running.copy())
     maxprefix=max(abs(v) for row in prefixes for v in row);bound=X*maxprefix**2;meter.check(bound);meter.add(81*X)
     engine='python_int';gram=None
     if use_numpy and bound<=2**63-1:
      try:
       import numpy as np
       mat=np.array(prefixes,dtype=np.int64);gram=(mat.T@mat).tolist();engine='numpy_int64_proved_safe'
      except ImportError:pass
     if gram is None:gram=[[sum(row[i]*row[j] for row in prefixes) for j in range(9)] for i in range(9)]
     den=X*X*Q*Q;meter.check(den)
     diag=sum(gram[i][i] for i in range(9));cross=2*sum(gram[i][j] for i in range(9) for j in range(i+1,9));total=diag+cross
     for val in (diag,cross,total):meter.check(val)
     rows.append(dict(X=X,target_id=canonical_id(t),scheme_id=canonical_id(scheme),cutoffs=dict(z=z,u=u),gram_numerators=gram,gram_denominator=den,E=str(F(total,den)),diagonal=str(F(diag,den)),cross=str(F(cross,den)),component_source_counts=coverage,source_max=source_max,source_coverage_sha256=canonical_id(classmap),source_coefficients_sha256=canonical_id(a[:source_max+1]),weight_common_denominator=Q,gram_engine=engine,prefix_abs_bound=maxprefix,int64_gram_abs_bound=bound,source_coverage_complete=sum(coverage)==source_max,global_bound_proved=False))
  return dict(status='available',value=dict(rows=rows,components=COMPONENTS,source_provenance=provenance,complete_horizon=N,global_bound_proved=False,RH_proved=False),cost=meter.cost,cost_scope='complete source scalar proxy plus sieve/event/prefix/Gram operations; no physical-memory or total bit-cost certification')
 except OverflowError as e:return dict(status='missing',value=None,cost=meter.cost,reason=str(e))
 except (ValueError,TypeError,KeyError,ZeroDivisionError) as e:return dict(status='invalid',value=None,cost=meter.cost,reason=str(e))

def _calibration(x,r,l):
 _int(x,1);_int(r);_int(l)
 res=source.actual_coefficients(x,r,l)
 if res['status']!='available':raise ValueError('complete calibration source unavailable')
 meter=Meter(10000000,1000000);return res['coefficients'],_factor_table(x,meter)
def rough_prefix(x,z,r,l):
 _int(z);a,f=_calibration(x,r,l)
 return sum(a[n] for n in range(1,x+1) if n==1 or f[n][0]>z)
def least_prime_decomposition(x,z,r,l):
 _int(z);a,f=_calibration(x,r,l);terms=[]
 for p in range(max(2,z+1),x+1):
  if f[p][0]!=p:continue
  pe=p;e=1
  while pe<=x:
   core_sum=sum(a[m] for m in range(1,x//pe+1) if m==1 or f[m][0]>p)
   terms.append(dict(prime=p,exponent=e,prime_power=pe,coefficient=a[pe],core_prefix=core_sum,contribution=a[pe]*core_sum));pe*=p;e+=1
 lhs=sum(a[n] for n in range(1,x+1) if n==1 or f[n][0]>z)
 return dict(value=lhs,unit=1,terms=terms,remainder=0,reconstructed=1+sum(t['contribution'] for t in terms),complete=True,global_bound_proved=False)
def log_prime_forcing(n,r,l):
 a,f=_calibration(n,r,l);lhs={};rhs={};m=n
 while m>1:
  p=f[m][0];e=0
  while m%p==0:m//=p;e+=1
  lhs[p]=a[n]*e;power=p;j=1;s=0
  while n%power==0:s+=(-r+l*(-1)**j)*a[n//power];power*=p;j+=1
  rhs[p]=s
 return dict(n=n,r=r,l=l,lhs_log_prime_coefficients=lhs,rhs_log_prime_coefficients=rhs,complete=True,remainder=0,identity_verified=lhs==rhs,global_bound_proved=False)

def prime_singleton_obstruction(target,scheme,eta,weight):
 """Analytical rejection gate for a positive uncentered prime singleton potential.
 Does not refute the target's direct critical-energy claim.
 """
 terms=_target(target);v=_rat(weight);eta=_rat(eta)
 if not isinstance(scheme,dict) or set(scheme)!={'prime_power','core_power'}:raise ValueError('scheme schema')
 if v<0 or eta<0:raise ValueError('nonnegative potential weight/exponent required')
 applies=(len(terms)==1 and terms[0]['divisor']==1 and _rat(scheme['prime_power'])==F(1,2) and _rat(scheme['core_power'])==F(1,2) and v>0 and eta<1)
 coefficient=F(terms[0]['weight']) if len(terms)==1 and terms[0]['divisor']==1 else F(0)
 k=target['r']+target['l']
 return dict(kind='uncentered_prime_singleton_growth_obstruction',applies=applies,target_id=canonical_id(target),scheme_id=canonical_id(scheme),component_index=5,component=COMPONENTS[5],eta=str(eta),weight=str(v),threshold=4096,potential_lower_coefficient=str(v*coefficient**2*k*k/128) if applies else None,potential_lower_form='constant * X^(1-eta)/(log X)^2',global_potential_innovation_claim_refuted=applies,direct_target_energy_claim_refuted=False,RH_refuted=False,independently_verified=False,scope='Rejects W=E+V cofinal subpower innovation if V contains this positive singleton feature /ceil(X^eta), all other potential terms nonnegative. Does not reject direct target energy.')
