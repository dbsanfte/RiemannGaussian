"""Independent finite actual/counterfeit controls, stdlib only.
Finite checks do not prove the theoretical all-scale counterfeit obstruction.
"""
from fractions import Fraction
from math import gcd
import hashlib,json
DEFAULT_HORIZON_CAP=1000000

def _int(n,minimum=0):
 if type(n)is not int or n<minimum:raise ValueError('strict integer domain')
 return n

def _primes(P,cap=DEFAULT_HORIZON_CAP):
 if type(P)not in (list,tuple,set,frozenset):raise ValueError('finite prime collection')
 P=list(P)
 if len(set(P))!=len(P):raise ValueError('duplicate primes')
 for p in P:
  _int(p,2)
  if p>cap:raise OverflowError('prime normalization cap')
  if any(p%d==0 for d in range(2,__import__('math').isqrt(p)+1)):raise ValueError('composite normalization')
 return sorted(P)

def digest(v):return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def coefficients(horizon,target='mu',P=(),*,horizon_cap=DEFAULT_HORIZON_CAP):
 _int(horizon,1);_int(horizon_cap,1)
 if horizon>horizon_cap:raise OverflowError('coefficient horizon cap')
 if type(target)is not str or target not in ('mu','c','counterfeit'):raise ValueError('target')
 P=_primes(P,horizon_cap)
 if any(p>horizon_cap for p in P):raise OverflowError('prime normalization cap')
 spf=list(range(horizon+1));spf[1]=1
 for p in range(2,horizon+1):
  if spf[p]==p:
   for n in range(p*p,horizon+1,p):
    if spf[n]==n:spf[n]=p
 values=[0]*(horizon+1);values[1]=1;squarefree=[False,True]+[False]*(horizon-1);omega=[0]*(horizon+1);normalized=set(P)
 for n in range(2,horizon+1):
  p=spf[n];m=n;e=0
  while m%p==0:m//=p;e+=1
  omega[n]=omega[m]+e;squarefree[n]=e==1 and squarefree[m]
  if target=='c':local=2*(-1)**e
  elif e>1:local=0
  elif target=='mu' or p in normalized:local=-1
  else:local=1
  values[n]=local*values[m]
 return dict(target=target,P=P,horizon=horizon,coefficients=values,spf=spf,squarefree=squarefree,Omega=omega,coefficients_sha256=digest(values),finite_only=True,actual_all_scale_signed_bound_proved=False,RH_proved=False)

def block_energy(values,X):
 _int(X,1)
 if type(values)is not list or len(values)<4*X:raise ValueError('complete prefix horizon required')
 if any(type(v)is not int for v in values):raise ValueError('integer coefficients')
 prefix=[0]*len(values)
 for n in range(1,len(values)):prefix[n]=prefix[n-1]+values[n]
 A=sum(prefix[n]**2 for n in range(X,2*X));child=sum(prefix[n]**2 for n in range(2*X,4*X))
 return dict(X=X,A_X=A,A_2X=child,Delta=child-4*A,complete_horizon=4*X-1)

def audit_counterfeit(P,pair_limit,row_limit,scales=(),*,horizon_cap=DEFAULT_HORIZON_CAP,pair_work_cap=1000000,row_work_cap=1000000):
 _int(pair_limit,1);_int(row_limit,1);_int(pair_work_cap,1);_int(row_work_cap,1);_int(horizon_cap,1);scales=list(scales)
 if len(set(scales))!=len(scales):raise ValueError('duplicate scales')
 if row_limit*(row_limit+1)//2>row_work_cap:raise OverflowError('complete row budget')
 for X in scales:_int(X,1)
 if pair_limit**2>pair_work_cap:raise OverflowError('complete ordered pair budget')
 H=max(pair_limit**2,row_limit,max([4*X-1 for X in scales],default=1));data=coefficients(H,'counterfeit',P,horizon_cap=horizon_cap);f=data['coefficients'];spf=data['spf'];P=data['P'];normal=set(P)
 pairs=zeros=0
 for a in range(1,pair_limit+1):
  for b in range(1,pair_limit+1):
   if gcd(a,b)!=1:continue
   pairs+=1;zeros+=f[a]*f[b]==0
   if f[a]*f[b]!=f[a*b] or f[a]*f[b]*f[a*b]!=f[a*b]**2:raise ArithmeticError('cycle mismatch')
 for n in range(1,H+1):
  if abs(f[n])>1 or ((f[n]!=0)!=data['squarefree'][n]):raise ArithmeticError('support mismatch')
 power_checks=0
 for p in P:
  power=p;e=1
  while power<=H:
   if f[power]!=(-1 if e==1 else 0):raise ArithmeticError('normalized local mismatch')
   power_checks+=1;power*=p;e+=1
 inverse=[]
 for n in range(1,row_limit+1):
  if any(n%p==0 for p in P):
   total=sum(f[d] for d in range(1,n+1) if n%d==0)
   if total:raise ArithmeticError('partial inverse-row mismatch')
   inverse.append(n)
 mismatch=[dict(prime=p,counterfeit=f[p],actual_mu=-1) for p in range(2,H+1) if spf[p]==p and p not in normal]
 return dict(P=P,pair_limit=pair_limit,row_limit=row_limit,horizon=H,coefficients_sha256=data['coefficients_sha256'],ordered_coprime_pairs_checked=pairs,zero_cycle_pairs_checked=zeros,all_support_indices_checked=H,normalized_prime_powers_checked=power_checks,inverse_rows_checked=inverse,normalization_mismatches=mismatch,energies=[block_energy(f,X) for X in scales],all_finite_premise_checks_passed=True,theoretical_obstruction_source='prime_pair_forcing_next_certificate_scope.txt',theoretical_obstruction_source_not_verified_by_finite_checks=True,scope='generic partial-prime premises, not actual mu',finite_only=True,actual_all_scale_signed_bound_proved=False,RH_proved=False)

def certify_stored_counterexample(audit,X,D,*,horizon_cap=DEFAULT_HORIZON_CAP):
 _int(X,1)
 if type(D)not in (str,int,Fraction):raise ValueError('exact rational bound')
 D=Fraction(D)
 if D<0:raise ValueError('nonnegative proposed bound')
 if type(audit)is not dict or audit.get('all_finite_premise_checks_passed')is not True or audit.get('scope')!='generic partial-prime premises, not actual mu':raise ValueError('counterfeit audit required')
 rows=[r for r in audit['energies'] if r['X']==X]
 if len(rows)!=1:raise ValueError('unique complete scale required')
 row=rows[0]
 # Recompute coefficients and energy independently of untrusted stored energy.
 data=coefficients(audit['horizon'],'counterfeit',audit['P'],horizon_cap=horizon_cap)
 if data['coefficients_sha256']!=audit['coefficients_sha256'] or block_energy(data['coefficients'],X)!=row:raise ValueError('stored arithmetic mismatch')
 margin=Fraction(row['Delta'])-D
 return dict(certified_finite_counterexample=margin>0,X=X,Delta=row['Delta'],proposed_bound=str(D),margin=str(margin),coefficients_sha256=data['coefficients_sha256'],scope='generic partial-prime premises only; not actual Mobius counterexample',global_certificate_refuted=False,actual_RH_refuted=False)
