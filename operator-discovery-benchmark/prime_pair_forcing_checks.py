"""Independent original-pair prime forcing and rational log enclosure checks.
No arithmetic producer imports; finite certificates do not prove signed bounds.
"""
from fractions import Fraction as F
import hashlib,json,math

def require(ok,message):
 if not ok:raise ValueError(message)
def integer(x,minimum=0):
 require(type(x) is int and x>=minimum,'exact integer domain');return x
def rational(x):
 require(type(x) in (int,str) or isinstance(x,F),'exact rational');return F(x)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def factor_data(N):
 least=list(range(N+1));exponent=[0]*(N+1);core=[0]*(N+1);core[1]=1
 for p in range(2,math.isqrt(N)+1):
  if least[p]==p:
   for n in range(p*p,N+1,p):
    if least[n]==n:least[n]=p
 for n in range(2,N+1):
  p=least[n];q=n//p
  if q%p==0:exponent[n]=exponent[q]+1;core[n]=core[q]
  else:exponent[n]=1;core[n]=q
 return least,exponent,core
def coefficients(N,target,table=None):
 require(target in ('mu','c'),'actual target mu/c');least,e,core=table or factor_data(N);a=[0]*(N+1);a[1]=1
 for n in range(2,N+1):a[n]=a[core[n]]*((-1 if e[n]==1 else 0) if target=='mu' else 2*(-1)**e[n])
 return a
def K(X,t):return max(0,2*X-max(X,t))
def J(X,t):return K(2*X,t)-4*K(X,t)
def target_delta(X,a):
 prefix=[0]*len(a)
 for n in range(1,len(a)):prefix[n]=prefix[n-1]+a[n]
 AX=sum(prefix[n]**2 for n in range(X,2*X));A2=sum(prefix[n]**2 for n in range(2*X,4*X))
 return A2-4*AX

def _atanh_log(v,precision):
 """ln((1+v)/(1-v)), 0<=v<=1/3; exact positive tail."""
 require(F(0)<=v<=F(1,3),'atanh domain');tol=F(1,1<<precision);power=v;acc=F(0);j=0
 while True:
  acc+=2*power/(2*j+1);j+=1;power*=v*v
  tail=2*power/((2*j+1)*(1-v*v))
  if tail<=tol:return acc,acc+tail

def log_interval(n,precision=80):
 integer(n,1);integer(precision,1)
 if n==1:return F(0),F(0)
 shift=n.bit_length()-1;v=F(n-(1<<shift),n+(1<<shift));lo,hi=_atanh_log(v,precision+shift.bit_length()+2);l2,h2=_atanh_log(F(1,3),precision+shift.bit_length()+2)
 return lo+shift*l2,hi+shift*h2

def ratio_interval(p,denominator,precision=80):
 integer(p,2);integer(denominator,2);q=denominator;e=0
 while q%p==0:q//=p;e+=1
 if q==1:return F(1,e),F(1,e)
 a,b=log_interval(p,precision);c,d=log_interval(denominator,precision);return a/d,b/c

def ratio_ticks(p,denominator,bits=32):
 D=1<<integer(bits,1);lo,hi=ratio_interval(p,denominator,bits+32)
 lower=(lo*D).numerator//(lo*D).denominator;upper=-((-hi*D).numerator//(-hi*D).denominator)
 return lower,upper

def validate_ratio_enclosure(p,denominator,lower,upper,D):
 integer(D,1);require(rational(lower)<=rational(upper),'ordered ratio interval')
 lo,hi=ratio_interval(p,denominator,max(80,D.bit_length()+32));require(rational(lower)/D<=lo and hi<=rational(upper)/D,'log-ratio enclosure not independently certified');return True

def original_pair_terms(X,target,B,bits=32):
 """Enumerate ORIGINAL i,j, then eligible prime-power divisors k|i.
 All terms, including coefficient-zero records, remain in the complete domain.
 """
 integer(X,1);integer(B,1);integer(bits,1);N=4*X-1;table=factor_data(N);a=coefficients(N,target,table);least,e,core=table;terms=[];counts={'thin':0,'dense':0};intervals={'thin':[0,0],'dense':[0,0]};ratio_cache={}
 for i in range(2,N+1):
  q=i;powers=[]
  while q>1:
   p=least[q];valuation=0
   while q%p==0:q//=p;valuation+=1
   for exponent in range(1,valuation+1):
    if target=='mu' or exponent%2:powers.append((p,exponent,p**exponent))
  for j in range(1,N+1):
   for p,exponent,k in powers:
    aa=i//k;height=max(aa,j)//math.gcd(aa,j);kind='thin' if height<=B else 'dense';coefficient=a[aa]*a[j]*J(X,max(i,j));key=(p,i*j)
    if key not in ratio_cache:ratio_cache[key]=ratio_ticks(*key,bits)
    lower,upper=ratio_cache[key];lo,hi=(coefficient*lower,coefficient*upper) if coefficient>=0 else (coefficient*upper,coefficient*lower)
    intervals[kind][0]+=lo;intervals[kind][1]+=hi;counts[kind]+=1
    terms.append(dict(i=i,j=j,prime=p,exponent=exponent,prime_power=k,a=aa,b=j,core_height=height,kind=kind,coefficient=coefficient,ratio_lower=lower,ratio_upper=upper))
 kappa=1 if target=='mu' else 2;delta=target_delta(X,a);S=F(J(X,1)-delta,2*kappa);D=1<<bits
 total=[intervals['thin'][i]+intervals['dense'][i] for i in (0,1)];require(F(total[0],D)<=S<=F(total[1],D),'full exact forcing identity interval')
 return dict(X=X,target=target,B=B,N=N,ratio_denominator=D,terms=terms,counts=counts,intervals=intervals,total_interval=total,Delta=delta,J_unit=J(X,1),kappa=kappa,exact_total_forcing=str(S),coefficient_sha256=digest(a),global_bound_proved=False)

def cutoff_descriptor(c):
 require(isinstance(c,dict),'cutoff dict')
 if c.get('kind')=='fixed':require(set(c)=={'kind','value'},'fixed cutoff schema');return dict(kind='fixed',value=integer(c['value']))
 require(c.get('kind') in ('power','bit_length_power') and set(c)=={'kind','power'},'power cutoff schema');p=rational(c['power']);require(p>=0,'nonnegative cutoff power');return dict(kind=c['kind'],power=str(p))
def floor_root(n,k):
 integer(n);integer(k,1)
 if n<2:return n
 lo=0;hi=1<<((n.bit_length()+k-1)//k)
 while hi-lo>1:
  m=(hi+lo)//2
  if m**k<=n:lo=m
  else:hi=m
 return hi if hi**k<=n else lo
def cutoff_value(X,c):
 c=cutoff_descriptor(c)
 if c['kind']=='fixed':return c['value']
 p=F(c['power']);n=X if c['kind']=='power' else X.bit_length();return floor_root(n**p.numerator,p.denominator)
def component_certificate(target,c):
 require(target in ('mu','c'),'target');c=cutoff_descriptor(c);s,r=(1,1) if target=='mu' else (3,4);gamma=F(c.get('power','0'))
 if c['kind']=='fixed':B=c['value'];scalar=F(8*B*(1+B.bit_length())**s);degree=r;loss=F(0)
 elif c['kind']=='bit_length_power':
  m=-((-gamma.numerator)//gamma.denominator);scalar=8*2**m*(1+2*gamma)**s;degree=m+s+r;loss=F(0)
 else:scalar=8*(1+gamma)**s;degree=s+r;loss=gamma
 return dict(admitted_component_bound=True,cofinal_critical_component_bound=loss==0,scalar=str(scalar),ordinary_X_power=str(2+loss),log_4X_power=degree,cofinal_conversion=dict(log_definition='L=1+log(4X)',integer_degree=degree,outer=2**(degree-1),constant_term=3**degree,q_power=degree,q_coefficient=math.factorial(degree),inequality='L^d <= 2^(d-1)*(3^d+d!*q^d)*ceil(X^(1/q)), q integer>=1'),bound='|S_prefix| <= scalar*X^ordinary_X_power*(1+log(4X))^log_4X_power',full_signed_bound_proved=False,RH_proved=False)

def validate_log_bounds(bounds,D):
 integer(D,2);require(D&(D-1)==0,'binary log denominator');bits=D.bit_length()-1;require(bits>=8,'log precision')
 for n,pair in enumerate(bounds,1):
  require(len(pair)==2 and all(type(v) is int for v in pair),'integer log endpoints');lower,upper=pair;require(lower<=upper,'ordered log endpoints')
  if n==1:require(pair==[0,0],'unit logarithm');continue
  require(lower>0,'positive log denominator');precision=bits+32
  for attempt in range(6):
   lo,hi=log_interval(n,precision)
   if F(lower,D)<=lo and hi<=F(upper,D):break
   precision*=2
  else:raise ValueError('log bounds not independently certified')
 return True

def original_pair_histogram(X,target,log_bounds,D,*,height_cache=True):
 """Different loop origin than producer: fix actual i, then divisors k|i.
 Per-triple arithmetic is integer only after global log certification.
 """
 N=4*X-1;table=factor_data(N);a=coefficients(N,target,table);least,e,core=table;logs=[[0,0]]+log_bounds;weights=[J(X,t) for t in range(N+1)];hist=[[0,0,0,0] for _ in range(N+1)];heights={}
 for i in range(2,N+1):
  factors=[];q=i
  while q>1:
   p=least[q];v=0
   while q%p==0:q//=p;v+=1
   for exp in range(1,v+1):
    if target=='mu' or exp%2:factors.append((p,p**exp))
  for p,k in factors:
   aa=i//k;fa=a[aa];heightrow=heights.get(aa)
   if heightrow is None and height_cache:
    from array import array
    code='H' if N<=65535 else 'I';heightrow=array(code,(max(aa,j)//math.gcd(aa,j) for j in range(1,N+1)));heights[aa]=heightrow
   lp_lo,lp_hi=logs[p];li_lo,li_hi=logs[i]
   for j in range(1,N+1):
    height=heightrow[j-1] if heightrow is not None else max(aa,j)//math.gcd(aa,j);entry=hist[height];entry[2]+=1;coefficient=fa*a[j]*weights[max(i,j)]
    if not coefficient:entry[3]+=1;continue
    lj_lo,lj_hi=logs[j];lower=D*lp_lo//(li_hi+lj_hi);den=li_lo+lj_lo;upper=(D*lp_hi+den-1)//den
    entry[0]+=coefficient*(lower if coefficient>0 else upper);entry[1]+=coefficient*(upper if coefficient>0 else lower)
 return {str(h):dict(lo=v[0],hi=v[1],triples=v[2],zero_terms=v[3]) for h,v in enumerate(hist) if v[2]},a

def validate_profile(profile,scales,targets,cutoffs):
 require(isinstance(profile,dict) and profile.get('status')=='available','complete available profile');value=profile['value'];scales=list(scales);targets=list(targets);cutoffs=[cutoff_descriptor(c) for c in cutoffs];require(scales and targets and cutoffs,'nonempty dimensions')
 for X in scales:integer(X,1)
 require(len(set(scales))==len(scales) and len(set(targets))==len(targets) and all(t in ('mu','c') for t in targets) and len({digest(c) for c in cutoffs})==len(cutoffs),'declared unique dimensions');Nmax=4*max(scales)-1
 require(value['complete_horizon']==Nmax,'complete horizon');D=integer(value['log_denominator'],2);bounds=value['log_bounds'];require(len(bounds)==Nmax and value['logs_sha256']==digest(bounds),'log coverage/hash');validate_log_bounds(bounds,D)
 expected={(X,t,digest(c)) for X in scales for t in targets for c in cutoffs};rows={}
 for row in value['rows']:
  require(all(type(row.get(k)) is int for k in ('X','B','N','D','bits','kappa','Delta','J1','complete_triples','zero_terms')),'exact integer row schema')
  require(row.get('full_signed_bound_proved') is False and row.get('RH_proved') is False and row.get('identity_interval_contains_exact') is True,'strict row flags')
  for interval in ('S','prefix','remainder'):require(set(row[interval])=={'lo','hi'} and all(type(v) is int for v in row[interval].values()),'integer interval schema')
  key=(row['X'],row['target'],row['cutoff_id']);require(key in expected and key not in rows,'row domain/duplicate');rows[key]=row
 require(set(rows)==expected,'complete row coverage');histograms=value['histograms'];require(set(histograms)=={t+':'+str(X) for X in scales for t in targets},'histogram coverage')
 for X in scales:
  N=4*X-1
  for t in targets:
   truth,a=original_pair_histogram(X,t,bounds,D);hist_id=t+':'+str(X);require(histograms[hist_id]==truth,'original-pair histogram mismatch');count=sum(v['triples'] for v in truth.values());zero=sum(v['zero_terms'] for v in truth.values());full={side:sum(v[side] for v in truth.values()) for side in ('lo','hi')};prefix=[0]*len(a)
   for n in range(1,len(a)):prefix[n]=prefix[n-1]+a[n]
   AX=sum(prefix[n]**2 for n in range(X,2*X));A2=sum(prefix[n]**2 for n in range(2*X,4*X));delta=A2-4*AX;kappa=1 if t=='mu' else 2;exact=F(J(X,1)-delta,2*kappa);require(F(full['lo'],D)<=exact<=F(full['hi'],D),'full forcing identity')
   for cutoff in cutoffs:
    row=rows[X,t,digest(cutoff)];B=cutoff_value(X,cutoff);pre={side:sum(v[side] for h,v in truth.items() if int(h)<=B) for side in ('lo','hi')};rem={side:full[side]-pre[side] for side in ('lo','hi')}
    fields=dict(X=X,target=t,cutoff=cutoff,cutoff_id=digest(cutoff),B=B,N=N,D=D,bits=D.bit_length()-1,kappa=kappa,S=full,prefix=pre,remainder=rem,Delta=delta,J1=J(X,1),exact_full_S=str(exact),histogram_id=hist_id,histogram_sha256=digest(truth),complete_triples=count,zero_terms=zero,coefficients_sha256=digest(a),prefix_sha256=digest(prefix),identity_interval_contains_exact=True,original_energy=dict(A_X=AX,A_2X=A2),component_certificate=component_certificate(t,cutoff),coverage=dict(prefix_triples=sum(v['triples'] for h,v in truth.items() if int(h)<=B),remainder_triples=sum(v['triples'] for h,v in truth.items() if int(h)>B),all_triples=count,complete=True),normalized_negative_remainder=dict(lower=str(F(-rem['hi'],D*X*X)),upper=str(F(-rem['lo'],D*X*X))),full_signed_bound_proved=False,RH_proved=False)
    for key,val in fields.items():require(row.get(key)==val,'actual row '+key+' mismatch')
 require(value['full_signed_bound_proved'] is False and value['RH_proved'] is False,'no global promotion')
 return dict(verified=True,rows=len(rows),log_bounds_independently_certified=True,original_pairs_independently_reconstructed=True,full_signed_bound_proved=False)

# Public handoff names; both remain independent of the producer.
verify_profile=validate_profile
prefix_certificate=component_certificate
