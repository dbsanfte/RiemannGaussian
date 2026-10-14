"""Fixed shared-group templates; no coefficient responses or scoring.
Relation anchors: coprime products use a*b; gcd products use max(a,b).
All original pair terms remain, with stable positional groups including empties.
"""
from fractions import Fraction as F
import hashlib,json,math
import grouped_arithmetic_language as L

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def descriptors():
 squares=[dict(family='constant',region='all',weight='critical_normalizer')]
 squares +=[dict(family='coordinate',region=r,weight=w) for r in ('all','head','tail') for w in ('one','X','X2')]
 squares +=[dict(family='prefix',region=r,weight=w) for r in ('all','initial','parent','child') for w in ('one','X')]
 squares +=[dict(family='pair',domain=d,sign=s,weight=w) for d in ('all','coprime','noncoprime','divides') for s in (1,-1) for w in ('one','child_kernel','abs_defect_kernel')]
 squares +=[dict(family='divisor_row',region=r,weight=w) for r in ('all','head','tail') for w in ('one','X')]
 squares +=[dict(family='product',domain=d,weight=w) for d in ('all','coprime') for w in ('one','child_kernel')]
 relations=[dict(family=f,region=r,weight=w,multiplier=m) for f in ('norm','prime_power','squarefree_zero','inverse_row','coprime_product') for r in ('all','head','tail') for w in ('one','X','defect_kernel','child_rowmass') for m in ('one','anchor','prefix')]
 relations +=[dict(family='gcd_product',region=r,weight=w,multiplier='one') for r in ('all','head','tail') for w in ('one','X','defect_kernel','child_rowmass')]
 relations +=[dict(family='unit',region='all',weight='one',multiplier=m) for m in ('one','anchor','global_prefix')]
 return dict(square=[dict(d,id=digest(d)) for d in squares],relation=[dict(d,id=digest(d)) for d in relations])
def _ceilroot(X,q):
 if X==1:return 1
 if q>=X.bit_length():return 2
 lo=1;hi=X
 while lo<hi:
  mid=(lo+hi)//2
  if mid**q>=X:hi=mid
  else:lo=mid+1
 return lo
def build_instance(target,X,q,C,claim='critical',*,max_n=127,max_operations=200000000,max_terms=10000):
 if type(target)is not str or target not in ('mu','c') or any(type(v)is not int or v<1 for v in (X,q,max_n,max_operations,max_terms)):raise ValueError('template domain')
 if type(C)not in (int,str,F):raise ValueError('exact nonnegative C')
 C=F(C)
 if C<0 or claim not in ('critical','unsigned_calibration'):raise ValueError('template claim')
 N=4*X-1
 if N>max_n:raise OverflowError('template horizon cap')
 # Conservative polynomial pair/prefix work, before generation.
 if N**4*16>max_operations:raise OverflowError('template construction work preflight')
 used=0
 def charge(n=1):
  nonlocal used
  used+=n
  if used>max_operations:raise OverflowError('template work budget')
 def serial(p):
  charge(len(p))
  if len(p)>max_terms:raise OverflowError('template polynomial term budget')
  return L.dump_poly(p)
 def K(Y,t):return max(0,2*Y-max(Y,t))
 def J(t):return K(2*X,t)-4*K(X,t)
 def rowmass(i):
  a=max(2*X,i);b=4*X-1
  return (a+b)*(b-a+1)//2 if a<=b else 0
 def region(r,i):return r=='all' or r=='head' and i<=2*X or r=='tail' and i>2*X or r=='initial' and i<X or r=='parent' and X<=i<2*X or r=='child' and 2*X<=i<4*X
 factors={i:L.factor_witness(i,max_n=max_n,max_operations=max_operations) for i in range(1,N+1)}
 norm={i:int(all(e==1 for p,e in factors[i])) if target=='mu' else 4**len(factors[i]) for i in factors}
 prefixes=[{}]
 for i in range(1,N+1):prefixes.append(L.add(prefixes[-1],L.variable(i)))
 D=C*X*X*_ceilroot(X,q);delta={}
 for b in range(1,N+1):
  for a in range(1,b+1):
   charge();coef=J(b)*(1 if a==b else 2)
   if coef:delta[a,b]=F(coef)
 unsigned=sum(rowmass(i)*norm[i] for i in range(1,N+1));lhs=L.add(L.constant(D if claim=='critical' else unsigned),L.scale(delta,-1));dictionary=descriptors();square_groups=[];relation_groups=[]
 pairs=[(a,b) for a in range(1,N+1) for b in range(a+1,N+1)]
 for descriptor in dictionary['square']:
  family=descriptor['family'];group=[]
  if family=='constant':group=[dict(weight=str(X*X*_ceilroot(X,q)),poly=serial(L.constant(1)))]
  elif family in ('coordinate','prefix','divisor_row'):
   indices=range(2,N+1) if family=='divisor_row' else range(1,N+1)
   for i in indices:
    if not region(descriptor['region'],i):continue
    p=L.variable(i) if family=='coordinate' else prefixes[i] if family=='prefix' else L.add(*(L.variable(d) for d in range(1,i+1) if i%d==0))
    w=1 if descriptor['weight']=='one' else X if descriptor['weight']=='X' else X*X;group.append(dict(weight=str(w),poly=serial(p)))
  else:
   for a,b in pairs:
    charge();domain=descriptor['domain']
    if domain=='coprime' and math.gcd(a,b)!=1 or domain=='noncoprime' and math.gcd(a,b)==1 or domain=='divides' and b%a:continue
    p=L.add(L.variable(a),L.scale(L.variable(b),descriptor['sign'])) if family=='pair' else {(a,b):F(1)}
    w=1 if descriptor['weight']=='one' else K(2*X,b) if descriptor['weight']=='child_kernel' else abs(J(b));group.append(dict(weight=str(w),poly=serial(p)))
  square_groups.append(group)
 specs={f:[] for f in ('norm','prime_power','squarefree_zero','inverse_row','coprime_product','gcd_product','unit')};specs['unit']=[dict(kind='unit')]
 for i in range(1,N+1):
  specs['norm'].append(dict(kind='norm',n=i,factors=factors[i]))
  if len(factors[i])==1:p,e=factors[i][0];specs['prime_power'].append(dict(kind='prime_power',p=p,e=e))
  if target=='mu' and any(e>1 for p,e in factors[i]):specs['squarefree_zero'].append(dict(kind='squarefree_zero',n=i))
  if target=='mu' and i>=2:specs['inverse_row'].append(dict(kind='inverse_row',n=i))
 for a in range(1,N+1):
  for b in range(a,N+1):
   charge();specs['gcd_product'].append(dict(kind='gcd_product',a=a,b=b,factors_a=factors[a],factors_b=factors[b]))
   if a>=2 and a*b<=N and math.gcd(a,b)==1:specs['coprime_product'].append(dict(kind='coprime_product',a=a,b=b))
 def anchor(s):
  if s['kind']=='coprime_product':return s['a']*s['b']
  if s['kind']=='gcd_product':return max(s['a'],s['b'])
  return s.get('n',s['p']**s['e'] if s['kind']=='prime_power' else 1)
 for descriptor in dictionary['relation']:
  group=[]
  for spec in specs[descriptor['family']]:
   i=anchor(spec)
   if not region(descriptor['region'],i):continue
   w=1 if descriptor['weight']=='one' else X if descriptor['weight']=='X' else J(i) if descriptor['weight']=='defect_kernel' else rowmass(i)
   m=descriptor['multiplier'];p=L.constant(1) if m=='one' else L.variable(i) if m=='anchor' else prefixes[-1] if m=='global_prefix' else prefixes[i]
   group.append(dict(spec=spec,multiplier=serial(L.scale(p,w))))
  relation_groups.append(group)
 return dict(instance=dict(target=target,horizon=N,lhs=serial(lhs),square_groups=square_groups,relation_groups=relation_groups),square_ids=[d['id'] for d in dictionary['square']],relation_ids=[d['id'] for d in dictionary['relation']],D=str(D if claim=='critical' else unsigned),critical_budget=str(D),unsigned_bound=str(unsigned),X=X,q=q,C=str(C),claim=claim,dictionary_sha256=digest(dictionary),construction_cost=used,global_bound_proved=False)
