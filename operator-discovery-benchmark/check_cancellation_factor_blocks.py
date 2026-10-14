"""Independent exact factor-block audit; no producer arithmetic imports."""
from fractions import Fraction as F
from math import gcd
import hashlib,json,re

def require(c,m):
 if not c:raise ValueError(m)
def digest(v):return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def integer(n,minimum=0):
 require(type(n)is int and n>=minimum,'strict integer');return n

def rational(x):
 require(type(x)in(str,int,F),'exact rational')
 if type(x)is str:
  if len(x)>3000:raise OverflowError('raw rational size')
  require(re.fullmatch(r'-?[0-9]+(?:/[0-9]+)?',x)is not None,'rational literal')
 elif type(x)is int and abs(x).bit_length()>4096:raise OverflowError('integer bits')
 q=F(x)
 if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>4096:raise OverflowError('rational bits')
 return q

def floor_scaled_power(X,coefficient,power,*,max_bits=100000):
 integer(X,1)
 require(type(coefficient)in(str,int,F) and type(power)in(str,int,F),'exact cutoff')
 c,p=rational(coefficient),rational(power);require(c>=0 and p>=0,'nonnegative cutoff')
 if not c:return 0
 if p.denominator*(max(c.numerator.bit_length(),c.denominator.bit_length())+X.bit_length())+p.numerator*X.bit_length()>max_bits:raise OverflowError('independent cutoff bit preflight')
 # Compare t^q * den(c)^q <= num(c)^q * X^r, exactly.
 q=p.denominator;right=c.numerator**q*X**p.numerator;den=c.denominator**q
 lo=0;hi=1
 while hi**q*den<=right:hi*=2
 while lo+1<hi:
  mid=(lo+hi)//2
  if mid**q*den<=right:lo=mid
  else:hi=mid
 return lo

def polynomial(p):
 require(type(p)is list,'canonical polynomial');out={};last=None
 for t in p:
  require(type(t)is dict and set(t)=={'m','c'} and type(t['m'])is list and type(t['c'])is str,'polynomial schema');m=tuple(t['m']);q=rational(t['c'])
  require(all(type(i)is int and i>0 for i in m) and tuple(sorted(m))==m and q and str(q)==t['c'],'canonical polynomial term')
  require(last is None or last<m,'ordered unique monomial');last=m;out[m]=q
 return out

def canonical(p):return [dict(m=list(m),c=str(q)) for m,q in sorted(p.items()) if q]
def add(a,b):
 p=dict(a)
 for m,q in b.items():p[m]=p.get(m,F(0))+q
 return {m:q for m,q in p.items() if q}
def multiply(a,b):
 p={}
 for x,q in a.items():
  for y,r in b.items():m=tuple(sorted(x+y));p[m]=p.get(m,F(0))+q*r
 return {m:q for m,q in p.items() if q}

def expected_parts(spec,X,H,*,max_pairs=100000):
 require(type(spec)is dict and set(spec)=={'kind','product_scale','coprime','cuts','kernel'} and spec['kind']=='factor_bilinear' and type(spec['coprime'])is bool,'spec schema');integer(X,1);integer(H,1)
 if H>4096:raise OverflowError('independent horizon cap')
 T=floor_scaled_power(X,spec['product_scale'],'1');require(T<=H,'complete source/product horizon')
 bounds={}
 require(set(spec['cuts'])=={'left','right'},'cut axes')
 for axis in ('left','right'):
  a=spec['cuts'][axis];require(set(a)=={'lower','upper'},'cut bounds');bounds[axis]=[]
  for name in ('lower','upper'):
   c=a[name];require(set(c)=={'coefficient','power'},'cut schema');bounds[axis].append(floor_scaled_power(X,c['coefficient'],c['power']))
  require(bounds[axis][0]<=bounds[axis][1],'ordered cuts')
 records={k:[] for k in ('full','inside','complement')};count=0
 for a in range(1,T+1):
  for b in range(1,T//a+1):
   count+=1
   if count>max_pairs:raise OverflowError('complete independent pair cap')
   if spec['coprime'] and gcd(a,b)!=1:continue
   w=F(0)
   for t in spec['kernel']:
    require(set(t)=={'coefficient','a_power','b_power','x_power'},'kernel schema')
    for key in ('a_power','b_power','x_power'):
     integer(t[key])
     if t[key]>32:raise OverflowError('independent kernel power cap')
    w+=rational(t['coefficient'])*a**t['a_power']*b**t['b_power']*X**t['x_power']
   row=(a,b,w);records['full'].append(row)
   key='inside' if bounds['left'][0]<=a<=bounds['left'][1] and bounds['right'][0]<=b<=bounds['right'][1] else 'complement';records[key].append(row)
 return T,bounds,records

def check_block(output,*,max_pairs=100000):
 require(type(output)is dict,'output dict');spec=output['spec'];X=output['X'];H=output['horizon'];require(output['target']in('mu','c'),'target');T,bounds,records=expected_parts(spec,X,H,max_pairs=max_pairs)
 require(output['spec_sha256']==digest(spec) and output['product_horizon']==T and output['cutoffs']==bounds,'source/cutoff binding');multiplier=polynomial(output['multiplier']);require(all(n<=H for m in multiplier for n in m),'multiplier horizon');require(set(output['parts'])=={'full','inside','complement'},'complete parts')
 for name,rows in records.items():
  actual=output['parts'][name];bil={};proj={};res={};rels=[];counts={};pairs=[];rsum={}
  for a,b,w in rows:
   pairs.append([a,b]);bil=add(bil,{tuple(sorted((a,b))):w})
   if gcd(a,b)==1:
    proj=add(proj,{(a*b,):w});q=counts.setdefault(str(a*b),dict(count=0,kernel_weight=F(0)));q['count']+=1;q['kernel_weight']+=w
    mp={m:w*v for m,v in multiplier.items() if w*v};rel=dict(spec=dict(kind='coprime_product',a=a,b=b),multiplier=canonical(mp));rels.append(rel)
    # Independent expansion xa*xb-xab, with every zero and collision retained.
    rho=add({tuple(sorted((a,b))):F(1)},{(a*b,):F(-1)});rsum=add(rsum,multiply(mp,rho))
   else:res=add(res,{tuple(sorted((a,b))):w})
  diff=multiply(add(bil,{m:-q for m,q in add(proj,res).items()}),multiplier)
  require(diff==rsum,'independent complete relation identity')
  for field,p in [('bilinear',bil),('coprime_projection',proj),('noncoprime_residual',res),('rewrite_difference',diff)]:require(actual[field]==canonical(p),'exact '+name+' '+field)
  require(actual['relations']==rels and actual['pairs']==pairs and actual['pair_count']==len(pairs) and actual['pairs_sha256']==digest(pairs),'complete ordered pairs/relations')
  expected={n:dict(count=q['count'],kernel_weight=str(q['kernel_weight'])) for n,q in counts.items()};require(actual['projection_multiplicities']==expected,'all product multiplicities')
 require(polynomial(output['parts']['full']['bilinear'])==add(polynomial(output['parts']['inside']['bilinear']),polynomial(output['parts']['complement']['bilinear'])),'complete complement')
 require(output.get('coefficient_table_used')is False and output.get('global_bound_proved')is False and output.get('RH_proved')is False,'scope flags')
 require(output['cost']['complete_unfiltered_pairs']==sum(T//a for a in range(1,T+1)),'unfiltered source count')
 return dict(verified=True,complete_pair_partition_verified=True,all_product_multiplicities_verified=True,coefficient_rewrite_verified=True,producer_math_imported=False,global_bound_proved=False,RH_proved=False)
