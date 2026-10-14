"""Complete ordered factor-bilinear partition and coprime rewrite certificates.
Supplied exact identities only; no arithmetic coefficients or signed estimates.
This compiler is not integrated into the finite five-atom Gram search.
"""
from fractions import Fraction as F
from math import gcd
import json,hashlib
import grouped_arithmetic_language as L

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def rational(s,nonnegative=False,max_bits=2048):
 if type(s)is not str or len(s)>2*max_bits+3 or any(c not in '-0123456789/' for c in s):raise ValueError('canonical rational string')
 q=F(s)
 if str(q)!=s or nonnegative and q<0:raise ValueError('rational domain')
 if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_bits:raise OverflowError('rational bits')
 return q

def floor_scaled_power(X,cut,*,max_exponent=64,max_bits=2048):
 if type(X)is not int or X<1 or type(cut)is not dict or set(cut)!={'coefficient','power'}:raise ValueError('cut schema')
 c=rational(cut['coefficient'],True,max_bits);p=rational(cut['power'],True,max_bits);a,b=p.numerator,p.denominator
 if max(a,b)>max_exponent:raise OverflowError('cut exponent cap')
 if not c:return 0
 if b*(c.numerator.bit_length()+c.denominator.bit_length())+a*X.bit_length()>max_bits:raise OverflowError('cut power bit cap')
 numerator=c.numerator**b*X**a;denominator=c.denominator**b
 lo=0;hi=1
 while hi**b*denominator<=numerator:hi*=2
 while lo+1<hi:
  mid=(lo+hi)//2
  if mid**b*denominator<=numerator:lo=mid
  else:hi=mid
 return lo

def build_block(spec,X,horizon,target='mu',multiplier=None,*,max_horizon=4096,max_pairs=200000,max_operations=20000000,max_terms=10000,max_degree=12,max_coefficient_bits=2048,max_kernel_power=16):
 for v in (X,horizon,max_horizon,max_pairs,max_operations,max_terms,max_degree,max_coefficient_bits,max_kernel_power):
  if type(v)is not int or v<1:raise ValueError('positive integer bounds')
 if horizon>max_horizon:raise OverflowError('source horizon cap')
 if X.bit_length()>max_coefficient_bits:raise OverflowError('scale integer bits')
 if target not in ('mu','c') or type(spec)is not dict or set(spec)!={'kind','product_scale','coprime','cuts','kernel'} or spec['kind']!='factor_bilinear' or type(spec['coprime'])is not bool:raise ValueError('factor spec schema')
 scale=rational(spec['product_scale'],True,max_coefficient_bits);H=(scale.numerator*X)//scale.denominator
 if H>horizon:raise ValueError('complete product domain exceeds source horizon')
 cuts=spec['cuts']
 if type(cuts)is not dict or set(cuts)!={'left','right'}:raise ValueError('factor cuts')
 endpoints={}
 for side in ('left','right'):
  c=cuts[side]
  if type(c)is not dict or set(c)!={'lower','upper'}:raise ValueError('cut interval')
  endpoints[side]=[floor_scaled_power(X,c[k],max_bits=max_coefficient_bits)for k in ('lower','upper')]
  if endpoints[side][0]>endpoints[side][1]:raise ValueError('reversed cut interval')
 if type(spec['kernel'])is not list or len(spec['kernel'])>max_terms:raise ValueError('kernel terms')
 kernel=[]
 for term in spec['kernel']:
  if type(term)is not dict or set(term)!={'coefficient','a_power','b_power','x_power'}:raise ValueError('kernel schema')
  q=rational(term['coefficient'],False,max_coefficient_bits);powers=[term[k]for k in ('a_power','b_power','x_power')]
  if any(type(v)is not int or v<0 for v in powers):raise ValueError('kernel integer powers')
  if any(v>max_kernel_power for v in powers):raise OverflowError('kernel power cap')
  kernel.append((q,powers))
 if multiplier is not None and (type(multiplier)is not list or len(multiplier)>max_terms):raise OverflowError('multiplier input terms')
 mul=L.constant(1)if multiplier is None else L.load_poly(multiplier)
 if len(mul)>max_terms or any(len(m)+2>max_degree or any(n>horizon for n in m)for m in mul):raise OverflowError('multiplier term/degree/horizon cap')
 if any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in mul.values()):raise OverflowError('multiplier bits')
 if H>max_pairs or H>max_operations:raise OverflowError('factor domain minimum work')
 pairs_count=sum(H//a for a in range(1,H+1))
 if pairs_count>max_pairs or pairs_count*max(1,len(kernel))*max(1,len(mul))>max_operations:raise OverflowError('complete factor work preflight')
 records={k:dict(bilinear={},coprime_projection={},noncoprime_residual={},relations=[],multiplicity={},pairs=[])for k in ('full','inside','complement')};used=0
 def charge(n=1):
  nonlocal used
  used+=n
  if used>max_operations:raise OverflowError('factor expansion work')
 def merge(old,new):
  charge(len(old)+len(new));out=L.add(old,new)
  if len(out)>max_terms:raise OverflowError('factor expanded terms')
  if any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in out.values()):raise OverflowError('factor expanded coefficient bits')
  return out
 for a in range(1,H+1):
  for b in range(1,H//a+1):
   charge()
   cop=gcd(a,b)==1
   if spec['coprime'] and not cop:continue
   weight=F(0)
   for q,(ap,bp,xp)in kernel:
    if ap*max(1,a.bit_length())+bp*max(1,b.bit_length())+xp*X.bit_length()>max_coefficient_bits:raise OverflowError('kernel evaluation bits')
    weight+=q*a**ap*b**bp*X**xp;charge()
   if max(abs(weight.numerator).bit_length(),weight.denominator.bit_length())>max_coefficient_bits:raise OverflowError('kernel result bits')
   inside=endpoints['left'][0]<=a<=endpoints['left'][1] and endpoints['right'][0]<=b<=endpoints['right'][1]
   for name in ('full','inside'if inside else 'complement'):
    rec=records[name];rec['pairs'].append([a,b]);pair=L.scale({tuple(sorted((a,b))):F(1)},weight);rec['bilinear']=merge(rec['bilinear'],pair)
    if cop:
     rec['coprime_projection']=merge(rec['coprime_projection'],L.scale(L.variable(a*b),weight))
     m=rec['multiplicity'].setdefault(str(a*b),dict(count=0,kernel_weight=F(0)));m['count']+=1;m['kernel_weight']+=weight
     rec['relations'].append(dict(spec=dict(kind='coprime_product',a=a,b=b),multiplier=L.dump_poly(L.scale(mul,weight))))
    else:rec['noncoprime_residual']=merge(rec['noncoprime_residual'],pair)
 out={}
 for name,rec in records.items():
  projected=merge(rec['coprime_projection'],rec['noncoprime_residual'])
  rewrite_difference=L.mul(L.add(rec['bilinear'],L.scale(projected,-1)),mul,max_terms=max_terms,max_operations=max_operations)
  relation_sum={}
  for term in rec['relations']:
   charge(len(mul)*3);relation_sum=merge(relation_sum,L.mul(L.load_poly(term['multiplier']),L.relation(term['spec'],target,horizon),max_terms=max_terms,max_operations=max_operations))
  if relation_sum!=rewrite_difference:raise ValueError('complete coprime rewrite mismatch')
  out[name]=dict(bilinear=L.dump_poly(rec['bilinear']),coprime_projection=L.dump_poly(rec['coprime_projection']),noncoprime_residual=L.dump_poly(rec['noncoprime_residual']),relations=rec['relations'],rewrite_difference=L.dump_poly(rewrite_difference),rewrite_coefficient_verified=True,pairs=rec['pairs'],pairs_sha256=digest(rec['pairs']),pair_count=len(rec['pairs']),projection_multiplicities={n:dict(count=m['count'],kernel_weight=str(m['kernel_weight']))for n,m in sorted(rec['multiplicity'].items(),key=lambda x:int(x[0]))})
 if L.load_poly(out['full']['bilinear'])!=L.add(L.load_poly(out['inside']['bilinear']),L.load_poly(out['complement']['bilinear'])):raise ValueError('full complement mismatch')
 return dict(spec=spec,spec_sha256=digest(spec),X=X,horizon=horizon,product_horizon=H,cutoffs=endpoints,target=target,multiplier=L.dump_poly(mul),parts=out,cost=dict(operations=used,complete_unfiltered_pairs=pairs_count),complete_partition_verified=True,coefficient_table_used=False,integrated_into_five_atom_Gram_search=False,global_bound_proved=False,RH_proved=False,scope='supplied finite factor-partition/coprime rewrite identities; no signed bound inferred')
