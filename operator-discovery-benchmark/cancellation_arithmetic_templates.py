"""Balanced finite AST dictionary extension. Full original defect retained.
No learned coefficients, coefficient-response tables, or all-scale bound supplied.
"""
from fractions import Fraction as F
import math
import grouped_arithmetic_templates as B
import grouped_arithmetic_language as L
from cancellation_arithmetic_language import compile_expression

def descriptors():
 d=B.descriptors()
 atoms=('prefix','half','even','mod3one','prime')
 mixes=[(a,b,sign)for i,a in enumerate(atoms)for b in atoms[i+1:]for sign in (1,-1)]
 sq=[dict(family='signed_block',region=r,contrast=a,weight='one')for r in ('parent','child')for a in atoms]
 sq +=[dict(family='signed_block',region=r,contrast='mix',left=a,right=b,sign=sign,weight='one')for r in ('parent','child')for a,b,sign in mixes]
 sq +=[dict(family='signed_block',region=r,contrast='growing_prime',root_order=k,weight='one')for r in ('parent','child')for k in (2,3)]
 rel=[dict(family=f,region=r,multiplier=m,weight=w)for f in ('norm_core','gcd_pair','prime_transport')for r in ('all','head','tail')for m in ('product','difference')for w in ('one','defect_kernel')]
 return dict(square=d['square']+[dict(v,id=B.digest(v))for v in sq],relation=d['relation']+[dict(v,id=B.digest(v))for v in rel])
def contrast_ast(kind,t):
 I=lambda n:['int',n];V=lambda n:['v',n]
 pref=lambda hi:['sum','j',I(1),hi,['x',V('j')]]
 if kind=='prefix':return pref(I(t))
 if kind=='half':return pref(I(t//2))
 if kind in ('even','mod3one','prime'):
  pred=['eq',['imod',V('j'),I(2)],I(0)] if kind=='even' else ['eq',['imod',V('j'),I(3)],I(1)] if kind=='mod3one' else ['prime',V('j')]
  return ['sum','j',I(1),I(t),['guard',pred,['x',V('j')]]]
 raise ValueError('contrast')
def descriptor_ast(desc,t,X):
 if desc['contrast']=='mix':return ['add',contrast_ast(desc['left'],t),['scale',str(desc['sign']),contrast_ast(desc['right'],t)]]
 if desc['contrast']=='growing_prime':
  return ['sum','p',['int',2],['int',B._ceilroot(X,desc['root_order'])],['guard',['prime',['v','p']],['sum','j',['int',1],['idiv',['int',t],['v','p']],['guard',['eq',['gcd',['v','j'],['v','p']],['int',1]],['x',['v','j']]]]]]
 return contrast_ast(desc['contrast'],t)
def build_instance(target,X,q,C,claim='critical',*,max_horizon=80,max_columns=1024,max_operations=200000000,max_terms=10000):
 N=4*X-1
 if type(max_horizon)is not int or max_horizon<1 or N>max_horizon:raise OverflowError('extension horizon cap')
 d=descriptors()
 if len(d['square'])+2*len(d['relation'])+1>max_columns:raise OverflowError('extension column cap')
 b=B.build_instance(target,X,q,C,claim,max_n=max_horizon,max_operations=max_operations,max_terms=max_terms)
 sq=b['instance']['square_groups'];rel=b['instance']['relation_groups'];used=b['construction_cost']
 def charge(n=1):
  nonlocal used
  used+=n
  if used>max_operations:raise OverflowError('extension work cap')
 def dump(p):
  charge(len(p))
  if len(p)>max_terms:raise OverflowError('extension term cap')
  return L.dump_poly(p)
 def J(n):return max(0,4*X-max(2*X,n))-4*max(0,2*X-max(X,n))
 def region(r,n):return r=='all' or r=='head' and n<=2*X or r=='tail' and n>2*X
 ast_archive=[];cache={}
 for desc in d['square'][52:]:
  group=[]
  for t in range(X,2*X) if desc['region']=='parent' else range(2*X,4*X):
   key=(B.digest(desc),t)
   if key not in cache:
    ast=descriptor_ast(desc,t,X);compiled=compile_expression(ast,X,N,max_operations=max_operations-used,max_terms=max_terms,max_degree=6);cache[key]=compiled['poly'];charge(compiled['operations']);ast_archive.append(dict(descriptor_id=desc['id'],t=t,ast=ast,poly_sha256=B.digest(compiled['poly'])))
   group.append(dict(weight=str(1 if desc['weight']=='one' else X if desc['weight']=='X' else X*X),poly=cache[key]))
  sq.append(group)
 factors={n:L.factor_witness(n,max_n=max_horizon)for n in range(1,N+1)}
 prefixes=[{}]
 for n in range(1,N+1):prefixes.append(L.add(prefixes[-1],L.variable(n)))
 for desc in d['relation'][195:]:
  group=[]
  for a in range(1,N+1):
   for c in range(1 if desc['family']=='prime_transport' else a,N+1):
    charge();anchor=c
    if desc['family']=='prime_transport':
     if len(factors[a])!=1 or factors[a][0][1]!=1 or a*c>N or math.gcd(a,c)!=1:continue
     anchor=a*c;spec=dict(kind='coprime_product',a=a,b=c)
     p=L.mul(L.variable(a),L.variable(c)) if desc['multiplier']=='product' else L.mul(L.variable(c),L.add(prefixes[anchor],L.scale(prefixes[c],-1)))
    elif desc['family']=='norm_core':
     g=math.gcd(a,c);u=a//g;v=c//g;spec=dict(kind='norm',n=g,factors=factors[g]);left=L.variable(u);right=L.variable(v)
     p=L.mul(left,right) if desc['multiplier']=='product' else L.mul(L.add(left,L.scale(right,-1)),L.add(left,L.scale(right,-1)))
    else:
     spec=dict(kind='gcd_product',a=a,b=c,factors_a=factors[a],factors_b=factors[c]);left=L.variable(a);right=L.variable(c)
     p=L.mul(left,right) if desc['multiplier']=='product' else L.mul(L.add(left,L.scale(right,-1)),L.add(left,L.scale(right,-1)))
    if not region(desc['region'],anchor):continue
    w=1 if desc['weight']=='one' else J(anchor)
    group.append(dict(spec=spec,multiplier=dump(L.scale(p,w))))
  rel.append(group)
 b.update(square_ids=[v['id']for v in d['square']],relation_ids=[v['id']for v in d['relation']],dictionary_sha256=B.digest(d),construction_cost=used,ast_archive=ast_archive,extension_scope='balanced generic finite dictionary; original lhs and all original groups retained')
 return b
