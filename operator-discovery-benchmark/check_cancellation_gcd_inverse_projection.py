"""Independent complete Mobius gcd-inverse projection audit."""
from fractions import Fraction as F
from math import gcd
import check_cancellation_factor_blocks as P
import check_grouped_arithmetic as G

def check_projection(H,kernel,output,*,max_horizon=128,max_operations=20000000):
 P.integer(H,1)
 if H>max_horizon or H**3>max_operations:raise OverflowError('complete independent domain budget')
 P.require(type(kernel)is list and len(kernel)==H and all(type(r)is list and len(r)==H for r in kernel),'full HxH kernel')
 K=[]
 for row in kernel:
  r=[]
  for x in row:
   P.require(type(x)is str,'canonical kernel string');v=P.rational(x);P.require(str(v)==x,'canonical kernel');r.append(v)
  K.append(r)
 used=0
 def charge(n):
  nonlocal used
  used+=n
  if used>max_operations:raise OverflowError('independent expansion work')
 def add(a,b):
  charge(len(a)+len(b));return P.add(a,b)
 def multiply(a,b):
  charge(len(a)*len(b));return P.multiply(a,b)
 full={};co={};non={};signed={};relations=[];pairs=[];cp=[];np=[];blocks=[({},[])for d in range(H)]
 for a in range(1,H+1):
  for b in range(1,H+1):
   charge(1);w=K[a-1][b-1];g=gcd(a,b);pair={tuple(sorted((a,b))):w}if w else {};pairs.append([a,b]);full=add(full,pair)
   if g==1:co=add(co,pair);cp.append([a,b]);spec=dict(kind='unit')
   else:non=add(non,pair);np.append([a,b]);spec=dict(kind='inverse_row',n=g)
   relations.append(dict(spec=spec,multiplier=P.canonical(pair)))
   # Independent common-divisor membership, including zero-weight pairs.
   for d in range(1,H+1):
    charge(1)
    if a%d==0 and b%d==0:
     poly,ps=blocks[d-1];blocks[d-1]=(add(poly,pair),ps+[[a,b]])
     if w:signed=add(signed,{tuple(sorted((d,a,b))):w})
 difference=add(signed,{m:-v for m,v in co.items()})
 fields=dict(full_pair_polynomial=full,coprime_projection=co,noncoprime_complement=non,signed_divisor_polynomial=signed,difference=difference)
 for n,p in fields.items():P.require(output[n]==P.canonical(p),'complete polynomial '+n)
 P.require(output['target']=='mu' and output['horizon']==H and output['kernel_sha256']==P.digest(kernel),'target/kernel binding')
 source=dict(full_pairs_sha256=P.digest(pairs),full_pair_count=H*H,coprime_pairs_sha256=P.digest(cp),coprime_pair_count=len(cp),noncoprime_pairs_sha256=P.digest(np),noncoprime_pair_count=len(np),product_indices_used=False);P.require(output['source']==source,'complete all pair coverage')
 expected=[dict(d=d,polynomial=P.canonical(p),pairs_sha256=P.digest(ps),pair_count=len(ps))for d,(p,ps)in enumerate(blocks,1)];P.require(output['divisor_blocks']==expected,'all divisor blocks')
 cert=dict(target='mu',horizon=H,lhs=P.canonical(difference),squares=[],relations=relations);P.require(output['certificate']==cert,'exact full inverse/unit columns');G.verify_certificate(cert)
 dec=output['kernel_PSD_decomposition'];expr=output['signed_square_expression']
 if dec is None:P.require(expr==[],'no claimed decomposition')
 else:
  weights=[P.rational(v)for v in dec['positive_pivots']];vectors=[[P.rational(v)for v in row]for row in dec['covectors']];P.require(len(weights)==len(vectors) and all(v>=0 for v in weights) and all(len(v)==H for v in vectors),'nonnegative kernel factors')
  rebuilt=[[sum((w*v[i]*v[j]for w,v in zip(weights,vectors)),F(0))for j in range(H)]for i in range(H)];P.require(rebuilt==K,'independent PSD rank-one reconstruction');P.require(dec['matrix']==[[str(v)for v in row]for row in K],'kernel matrix archive')
  expected=[]
  for d in range(1,H+1):
   for w,vector in zip(weights,vectors):
    poly={(a,):v for a,v in enumerate(vector,1)if a%d==0 and v}
    if poly:expected.append(dict(signed_weight_variable=d,nonnegative_rational_factor=str(w),poly=P.canonical(poly)))
  P.require(expr==expected,'complete signed expression');poly={}
  for term in expr:
   a=P.polynomial(term['poly']);square=multiply(a,a);d=term['signed_weight_variable'];w=P.rational(term['nonnegative_rational_factor']);poly=add(poly,{tuple(sorted((d,)+m)):w*v for m,v in square.items()})
  P.require(poly==signed,'full signed expression crosses')
 P.require(output['signed_expression_is_PSD_certificate'] is False and output['arithmetic_values_substituted'] is False and output['global_bound_proved'] is False and output['RH_proved'] is False,'honest signed/finite scope')
 return dict(verified=True,complete_pair_domain=True,complete_divisor_identity=True,signed_expression_not_PSD=True,global_bound_proved=False,RH_proved=False)
