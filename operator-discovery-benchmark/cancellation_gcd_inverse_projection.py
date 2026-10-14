"""Complete gcd-inverse rewriting for the actual Mobius inverse-of-ones axioms.
No coefficient values are substituted. Signed divisor-square expressions are
NOT nonnegative/PSD certificates or signed cancellation estimates.
"""
from fractions import Fraction as F
from math import gcd
import hashlib,json
import grouped_arithmetic_language as L
import cancellation_gram_language as P

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def build_projection(horizon,kernel,target='mu',*,psd_kernel=False,max_horizon=128,max_operations=20000000,max_terms=10000,max_coefficient_bits=4096):
 for v in (horizon,max_horizon,max_operations,max_terms,max_coefficient_bits):
  if type(v)is not int or v<1:raise ValueError('positive strict limits')
 if target!='mu':raise ValueError('this inverse-of-ones identity is mu-specific')
 if type(psd_kernel)is not bool:raise ValueError('PSD option boolean')
 H=horizon
 if H>max_horizon or H*H>max_operations:raise OverflowError('complete source preflight')
 if type(kernel)is not list or len(kernel)!=H or any(type(row)is not list or len(row)!=H for row in kernel):raise ValueError('complete HxH kernel required')
 K=[]
 for row in kernel:
  r=[]
  for value in row:
   if type(value)is not str or len(value)>2*max_coefficient_bits+3 or any(c not in '-0123456789/'for c in value):raise ValueError('canonical rational kernel')
   q=F(value)
   if str(q)!=value:raise ValueError('canonical kernel')
   if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('kernel bits')
   r.append(q)
  K.append(r)
 used=0
 def charge(n):
  nonlocal used
  used+=n
  if used>max_operations:raise OverflowError('complete expansion work')
 def merge(a,b):
  charge(len(a)+len(b));out=L.add(a,b)
  if len(out)>max_terms:raise OverflowError('expanded terms')
  if any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in out.values()):raise OverflowError('expanded coefficient bits')
  return out
 full={};coprime={};complement={};divisor={};relations=[];pairs=[];copairs=[];nonpairs=[];blocks={d:dict(poly={},pairs=[])for d in range(1,H+1)}
 for a in range(1,H+1):
  for b in range(1,H+1):
   charge(1);g=gcd(a,b);w=K[a-1][b-1];pair={tuple(sorted((a,b))):w}if w else {};pairs.append([a,b]);full=merge(full,pair)
   if g==1:copairs.append([a,b]);coprime=merge(coprime,pair);spec=dict(kind='unit')
   else:nonpairs.append([a,b]);complement=merge(complement,pair);spec=dict(kind='inverse_row',n=g)
   # Retain zero-weight relation records and all zero-weight source pairs.
   relations.append(dict(spec=spec,multiplier=L.dump_poly(pair)))
   for d in range(1,g+1):
    charge(1)
    if g%d==0:
     blocks[d]['pairs'].append([a,b]);blocks[d]['poly']=merge(blocks[d]['poly'],pair)
     if w:divisor=merge(divisor,{tuple(sorted((d,a,b))):w})
 if full!=L.add(coprime,complement):raise ValueError('complete pair complement mismatch')
 difference=L.add(divisor,L.scale(coprime,-1));rhs={}
 for term in relations:
  p=L.load_poly(term['multiplier']);r=L.relation(term['spec'],'mu',H,max_operations=max_operations);charge(len(p)*len(r));rhs=merge(rhs,L.mul(p,r,max_terms=max_terms,max_operations=max_operations))
 if rhs!=difference:raise ValueError('inverse-row coefficient reconstruction mismatch')
 certificate=dict(target='mu',horizon=H,lhs=L.dump_poly(difference),squares=[],relations=relations)
 verified=L.compile_certificate(certificate,max_terms=max_terms,max_operations=max_operations,max_horizon=max_horizon)
 signed_squares=[];kernel_psd=None
 if psd_kernel:
  kernel_psd=P.ldlt_psd(kernel,max_dimension=max_horizon,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits)
  for d in range(1,H+1):
   for pivot,vector in zip(kernel_psd['positive_pivots'],kernel_psd['covectors']):
    p={}
    for a,v in enumerate(vector,1):
     if a%d==0 and F(v):p[(a,)]=F(v)
    if p:signed_squares.append(dict(signed_weight_variable=d,nonnegative_rational_factor=pivot,poly=L.dump_poly(p)))
  rebuilt={}
  for term in signed_squares:
   p=L.load_poly(term['poly']);charge(len(p)**2);square=L.mul(p,p,max_terms=max_terms,max_operations=max_operations)
   for m,q in square.items():rebuilt=merge(rebuilt,{tuple(sorted((term['signed_weight_variable'],)+m)):q*F(term['nonnegative_rational_factor'])})
  if rebuilt!=divisor:raise ValueError('signed square expression mismatch')
 return dict(target='mu',horizon=H,kernel_sha256=digest(kernel),full_pair_polynomial=L.dump_poly(full),coprime_projection=L.dump_poly(coprime),noncoprime_complement=L.dump_poly(complement),signed_divisor_polynomial=L.dump_poly(divisor),difference=L.dump_poly(difference),certificate=certificate,identity_verified=verified['finite_identity_verified'],source=dict(full_pairs_sha256=digest(pairs),full_pair_count=len(pairs),coprime_pairs_sha256=digest(copairs),coprime_pair_count=len(copairs),noncoprime_pairs_sha256=digest(nonpairs),noncoprime_pair_count=len(nonpairs),product_indices_used=False),divisor_blocks=[dict(d=d,polynomial=L.dump_poly(rec['poly']),pairs_sha256=digest(rec['pairs']),pair_count=len(rec['pairs']))for d,rec in blocks.items()],kernel_PSD_decomposition=kernel_psd,signed_square_expression=signed_squares,signed_expression_is_PSD_certificate=False,arithmetic_values_substituted=False,cost=dict(operations=used),global_bound_proved=False,RH_proved=False,scope='supplied complete Mobius inverse-row/gcd projection identity; signed weights x_d remain; no cancellation bound')
