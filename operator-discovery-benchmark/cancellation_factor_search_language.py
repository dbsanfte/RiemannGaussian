"""Cost-ordered factor block closure groups, before any bound-search scores.
Full original defect and every old group survive. Closure is a supplied identity,
not an estimate; all noncoprime and inside/complement crosses are retained.
"""
from fractions import Fraction as F
import math,json
import grouped_arithmetic_language as L
import grouped_arithmetic_templates as B
import cancellation_arithmetic_templates as OLD
import cancellation_factor_blocks as FACTOR
DEFAULT_SPEC={'version':'factor-closure-v1','max_fraction_denominator':6,'max_blocks':44,'kernels':['one','a','b','a_minus_b'],'max_extra_columns':352}

def template_catalog(spec=None):
 spec=dict(DEFAULT_SPEC)if spec is None else spec
 if type(spec)is not dict or set(spec)!=set(DEFAULT_SPEC)or spec['version']!=DEFAULT_SPEC['version']:raise ValueError('fixed enumeration schema')
 for key in ('max_fraction_denominator','max_blocks','max_extra_columns'):
  if type(spec[key])is not int or spec[key]<1:raise ValueError('enumeration integer bounds')
 if spec['max_fraction_denominator']>6 or spec['max_blocks']>44 or spec['max_extra_columns']>352:raise OverflowError('finite enumeration cap')
 if spec['kernels']!=DEFAULT_SPEC['kernels']:raise ValueError('fixed generic kernel productions')
 powers=sorted({F(a,b)for b in range(2,spec['max_fraction_denominator']+1)for a in range(1,b)})
 catalog=[]
 for theta in powers:
  for kernel in spec['kernels']:
   cost=theta.numerator+theta.denominator+(0 if kernel=='one'else 1 if kernel in ('a','b')else 2)
   descriptor=dict(family='factor_closure',theta=str(theta),kernel=kernel,kernel_degree=0 if kernel=='one'else 1,normalizer='N^-kernel_degree',coprime=True,scale_map='N=4X-1',product_domain='ordered a,b>=1;ab<=N;gcd(a,b)=1',cells='inside_and_complete_complement')
   catalog.append(dict(descriptor,id=B.digest(descriptor),symbolic_cost=cost))
 catalog.sort(key=lambda d:(d['symbolic_cost'],json.dumps(d,sort_keys=True,separators=(',',':'))))
 selected=catalog[:min(spec['max_blocks'],spec['max_extra_columns']//8)]
 return dict(spec=spec,selected=selected,unselected=catalog[len(selected):],selection='symbolic cost, then canonical serialization; no responses')

def descriptors(spec=None):
 catalog=template_catalog(spec);old=OLD.descriptors();sq=[];rel=[]
 for block in catalog['selected']:
  common=dict(block_id=block['id'],theta=block['theta'],kernel=block['kernel'],kernel_degree=block['kernel_degree'],normalizer=block['normalizer'],cells='inside_and_complete_complement',scale_map='N=4X-1')
  for form in ('B','C_plus_R','prefix_plus_cell_contrast','prefix_minus_cell_contrast'):sq.append(dict(common,family='factor_square',form=form))
  for form in ('B_plus_C_plus_R','T'):rel.append(dict(common,family='factor_relation_closure',multiplier_form=form))
 return dict(square=old['square']+[dict(v,id=B.digest(v))for v in sq],relation=old['relation']+[dict(v,id=B.digest(v))for v in rel])

def block_spec(descriptor):
 def cut(c,p):return dict(coefficient=c,power=p)
 kernel=descriptor['kernel'];terms=[]
 if kernel in ('one','a','a_minus_b'):terms.append(dict(coefficient='1',a_power=0 if kernel=='one'else 1,b_power=0,x_power=0))
 if kernel in ('b','a_minus_b'):terms.append(dict(coefficient='-1'if kernel=='a_minus_b'else '1',a_power=0,b_power=1,x_power=0))
 return dict(kind='factor_bilinear',product_scale='1',coprime=True,cuts=dict(left=dict(lower=cut('1','0'),upper=cut('1',descriptor['theta'])),right=dict(lower=cut('1','0'),upper=cut('1','1'))),kernel=terms)

def build_instance(target,X,q,C,claim='critical',*,spec=None,max_horizon=80,max_columns=1024,max_operations=200000000,max_terms=30000,max_coefficient_bits=4096):
 catalog=template_catalog(spec);d=descriptors(spec)
 if len(d['square'])+2*len(d['relation'])+1>max_columns:raise OverflowError('complete extended LP columns')
 b=OLD.build_instance(target,X,q,C,claim,max_horizon=max_horizon,max_columns=max_columns,max_operations=max_operations,max_terms=max_terms);N=4*X-1;used=b['construction_cost'];archive=[]
 def charge(n):
  nonlocal used
  used+=n
  if used>max_operations:raise OverflowError('factor search construction budget')
 def product(a,c):
  charge(len(a)*len(c));return L.mul(a,c,max_terms=max_terms,max_operations=max_operations)
 for descriptor in catalog['selected']:
  result=FACTOR.build_block(block_spec(descriptor),N,N,target,max_horizon=max_horizon,max_operations=max_operations-used,max_terms=max_terms,max_degree=12)
  charge(result['cost']['operations']);normalization=F(1,N**descriptor['kernel_degree']);square_groups={f:[]for f in ('B','C_plus_R','prefix_plus_cell_contrast','prefix_minus_cell_contrast')};relation_groups={f:[]for f in ('B_plus_C_plus_R','T')};cells={}
  for cell in ('inside','complement'):
   part=result['parts'][cell];bilinear=L.scale(L.load_poly(part['bilinear']),normalization);projected=L.scale(L.add(L.load_poly(part['coprime_projection']),L.load_poly(part['noncoprime_residual'])),normalization);difference=L.add(bilinear,L.scale(projected,-1));plus=L.add(bilinear,projected)
   for key,p in (('B',bilinear),('C_plus_R',projected)):square_groups[key].append(dict(weight='1',poly=L.dump_poly(p)))
   for key,multiplier in (('B_plus_C_plus_R',plus),('T',difference)):
    for term in part['relations']:
     relation_groups[key].append(dict(spec=term['spec'],multiplier=L.dump_poly(product(L.scale(L.load_poly(term['multiplier']),normalization),multiplier))))
   # Exact closure identities verified symbolically, retaining all mixed terms.
   relation_sum={}
   for term in part['relations']:relation_sum=L.add(relation_sum,product(L.scale(L.load_poly(term['multiplier']),normalization),L.relation(term['spec'],target,N)))
   if relation_sum!=difference:raise ValueError('factor relation sum incomplete')
   if L.add(product(bilinear,bilinear),L.scale(product(projected,projected),-1))!=product(relation_sum,plus):raise ValueError('factor difference-square closure')
   cells[cell]=dict(pair_count=part['pair_count'],pairs_sha256=part['pairs_sha256'],projection_multiplicities=part['projection_multiplicities'],polynomial_sha256={key:B.digest(part[key])for key in ('bilinear','coprime_projection','noncoprime_residual')},zero_bilinear=not bilinear,zero_difference=not difference)
  charge(N*N)
  prefix=L.add(*(L.variable(n)for n in range(1,N+1)))
  Uinside=L.scale(L.add(L.load_poly(result['parts']['inside']['coprime_projection']),L.load_poly(result['parts']['inside']['noncoprime_residual'])),normalization)
  Ucomplement=L.scale(L.add(L.load_poly(result['parts']['complement']['coprime_projection']),L.load_poly(result['parts']['complement']['noncoprime_residual'])),normalization)
  contrast=L.add(Uinside,L.scale(Ucomplement,-1))
  square_groups['prefix_plus_cell_contrast']=[dict(weight='1',poly=L.dump_poly(L.add(prefix,contrast)))]
  square_groups['prefix_minus_cell_contrast']=[dict(weight='1',poly=L.dump_poly(L.add(prefix,L.scale(contrast,-1))))]
  b['instance']['square_groups'].extend(square_groups[k]for k in ('B','C_plus_R','prefix_plus_cell_contrast','prefix_minus_cell_contrast'));b['instance']['relation_groups'].extend(relation_groups[k]for k in ('B_plus_C_plus_R','T'))
  archive.append(dict(descriptor=descriptor,factor_scale=N,normalization=str(normalization),archive_polynomials='unnormalized complete source; builderpolynomials and primitive multipliers scaled by normalization',spec_sha256=result['spec_sha256'],cutoffs=result['cutoffs'],full_pair_count=result['parts']['full']['pair_count'],full_pairs_sha256=result['parts']['full']['pairs_sha256'],cells=cells,complete_partition_verified=True,difference_square_closure_verified=True))
 for group in b['instance']['square_groups'][106:]+b['instance']['relation_groups'][231:]:
  for term in group:
   poly=L.load_poly(term.get('poly',term.get('multiplier')));charge(len(poly))
   if len(poly)>max_terms:raise OverflowError('factor final term cap')
   if any(max(abs(v.numerator).bit_length(),v.denominator.bit_length())>max_coefficient_bits for v in poly.values()):raise OverflowError('factor final coefficient bits')
 b.update(square_ids=[v['id']for v in d['square']],relation_ids=[v['id']for v in d['relation']],dictionary_sha256=B.digest(d),construction_cost=used,factor_archive=archive,enumeration_catalog=catalog,factor_extension_scope='supplied complete factor/coprime closure; no signed estimate; full target preserved')
 return b
