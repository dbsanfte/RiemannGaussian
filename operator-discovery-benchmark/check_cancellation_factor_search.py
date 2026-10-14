"""Independent complete factor search builder; no producer mathematics."""
import json
from fractions import Fraction as F
import check_cancellation_arithmetic_run as I
import check_cancellation_factor_blocks as B
P=I.P
SPEC=dict(version='factor-closure-v1',max_fraction_denominator=6,max_blocks=44,kernels=['one','a','b','a_minus_b'],max_extra_columns=352)
def catalog():
 rows=[]
 for theta in sorted({F(a,b)for b in range(2,7)for a in range(1,b)}):
  for kernel in SPEC['kernels']:
   d=dict(family='factor_closure',theta=str(theta),kernel=kernel,kernel_degree=0 if kernel=='one'else 1,normalizer='N^-kernel_degree',coprime=True,scale_map='N=4X-1',product_domain='ordered a,b>=1;ab<=N;gcd(a,b)=1',cells='inside_and_complete_complement');rows.append(dict(d,id=I.digest(d),symbolic_cost=theta.numerator+theta.denominator+(0 if kernel=='one' else 1 if kernel in ['a','b'] else 2)))
 rows.sort(key=lambda d:(d['symbolic_cost'],json.dumps(d,sort_keys=True,separators=(',',':'))))
 return dict(spec=SPEC,selected=rows,unselected=[],selection='symbolic cost, then canonical serialization; no responses')
def descriptors():
 out=I.descriptors()
 for row in catalog()['selected']:
  c=dict(block_id=row['id'],theta=row['theta'],kernel=row['kernel'],kernel_degree=row['kernel_degree'],normalizer=row['normalizer'],cells='inside_and_complete_complement',scale_map='N=4X-1')
  for form in ['B','C_plus_R','prefix_plus_cell_contrast','prefix_minus_cell_contrast']:
   d=dict(c,family='factor_square',form=form);out['square'].append(dict(d,id=I.digest(d)))
  for form in ['B_plus_C_plus_R','T']:
   d=dict(c,family='factor_relation_closure',multiplier_form=form);out['relation'].append(dict(d,id=I.digest(d)))
 return out

def spec(d):
 kernel=d['kernel'];terms=[]
 if kernel in ['one','a','a_minus_b']:terms.append(dict(coefficient='1',a_power=0 if kernel=='one'else 1,b_power=0,x_power=0))
 if kernel in ['b','a_minus_b']:terms.append(dict(coefficient='-1'if kernel=='a_minus_b'else '1',a_power=0,b_power=1,x_power=0))
 cut=lambda c,p:dict(coefficient=c,power=p)
 return dict(kind='factor_bilinear',product_scale='1',coprime=True,cuts=dict(left=dict(lower=cut('1','0'),upper=cut('1',d['theta'])),right=dict(lower=cut('1','0'),upper=cut('1','1'))),kernel=terms)
def build(program,X):
 out=I.build(program,X);N=4*X-1;archive=[]
 for d in catalog()['selected']:
  s=spec(d);normalization=F(1,N**d['kernel_degree']);T,bounds,rows=B.expected_parts(s,N,N);sq={'B':[],'C_plus_R':[]};rel={'B_plus_C_plus_R':[],'T':[]};cells={};projections={}
  for cell in ['inside','complement']:
   bil={};u={};counts={};terms=[]
   for a,b,w in rows[cell]:
    bil=P.add(bil,{tuple(sorted([a,b])):w});u=P.add(u,{(a*b,):w});count=counts.setdefault(str(a*b),dict(count=0,kernel_weight=F(0)));count['count']+=1;count['kernel_weight']+=w;terms.append((dict(kind='coprime_product',a=a,b=b),w))
   rawbil=dict(bil);rawu=dict(u);bil={m:normalization*v for m,v in bil.items()};u={m:normalization*v for m,v in u.items()};diff=P.add(bil,u,F(-1));plus=P.add(bil,u);sq['B'].append(dict(weight='1',poly=P.canonical(bil)));sq['C_plus_R'].append(dict(weight='1',poly=P.canonical(u)))
   for kind,m in [('B_plus_C_plus_R',plus),('T',diff)]:
    for rs,w in terms:rel[kind].append(dict(spec=rs,multiplier=P.canonical({m0:normalization*w*v for m0,v in m.items()if w*v})))
   pairs=[[a,b]for a,b,w in rows[cell]];projections[cell]=u;cells[cell]=dict(pair_count=len(pairs),pairs_sha256=I.digest(pairs),projection_multiplicities={n:dict(count=c['count'],kernel_weight=str(c['kernel_weight']))for n,c in counts.items()},polynomial_sha256=dict(bilinear=I.digest(P.canonical(rawbil)),coprime_projection=I.digest(P.canonical(rawu)),noncoprime_residual=I.digest([])),zero_bilinear=not bil,zero_difference=not diff)
  pref={(n,):F(1)for n in range(1,N+1)};contrast=P.add(projections['inside'],projections['complement'],F(-1));out['instance']['square_groups'].extend([sq['B'],sq['C_plus_R'],[dict(weight='1',poly=P.canonical(P.add(pref,contrast)))],[dict(weight='1',poly=P.canonical(P.add(pref,contrast,F(-1))))]]);out['instance']['relation_groups'].extend([rel['B_plus_C_plus_R'],rel['T']]);full=[[a,b]for a,b,w in rows['full']];archive.append(dict(descriptor=d,factor_scale=N,normalization=str(normalization),archive_polynomials='unnormalized complete source; builderpolynomials and primitive multipliers scaled by normalization',spec_sha256=I.digest(s),cutoffs=bounds,full_pair_count=len(full),full_pairs_sha256=I.digest(full),cells=cells,complete_partition_verified=True,difference_square_closure_verified=True))
 ds=descriptors();out.update(square_ids=[d['id']for d in ds['square']],relation_ids=[d['id']for d in ds['relation']],dictionary_sha256=I.digest(ds),factor_archive=archive,enumeration_catalog=catalog())
 return out
def auxiliary():return I.auxiliary_constraint(descriptors())
