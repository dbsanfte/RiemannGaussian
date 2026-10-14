"""Sufficient exact dual search for the full shared 5-atom PSD Gram cone.
Extra equations force offdiagonal Gram dual entries zero. Failure of this
restricted search says nothing about full Gram feasibility.
"""
from fractions import Fraction as F
import time,math
import grouped_arithmetic_synthesis as S
import arithmetic_cycle_language as L
import cancellation_gram_language as G
import cancellation_dual_column_search as A
from exact_dual_support_reconstruction import reconstruct_dual

def propose(instances,scales,allow_constant_slack=True,*,time_limit=60,max_denominator=2**4096,max_rows=1200,max_variables=40000,max_work=30000000,**limits):
 start=time.monotonic();defaults=dict(max_columns=1024,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=4096,max_degree=12);defaults.update(limits)
 try:
  if type(allow_constant_slack)is not bool or type(scales)is not list or len(scales)>len(instances):raise ValueError('declared scales/slack')
  if isinstance(time_limit,bool) or type(time_limit)not in (int,float) or not math.isfinite(time_limit) or time_limit<=0:raise ValueError('positive finite time limit')
  cols,lhs,ms,(ns,nr)=S._limits(instances,**defaults,deadline=start+time_limit)
  if allow_constant_slack:ms=S._add_slacks(cols,lhs,ms,len(instances),defaults['max_columns'],defaults['max_monomials'])
  original_count=len(cols);cross=[];atom_blocks={};used=0
  for region in ('parent','child'):
   blocks=[]
   for z,X in enumerate(scales):
    if type(X)is not int or X<1 or instances[z]['horizon']!=4*X-1:raise ValueError('ordinary scale horizon')
    start_t,end_t=(X,2*X) if region=='parent' else (2*X,4*X)
    blocks.append([[{(n,):F(1) for n in A._indices(atom,t)} for atom in A.ATOMS] for t in range(start_t,end_t)])
   atom_blocks[region]=blocks
   for i in range(5):
    for j in range(i+1,5):
     column={}
     for z,bs in enumerate(blocks):
      for atoms in bs:
       used+=len(atoms[i])*len(atoms[j])
       if used>defaults['max_operations']:raise OverflowError('dual Gram expansion work')
       p=L.mul(atoms[i],atoms[j],max_terms=defaults['max_monomials'],max_operations=defaults['max_operations'])
       for m,q in p.items():column[(z,)+m]=column.get((z,)+m,F(0))+q
     cross.append(column)
  for inst in instances[len(scales):]:
   if inst['target']!='mu' or inst['horizon']!=1 or inst['lhs']!=[] or any(inst['square_groups']):raise ValueError('auxiliary Gram domains must be empty')
  cols.extend(cross);ms=sorted(set(lhs)|{m for p in cols for m in p})
  if len(ms)>defaults['max_monomials']:raise OverflowError('extended Gram monomial limit')
  nonnegative=list(range(ns))+list(range(ns+2*nr,original_count));relations=list(range(ns,ns+2*nr))+list(range(original_count,len(cols)))
  remaining=time_limit-(time.monotonic()-start)
  if remaining<=0:raise TimeoutError('Gram preparation deadline')
  out=reconstruct_dual(cols,lhs,ms,nonnegative,relations,time_limit=remaining,max_rows=max_rows,max_variables=max_variables,max_work=max_work,max_denominator=max_denominator,max_coefficient_bits=defaults['max_coefficient_bits'])
  out['restricted_dual_search']='offdiagonal full Gram entries exactly zero; sufficient search only'
  if not out.get('certified'):return out
  y=dict(zip(ms,map(F,out['weights'])));gram_duals={}
  for region,blocks in atom_blocks.items():
   H=[[F(0) for _ in range(5)] for _ in range(5)]
   for z,bs in enumerate(blocks):
    for atoms in bs:
     for i in range(5):
      for j in range(i,5):
       p=L.mul(atoms[i],atoms[j],max_terms=defaults['max_monomials'],max_operations=defaults['max_operations'])
       if any((z,)+m not in y for m in p):raise ValueError('missing Gram dual coordinate')
       H[i][j]+=sum((q*y[(z,)+m] for m,q in p.items()),F(0));H[j][i]=H[i][j]
   if any(H[i][j] for i in range(5) for j in range(5) if i!=j):raise ValueError('nonzero restricted Gram cross')
   gram_duals[region]=dict(matrix=[[str(q) for q in row] for row in H],PSD_certificate=G.ldlt_psd(H,max_coefficient_bits=defaults['max_coefficient_bits']))
  out['monomials']=[dict(instance=m[0],m=list(m[1:])) for m in ms];out['extra_cross_dots']=out['columns_dot_y'][original_count:];out['columns_dot_y']=out['columns_dot_y'][:original_count];out['gram_duals']=gram_duals
  out['ordinary_constant_coordinates']=[str(y.get((z,),F(0))) for z in range(len(scales))];out['all_C_q_extension_requires_zero_constant_coordinates']=all(y.get((z,),F(0))==0 for z in range(len(scales)))
  out['scope']='exact separation of declared full shared Gram finite cone only; not actual arithmetic refutation';return out
 except (OverflowError,TimeoutError,MemoryError,ImportError) as e:return dict(status='missing_resource',certified=False,reason=str(e),restricted_dual_search=True,global_bound_proved=False)
 except (ValueError,TypeError,KeyError,ZeroDivisionError) as e:return dict(status='uncertified',certified=False,reason=str(e),restricted_dual_search=True,global_bound_proved=False)
