"""Unrestricted exact joint span diagnostic. Signed squares are NOT SOS proofs."""
from fractions import Fraction as F
import time,math
import grouped_arithmetic_synthesis as G
from arithmetic_cycle_synthesis import exact_support_solution
from exact_dual_support_reconstruction import reconstruct_dual

def analyze(instances,*,include_constants=True,time_limit=60,dual_time_limit=90,max_columns=1024,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=4096,max_degree=12,max_denominator=2**4096,max_rows=1400,max_variables=60000,max_work=100000000):
 start=time.monotonic();diagnostics={};deadline=start+time_limit
 try:
  for v in (max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,max_denominator,max_rows,max_variables,max_work):
   if type(v)is not int or v<1:raise ValueError('positive resource bounds')
  if type(include_constants)is not bool or any(isinstance(v,bool) or type(v)not in (int,float) or not math.isfinite(v) or v<=0 for v in (time_limit,dual_time_limit)):raise ValueError('time/constant domain')
  columns,lhs,monomials,shape=G._limits(instances,max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,deadline)
  if include_constants:monomials=G._add_slacks(columns,lhs,monomials,len(instances),max_columns,max_monomials)
  diagnostics.update(column_count=len(columns),monomial_count=len(monomials),column_order='square groups, relation plus/minus pairs, optional per-instance constants; ALL signed',shape=list(shape))
  domain=[dict(instance=m[0],m=list(m[1:]))for m in monomials]
  full=None
  if not lhs:full=[F(0)]*len(columns)
  elif columns:
   if len(columns)*2*len(monomials)>max_work:raise OverflowError('dense span LP work cap')
   from scipy.optimize import linprog
   paired=columns+[{m:-v for m,v in p.items()}for p in columns]
   A=[[float(p.get(m,0))for p in paired]for m in monomials];b=[float(lhs.get(m,0))for m in monomials]
   if any(not math.isfinite(v)for row in A for v in row) or any(not math.isfinite(v)for v in b):raise OverflowError('float conversion')
   remaining=deadline-time.monotonic()
   if remaining<=0:raise TimeoutError('span preparation deadline')
   result=linprog([1.0]*len(paired),A_eq=A,b_eq=b,bounds=(0,None),method='highs',options={'time_limit':remaining})
   diagnostics.update(lp_status=int(result.status),lp_message=str(result.message),float_optimality_claim=False)
   if time.monotonic()>deadline or result.status==1:raise TimeoutError('span proposal limit')
   if result.success:
    support=[i for i,v in enumerate(result.x)if v>1e-9];diagnostics['support']=support
    if len(monomials)*max(1,len(support))**2>max_work:raise OverflowError('span exact elimination cap')
    exact=exact_support_solution(paired,lhs,support,deadline=deadline,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits)
    if exact is not None and all(v>=0 for v in exact):
     answer=[F(0)]*len(paired)
     for i,v in zip(support,exact):answer[i]=v
     full=[answer[i]-answer[i+len(columns)]for i in range(len(columns))]
  if full is not None:
   reconstruction={}
   for p,w in zip(columns,full):
    for m,v in p.items():reconstruction[m]=reconstruction.get(m,F(0))+w*v
   reconstruction={m:v for m,v in reconstruction.items()if v}
   if reconstruction!=lhs:raise ValueError('full original coefficient mismatch')
   polynomials=[[]for _ in instances]
   for m,v in sorted(reconstruction.items()):polynomials[m[0]].append(dict(m=list(m[1:]),c=str(v)))
   expanded_columns=[[dict(instance=m[0],m=list(m[1:]),c=str(v))for m,v in sorted(p.items())]for p in columns]
   return dict(status='exact_span_member',columns=expanded_columns,exact_weights=list(map(str,full)),monomials=domain,reconstructed_polynomials=polynomials,full_original_coefficient_match=True,diagnostics=diagnostics,positivity_certificate=False,global_bound_proved=False,RH_proved=False)
  dual=reconstruct_dual(columns,lhs,monomials,[],list(range(len(columns))),time_limit=dual_time_limit,max_rows=max_rows,max_variables=max_variables,max_work=max_work,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits)
  if dual.get('certified'):
   dual['monomials']=domain
   return dict(status='exact_span_obstruction',annihilator=dual,all_columns_dot_zero=True,lhs_dot_y='-1',diagnostics=diagnostics,scope='declared finite linear span only; not arithmetic bound refutation',positivity_certificate=False,global_bound_proved=False,RH_proved=False)
  return dict(status='missing_resource' if dual['status']=='missing_resource' else 'uncertified',annihilator_attempt=dual,diagnostics=diagnostics,positivity_certificate=False,global_bound_proved=False,RH_proved=False)
 except (OverflowError,TimeoutError,MemoryError,ImportError)as e:return dict(status='missing_resource',reason=str(e),diagnostics=diagnostics,positivity_certificate=False,global_bound_proved=False,RH_proved=False)
 except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError)as e:return dict(status='uncertified',reason=str(e),diagnostics=diagnostics,positivity_certificate=False,global_bound_proved=False,RH_proved=False)
