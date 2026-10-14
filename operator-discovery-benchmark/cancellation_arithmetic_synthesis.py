"""Structural-only L1 proposal objective; exact grouped certificate admission unchanged.
Scalar slack has zero cost, so scalar padding cannot improve this objective.
No uniqueness, minimality or all-scale conclusion is inferred from numerical LP.
"""
from fractions import Fraction as F
import time,math
import grouped_arithmetic_synthesis as G
from arithmetic_cycle_synthesis import exact_support_solution

def objective_costs(square_count,relation_count,instance_count,allow_constant_slack=True):
 if any(type(v)is not int or v<0 for v in (square_count,relation_count,instance_count)) or type(allow_constant_slack)is not bool:raise ValueError('objective shape')
 return [1]*(square_count+2*relation_count)+([0]*instance_count if allow_constant_slack else [])

def synthesize(instances,*,allow_constant_slack=True,max_columns=1024,max_monomials=10000,max_operations=200000000,max_coefficient_bits=2048,max_horizon=4096,max_degree=12,max_denominator=1000000,time_limit=10):
 start=time.monotonic();diagnostics={'objective':'structural-only L1: square/relation plus-minus costs1; per-instance constant slack cost0','lp_optimality_claim':False}
 try:
  for v in (max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,max_denominator):
   if type(v)is not int or v<1:raise ValueError('positive limits')
  if type(allow_constant_slack)is not bool or isinstance(time_limit,bool) or not isinstance(time_limit,(int,float)) or not math.isfinite(time_limit) or time_limit<=0:raise ValueError('limit/flag domain')
  deadline=start+time_limit
  limits=dict(max_columns=max_columns,max_monomials=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,max_degree=max_degree)
  columns,lhs,monomials,shape=G._limits(instances,**limits,deadline=deadline)
  if allow_constant_slack:monomials=G._add_slacks(columns,lhs,monomials,len(instances),max_columns,max_monomials)
  costs=objective_costs(*shape,len(instances),allow_constant_slack);diagnostics['objective_costs']=costs
  if not lhs:answer=[F(0)]*len(columns)
  else:
   if not columns:return dict(status='no_certificate_found',reason='no columns',diagnostics=diagnostics,global_bound_proved=False)
   from scipy.optimize import linprog
   A=[[float(p.get(m,0))for p in columns]for m in monomials];b=[float(lhs.get(m,0))for m in monomials]
   if any(not math.isfinite(v) for row in A for v in row) or any(not math.isfinite(v)for v in b):raise OverflowError('float conversion')
   result=linprog(costs,A_eq=A,b_eq=b,bounds=(0,None),method='highs',options={'time_limit':max(.001,deadline-time.monotonic())})
   diagnostics.update(lp_status=int(result.status),lp_message=str(result.message),float_objective=None if result.fun is None else float(result.fun))
   if time.monotonic()>deadline:raise TimeoutError('proposal deadline')
   if not result.success:return dict(status='missing_resource' if result.status==1 else 'no_certificate_found',reason='no float support; not mathematical infeasibility',diagnostics=diagnostics,global_bound_proved=False)
   support=[i for i,v in enumerate(result.x)if v>1e-9];diagnostics['proposed_support']=support
   if len(monomials)*max(1,len(support))**2>max_operations:raise OverflowError('elimination budget')
   exact=exact_support_solution(columns,lhs,support,deadline=deadline,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits)
   if exact is None or any(w<0 for w in exact):return dict(status='no_certificate_found',reason='support not exactly reconstructed',diagnostics=diagnostics,global_bound_proved=False)
   answer=[F(0)]*len(columns)
   for i,w in zip(support,exact):answer[i]=w
  residue={}
  for p,w in zip(columns,answer):
   for m,v in p.items():residue[m]=residue.get(m,F(0))+v*w
  if {m:v for m,v in residue.items()if v}!=lhs:raise ValueError('exact coefficient mismatch')
  n,r=shape;weights=dict(square_weights=list(map(str,answer[:n])),relation_weights=[str(answer[n+2*j]-answer[n+2*j+1])for j in range(r)])
  certs=[G.instantiate_certificate(i,weights,**limits,max_denominator=max_denominator,time_limit=time_limit,deadline=deadline,allow_constant_slack=allow_constant_slack)for i in instances]
  diagnostics.update(exact_lp_weights=list(map(str,answer)),exact_structural_objective=str(sum(F(c)*w for c,w in zip(costs,answer))),elapsed_seconds=time.monotonic()-start)
  return dict(status='finite_certificate',weights=weights,constant_slacks=list(map(str,answer[n+2*r:]))if allow_constant_slack else [],allow_constant_slack=allow_constant_slack,certificates=certs,diagnostics=diagnostics,global_bound_proved=False,RH_proved=False,scope='finite shared structural identity; zero-cost evaluated scalar residual; no optimality or global estimate')
 except (OverflowError,TimeoutError,MemoryError,ImportError)as e:return dict(status='missing_resource',reason=str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
 except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError)as e:return dict(status='no_certificate_found',reason='rejected: '+str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
