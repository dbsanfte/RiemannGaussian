"""Posthoc finite Farkas support reconstruction; no global mathematical claims.
Floating LP proposes support; exact equality reconstruction and original dots
are mandatory. No frozen search artifact is altered.
"""
from fractions import Fraction as F
import math,time
from arithmetic_cycle_synthesis import exact_support_solution

def _positive(n):
 if type(n)is not int or n<1:raise ValueError('positive strict integer limit')
 return n

def reconstruct_dual(columns,lhs,monomials,nonnegative_indices,relation_indices,*,time_limit=30,max_rows=1200,max_variables=20000,max_work=5000000,max_denominator=1000000,max_coefficient_bits=4096):
 start=time.monotonic();diagnostics={}
 try:
  for x in (max_rows,max_variables,max_work,max_denominator,max_coefficient_bits):_positive(x)
  if isinstance(time_limit,bool) or type(time_limit)not in (int,float) or not math.isfinite(time_limit) or time_limit<=0:raise ValueError('finite positive time limit')
  deadline=start+time_limit
  if type(columns)is not list or type(lhs)is not dict or type(monomials)is not list or len(set(monomials))!=len(monomials):raise ValueError('finite column domain')
  if type(nonnegative_indices)is not list or type(relation_indices)is not list:raise ValueError('column classification')
  ids=nonnegative_indices+relation_indices
  if any(type(i)is not int or not 0<=i<len(columns) for i in ids) or len(set(ids))!=len(ids) or set(ids)!=set(range(len(columns))):raise ValueError('complete unique column classifications')
  if set(monomials)!=set(lhs)|{m for p in columns for m in p}:raise ValueError('complete monomial domain')
  for p in columns+[lhs]:
   if type(p)is not dict or any(type(q)not in (F,int) for q in p.values()):raise ValueError('exact rational columns')
   if any(max(abs(F(q).numerator).bit_length(),F(q).denominator.bit_length())>max_coefficient_bits for q in p.values()):raise OverflowError('input coefficient bits')
  # Each relation yields equality; each square yields a nonnegative slack equation.
  selected=relation_indices+nonnegative_indices;rows=len(selected)+1;M=len(monomials);variables=2*M+len(nonnegative_indices)
  if rows>max_rows or variables>max_variables or rows*variables>max_work:raise OverflowError('dual dense equation preflight')
  equations=[]
  for m in monomials:
   p={j:F(columns[i].get(m,0)) for j,i in enumerate(selected) if columns[i].get(m,0)}
   if lhs.get(m,0):p[rows-1]=F(lhs[m])
   equations.append(p)
  equations +=[{r:-q for r,q in p.items()} for p in equations[:M]]
  equations +=[{len(relation_indices)+j:F(-1)} for j in range(len(nonnegative_indices))]
  target={rows-1:F(-1)}
  from scipy.optimize import linprog
  matrix=[[float(p.get(r,0)) for p in equations] for r in range(rows)];rhs=[0.0]*(rows-1)+[-1.0]
  if any(not math.isfinite(v) for row in matrix for v in row):raise OverflowError('float conversion')
  remaining=deadline-time.monotonic()
  if remaining<=0:raise TimeoutError('dual proposal deadline')
  result=linprog([1.0]*variables,A_eq=matrix,b_eq=rhs,bounds=(0,None),method='highs',options={'time_limit':remaining})
  diagnostics=dict(equation_rows=rows,variables=variables,lp_status=int(result.status),lp_success=bool(result.success),support_method='nonnegative y+/y- plus square slack; positive L1 objective; exact reconstruction',optimality_claim=False)
  if time.monotonic()>deadline:raise TimeoutError('dual support deadline')
  if not result.success:return dict(status='uncertified',certified=False,reason='no usable float support; no cone conclusion',diagnostics=diagnostics,global_bound_proved=False)
  support=[i for i,x in enumerate(result.x) if x>1e-9];diagnostics['support']=support
  if rows*max(1,len(support))**2>max_work:raise OverflowError('exact dual elimination preflight')
  answer=exact_support_solution(equations,target,support,deadline=deadline,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits)
  if answer is None or any(q<0 for q in answer):return dict(status='uncertified',certified=False,reason='support failed exact nonnegative equations',diagnostics=diagnostics,global_bound_proved=False)
  full=[F(0)]*variables
  for i,q in zip(support,answer):full[i]=q
  reconstructed={}
  for w,p in zip(full,equations):
   for r,q in p.items():reconstructed[r]=reconstructed.get(r,F(0))+w*q
  if {r:q for r,q in reconstructed.items() if q}!=target:raise ValueError('exact equality reconstruction mismatch')
  y={m:full[j]-full[j+M] for j,m in enumerate(monomials)};dots=[sum((y[m]*F(q) for m,q in p.items()),F(0)) for p in columns];bdot=sum((y[m]*F(q) for m,q in lhs.items()),F(0))
  if bdot!=-1 or any(dots[i]<0 for i in nonnegative_indices) or any(dots[i]!=0 for i in relation_indices):raise ValueError('original exact Farkas dot failure')
  return dict(status='exact_separator',certified=True,monomials=monomials,weights=list(map(str,(y[m] for m in monomials))),columns_dot_y=list(map(str,dots)),lhs_dot_y=str(bdot),diagnostics=diagnostics,scope='declared finite cone only, not false actual arithmetic',global_bound_proved=False,RH_proved=False)
 except (OverflowError,TimeoutError,MemoryError,ImportError) as e:return dict(status='missing_resource',certified=False,reason=str(e),diagnostics=diagnostics,global_bound_proved=False)
 except (ValueError,TypeError,KeyError,ZeroDivisionError) as e:return dict(status='uncertified',certified=False,reason=str(e),diagnostics=diagnostics,global_bound_proved=False)

def reconstruct_joint_separator(instances,*,allow_constant_slack=False,time_limit=30,max_rows=1200,max_variables=20000,max_work=5000000,max_denominator=1000000,**limits):
 import grouped_arithmetic_synthesis as S
 if type(allow_constant_slack)is not bool:raise ValueError('boolean slack mode')
 if isinstance(time_limit,bool) or type(time_limit)not in (int,float) or not math.isfinite(time_limit) or time_limit<=0:raise ValueError('finite positive time limit')
 start=time.monotonic();defaults=dict(max_columns=1024,max_monomials=10000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=4096,max_degree=12);defaults.update(limits)
 try:
  cols,lhs,ms,(ns,nr)=S._limits(instances,**defaults,deadline=start+time_limit)
  if allow_constant_slack:ms=S._add_slacks(cols,lhs,ms,len(instances),defaults['max_columns'],defaults['max_monomials'])
  remaining=time_limit-(time.monotonic()-start)
  if remaining<=0:raise TimeoutError('joint preparation deadline')
  nonnegative=list(range(ns))+list(range(ns+2*nr,len(cols)));relations=list(range(ns,ns+2*nr))
  out=reconstruct_dual(cols,lhs,ms,nonnegative,relations,time_limit=remaining,max_rows=max_rows,max_variables=max_variables,max_work=max_work,max_denominator=max_denominator,max_coefficient_bits=defaults['max_coefficient_bits'])
  if out['certified']:out['monomials']=[dict(instance=m[0],m=list(m[1:])) for m in out['monomials']]
  return out
 except (OverflowError,TimeoutError,MemoryError) as e:return dict(status='missing_resource',certified=False,reason=str(e),global_bound_proved=False)
