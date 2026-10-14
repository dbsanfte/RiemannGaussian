"""Fixed-support rational reconstruction using FLINT, without floating proposals.
Caps cover declared dimensions, input/output bits and a conservative work proxy.
Native RREF is not interruptible: deadline is checked before/after the C call;
no hard internal C operation, intermediate-bit or elapsed-time cap is claimed.
"""
from fractions import Fraction as F
import time,math

def exact_support_solution(columns,lhs,support,*,deadline=None,max_rows=20000,max_columns=2000,max_cells=2000000,max_work=2000000000,max_denominator=2**4096,max_coefficient_bits=4096):
 for v in (max_rows,max_columns,max_cells,max_work,max_denominator,max_coefficient_bits):
  if type(v)is not int or v<1:raise ValueError('positive strict resource bounds')
 if deadline is not None and (type(deadline)not in(int,float)or not math.isfinite(deadline)):raise ValueError('absolute deadline')
 def checktime():
  if deadline is not None and time.monotonic()>deadline:raise TimeoutError('native reconstruction deadline; native call cannot be interrupted')
 checktime()
 if type(columns)is not list or type(lhs)is not dict or type(support)is not list or any(type(i)is not int or not 0<=i<len(columns)for i in support)or len(set(support))!=len(support):raise ValueError('sparse support schema')
 if len(support)>max_columns:raise OverflowError('support column cap')
 def exact(p):
  if type(p)is not dict:raise ValueError('sparse exact polynomial')
  out={}
  for key,value in p.items():
   if type(value)not in(int,F):raise ValueError('exact rational input only')
   q=F(value)
   if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('input coefficient bits')
   if q:out[key]=q
  return out
 target=exact(lhs);selected=[exact(columns[i])for i in support];keys=set(target)
 for p in selected:keys.update(p)
 # Caller supplies arbitrary hashable row labels; deterministic insertion-free ordering.
 try:rows=sorted(keys)
 except TypeError:raise ValueError('comparable row keys required')
 n=len(support);m=len(rows)
 if m>max_rows or m*(n+1)>max_cells or m*max(1,n)**2>max_work:raise OverflowError('native RREF dimension/work proxy')
 if not support:return []if not target else None
 from flint import fmpq_mat,fmpq
 matrix=fmpq_mat(m,n+1)
 for r,key in enumerate(rows):
  for j,p in enumerate(selected):
   q=p.get(key,F(0))
   if q:matrix[r,j]=fmpq(q.numerator,q.denominator)
  q=target.get(key,F(0))
  if q:matrix[r,n]=fmpq(q.numerator,q.denominator)
  if r%64==0:checktime()
 checktime();reduced,rank=matrix.rref();checktime();answer=[F(0)]*n
 for r in range(rank):
  pivot=next((j for j in range(n+1)if reduced[r,j]),None)
  if pivot is None:continue
  if pivot==n:return None
  q=reduced[r,n];v=F(int(q.numerator),int(q.denominator))
  if v.denominator>max_denominator or max(abs(v.numerator).bit_length(),v.denominator.bit_length())>max_coefficient_bits:raise OverflowError('output rational limits')
  answer[pivot]=v
 rebuilt={}
 for p,w in zip(selected,answer):
  for key,q in p.items():rebuilt[key]=rebuilt.get(key,F(0))+w*q
 if {k:v for k,v in rebuilt.items()if v}!=target:raise ValueError('native original equality mismatch')
 checktime();return answer

def reconstruct_dual_fixed_support(columns,lhs,monomials,nonnegative_indices,relation_indices,saved_support,*,time_limit=120,max_rows=2000,max_variables=60000,max_cells=2000000,max_work=2000000000,max_denominator=2**4096,max_coefficient_bits=4096):
 start=time.monotonic();diagnostics={'method':'saved support only; native exact RREF; no new floating LP','native_call_interruptible':False}
 try:
  if type(time_limit)not in(int,float)or time_limit<=0 or not math.isfinite(time_limit):raise ValueError('positive time limit')
  if any(type(v)is not int or v<1 for v in (max_rows,max_variables,max_cells,max_work,max_denominator,max_coefficient_bits)):raise ValueError('positive limits')
  if type(columns)is not list or type(lhs)is not dict or type(monomials)is not list or len(set(monomials))!=len(monomials):raise ValueError('dual exact domain')
  ids=nonnegative_indices+relation_indices
  if any(type(i)is not int or not 0<=i<len(columns)for i in ids)or len(set(ids))!=len(ids)or set(ids)!=set(range(len(columns))):raise ValueError('complete unique classifications')
  if set(monomials)!=set(lhs)|{m for p in columns for m in p}:raise ValueError('complete monomial domain')
  for p in columns+[lhs]:
   if type(p)is not dict or any(type(q)not in(int,F)for q in p.values()):raise ValueError('exact rational input only')
   if any(max(abs(F(q).numerator).bit_length(),F(q).denominator.bit_length())>max_coefficient_bits for q in p.values()):raise OverflowError('original coefficient bits')
  selected=relation_indices+nonnegative_indices;rows=len(selected)+1;M=len(monomials);variables=2*M+len(nonnegative_indices)
  if rows>max_rows or variables>max_variables:raise OverflowError('dual equation dimensions')
  if rows*variables>max_work:raise OverflowError('dual equation build proxy')
  eq=[]
  for m in monomials:
   p={j:F(columns[i].get(m,0))for j,i in enumerate(selected)if columns[i].get(m,0)}
   if lhs.get(m,0):p[rows-1]=F(lhs[m])
   eq.append(p)
  eq.extend({r:-q for r,q in p.items()}for p in eq[:M]);eq.extend({len(relation_indices)+j:F(-1)}for j in range(len(nonnegative_indices)))
  target={rows-1:F(-1)};deadline=start+time_limit
  answer=exact_support_solution(eq,target,saved_support,deadline=deadline,max_rows=max_rows,max_columns=max_variables,max_cells=max_cells,max_work=max_work,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits)
  diagnostics.update(equation_rows=rows,variables=variables,support_size=len(saved_support),elapsed_seconds=time.monotonic()-start)
  if answer is None or any(q<0 for q in answer):return dict(status='uncertified',certified=False,reason='saved support has no admitted nonnegative exact reconstruction',diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
  full=[F(0)]*variables
  for i,q in zip(saved_support,answer):full[i]=q
  y={m:full[j]-full[j+M]for j,m in enumerate(monomials)};dots=[sum((y[m]*F(q)for m,q in p.items()),F(0))for p in columns];bdot=sum((y[m]*F(q)for m,q in lhs.items()),F(0))
  if bdot!=-1 or any(dots[i]<0 for i in nonnegative_indices)or any(dots[i]!=0 for i in relation_indices):raise ValueError('original dual dot mismatch')
  return dict(status='exact_separator',certified=True,monomials=monomials,weights=[str(y[m])for m in monomials],columns_dot_y=list(map(str,dots)),lhs_dot_y=str(bdot),exact_support_weights=list(map(str,answer)),saved_support=saved_support,diagnostics=diagnostics,scope='declared finite cone; not an actual arithmetic bound refutation',global_bound_proved=False,RH_proved=False)
 except (OverflowError,TimeoutError,MemoryError,ImportError)as e:return dict(status='missing_resource',certified=False,reason=str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
 except (ValueError,TypeError,KeyError,ZeroDivisionError)as e:return dict(status='uncertified',certified=False,reason=str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
