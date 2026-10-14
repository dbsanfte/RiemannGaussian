"""Exact proportional augmented-row compression before fixed-support native RREF.
No floating proposal/refit. All original equations are checked after solution.
Native C calls require an external process deadline for hard elapsed bounds.
"""
from fractions import Fraction as F
import hashlib,json,time,math
import native_exact_support as N

def digest(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()

def exact_support_solution(columns,lhs,support,*,deadline=None,max_rows=20000,max_columns=2000,max_cells=2000000,max_work=450000000,max_denominator=2**4096,max_coefficient_bits=4096,max_preprocessing_operations=200000000,max_preprocessing_cells=4000000,diagnostics=None):
 for value in (max_rows,max_columns,max_cells,max_work,max_denominator,max_coefficient_bits,max_preprocessing_operations,max_preprocessing_cells):
  if type(value)is not int or value<1:raise ValueError('positive strict resource bounds')
 if deadline is not None and(type(deadline)not in(int,float)or not math.isfinite(deadline)):raise ValueError('absolute deadline')
 if diagnostics is None:diagnostics={}
 used=0;cells=0
 def charge(work=1,new_cells=0):
  nonlocal used,cells
  used+=work;cells+=new_cells
  if used>max_preprocessing_operations or used>max_work:raise OverflowError('compression preprocessing work cap')
  if cells>max_preprocessing_cells:raise OverflowError('compression preprocessing cell cap')
  if deadline is not None and time.monotonic()>deadline:raise TimeoutError('compression deadline; native call is not interruptible')
 def rational(q):
  charge()
  if type(q)not in(int,F):raise ValueError('exact rational input only')
  q=F(q)
  if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('compression coefficient bits')
  return q
 charge(0)
 if type(columns)is not list or type(lhs)is not dict or type(support)is not list or any(type(i)is not int or not 0<=i<len(columns)for i in support)or len(set(support))!=len(support):raise ValueError('sparse support schema')
 if len(support)>max_columns:raise OverflowError('support column cap')
 selected=[];keys=set(lhs);n=len(support)
 for i in support:
  if type(columns[i])is not dict:raise ValueError('sparse exact polynomial')
  p={}
  for key,q in columns[i].items():
   q=rational(q);keys.add(key)
   if q:p[key]=q;charge(new_cells=1)
  selected.append(p)
 target={key:rational(q)for key,q in lhs.items()}
 try:labels=sorted(keys)
 except TypeError:raise ValueError('comparable row keys required')
 if len(labels)>max_rows:raise OverflowError('original row cap')
 row_lookup={key:r for r,key in enumerate(labels)};rows=[{}for _ in labels]
 for j,p in enumerate(selected):
  for key,q in p.items():rows[row_lookup[key]][j]=q;charge(new_cells=1)
 for key,q in target.items():
  if q:rows[row_lookup[key]][n]=q;charge(new_cells=1)
 encoded=[];seen={};retained=[];mapping=[];pivots={}
 for r,row in enumerate(rows):
  charge()
  encoded.append([[j,str(q)]for j,q in sorted(row.items())])
  if not row:mapping.append(dict(row=r,representative=None,ratio='0'));continue
  pivot=row[min(row)];normalized=[]
  for j,q in sorted(row.items()):normalized.append((j,rational(q/pivot)));charge(new_cells=1)
  signature=tuple(normalized)
  if signature not in seen:seen[signature]=r;retained.append(r);pivots[r]=pivot
  representative=seen[signature];ratio=rational(pivot/pivots[representative])
  # Verify the saved ratio exactly now; checker can repeat from original data.
  for j,q in row.items():
   charge();rational(ratio*rows[representative].get(j,F(0)))
   if q!=ratio*rows[representative].get(j,F(0)):raise ValueError('compression proportional mapping mismatch')
  mapping.append(dict(row=r,representative=representative,ratio=str(ratio)))
 reduced_columns=[{}for _ in support];reduced_target={}
 for k,r in enumerate(retained):
  for j,q in rows[r].items():
   charge(new_cells=1)
   if j==n:reduced_target[k]=q
   else:reduced_columns[j][k]=q
 native_proxy=len(retained)*max(1,n)**2
 # Reserve work for post-native full-original equality verification as well.
 verification_proxy=4*sum(map(len,selected))+len(target)+len(labels)+1
 total=used+native_proxy+verification_proxy
 info=dict(original_row_labels=labels,retained_rows=retained,mapping=mapping,original_system_hash=digest(encoded),original_row_order_hash=digest(labels),
  original_rows=len(labels),reduced_rows=len(retained),support_size=n,original_work_proxy=len(labels)*max(1,n)**2,
  preprocessing_work=used,verification_work_reserve=verification_proxy,native_work_proxy=native_proxy,total_work_proxy=total,preprocessing_cells=cells)
 diagnostics['row_compression']=info
 if total>max_work:raise OverflowError('compressed native plus preprocessing total work proxy')
 answer=N.exact_support_solution(reduced_columns,reduced_target,list(range(n)),deadline=deadline,max_rows=max_rows,max_columns=max_columns,max_cells=max_cells,max_work=max_work-used-verification_proxy,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits)
 if answer is None:return None
 rebuilt={}
 for p,w in zip(selected,answer):
  for key,q in p.items():
   charge(2);value=rational(rebuilt.get(key,F(0))+rational(w*q))
   if value:rebuilt[key]=value
   else:rebuilt.pop(key,None)
 if rebuilt!={key:q for key,q in target.items()if q}:raise ValueError('compressed full original equality mismatch')
 charge()
 info['preprocessing_actual_work']=used
 return answer

def reconstruct_dual_fixed_support(columns,lhs,monomials,nonnegative_indices,relation_indices,saved_support,*,time_limit=120,max_rows=2000,max_variables=60000,max_cells=2000000,max_work=450000000,max_denominator=2**4096,max_coefficient_bits=4096,max_preprocessing_operations=200000000,max_preprocessing_cells=4000000):
 start=time.monotonic();diagnostics={'method':'saved support only; exact augmented row compression; native RREF; no new floating LP','native_call_interruptible':False}
 try:
  if type(time_limit)not in(int,float)or time_limit<=0 or not math.isfinite(time_limit):raise ValueError('positive time limit')
  if any(type(v)is not int or v<1 for v in (max_rows,max_variables,max_cells,max_work,max_denominator,max_coefficient_bits,max_preprocessing_operations,max_preprocessing_cells)):raise ValueError('positive limits')
  if type(columns)is not list or type(lhs)is not dict or type(monomials)is not list or len(set(monomials))!=len(monomials):raise ValueError('dual exact domain')
  ids=nonnegative_indices+relation_indices
  if any(type(i)is not int or not 0<=i<len(columns)for i in ids)or len(set(ids))!=len(ids)or set(ids)!=set(range(len(columns))):raise ValueError('complete unique classifications')
  if set(monomials)!=set(lhs)|{m for p in columns for m in p}:raise ValueError('complete monomial domain')
  for p in columns+[lhs]:
   if type(p)is not dict or any(type(q)not in(int,F)for q in p.values()):raise ValueError('exact rational input only')
   if any(max(abs(F(q).numerator).bit_length(),F(q).denominator.bit_length())>max_coefficient_bits for q in p.values()):raise OverflowError('original coefficient bits')
  selected=relation_indices+nonnegative_indices;rows=len(selected)+1;M=len(monomials);variables=2*M+len(nonnegative_indices)
  if rows>max_rows or variables>max_variables:raise OverflowError('dual equation dimensions')
  build_proxy=rows*variables
  dual_verification_proxy=3*sum(map(len,columns))+2*len(lhs)+variables+2*M+len(saved_support)+1
  if build_proxy+dual_verification_proxy>=max_work:raise OverflowError('dual equation build proxy')
  eq=[]
  for m in monomials:
   p={j:F(columns[i].get(m,0))for j,i in enumerate(selected)if columns[i].get(m,0)}
   if lhs.get(m,0):p[rows-1]=F(lhs[m])
   eq.append(p)
  eq.extend({r:-q for r,q in p.items()}for p in eq[:M]);eq.extend({len(relation_indices)+j:F(-1)}for j in range(len(nonnegative_indices)))
  target={rows-1:F(-1)};deadline=start+time_limit
  try:
   answer=exact_support_solution(eq,target,saved_support,deadline=deadline,max_rows=max_rows,max_columns=max_variables,max_cells=max_cells,max_work=max_work-build_proxy-dual_verification_proxy,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits,max_preprocessing_operations=max_preprocessing_operations,max_preprocessing_cells=max_preprocessing_cells,diagnostics=diagnostics)
  finally:
   if 'row_compression'in diagnostics:
    diagnostics['row_compression']['dual_build_work_proxy']=build_proxy
    diagnostics['row_compression']['dual_verification_work_reserve']=dual_verification_proxy
    diagnostics['row_compression']['total_work_proxy']+=build_proxy+dual_verification_proxy
  diagnostics.update(equation_rows=rows,variables=variables,support_size=len(saved_support),elapsed_seconds=time.monotonic()-start)
  if answer is None or any(q<0 for q in answer):return dict(status='uncertified',certified=False,reason='saved support has no admitted nonnegative exact reconstruction',diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
  full=[F(0)]*variables
  for i,q in zip(saved_support,answer):full[i]=q
  def checked(q):
   if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('dual verification coefficient bits')
   if time.monotonic()>deadline:raise TimeoutError('dual verification deadline')
   return q
  y={m:checked(full[j]-full[j+M])for j,m in enumerate(monomials)}
  def dot(p):
   total=F(0)
   for m,q in p.items():total=checked(total+checked(y[m]*F(q)))
   return total
  dots=[dot(p)for p in columns];bdot=dot(lhs)
  if bdot!=-1 or any(dots[i]<0 for i in nonnegative_indices)or any(dots[i]!=0 for i in relation_indices):raise ValueError('original dual dot mismatch')
  return dict(status='exact_separator',certified=True,monomials=monomials,weights=[str(y[m])for m in monomials],columns_dot_y=list(map(str,dots)),lhs_dot_y=str(bdot),exact_support_weights=list(map(str,answer)),saved_support=saved_support,diagnostics=diagnostics,scope='declared finite cone; not an actual arithmetic bound refutation',global_bound_proved=False,RH_proved=False)
 except (OverflowError,TimeoutError,MemoryError,ImportError)as e:return dict(status='missing_resource',certified=False,reason=str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
 except (ValueError,TypeError,KeyError,ZeroDivisionError)as e:return dict(status='uncertified',certified=False,reason=str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
