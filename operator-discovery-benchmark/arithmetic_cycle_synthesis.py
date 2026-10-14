"""Generic finite rational SOS synthesis. Float LP proposes support only.
No actual coefficient-response imports; no global bound or RH admission.
"""
from fractions import Fraction as F
import time,math
import arithmetic_cycle_language as language

def _positive(x,name):
 if type(x) is not int or x<1:raise ValueError(name+' positive integer required')
 return x

def exact_support_solution(columns,lhs,support,*,deadline=None,max_denominator=1000000,max_coefficient_bits=4096):
 """Exact RREF with free variables zero; returns None on inconsistency."""
 monomials=sorted(set(lhs)|{m for i in support for m in columns[i]});n=len(support);A=[[columns[i].get(m,F(0)) for i in support]+[lhs.get(m,F(0))] for m in monomials];pivots=[];row=0
 def guard():
  if deadline is not None and time.monotonic()>deadline:raise TimeoutError('exact reconstruction time limit')
 def check(q):
  if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('exact coefficient bit limit')
 for col in range(n):
  guard();pivot=next((j for j in range(row,len(A)) if A[j][col]),None)
  if pivot is None:continue
  A[row],A[pivot]=A[pivot],A[row];v=A[row][col];A[row]=[x/v for x in A[row]]
  for x in A[row]:check(x)
  for j in range(len(A)):
   guard()
   if j==row or not A[j][col]:continue
   v=A[j][col];A[j]=[x-v*y for x,y in zip(A[j],A[row])]
   for x in A[j]:check(x)
  pivots.append(col);row+=1
  if row==len(A):break
 if any(not any(r[:n]) and r[n] for r in A):return None
 answer=[F(0)]*n
 for j,col in enumerate(pivots):answer[col]=A[j][n]
 if any(q.denominator>max_denominator for q in answer):raise OverflowError('certificate denominator limit')
 return answer

def synthesize(target,horizon,lhs,square_basis,relation_columns,*,max_columns=256,max_monomials=4096,max_denominator=1000000,time_limit=30,max_coefficient_bits=4096,max_horizon=100000,max_degree=12,max_operations=1000000):
 start=time.monotonic();diagnostics={};deadline=None
 try:
  _positive(horizon,'horizon');_positive(max_horizon,'max horizon');_positive(max_degree,'degree');_positive(max_operations,'operations')
  if horizon>max_horizon:raise OverflowError('source horizon limit')
  _positive(max_columns,'columns');_positive(max_monomials,'monomials');_positive(max_denominator,'denominator');_positive(max_coefficient_bits,'coefficient bits')
  if isinstance(time_limit,bool) or not isinstance(time_limit,(int,float)) or not math.isfinite(time_limit) or time_limit<=0:raise ValueError('positive finite time limit')
  deadline=start+time_limit;operations=0
  if target not in ('mu','c') or type(square_basis)is not list or type(relation_columns)is not list:raise ValueError('synthesis domain')
  def guard():
   if time.monotonic()>deadline:raise TimeoutError('synthesis time limit')
  if len(square_basis)+2*len(relation_columns)>max_columns:raise OverflowError('LP column limit')
  def load(data):
   guard()
   if type(data)is not list:raise ValueError('canonical polynomial list required')
   if len(data)>max_monomials:raise OverflowError('input monomial limit')
   if any(type(t)is dict and type(t.get('m'))is list and len(t['m'])>max_degree for t in data):raise OverflowError('polynomial degree limit')
   p=language.load_poly(data)
   if len(p)>max_monomials:raise OverflowError('polynomial monomial limit')
   for m,q in p.items():
    if any(i>horizon for i in m):raise ValueError('index outside source horizon')
    if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('input coefficient bit limit')
   return p
  L=load(lhs);squares=[load(s) for s in square_basis];columns=[];origins=[]
  if len(squares)+2*len(relation_columns)>max_columns:raise OverflowError('LP column limit')
  def multiply(a,b):
   nonlocal operations
   operations+=len(a)*len(b)
   if operations>max_operations:raise OverflowError('total expansion operation limit')
   if any(len(x)+len(y)>max_degree for x in a for y in b):raise OverflowError('expanded degree limit')
   guard();return language.mul(a,b,max_terms=max_monomials,max_operations=max_operations)
  for i,p in enumerate(squares):columns.append(multiply(p,p));origins.append(('square',i,1))
  relations=[]
  for i,group in enumerate(relation_columns):
   guard()
   if type(group)is not list or not group:raise ValueError('nonempty grouped relation column')
   if len(group)>max_columns:raise OverflowError('grouped relation term limit')
   q={}
   for term in group:
    guard()
    if type(term)is not dict or set(term)!={'spec','multiplier'}:raise ValueError('grouped relation schema')
    p=load(term['multiplier']);rel=language.relation(term['spec'],target,horizon);q=language.add(q,multiply(p,rel))
    if len(q)>max_monomials:raise OverflowError('grouped monomial limit')
   relations.append(q);columns.extend([q,language.scale(q,-1)]);origins.extend([('relation',i,1),('relation',i,-1)])
  monomials=sorted(set(L)|{m for c in columns for m in c})
  if len(monomials)>max_monomials:raise OverflowError('matching monomial limit')
  for c in columns:
   for q in c.values():
    if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('expanded coefficient bit limit')
  guard();diagnostics.update(columns=len(columns),monomials=len(monomials),objective='sum all nonnegative LP variables, unit costs; signed relations plus/minus')
  if not L:answer=[F(0)]*len(columns);diagnostics['lp_status']='zero polynomial exact'
  else:
   if not columns:return dict(status='no_certificate_found',reason='empty declared basis cannot match nonzero lhs',solver_diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
   try:from scipy.optimize import linprog
   except ImportError:return dict(status='missing_resource',reason='scipy linprog unavailable',solver_diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
   matrix=[[float(c.get(m,F(0))) for c in columns] for m in monomials];rhs=[float(L.get(m,F(0))) for m in monomials];guard()
   if any(not math.isfinite(x) for row in matrix for x in row) or any(not math.isfinite(x) for x in rhs):raise OverflowError('finite float proposal conversion')
   remaining=deadline-time.monotonic();result=linprog([1.0]*len(columns),A_eq=matrix,b_eq=rhs,bounds=(0,None),method='highs',options={'time_limit':max(0.001,remaining)})
   diagnostics.update(lp_status=int(result.status),lp_success=bool(result.success),lp_message=str(result.message),float_weights=None if result.x is None else [float(x) for x in result.x],float_objective=None if result.fun is None else float(result.fun));guard()
   if not result.success and result.status==1:return dict(status='missing_resource',reason='native LP time or iteration limit; no infeasibility claim',solver_diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
   if not result.success:return dict(status='no_certificate_found',reason='float solver found no usable support; no mathematical infeasibility claim',solver_diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
   support=[i for i,x in enumerate(result.x) if x>1e-9];diagnostics['proposed_support']=support
   if len(monomials)*max(1,len(support))**2>max_operations:raise OverflowError('exact elimination operation bound')
   exact=exact_support_solution(columns,L,support,deadline=deadline,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits)
   if exact is None or any(x<0 for x in exact):return dict(status='no_certificate_found',reason='proposed support failed exact nonnegative reconstruction',solver_diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
   answer=[F(0)]*len(columns)
   for i,x in zip(support,exact):answer[i]=x
  reconstructed={}
  for q,c in zip(answer,columns):reconstructed=language.add(reconstructed,language.scale(c,q))
  if reconstructed!=L:return dict(status='no_certificate_found',reason='exact polynomial residue nonzero',solver_diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
  signed=[F(0)]*len(relations);cert_squares=[]
  for q,(kind,i,sign) in zip(answer,origins):
   if kind=='square' and q:cert_squares.append(dict(weight=str(q),poly=square_basis[i]))
   elif kind=='relation':signed[i]+=sign*q
  cert_relations=[]
  for q,group in zip(signed,relation_columns):
   if q:
    for term in group:cert_relations.append(dict(spec=term['spec'],multiplier=language.dump_poly(language.scale(load(term['multiplier']),q))))
  certificate=dict(target=target,horizon=horizon,lhs=lhs,squares=cert_squares,relations=cert_relations);guard()
  validation=language.compile_certificate(certificate,max_terms=max_monomials,max_operations=max_operations);guard()
  diagnostics.update(exact_lp_weights=list(map(str,answer)),signed_relation_weights=list(map(str,signed)),elapsed_seconds=time.monotonic()-start,optimality_claim=False)
  return dict(status='finite_certificate',certificate=certificate,validation=validation,solver_diagnostics=diagnostics,global_bound_proved=False,actual_all_scale_signed_bound_proved=False,RH_proved=False)
 except (OverflowError,TimeoutError,MemoryError) as e:return dict(status='missing_resource',reason=str(e),solver_diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
 except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError) as e:return dict(status='no_certificate_found',reason='invalid or rejected synthesis input: '+str(e),solver_diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
