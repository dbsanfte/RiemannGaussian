"""Shared rational grouped cone synthesis; finite identities, no RH estimate."""
from fractions import Fraction as F
import time,math
import grouped_arithmetic_language as L
from arithmetic_cycle_synthesis import exact_support_solution

def _limits(instances,max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,deadline):
 if type(instances)is not list or not instances:raise ValueError('nonempty instances required')
 columns=None;lhs={};parsed=[];operations=0;shape=None
 def check(poly,horizon):
  if type(poly)is not list or len(poly)>max_monomials:raise OverflowError('input polynomial terms')
  p=L.load_poly(poly)
  for m,q in p.items():
   if len(m)>max_degree:raise OverflowError('polynomial degree limit')
   if any(i>horizon for i in m):raise ValueError('index outside horizon')
   if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('coefficient bits')
  return p
 def multiply(a,b):
  nonlocal operations
  operations+=len(a)*len(b)
  if operations>max_operations or time.monotonic()>deadline:raise OverflowError('expansion work/time')
  if any(len(x)+len(y)>max_degree for x in a for y in b):raise OverflowError('expanded polynomial degree')
  return L.mul(a,b,max_terms=max_monomials,max_operations=max_operations)
 for index,instance in enumerate(instances):
  if type(instance)is not dict or set(instance)!={'target','horizon','lhs','square_groups','relation_groups'}:raise ValueError('instance schema')
  H=instance['horizon'];target=instance['target']
  if type(H)is not int or H<1 or target not in ('mu','c'):raise ValueError('instance domain')
  if H>max_horizon:raise OverflowError('horizon limit')
  squares=instance['square_groups'];relations=instance['relation_groups']
  if type(squares)is not list or type(relations)is not list:raise ValueError('group arrays')
  current=(len(squares),len(relations))
  if shape is None:
   shape=current
   if current[0]+2*current[1]>max_columns:raise OverflowError('column limit')
   columns=[{} for _ in range(current[0]+2*current[1])]
  if shape!=current:raise ValueError('shared group count/order mismatch')
  b=check(instance['lhs'],H)
  for m,q in b.items():lhs[(index,)+m]=q
  expanded=[]
  for group in squares:
   if type(group)is not list or len(group)>max_operations:raise ValueError('square group list')
   column={}
   for term in group:
    if type(term)is not dict or set(term)!={'weight','poly'} or type(term['weight'])is not str:raise ValueError('square group term')
    w=F(term['weight'])
    if w<0 or str(w)!=term['weight']:raise ValueError('nonnegative canonical fixed square weight')
    if max(abs(w.numerator).bit_length(),w.denominator.bit_length())>max_coefficient_bits:raise OverflowError('fixed square weight coefficient bits')
    p=check(term['poly'],H);column=L.add(column,L.scale(multiply(p,p),w))
   expanded.append(column)
  for group in relations:
   if type(group)is not list:raise ValueError('relation group list')
   column={}
   for term in group:
    if type(term)is not dict or set(term)!={'spec','multiplier'}:raise ValueError('relation group term')
    p=check(term['multiplier'],H);r=L.relation(term['spec'],target,H,max_operations=max_operations);column=L.add(column,multiply(p,r))
   expanded.extend([column,L.scale(column,-1)])
  for dest,p in zip(columns,expanded):
   if len(p)>max_monomials:raise OverflowError('expanded group terms')
   for m,q in p.items():
    if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('expanded coefficient bits')
    dest[(index,)+m]=q
  parsed.append(instance)
 monomials=sorted(set(lhs)|{m for p in columns for m in p})
 if len(monomials)>max_monomials:raise OverflowError('stacked monomial limit')
 return columns,lhs,monomials,shape

def _add_slacks(columns,lhs,monomials,count,max_columns,max_monomials):
 if len(columns)+count>max_columns:raise OverflowError('slack column limit')
 columns.extend([{(i,):F(1)} for i in range(count)])
 monomials=sorted(set(monomials)|{(i,) for i in range(count)})
 if len(monomials)>max_monomials:raise OverflowError('slack monomial limit')
 return monomials

def instantiate_certificate(instance,weights,*,max_columns=1024,max_monomials=10000,max_operations=200000000,max_coefficient_bits=2048,max_horizon=4096,max_degree=12,max_denominator=1000000,time_limit=10,deadline=None,allow_constant_slack=False):
 # Group meanings/order are a positional caller contract; descriptor IDs belong to the runner.
 for v in (max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,max_denominator):
  if type(v)is not int or v<1:raise ValueError('positive resource bounds')
 if isinstance(time_limit,bool) or not isinstance(time_limit,(int,float)) or not math.isfinite(time_limit) or time_limit<=0:raise ValueError('positive finite time limit')
 if deadline is None:deadline=time.monotonic()+time_limit
 _limits([instance],max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,deadline)
 if type(weights)is not dict or set(weights)!={'square_weights','relation_weights'}:raise ValueError('shared weights schema')
 if type(weights['square_weights'])is not list or type(weights['relation_weights'])is not list or any(type(v)is not str or str(F(v))!=v for v in weights['square_weights']+weights['relation_weights']):raise ValueError('canonical rational shared weight strings')
 sw=list(map(F,weights['square_weights']));rw=list(map(F,weights['relation_weights']))
 if any(max(abs(w.numerator).bit_length(),w.denominator.bit_length())>max_coefficient_bits for w in sw+rw):raise OverflowError('shared weight coefficient bits')
 if len(sw)!=len(instance['square_groups']) or len(rw)!=len(instance['relation_groups']) or any(w<0 for w in sw):raise ValueError('shared weight domains')
 squares=[];relations=[]
 for w,group in zip(sw,instance['square_groups']):
  for term in group:
   weight=w*F(term['weight'])
   if max(abs(weight.numerator).bit_length(),weight.denominator.bit_length())>max_coefficient_bits:raise OverflowError('expanded square weight bits')
   if weight:squares.append(dict(weight=str(weight),poly=term['poly']))
 for w,group in zip(rw,instance['relation_groups']):
  if w:
   for term in group:relations.append(dict(spec=term['spec'],multiplier=L.dump_poly(L.scale(L.load_poly(term['multiplier']),w))))
 if type(allow_constant_slack)is not bool:raise ValueError('slack flag bool')
 if allow_constant_slack:
  rhs={}
  for term in squares:rhs=L.add(rhs,L.scale(L.mul(L.load_poly(term['poly']),L.load_poly(term['poly']),max_terms=max_monomials,max_operations=max_operations),F(term['weight'])))
  for term in relations:rhs=L.add(rhs,L.mul(L.load_poly(term['multiplier']),L.relation(term['spec'],instance['target'],instance['horizon'],max_operations=max_operations),max_terms=max_monomials,max_operations=max_operations))
  residue=L.add(L.load_poly(instance['lhs']),L.scale(rhs,-1))
  if any(m for m in residue) or residue.get((),F(0))<0:raise ValueError('nonconstant or negative scalar remainder')
  scalar=residue.get((),F(0))
  if scalar:squares.append(dict(weight=str(scalar),poly=L.dump_poly(L.constant(1))))
 cert=dict(target=instance['target'],horizon=instance['horizon'],lhs=instance['lhs'],squares=squares,relations=relations);L.compile_certificate(cert,max_terms=max_monomials,max_operations=max_operations,max_horizon=max_horizon)
 if time.monotonic()>deadline:raise TimeoutError('certificate deadline')
 return cert

def synthesize(instances,*,max_columns=1024,max_monomials=10000,max_operations=200000000,max_coefficient_bits=2048,max_horizon=4096,max_degree=12,max_denominator=1000000,time_limit=10,allow_constant_slack=False):
 start=time.monotonic();diagnostics={}
 try:
  for v in (max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,max_denominator):
   if type(v)is not int or v<1:raise ValueError('positive resource bounds')
  if isinstance(time_limit,bool) or not isinstance(time_limit,(int,float)) or not math.isfinite(time_limit) or time_limit<=0:raise ValueError('positive finite time limit')
  if type(allow_constant_slack)is not bool:raise ValueError('slack flag bool')
  deadline=start+time_limit;columns,lhs,monomials,shape=_limits(instances,max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,deadline);monomials=_add_slacks(columns,lhs,monomials,len(instances),max_columns,max_monomials) if allow_constant_slack else monomials;diagnostics.update(instances=len(instances),columns=len(columns),monomials=len(monomials),objective='unit L1 costs, shared nonnegative squares and signed plus/minus relation groups')
  if not lhs:answer=[F(0)]*len(columns)
  else:
   if not columns:return dict(status='no_certificate_found',reason='nonzero target with no columns',diagnostics=diagnostics)
   try:from scipy.optimize import linprog
   except ImportError:return dict(status='missing_resource',reason='scipy unavailable',diagnostics=diagnostics)
   A=[[float(p.get(m,F(0))) for p in columns] for m in monomials];b=[float(lhs.get(m,F(0))) for m in monomials]
   if any(not math.isfinite(v) for row in A for v in row) or any(not math.isfinite(v) for v in b):raise OverflowError('float proposal conversion')
   result=linprog([1.0]*len(columns),A_eq=A,b_eq=b,bounds=(0,None),method='highs',options={'time_limit':max(0.001,deadline-time.monotonic())});diagnostics.update(lp_status=int(result.status),lp_message=str(result.message),float_objective=None if result.fun is None else float(result.fun))
   if time.monotonic()>deadline:raise TimeoutError('solver time limit')
   if not result.success:return dict(status='missing_resource' if result.status==1 else 'no_certificate_found',reason='float proposal unavailable; no mathematical infeasibility claim',diagnostics=diagnostics)
   support=[i for i,v in enumerate(result.x) if v>1e-9];diagnostics['proposed_support']=support
   if len(monomials)*max(1,len(support))**2>max_operations:raise OverflowError('exact elimination work bound')
   exact=exact_support_solution(columns,lhs,support,deadline=deadline,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits)
   if exact is None or any(v<0 for v in exact):return dict(status='no_certificate_found',reason='support failed exact nonnegative reconstruction',diagnostics=diagnostics)
   answer=[F(0)]*len(columns)
   for i,v in zip(support,exact):answer[i]=v
  reconstructed={}
  for p,w in zip(columns,answer):
   for m,q in p.items():reconstructed[m]=reconstructed.get(m,F(0))+w*q
  reconstructed={m:q for m,q in reconstructed.items() if q}
  if reconstructed!=lhs:return dict(status='no_certificate_found',reason='nonzero exact stacked residue',diagnostics=diagnostics)
  n,r=shape;weights=dict(square_weights=list(map(str,answer[:n])),relation_weights=[str(answer[n+2*j]-answer[n+2*j+1]) for j in range(r)]);certs=[instantiate_certificate(instance,weights,max_columns=max_columns,max_monomials=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,max_degree=max_degree,max_denominator=max_denominator,time_limit=time_limit,deadline=deadline,allow_constant_slack=allow_constant_slack) for instance in instances]
  if time.monotonic()>deadline:raise TimeoutError('certificate expansion time limit')
  diagnostics.update(exact_lp_weights=list(map(str,answer)),elapsed_seconds=time.monotonic()-start,lp_optimality_claim=False)
  return dict(status='finite_certificate',weights=weights,constant_slacks=list(map(str,answer[n+2*r:])) if allow_constant_slack else [],allow_constant_slack=allow_constant_slack,certificates=certs,validations=[L.compile_certificate(c,max_terms=max_monomials,max_operations=max_operations,max_horizon=max_horizon) for c in certs],diagnostics=diagnostics,global_bound_proved=False,RH_proved=False,scope='same shared weights match all declared finite instances only; no global template theorem')
 except (OverflowError,TimeoutError,MemoryError) as e:return dict(status='missing_resource',reason=str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
 except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError) as e:return dict(status='no_certificate_found',reason='invalid/rejected input: '+str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)

def find_separator(instances,*,max_denominator=1000000,time_limit=10,allow_constant_slack=False,**limits):
 if type(max_denominator)is not int or max_denominator<1 or isinstance(time_limit,bool) or not isinstance(time_limit,(int,float)) or not math.isfinite(time_limit) or time_limit<=0:return dict(status='uncertified',certified=False,reason='invalid dual limits')
 defaults=dict(max_columns=1024,max_monomials=10000,max_operations=200000000,max_coefficient_bits=2048,max_horizon=4096,max_degree=12);defaults.update(limits);start=time.monotonic()
 try:
  columns,lhs,monomials,shape=_limits(instances,**defaults,deadline=start+time_limit)
  if type(allow_constant_slack)is not bool:raise ValueError('slack flag bool')
  if allow_constant_slack:monomials=_add_slacks(columns,lhs,monomials,len(instances),defaults['max_columns'],defaults['max_monomials'])
  from scipy.optimize import linprog
  result=linprog([float(lhs.get(m,F(0))) for m in monomials],A_ub=[[-float(p.get(m,F(0))) for m in monomials] for p in columns] or None,b_ub=[0.0]*len(columns) or None,bounds=[(-1,1)]*len(monomials),method='highs',options={'time_limit':time_limit})
  if time.monotonic()>start+time_limit:raise TimeoutError('dual time limit')
  if not result.success:return dict(status='missing_resource' if result.status==1 else 'uncertified',certified=False,reason='float dual unavailable; no cone claim')
  for bound in sorted(set([1,min(16,max_denominator),min(256,max_denominator),max_denominator])):
   y={m:F(float(v)).limit_denominator(bound) for m,v in zip(monomials,result.x)};dots=[sum(y[m]*q for m,q in p.items()) for p in columns];bdot=sum(y[m]*q for m,q in lhs.items())
   if all(v>=0 for v in dots) and bdot<0:return dict(status='exact_separator',certified=True,monomials=[dict(instance=m[0],m=list(m[1:])) for m in monomials],weights=[str(y[m]) for m in monomials],columns_dot_y=list(map(str,dots)),lhs_dot_y=str(bdot),scope='declared shared finite cone inadequate; not actual arithmetic refutation',global_bound_proved=False)
  return dict(status='uncertified',certified=False,reason='rationalized dual failed exact inequalities')
 except (OverflowError,TimeoutError,MemoryError,ImportError) as e:return dict(status='missing_resource',certified=False,reason=str(e))
 except (ValueError,TypeError,KeyError,ZeroDivisionError) as e:return dict(status='uncertified',certified=False,reason=str(e))
