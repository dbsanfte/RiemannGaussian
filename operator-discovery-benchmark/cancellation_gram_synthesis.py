"""Shared PSD-Gram proposal plus exact coefficient and LDL admission.
Floating SDP is only a proposal. No infeasibility, optimality or global theorem.
"""
from fractions import Fraction as F
import time,math,copy
import grouped_arithmetic_synthesis as G
import grouped_arithmetic_language as L
import cancellation_arithmetic_templates as T
from cancellation_arithmetic_language import compile_expression
import cancellation_gram_language as P
from arithmetic_cycle_synthesis import exact_support_solution
ATOMS=('prefix','half','even','mod3one','prime')
UPPER=[(i,j)for i in range(5)for j in range(i,5)]
REGIONS=('parent','child')

def prepare(instances,scales,*,gram_blocks=None,max_columns=1024,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=80,max_degree=12,deadline=None):
 if deadline is None:deadline=time.monotonic()+90
 columns,lhs,ms,shape=G._limits(instances,max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,deadline)
 ms=G._add_slacks(columns,lhs,ms,len(instances),max_columns,max_monomials)
 if len(columns)+30>max_columns:raise OverflowError('Gram columns cap')
 blocks=[];used=0
 if gram_blocks is not None:
  if scales is not None or type(gram_blocks)is not list or len(gram_blocks)!=len(instances):raise ValueError('explicit Gram blocks schema')
  blocks=copy.deepcopy(gram_blocks)
 else:
  if type(scales)is not list or len(scales)>len(instances):raise ValueError('ordinary scales')
  for i,instance in enumerate(instances):
   row={r:[]for r in REGIONS}
   if i<len(scales):
    X=scales[i]
    if type(X)is not int or X<1 or instance['horizon']!=4*X-1:raise ValueError('full ordinary horizon')
    for region in REGIONS:
     for t in range(X,2*X)if region=='parent' else range(2*X,4*X):
      atoms=[]
      for atom in ATOMS:
       built=compile_expression(T.contrast_ast(atom,t),X,instance['horizon'],max_operations=max_operations-used,max_terms=max_monomials,max_degree=max_degree);used+=built['operations'];atoms.append(built['poly'])
      row[region].append(atoms)
   else:
    if instance['target']!='mu' or instance['horizon']!=1 or instance['lhs']!=[] or any(instance['square_groups']):raise ValueError('explicit gamma auxiliary row')
   blocks.append(row)
 offset=len(columns)
 for region in REGIONS:
  for a,b in UPPER:
   column={}
   for k,row in enumerate(blocks):
    if type(row)is not dict or set(row)!=set(REGIONS)or type(row[region])is not list:raise ValueError('Gram block regions')
    for atoms in row[region]:
     if type(atoms)is not list or len(atoms)!=5:raise ValueError('five atoms')
     ps=[]
     for poly in atoms:
      p=L.load_poly(poly)
      if ()in p or any(len(m)>max_degree or any(n>instances[k]['horizon'] for n in m)for m in p):raise ValueError('zero-constant horizon-bounded atoms')
      if any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in p.values()):raise OverflowError('Gram atom coefficient bits')
      ps.append(p)
     used+=len(ps[a])*len(ps[b])
     if used>max_operations or time.monotonic()>deadline:raise OverflowError('Gram expansion work/time')
     p=L.scale(L.mul(ps[a],ps[b],max_terms=max_monomials,max_operations=max_operations),1 if a==b else 2)
     for m,v in p.items():column[(k,)+m]=column.get((k,)+m,F(0))+v
   columns.append({m:v for m,v in column.items()if v})
 ms=sorted(set(lhs)|{m for p in columns for m in p})
 if len(ms)>max_monomials:raise OverflowError('full Gram monomial cap')
 return columns,lhs,ms,shape,offset,blocks

def instantiate_certificate(instance,weights,grams,blocks,*,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=80,time_limit=90,**other):
 if type(grams)is not dict or set(grams)!=set(REGIONS):raise ValueError('Gram regions')
 augmented=copy.deepcopy(instance);sw=list(weights['square_weights']);rw=list(weights['relation_weights']);proofs={}
 for region in REGIONS:
  proof=P.instantiate_sos(grams[region],blocks[region],max_terms=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits)
  proofs[region]=proof
  augmented['square_groups'].append(proof['squares']);sw.append('1')
 cert=G.instantiate_certificate(augmented,dict(square_weights=sw,relation_weights=rw),allow_constant_slack=True,max_monomials=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,time_limit=time_limit,**other)
 return dict(certificate=cert,Gram_proofs=proofs,global_bound_proved=False,RH_proved=False)

def synthesize(instances,scales=None,*,gram_blocks=None,time_limit=90,max_denominator=1000000,max_columns=1024,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=80,max_degree=12):
 start=time.monotonic();diagnostics={'objective':'unit scalar structural L1 plus Gram traces; constant slack zero','optimality_claim':False}
 try:
  for v in (max_denominator,max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree):
   if type(v)is not int or v<1:raise ValueError('positive strict limits')
  if isinstance(time_limit,bool)or type(time_limit)not in(int,float)or not math.isfinite(time_limit)or time_limit<=0:raise ValueError('positive time limit')
  deadline=start+time_limit
  limits=dict(max_columns=max_columns,max_monomials=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,max_degree=max_degree)
  cols,lhs,ms,shape,offset,blocks=prepare(instances,scales,gram_blocks=gram_blocks,deadline=deadline,**limits)
  if len(cols)*len(ms)>max_operations:raise OverflowError('SDP dense-size cap')
  import cvxpy as cp
  import numpy as np
  from scipy.sparse import csc_matrix
  scalar=cp.Variable(offset,nonneg=True);matrices={r:cp.Variable((5,5),symmetric=True)for r in REGIONS}
  v=cp.hstack([scalar]+[matrices[r][a,b]for r in REGIONS for a,b in UPPER]);lookup={m:i for i,m in enumerate(ms)};ii=[];jj=[];vv=[]
  for j,p in enumerate(cols):
   for m,q in p.items():ii.append(lookup[m]);jj.append(j);vv.append(float(q))
  rhs=np.array([float(lhs.get(m,0))for m in ms]);A=csc_matrix((vv,(ii,jj)),shape=(len(ms),len(cols)))
  if not all(math.isfinite(x)for x in vv)or not all(np.isfinite(rhs)):raise OverflowError('float coefficients')
  ns,nr=shape;objective=cp.sum(scalar[:ns+2*nr])+sum(cp.trace(matrices[r])for r in REGIONS)
  prob=cp.Problem(cp.Minimize(objective),[A@v==rhs]+[matrices[r]>>0 for r in REGIONS]);remaining=deadline-time.monotonic()
  if remaining<=0:raise TimeoutError('SDP preparation')
  try:prob.solve(solver='CLARABEL',time_limit=remaining)
  except cp.error.SolverError as e:return dict(status='uncertified',reason='numerical SDP solver failure: '+str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
  diagnostics.update(sdp_status=prob.status,columns=len(cols),monomials=len(ms),float_objective=float(prob.value) if prob.value is not None and math.isfinite(float(prob.value)) else None)
  if time.monotonic()>deadline or prob.status=='user_limit':raise TimeoutError('SDP deadline/solver iteration limit')
  if v.value is None:return dict(status='uncertified',reason='no numerical SDP proposal; no infeasibility theorem',diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
  floats=np.asarray(v.value).reshape(-1)
  if not all(np.isfinite(floats)):raise OverflowError('nonfinite SDP proposal')
  diagnostics['reconstruction_attempts']=[]
  # Rational approximation followed by an exact correction on the declared active face.
  for bound in sorted(set([min(64,max_denominator),min(4096,max_denominator),max_denominator])):
   initial=[F(float(x)).limit_denominator(bound)for x in floats]
   for i in range(offset):
    if abs(floats[i])<1e-7:initial[i]=F(0)
   residue=dict(lhs)
   for p,w in zip(cols,initial):
    for m,q in p.items():residue[m]=residue.get(m,F(0))-w*q
   residue={m:q for m,q in residue.items()if q}
   support=[i for i in range(offset)if floats[i]>1e-7]+list(range(offset,len(cols)))
   if len(ms)*max(1,len(support))**2>max_operations:raise OverflowError('Gram exact reconstruction work cap')
   correction=exact_support_solution(cols,residue,support,deadline=deadline,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits)
   if correction is None:diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='no exact active-face correction'));continue
   answer=initial[:]
   for i,q in zip(support,correction):answer[i]+=q
   if any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in answer):raise OverflowError('reconstructed coefficient bits')
   if any(x<0 for x in answer[:offset]):diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='negative scalar weight'));continue
   grams={};valid=True
   for k,r in enumerate(REGIONS):
    matrix=[[F(0)]*5 for _ in range(5)]
    for j,(a,b)in enumerate(UPPER):matrix[a][b]=matrix[b][a]=answer[offset+15*k+j]
    try:P.ldlt_psd([[str(q)for q in row]for row in matrix],max_operations=max_operations,max_coefficient_bits=max_coefficient_bits)
    except ValueError:valid=False;break
    grams[r]=[[str(q)for q in row]for row in matrix]
   if not valid:diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='exact matrix not PSD'));continue
   rebuilt={}
   for p,w in zip(cols,answer):
    for m,q in p.items():rebuilt[m]=rebuilt.get(m,F(0))+w*q
   if {m:q for m,q in rebuilt.items()if q}!=lhs:raise ValueError('original full coefficient mismatch')
   weights=dict(square_weights=list(map(str,answer[:ns])),relation_weights=[str(answer[ns+2*j]-answer[ns+2*j+1])for j in range(nr)])
   certificates=[]
   for instance,row in zip(instances,blocks):
    remaining=deadline-time.monotonic()
    if remaining<=0:raise TimeoutError('exact certificate deadline')
    certificates.append(instantiate_certificate(instance,weights,grams,row,max_monomials=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,time_limit=remaining,max_columns=max_columns+2,max_degree=max_degree,max_denominator=max_denominator))
   if time.monotonic()>deadline:raise TimeoutError('final certificate deadline')
   diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='exact PSD and full coefficient match'))
   return dict(status='finite_PSD_certificate',weights=weights,grams=grams,constant_slacks=list(map(str,answer[ns+2*nr:offset])),exact_column_weights=list(map(str,answer)),certificates=certificates,diagnostics=diagnostics,global_bound_proved=False,RH_proved=False,scope='finite shared PSD certificate; no uniform signed bound')
  return dict(status='uncertified',reason='numerical proposal lacks admitted rational PSD reconstruction',diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
 except (OverflowError,TimeoutError,MemoryError,ImportError)as e:return dict(status='missing_resource',reason=str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
 except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError)as e:return dict(status='uncertified',reason=str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
