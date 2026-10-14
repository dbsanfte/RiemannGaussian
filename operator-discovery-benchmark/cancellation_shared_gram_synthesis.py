"""Generic shared PSD proposals admitted only by exact equality and PSD.
Native RREF C calls require external worker timeout for hard elapsed bounds.
"""
from fractions import Fraction as F
import time,math,copy,json,hashlib
import grouped_arithmetic_synthesis as G
import grouped_arithmetic_language as L
import grouped_arithmetic_sparse as Sparse
import cancellation_shared_gram_language as P
from native_exact_support import exact_support_solution

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()
def upper(n):return [(a,b)for a in range(n)for b in range(a,n)]

def prepare(instances,gram_blocks,*,gram_specs=None,max_columns=1024,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=80,max_degree=12,deadline=None):
 if deadline is None:deadline=time.monotonic()+90
 columns,lhs,ms,shape=G._limits(instances,max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,deadline)
 ms=G._add_slacks(columns,lhs,ms,len(instances),max_columns,max_monomials)
 if type(gram_blocks)is not list or len(gram_blocks)!=len(instances)or any(type(row)is not dict for row in gram_blocks):raise ValueError('perinstance blocks schema')
 names=sorted(gram_blocks[0])
 if not names or any(type(r)is not str or not r for r in names)or any(set(row)!=set(names)for row in gram_blocks):raise ValueError('same named groups everywhere')
 if gram_specs is None:
  gram_specs={}
  for r in names:
   dims={len(atoms)for row in gram_blocks for atoms in row[r]}
   if len(dims)!=1:raise ValueError('declare empty group dimension')
   gram_specs[r]=dims.pop()
 if type(gram_specs)is not dict or set(gram_specs)!=set(names):raise ValueError('complete Gram specs dictionary')
 specs={r:gram_specs[r]for r in names}
 if any(type(n)is not int or not 1<=n<=64 for n in specs.values()):raise ValueError('bounded positive Gram dimensions')
 if len(columns)+sum(n*(n+1)//2 for n in specs.values())>max_columns:raise OverflowError('Gram column cap')
 parsed=[];used=0
 for k,row in enumerate(gram_blocks):
  dest={}
  for r,n in specs.items():
   if type(row[r])is not list:raise ValueError('complete blocks list')
   dest[r]=[]
   for atoms in row[r]:
    if type(atoms)is not list or len(atoms)!=n:raise ValueError('same Gram dimensions')
    ps=[]
    for atom in atoms:
     if type(atom)is not list or len(atom)>max_monomials:raise OverflowError('atom term cap')
     p=L.load_poly(atom)
     if any(len(m)>max_degree or any(i>instances[k]['horizon']for i in m)for m in p):raise ValueError('atom horizon/degree')
     if any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in p.values()):raise OverflowError('atom bits')
     ps.append(p)
    dest[r].append(ps)
  parsed.append(dest)
 offset=len(columns)
 for r,n in specs.items():
  for a,b in upper(n):
   column={}
   for k,row in enumerate(parsed):
    for ps in row[r]:
     used+=len(ps[a])*len(ps[b])
     if used>max_operations or time.monotonic()>deadline:raise OverflowError('Gram expansion work/time')
     if any(len(x)+len(y)>max_degree for x in ps[a]for y in ps[b]):raise OverflowError('expanded degree')
     p=L.scale(L.mul(ps[a],ps[b],max_terms=max_monomials,max_operations=max_operations),1 if a==b else 2)
     for m,q in p.items():
      key=(k,)+m;column[key]=column.get(key,F(0))+q
      if max(abs(column[key].numerator).bit_length(),column[key].denominator.bit_length())>max_coefficient_bits:raise OverflowError('column bits')
     if len(column)>max_monomials:raise OverflowError('column terms')
   columns.append({m:q for m,q in column.items()if q})
 ms=sorted(set(lhs)|{m for p in columns for m in p})
 if len(ms)>max_monomials:raise OverflowError('stacked monomial cap')
 return columns,lhs,ms,shape,offset,gram_blocks,specs

def instantiate_certificate(instance,weights,grams,blocks,*,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=80,time_limit=90,**other):
 if type(grams)is not dict or set(grams)!=set(blocks):raise ValueError('Gram regions')
 augmented=copy.deepcopy(instance);sw=list(weights['square_weights']);rw=list(weights['relation_weights']);proofs={};deadline=time.monotonic()+time_limit;used=0
 for region in sorted(grams):
  proof=P.instantiate_sos(grams[region],blocks[region],max_terms=max_monomials,max_operations=max_operations-used,max_coefficient_bits=max_coefficient_bits,deadline=deadline)
  used+=proof['operations']
  proofs[region]=proof
  augmented['square_groups'].append(proof['squares']);sw.append('1')
 if used>=max_operations:raise OverflowError('shared certificate operation cap')
 details=Sparse.instantiate_details(augmented,dict(square_weights=sw,relation_weights=rw),allow_constant_slack=True,max_monomials=max_monomials,max_operations=max_operations-used,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,time_limit=time_limit,deadline=deadline,**other)
 return dict(certificate=details["certificate"],constant_slack=details["constant_slack"],Gram_proofs=proofs,diagnostics=details["diagnostics"],global_bound_proved=False,RH_proved=False)

def synthesize(instances,gram_blocks,*,gram_specs=None,max_exact_cells=2000000,max_exact_work=2000000000,time_limit=90,max_denominator=1000000,max_columns=1024,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=80,max_degree=12):
 start=time.monotonic();diagnostics={'objective':'unit scalar structural L1 plus Gram traces; nonnegative perinstance scalar slack','optimality_claim':False,'numerical_threads':1,'native_call_interruptible':False}
 try:
  for v in (max_denominator,max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,max_exact_cells,max_exact_work):
   if type(v)is not int or v<1:raise ValueError('positive strict limits')
  if isinstance(time_limit,bool)or type(time_limit)not in(int,float)or not math.isfinite(time_limit)or time_limit<=0:raise ValueError('positive time limit')
  deadline=start+time_limit
  limits=dict(max_columns=max_columns,max_monomials=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,max_degree=max_degree)
  cols,lhs,ms,shape,offset,blocks,specs=prepare(instances,gram_blocks,gram_specs=gram_specs,deadline=deadline,**limits)
  if sum(map(len,cols))>max_operations:raise OverflowError('SDP dense-size cap')
  import cvxpy as cp
  import numpy as np
  from scipy.sparse import csc_matrix
  scalar=cp.Variable(offset,nonneg=True);matrices={r:cp.Variable((n,n),symmetric=True)for r,n in specs.items()}
  v=cp.hstack([scalar]+[matrices[r][a,b]for r,n in specs.items() for a,b in upper(n)]);lookup={m:i for i,m in enumerate(ms)};ii=[];jj=[];vv=[]
  for j,p in enumerate(cols):
   for m,q in p.items():ii.append(lookup[m]);jj.append(j);vv.append(float(q))
  rhs=np.array([float(lhs.get(m,0))for m in ms]);A=csc_matrix((vv,(ii,jj)),shape=(len(ms),len(cols)))
  if not all(math.isfinite(x)for x in vv)or not all(np.isfinite(rhs)):raise OverflowError('float coefficients')
  ns,nr=shape;objective=cp.sum(scalar[:ns+2*nr])+sum(cp.trace(matrices[r])for r in specs)
  prob=cp.Problem(cp.Minimize(objective),[A@v==rhs]+[matrices[r]>>0 for r in specs]);remaining=deadline-time.monotonic()
  if remaining<=0:raise TimeoutError('SDP preparation')
  try:prob.solve(solver='CLARABEL',time_limit=remaining,max_threads=1)
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
   correction=exact_support_solution(cols,residue,support,deadline=deadline,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits,max_rows=max_monomials,max_columns=max_columns,max_cells=max_exact_cells,max_work=max_exact_work)
   if correction is None:diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='no exact active-face correction'));continue
   answer=initial[:]
   for i,q in zip(support,correction):answer[i]+=q
   if any(q.denominator>max_denominator or max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in answer):raise OverflowError('reconstructed rational limits')
   if any(x<0 for x in answer[:offset]):diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='negative scalar weight'));continue
   grams={};valid=True
   pos=offset
   for r,n in specs.items():
    matrix=[[F(0)]*n for _ in range(n)]
    for a,b in upper(n):matrix[a][b]=matrix[b][a]=answer[pos];pos+=1
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
    certificates.append(instantiate_certificate(instance,weights,grams,row,max_monomials=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,time_limit=remaining,max_columns=max_columns+len(specs),max_degree=max_degree,max_denominator=max_denominator))
   if time.monotonic()>deadline:raise TimeoutError('final certificate deadline')
   diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='exact PSD and full coefficient match'))
   return dict(status='finite_PSD_certificate',weights=weights,grams=grams,gram_specs=specs,source_hashes=[digest(x)for x in instances],gram_block_hashes=[digest(x)for x in blocks],constant_slacks=list(map(str,answer[ns+2*nr:offset])),exact_column_weights=list(map(str,answer)),certificates=certificates,diagnostics=diagnostics,global_bound_proved=False,RH_proved=False,scope='finite shared PSD certificate; no uniform signed bound')
  return dict(status='uncertified',reason='numerical proposal lacks admitted rational PSD reconstruction',diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
 except (OverflowError,TimeoutError,MemoryError,ImportError)as e:return dict(status='missing_resource',reason=str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
 except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError)as e:return dict(status='uncertified',reason=str(e),diagnostics=diagnostics,global_bound_proved=False,RH_proved=False)
