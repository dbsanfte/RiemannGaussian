"""Versioned sparse SDP proposals with bounded checkpoint before native admission.
Row normalization changes numerical equations only, never exact admission data.
Native calls need external process time/memory enforcement.
"""
from fractions import Fraction as F
import time,math,copy,json
from cancellation_shared_gram_synthesis import prepare,instantiate_certificate,digest,upper
import cancellation_shared_gram_language as P
import check_cancellation_shared_gram as I
from native_exact_support import exact_support_solution

def emit_checkpoint(checkpoint,callback,max_bytes):
 if len(json.dumps(checkpoint,sort_keys=True,separators=(',',':'),allow_nan=False).encode())>max_bytes:raise OverflowError('proposal checkpoint byte cap')
 if callback is not None:
  try:callback(copy.deepcopy(checkpoint))
  except Exception as e:raise RuntimeError('checkpoint callback failed: '+str(e))from e

def proposal_checkpoint(instances,blocks,specs,columns,lhs,monomials,shape,offset,floats,support,diagnostics,*,max_checkpoint_bytes,row_normalization):
 layout=[dict(index=i,kind='scalar')for i in range(offset)]
 for name,n in specs.items():
  for a,b in upper(n):layout.append(dict(index=len(layout),kind='Gram',group=name,i=a,j=b))
 data=dict(schema='shared-Gram-SDP-proposal-v2',proposal_only=True,certified=False,global_bound_proved=False,RH_proved=False,
  source_hashes=[digest(x)for x in instances],gram_block_hashes=[digest(x)for x in blocks],gram_specs=specs,scalar_shape=list(shape),scalar_offset=offset,
  monomials=[dict(instance=m[0],m=list(m[1:]))for m in monomials],
  exact_columns_hash=digest([[[list(m),str(q)]for m,q in sorted(p.items())]for p in columns]),exact_target_hash=digest([[list(m),str(q)]for m,q in sorted(lhs.items())]),
  float_vector=[float(x)for x in floats],active_support=list(support),active_threshold=1e-7,column_layout=layout,
  numerical_options=dict(solver='CLARABEL',max_threads=1,row_normalization=row_normalization),solver_status=diagnostics.get('sdp_status'),float_objective=diagnostics.get('float_objective'),reconstruction_attempts=[])
 encoded=json.dumps(data,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
 if len(encoded)>max_checkpoint_bytes:raise OverflowError('proposal checkpoint byte cap')
 return data

def synthesize(instances,gram_blocks,*,gram_specs=None,max_exact_cells=2000000,max_exact_work=450000000,max_checkpoint_bytes=8388608,on_checkpoint=None,row_normalization=False,time_limit=90,max_denominator=1000000,max_columns=1024,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=80,max_degree=12):
 start=time.monotonic();checkpoint=None;diagnostics={'objective':'unit scalar structural L1 plus Gram traces; nonnegative perinstance scalar slack','optimality_claim':False,'numerical_threads':1,'native_call_interruptible':False}
 try:
  for v in (max_denominator,max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,max_exact_cells,max_exact_work,max_checkpoint_bytes):
   if type(v)is not int or v<1:raise ValueError('positive strict limits')
  if isinstance(time_limit,bool)or type(time_limit)not in(int,float)or not math.isfinite(time_limit)or time_limit<=0:raise ValueError('positive time limit')
  if type(row_normalization)is not bool or (on_checkpoint is not None and not callable(on_checkpoint)):raise ValueError('normalization bool and optional checkpoint callback')
  deadline=start+time_limit
  limits=dict(max_columns=max_columns,max_monomials=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,max_degree=max_degree)
  cols,lhs,ms,shape,offset,blocks,specs=prepare(instances,gram_blocks,gram_specs=gram_specs,deadline=deadline,**limits)
  if sum(map(len,cols))>max_operations:raise OverflowError('SDP sparse-size cap')
  import cvxpy as cp
  import numpy as np
  from scipy.sparse import csc_matrix
  scalar=cp.Variable(offset,nonneg=True);matrices={r:cp.Variable((n,n),symmetric=True)for r,n in specs.items()}
  v=cp.hstack([scalar]+[matrices[r][a,b]for r,n in specs.items() for a,b in upper(n)]);lookup={m:i for i,m in enumerate(ms)};ii=[];jj=[];vv=[]
  scales={m:abs(lhs.get(m,F(0)))for m in ms} if row_normalization else {m:F(1)for m in ms}
  if row_normalization:
   for column in cols:
    for m,q in column.items():scales[m]=max(scales[m],abs(q))
   scales={m:q or F(1)for m,q in scales.items()}
  for j,p in enumerate(cols):
   for m,q in p.items():ii.append(lookup[m]);jj.append(j);vv.append(float(q/scales[m]))
  rhs=np.array([float(lhs.get(m,0)/scales[m])for m in ms]);A=csc_matrix((vv,(ii,jj)),shape=(len(ms),len(cols)))
  if not all(math.isfinite(x)for x in vv)or not all(np.isfinite(rhs)):raise OverflowError('float coefficients')
  ns,nr=shape;objective=cp.sum(scalar[:ns+2*nr])+sum(cp.trace(matrices[r])for r in specs)
  prob=cp.Problem(cp.Minimize(objective),[A@v==rhs]+[matrices[r]>>0 for r in specs]);remaining=deadline-time.monotonic()
  if remaining<=0:raise TimeoutError('SDP preparation')
  solver_error=None
  try:prob.solve(solver='CLARABEL',time_limit=remaining,max_threads=1)
  except cp.error.SolverError as e:solver_error=str(e)
  diagnostics.update(sdp_status=prob.status,columns=len(cols),monomials=len(ms),row_normalization=row_normalization,float_objective=float(prob.value) if prob.value is not None and math.isfinite(float(prob.value)) else None,reconstruction_attempts=[])
  if v.value is None:
   return dict(status='uncertified',reason=('numerical SDP solver failure: '+solver_error)if solver_error else 'no numerical SDP proposal; no infeasibility theorem',diagnostics=diagnostics,proposal_checkpoint=None,global_bound_proved=False,RH_proved=False)
  floats=np.asarray(v.value).reshape(-1)
  if not all(np.isfinite(floats)):raise OverflowError('nonfinite SDP proposal')
  support=[i for i in range(offset)if floats[i]>1e-7]+list(range(offset,len(cols)))
  checkpoint=proposal_checkpoint(instances,blocks,specs,cols,lhs,ms,shape,offset,floats,support,diagnostics,max_checkpoint_bytes=max_checkpoint_bytes,row_normalization=row_normalization)
  checkpoint['reconstruction_limits']=dict(max_exact_work=max_exact_work,max_exact_cells=max_exact_cells,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits,max_operations=max_operations,time_limit=time_limit)
  checkpoint['reconstruction_attempts']=diagnostics['reconstruction_attempts']
  checkpoint['row_order_hash']=digest(checkpoint['monomials'])
  checkpoint['layout_hash']=digest(checkpoint['column_layout'])
  emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
  if solver_error:return dict(status='uncertified',reason='numerical SDP solver failure: '+solver_error,diagnostics=diagnostics,proposal_checkpoint=checkpoint,global_bound_proved=False,RH_proved=False)
  if time.monotonic()>deadline or prob.status=='user_limit':raise TimeoutError('SDP deadline/solver iteration limit')
  # Rational approximation followed by an exact correction on the declared active face.
  for bound in sorted(set([min(64,max_denominator),min(4096,max_denominator),max_denominator])):
   initial=[F(float(x)).limit_denominator(bound)for x in floats]
   for i in range(offset):
    if abs(floats[i])<1e-7:initial[i]=F(0)
   residue=dict(lhs)
   for p,w in zip(cols,initial):
    for m,q in p.items():residue[m]=residue.get(m,F(0))-w*q
   residue={m:q for m,q in residue.items()if q}
   diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='native correction started'))
   emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
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
   emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
   result=dict(status='finite_PSD_certificate',weights=weights,grams=grams,gram_specs=specs,source_hashes=[digest(x)for x in instances],gram_block_hashes=[digest(x)for x in blocks],constant_slacks=list(map(str,answer[ns+2*nr:offset])),exact_column_weights=list(map(str,answer)),certificates=certificates,diagnostics=diagnostics,proposal_checkpoint=checkpoint,global_bound_proved=False,RH_proved=False,scope='finite shared PSD certificate; no uniform signed bound')
   result['independent_check']=I.verify_primal(instances,blocks,specs,result)
   if time.monotonic()>deadline:raise TimeoutError('independent primal verification deadline')
   return result
  emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
  return dict(status='uncertified',reason='numerical proposal lacks admitted rational PSD reconstruction',diagnostics=diagnostics,proposal_checkpoint=checkpoint,global_bound_proved=False,RH_proved=False)
 except (OverflowError,TimeoutError,MemoryError,ImportError)as e:
  if checkpoint is not None:
   checkpoint['reconstruction_attempts']=copy.deepcopy(diagnostics.get('reconstruction_attempts',[]));checkpoint['failure']=str(e)
   if len(json.dumps(checkpoint,sort_keys=True,separators=(',',':'),allow_nan=False).encode())>max_checkpoint_bytes:checkpoint=None;diagnostics['checkpoint_omitted']='byte cap'
  return dict(status='missing_resource',reason=str(e),diagnostics=diagnostics,proposal_checkpoint=checkpoint,global_bound_proved=False,RH_proved=False)
 except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError)as e:
  if checkpoint is not None:
   checkpoint['reconstruction_attempts']=copy.deepcopy(diagnostics.get('reconstruction_attempts',[]));checkpoint['failure']=str(e)
   if len(json.dumps(checkpoint,sort_keys=True,separators=(',',':'),allow_nan=False).encode())>max_checkpoint_bytes:checkpoint=None;diagnostics['checkpoint_omitted']='byte cap'
  return dict(status='uncertified',reason=str(e),diagnostics=diagnostics,proposal_checkpoint=checkpoint,global_bound_proved=False,RH_proved=False)
