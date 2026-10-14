"""Anchored storage compilation and finite primal proposals.

Storage is a signed transport. Native exact correction uses the unchanged
compressed helper; checkpoints precede every native call. Hard process limits
are imposed by the enclosing runner.
"""
from fractions import Fraction as F
import time, math, copy, json
import cancellation_shared_gram_synthesis as BASE
import cancellation_shared_gram_synthesis_v2 as V2
import cancellation_shared_gram_language as P
import grouped_arithmetic_language as L
import native_exact_support_compressed as N
import cancellation_anchored_storage as A

digest=BASE.digest
upper=BASE.upper
emit_checkpoint=V2.emit_checkpoint

def validate_storage(gram_blocks, storage_blocks):
    if type(gram_blocks) is not list or type(storage_blocks) is not list or len(gram_blocks)!=len(storage_blocks):
        raise ValueError('complete storage instance coverage')
    for blocks, transport in zip(gram_blocks,storage_blocks):
        if type(blocks) is not dict or set(blocks)!={'full_child','full_parent'}:
            raise ValueError('complete regional full14 groups')
        if type(transport) is not dict or set(transport)!={'kind','child','parent','child_multiplier','parent_multiplier'}:
            raise ValueError('typed storage transport fields')
        if transport['kind']!='signed_storage_increment' or transport['child_multiplier']!='1' or transport['parent_multiplier']!='-4':
            raise ValueError('signed child-minus-four-parent orientation')
        if transport['child']!=blocks['full_child'] or transport['parent']!=blocks['full_parent']:
            raise ValueError('storage sources must equal complete regional geometry')

def prepare(instances, gram_blocks, storage_blocks, *, gram_specs=None, **limits):
    """Old seven-item compiler tuple, with three typed matrix groups.

    Item six remains the original regional blocks; storage sources are supplied
    explicitly and hashed separately. Every K pair is retained in the domain.
    """
    validate_storage(gram_blocks,storage_blocks)
    specs=A.gram_specs()
    if gram_specs is not None and gram_specs!=specs:
        raise ValueError('entire anchored full14 matrix cone required')
    cap=limits.get('max_columns',2048)
    base_limits=dict(limits)
    base_limits['max_columns']=cap-105
    if base_limits['max_columns']<1:
        raise OverflowError('anchored column cap')
    cols,lhs,ms,shape,offset,blocks,_=BASE.prepare(instances,gram_blocks,gram_specs={'full_child':14,'full_parent':14},**base_limits)
    used=0
    for j in range(105):
        child,parent=cols[offset+j],cols[offset+105+j]
        used+=len(child)+len(parent)
        if used>limits.get('max_operations',200000000):
            raise OverflowError('storage transport assembly work cap')
        if limits.get('deadline') is not None and time.monotonic()>limits['deadline']:
            raise TimeoutError('storage transport assembly deadline')
        p=dict(child)
        for m,q in parent.items():
            p[m]=p.get(m,F(0))-4*q
        cols.append({m:q for m,q in p.items() if q})
    bits=limits.get('max_coefficient_bits',4096)
    if any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>bits for p in cols for q in p.values()):
        raise OverflowError('storage coefficient bits')
    ms=sorted(set(lhs)|{m for p in cols for m in p})
    if len(ms)>limits.get('max_monomials',30000):
        raise OverflowError('complete storage monomial cap')
    if len(cols)>cap:
        raise OverflowError('anchored column cap')
    return cols,lhs,ms,shape,offset,blocks,specs

def compilation_charge(instances, blocks, columns):
    """Conservative deterministic reserve for exact geometry compilation.

    Counts source scalar data, full regional atom-pair products, column assembly
    and hash traversal. Native helper separately charges its equation build,
    compression and full original equation verification.
    """
    pairs=sum(len(row[i])*len(row[j]) for groups in blocks for rows in groups.values() for row in rows for i,j in upper(14))
    source=len(json.dumps(instances,sort_keys=True,separators=(',',':')).encode())
    return source+8*pairs+8*sum(map(len,columns))+1

def instantiate_certificate(instance,weights,grams,blocks,transport, **limits):
    validate_storage([blocks],[transport])
    if set(grams)!=set(A.gram_specs()):
        raise ValueError('complete anchored matrices')
    deadline=time.monotonic()+limits.get('time_limit',90)
    storage={}
    for region in ['child','parent']:
        storage[region]=P.instantiate_sos(grams['storage_K'],transport[region],
            max_terms=limits.get('max_monomials',30000),max_operations=limits.get('max_operations',200000000),
            max_coefficient_bits=limits.get('max_coefficient_bits',4096),deadline=deadline)
    child=L.load_poly(storage['child']['polynomial']);parent=L.load_poly(storage['parent']['polynomial'])
    increment=L.add(child,L.scale(parent,-4))
    transformed=copy.deepcopy(instance)
    transformed['lhs']=L.dump_poly(L.add(L.load_poly(instance['lhs']),L.scale(increment,-1)))
    regional={k:grams[k] for k in ['full_child','full_parent']}
    record=BASE.instantiate_certificate(transformed,weights,regional,blocks,**limits)
    return dict(original_lhs=instance['lhs'],transformed_lhs=transformed['lhs'],
        transformed_target_certificate=record['certificate'],Gram_proofs=record['Gram_proofs'],
        constant_slack=record['constant_slack'],storage_proof=dict(kind='signed_storage_increment',K=grams['storage_K'],
            child_multiplier='1',parent_multiplier='-4',child_polynomial=storage['child']['polynomial'],
            parent_polynomial=storage['parent']['polynomial'],polynomial=L.dump_poly(increment)),
        diagnostics=record['diagnostics'],global_bound_proved=False,RH_proved=False)

def proposal_checkpoint(instances,blocks,specs,columns,lhs,monomials,shape,offset,floats,support,diagnostics,*,max_checkpoint_bytes,row_normalization):
 layout=[dict(index=i,kind='scalar')for i in range(offset)]
 for name,n in specs.items():
  for a,b in upper(n):layout.append(dict(index=len(layout),kind='Gram',group=name,i=a,j=b))
 data=dict(schema='anchored-storage-SDP-proposal-v1',proposal_only=True,certified=False,global_bound_proved=False,RH_proved=False,
  source_hashes=[digest(x)for x in instances],gram_block_hashes=[digest(x)for x in blocks],gram_specs=specs,scalar_shape=list(shape),scalar_offset=offset,
  monomials=[dict(instance=m[0],m=list(m[1:]))for m in monomials],
  exact_columns_hash=digest([[[list(m),str(q)]for m,q in sorted(p.items())]for p in columns]),exact_target_hash=digest([[list(m),str(q)]for m,q in sorted(lhs.items())]),
  float_vector=[float(x)for x in floats],active_support=list(support),active_threshold=1e-7,column_layout=layout,
  numerical_options=dict(solver='CLARABEL',max_threads=1,row_normalization=row_normalization),solver_status=diagnostics.get('sdp_status'),float_objective=diagnostics.get('float_objective'),reconstruction_attempts=[])
 encoded=json.dumps(data,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
 if len(encoded)>max_checkpoint_bytes:raise OverflowError('proposal checkpoint byte cap')
 return data

def synthesize(instances,gram_blocks,storage_blocks,*,gram_specs=None,max_exact_cells=2000000,max_exact_work=450000000,max_checkpoint_bytes=8388608,on_checkpoint=None,row_normalization=False,time_limit=180,max_denominator=1000000,max_columns=2048,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=80,max_degree=12):
 start=time.monotonic();checkpoint=None;charged_work=0;diagnostics={'objective':'unit scalar structural L1 plus Gram traces; nonnegative perinstance scalar slack','optimality_claim':False,'numerical_threads':1,'native_call_interruptible':False}
 try:
  for v in (max_denominator,max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree,max_exact_cells,max_exact_work,max_checkpoint_bytes):
   if type(v)is not int or v<1:raise ValueError('positive strict limits')
  if isinstance(time_limit,bool)or type(time_limit)not in(int,float)or not math.isfinite(time_limit)or time_limit<=0:raise ValueError('positive time limit')
  if max_exact_work>450000000 or time_limit>180:raise ValueError('authorized total charged work/cooperative time ceiling')
  if type(row_normalization)is not bool or (on_checkpoint is not None and not callable(on_checkpoint)):raise ValueError('normalization bool and optional checkpoint callback')
  deadline=start+time_limit
  limits=dict(max_columns=max_columns,max_monomials=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,max_degree=max_degree)
  cols,lhs,ms,shape,offset,blocks,specs=prepare(instances,gram_blocks,storage_blocks,gram_specs=gram_specs,deadline=deadline,**limits)
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
  rhs=np.array([float(lhs.get(m,0)/scales[m])for m in ms]);sparse_A=csc_matrix((vv,(ii,jj)),shape=(len(ms),len(cols)))
  if not all(math.isfinite(x)for x in vv)or not all(np.isfinite(rhs)):raise OverflowError('float coefficients')
  ns,nr=shape;objective=cp.sum(scalar[:ns+2*nr])+sum(cp.trace(matrices[r])for r in specs)
  prob=cp.Problem(cp.Minimize(objective),[sparse_A@v==rhs]+[matrices[r]>>0 for r in specs]);remaining=deadline-time.monotonic()
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
  checkpoint['storage_block_hashes']=[digest(x) for x in storage_blocks]
  checkpoint['grammar_hash']=digest(A.SPEC)
  checkpoint['reconstruction_limits']=dict(max_exact_work=max_exact_work,max_exact_cells=max_exact_cells,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits,max_operations=max_operations,time_limit=time_limit)
  checkpoint['reconstruction_attempts']=diagnostics['reconstruction_attempts']
  checkpoint['row_order_hash']=digest(checkpoint['monomials'])
  checkpoint['layout_hash']=digest(checkpoint['column_layout'])
  compilation_reserve=compilation_charge(instances,blocks,cols)
  checkpoint['compilation_work_reserve']=compilation_reserve
  diagnostics['native_attempt_receipts']=[]
  checkpoint['native_attempt_receipts']=diagnostics['native_attempt_receipts']
  charged_work=compilation_reserve
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
   before=charged_work
   assembly_reserve=8*sum(map(len,cols))+len(lhs)+len(initial)+1
   charged_work+=assembly_reserve
   attempt=dict(bound=bound,initial_hash=digest(list(map(str,initial))),
    residual_hash=digest([[list(m),str(q)] for m,q in sorted(residue.items())]),
    support_hash=digest(support),charge_before=before,assembly_reserve=assembly_reserve,
    charge_before_native=charged_work,remaining_work=max_exact_work-charged_work,
    native_returned=False,native_gate_rejected=False,status='prepared')
   diagnostics['native_attempt_receipts'].append(attempt)
   checkpoint['total_charged_work_proxy_before_native']=charged_work
   emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
   if charged_work>=max_exact_work:raise OverflowError('total charged reconstruction work cap')
   exact_diagnostics={}
   try:
    correction=N.exact_support_solution(cols,residue,support,deadline=deadline,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits,max_rows=max_monomials,max_columns=max_columns,max_cells=max_exact_cells,max_work=max_exact_work-charged_work,diagnostics=exact_diagnostics)
    attempt.update(native_returned=True,status='returned',correction_available=correction is not None)
   except (OverflowError,TimeoutError,MemoryError,ValueError,RuntimeError) as error:
    attempt.update(status='failed',reason=str(error),native_gate_rejected=str(error)=='compressed native plus preprocessing total work proxy')
    raise
   finally:
    info=exact_diagnostics.get('row_compression',{})
    # A rejected native work gate did not execute its reserved elimination.
    charge=info.get('preprocessing_work',0) if attempt['native_gate_rejected'] else info.get('total_work_proxy',0)
    charged_work+=charge
    attempt.update(exact_diagnostics=copy.deepcopy(exact_diagnostics),native_charge=charge,charge_after=charged_work)
    diagnostics['total_charged_work_proxy']=charged_work
    diagnostics['exact_correction_diagnostics']=exact_diagnostics
    emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
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
   for instance,row,transport in zip(instances,blocks,storage_blocks):
    remaining=deadline-time.monotonic()
    if remaining<=0:raise TimeoutError('exact certificate deadline')
    certificates.append(instantiate_certificate(instance,weights,grams,row,transport,max_monomials=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,time_limit=remaining,max_columns=max_columns+len(specs),max_degree=max_degree,max_denominator=max_denominator))
   if time.monotonic()>deadline:raise TimeoutError('final certificate deadline')
   diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='exact PSD and full coefficient match'))
   emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
   result=dict(status='finite_PSD_certificate',weights=weights,grams=grams,gram_specs=specs,source_hashes=[digest(x)for x in instances],gram_block_hashes=[digest(x)for x in blocks],storage_block_hashes=[digest(x) for x in storage_blocks],grammar_hash=digest(A.SPEC),constant_slacks=list(map(str,answer[ns+2*nr:offset])),exact_column_weights=list(map(str,answer)),certificates=certificates,diagnostics=diagnostics,proposal_checkpoint=checkpoint,global_bound_proved=False,RH_proved=False,scope='finite shared PSD certificate; no uniform signed bound')
   result['state_matrix']=A.anchored_matrix(grams['storage_K'],max_operations=max_operations,max_coefficient_bits=max_coefficient_bits)
   import check_cancellation_anchored_storage as I
   result['independent_check']=I.verify_primal(instances,blocks,storage_blocks,specs,result)
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
