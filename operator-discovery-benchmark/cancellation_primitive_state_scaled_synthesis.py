"""Exact full15 solver with independently checked numerical row compression.

Only numerical proposals use floating arithmetic. A complete coefficient
reconstruction, all three PSD matrices and an independent callback are required
for admission. Existing generic scalar/Gram code is reused compositionally.
"""
from fractions import Fraction as F
import copy
import json
import math
import time
import cancellation_shared_gram_synthesis as BASE
import cancellation_anchored_storage_synthesis as OLD
import cancellation_shared_gram_synthesis_v2 as V2
import cancellation_shared_gram_language as P
import native_exact_support_compressed as N
import cancellation_affine_storage as A
import primitive_state_numerical_proposals as NUM
import check_primitive_state_numerical_proposals as NUMCHECK

FLAGS=dict(global_bound_proved=False,RH_proved=False)
digest=BASE.digest
upper=BASE.upper
emit_checkpoint=V2.emit_checkpoint
validate_storage=OLD.validate_storage
instantiate_certificate=OLD.instantiate_certificate


def prepare(instances, gram_blocks, storage_blocks, *, gram_specs=None, **limits):
    validate_storage(gram_blocks,storage_blocks)
    for groups in gram_blocks:
        for rows in groups.values():
            for row in rows:
                if type(row) is not list or len(row)!=15 or BASE.L.load_poly(row[0])!={():F(1)}:
                    raise ValueError('complete full15 row with constant unit atom')
    specs=A.gram_specs()
    if gram_specs is not None and gram_specs!=specs:
        raise ValueError('entire affine full15 matrix cone required')
    pairs=len(upper(15)); cap=limits.get('max_columns',2048)
    base_limits=dict(limits,max_columns=cap-pairs)
    if base_limits['max_columns']<1:
        raise OverflowError('affine storage column cap')
    cols,lhs,ms,shape,offset,blocks,_=BASE.prepare(instances,gram_blocks,
        gram_specs={'full_child':15,'full_parent':15},**base_limits)
    used=0
    for j in range(pairs):
        child,parent=cols[offset+j],cols[offset+pairs+j]
        used+=len(child)+len(parent)
        if used>limits.get('max_operations',200000000):
            raise OverflowError('affine storage assembly work cap')
        if limits.get('deadline') is not None and time.monotonic()>limits['deadline']:
            raise TimeoutError('affine storage assembly deadline')
        column=dict(child)
        for m,q in parent.items():column[m]=column.get(m,F(0))-4*q
        cols.append({m:q for m,q in column.items() if q})
    bits=limits.get('max_coefficient_bits',4096)
    if any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>bits for p in cols for q in p.values()):
        raise OverflowError('affine storage coefficient bits')
    ms=sorted(set(lhs)|{m for p in cols for m in p})
    if len(ms)>limits.get('max_monomials',30000):raise OverflowError('affine storage complete domain cap')
    if len(cols)>cap:raise OverflowError('affine storage column cap')
    return cols,lhs,ms,shape,offset,blocks,specs


def compilation_charge(instances, blocks, columns):
    pairs=sum(len(row[i])*len(row[j]) for groups in blocks for rows in groups.values() for row in rows for i,j in upper(15))
    source=len(json.dumps(instances,sort_keys=True,separators=(',',':')).encode())
    return source+8*pairs+8*sum(map(len,columns))+1


def proposal_checkpoint(*args,**kwargs):
    out=OLD.proposal_checkpoint(*args,**kwargs)
    out['schema']='affine-storage-SDP-proposal-v1'
    return out


def independent_admission(kind, instances, blocks, storage, specs, result, callback):
    if callback is None:
        import check_cancellation_affine_storage as I
        callback=getattr(I,'verify_'+kind)
    if not callable(callback):raise ValueError('independent verification callback must be callable')
    check=callback(instances,blocks,storage,specs,result)
    if type(check) is not dict or check.get('verified') is not True:
        raise ValueError('independent exact verification callback did not verify')
    return check


def synthesize(instances,gram_blocks,storage_blocks,*,gram_specs=None,max_exact_cells=2000000,
               max_exact_work=450000000,max_checkpoint_bytes=8388608,on_checkpoint=None,
               verification_callback=None,row_normalization=True,time_limit=360,max_denominator=1000000,
               max_columns=2048,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,
               max_horizon=80,max_degree=12):
    start=time.monotonic();checkpoint=None;charged_work=0
    diagnostics=dict(objective='unit scalar structural L1 plus Gram traces; nonnegative perinstance scalar slack',
                     optimality_claim=False,numerical_threads=1,native_call_interruptible=False,
                     reconstruction_attempts=[],native_attempt_receipts=[])
    try:
        if any(type(v) is not int or v<1 for v in (max_exact_cells,max_exact_work,max_checkpoint_bytes,max_denominator,max_columns,max_monomials,max_operations,max_coefficient_bits,max_horizon,max_degree)):
            raise ValueError('positive strict limits')
        if type(time_limit) not in (int,float) or not math.isfinite(time_limit) or not 0<time_limit<=360 or max_exact_work>450000000:
            raise ValueError('authorized total charged work/cooperative time ceiling')
        if row_normalization is not True or (on_checkpoint is not None and not callable(on_checkpoint)) or (verification_callback is not None and not callable(verification_callback)):
            raise ValueError('normalization bool and optional callbacks')
        deadline=start+time_limit
        cols,lhs,ms,shape,offset,blocks,specs=prepare(instances,gram_blocks,storage_blocks,gram_specs=gram_specs,
            deadline=deadline,max_columns=max_columns,max_monomials=max_monomials,max_operations=max_operations,
            max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,max_degree=max_degree)
        if sum(map(len,cols))>max_operations:raise OverflowError('SDP sparse-size cap')
        floats,numerical=NUM.primal_proposal(cols,lhs,ms,shape,offset,specs,deadline=deadline,
            max_operations=max_operations,max_cells=max_exact_cells,max_coefficient_bits=max_coefficient_bits)
        diagnostics['numerical_proposal']=numerical
        diagnostics['numerical_verification_pending']=True
        diagnostics['numerical_candidate_vector']=None if floats is None else floats.tolist()
        numerical_check=NUMCHECK.verify_system_proposal('primal',cols,lhs,ms,numerical,
            None if floats is None else floats.tolist(),shape=shape,offset=offset,specs=specs,
            deadline=deadline,max_operations=max_operations,max_cells=max_exact_cells,max_coefficient_bits=max_coefficient_bits)
        numerical_reserve=numerical_check['numerical_assembly_work_reserve']
        diagnostics['numerical_verification_pending']=False
        diagnostics.update(numerical_proposal=numerical,numerical_transformation_check=numerical_check,
            numerical_work_reserve=numerical_reserve,sdp_status=numerical.get('sdp_status'),columns=len(cols),
            monomials=len(ms),row_normalization=True,float_objective=None)
        if floats is None:
            return dict(status='uncertified',reason='no numerical SDP proposal after exact row compression; no infeasibility theorem',
                diagnostics=diagnostics,proposal_checkpoint=None,**FLAGS)
        ns,nr=shape
        support=numerical['support']
        checkpoint=proposal_checkpoint(instances,blocks,specs,cols,lhs,ms,shape,offset,floats,support,diagnostics,
            max_checkpoint_bytes=max_checkpoint_bytes,row_normalization=row_normalization)
        charged_work=compilation_charge(instances,blocks,cols)+numerical_reserve
        checkpoint.update(storage_block_hashes=list(map(digest,storage_blocks)),grammar_hash=digest(A.SPEC),
            reconstruction_limits=dict(max_exact_work=max_exact_work,max_exact_cells=max_exact_cells,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits,max_operations=max_operations,time_limit=time_limit),
            compilation_work_reserve=charged_work,native_attempt_receipts=diagnostics['native_attempt_receipts'],
            reconstruction_attempts=diagnostics['reconstruction_attempts'])
        checkpoint.update(numerical_proposal=numerical,numerical_work_reserve=numerical_reserve,
            numerical_transformation='exact augmented proportional-row compression and positive infinity scaling; identity columns')
        checkpoint.update(row_order_hash=digest(checkpoint['monomials']),layout_hash=digest(checkpoint['column_layout']))
        emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
        diagnostics.pop('numerical_candidate_vector',None)
        if time.monotonic()>deadline:raise TimeoutError('SDP numerical transformation deadline')
        for bound in sorted(set([min(64,max_denominator),min(4096,max_denominator),max_denominator])):
            initial=[F(float(x)).limit_denominator(bound) for x in floats]
            for i in range(offset):
                if abs(floats[i])<1e-7:initial[i]=F(0)
            residue=dict(lhs)
            for p,w in zip(cols,initial):
                for m,q in p.items():residue[m]=residue.get(m,F(0))-w*q
            residue={m:q for m,q in residue.items() if q}
            diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='native correction started'))
            before=charged_work;assembly=8*sum(map(len,cols))+len(lhs)+len(initial)+1;charged_work+=assembly
            attempt=dict(bound=bound,initial_hash=digest(list(map(str,initial))),residual_hash=digest([[list(m),str(q)] for m,q in sorted(residue.items())]),support_hash=digest(support),charge_before=before,assembly_reserve=assembly,
                charge_before_native=charged_work,remaining_work=max_exact_work-charged_work,native_returned=False,native_gate_rejected=False,status='prepared')
            diagnostics['native_attempt_receipts'].append(attempt)
            checkpoint['total_charged_work_proxy_before_native']=charged_work
            emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
            if charged_work>=max_exact_work:raise OverflowError('total charged reconstruction work cap')
            exact_diagnostics={}
            try:
                correction=N.exact_support_solution(cols,residue,support,deadline=deadline,max_denominator=max_denominator,
                    max_coefficient_bits=max_coefficient_bits,max_rows=max_monomials,max_columns=max_columns,max_cells=max_exact_cells,max_work=max_exact_work-charged_work,diagnostics=exact_diagnostics)
                attempt.update(native_returned=True,status='returned',correction_available=correction is not None)
            except (OverflowError,TimeoutError,MemoryError,ValueError,RuntimeError) as e:
                attempt.update(status='failed',reason=str(e),native_gate_rejected=str(e)=='compressed native plus preprocessing total work proxy')
                raise
            finally:
                info=exact_diagnostics.get('row_compression',{})
                charge=info.get('preprocessing_work',0) if attempt['native_gate_rejected'] else info.get('total_work_proxy',0)
                charged_work+=charge
                attempt.update(exact_diagnostics=copy.deepcopy(exact_diagnostics),native_charge=charge,charge_after=charged_work)
                diagnostics.update(total_charged_work_proxy=charged_work,exact_correction_diagnostics=exact_diagnostics)
                emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
            if correction is None:
                diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='no exact active-face correction'));continue
            answer=initial[:]
            for i,q in zip(support,correction):answer[i]+=q
            if any(q.denominator>max_denominator or max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in answer):raise OverflowError('reconstructed rational limits')
            if any(q<0 for q in answer[:offset]):
                diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='negative scalar weight'));continue
            grams={};pos=offset;valid=True
            for r,n in specs.items():
                matrix=[[F(0)]*n for _ in range(n)]
                for a,b in upper(n):matrix[a][b]=matrix[b][a]=answer[pos];pos+=1
                matrix=[[str(q) for q in row] for row in matrix]
                try:P.ldlt_psd(matrix,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits)
                except ValueError:valid=False;break
                grams[r]=matrix
            if not valid:
                diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='exact matrix not PSD'));continue
            rebuilt={}
            for p,w in zip(cols,answer):
                for m,q in p.items():rebuilt[m]=rebuilt.get(m,F(0))+w*q
            if {m:q for m,q in rebuilt.items() if q}!=lhs:raise ValueError('original full coefficient mismatch')
            weights=dict(square_weights=list(map(str,answer[:ns])),relation_weights=[str(answer[ns+2*j]-answer[ns+2*j+1]) for j in range(nr)])
            certificates=[]
            for instance,row,transport in zip(instances,blocks,storage_blocks):
                remaining=deadline-time.monotonic()
                if remaining<=0:raise TimeoutError('exact certificate deadline')
                certificates.append(instantiate_certificate(instance,weights,grams,row,transport,max_monomials=max_monomials,max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,time_limit=remaining,max_columns=max_columns+len(specs),max_degree=max_degree,max_denominator=max_denominator))
            diagnostics['reconstruction_attempts'].append(dict(bound=bound,status='exact PSD and full coefficient match'))
            result=dict(status='finite_PSD_certificate',weights=weights,grams=grams,gram_specs=specs,
                source_hashes=list(map(digest,instances)),gram_block_hashes=list(map(digest,blocks)),storage_block_hashes=list(map(digest,storage_blocks)),grammar_hash=digest(A.SPEC),
                constant_slacks=list(map(str,answer[ns+2*nr:offset])),exact_column_weights=list(map(str,answer)),certificates=certificates,diagnostics=diagnostics,proposal_checkpoint=checkpoint,
                scope='finite shared affine PSD certificate; no uniform signed bound',state_matrix=A.anchored_matrix(grams['storage_K']),**FLAGS)
            result['independent_check']=independent_admission('primal',instances,blocks,storage_blocks,specs,result,verification_callback)
            if time.monotonic()>deadline:raise TimeoutError('independent primal verification deadline')
            emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
            return result
        return dict(status='uncertified',reason='numerical proposal lacks admitted rational PSD reconstruction',diagnostics=diagnostics,proposal_checkpoint=checkpoint,**FLAGS)
    except (OverflowError,TimeoutError,MemoryError,ImportError) as e:status='missing_resource';error=e
    except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError) as e:status='uncertified';error=e
    if checkpoint is not None:
        checkpoint['failure']=str(error)
        if len(json.dumps(checkpoint,sort_keys=True,separators=(',',':'),allow_nan=False).encode())>max_checkpoint_bytes:
            checkpoint=None;diagnostics['checkpoint_omitted']='byte cap'
    return dict(status=status,reason=str(error),diagnostics=diagnostics,proposal_checkpoint=checkpoint,**FLAGS)
