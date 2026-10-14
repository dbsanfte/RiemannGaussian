"""Full15 dual proposals and exact leaf restoration with retained receipts.

K cross-equation removal is only a numerical algebraic optimization. Admission
checks the complete domain, every original scalar source and all 15x15 moments.
"""
from fractions import Fraction as F
import copy
import math
import time
import cancellation_affine_storage_synthesis as S
import cancellation_affine_storage as A
import cancellation_anchored_storage_dual as OLD
import check_cancellation_shared_gram as PSD
import native_exact_support_leaf as N
from cancellation_shared_gram_dual import classify
from cancellation_native_gram_dual import support_proposal

FLAGS=dict(global_bound_proved=False,RH_proved=False)
emit_checkpoint=OLD.emit_checkpoint
bounded_failure=OLD.bounded_failure
restricted_columns=OLD.restricted_columns


def make_checkpoint(*args,**kwargs):
    checkpoint=OLD.make_checkpoint(*args,**kwargs)
    checkpoint['schema']='affine-storage-dual-proposal-v1'
    return checkpoint


def propose(instances,gram_blocks,storage_blocks,*,gram_specs=None,on_checkpoint=None,verification_callback=None,
            max_checkpoint_bytes=8388608,time_limit=360,max_rows=2500,max_variables=60000,max_work=450000000,
            max_preprocessing_operations=200000000,max_preprocessing_cells=4000000,max_cells=4000000,
            max_denominator=2**4096,max_coefficient_bits=4096,max_columns=2048,max_monomials=30000,
            max_operations=200000000,max_horizon=80,max_degree=12):
    start=time.monotonic();checkpoint=None;diagnostics={}
    try:
        if type(time_limit) not in (int,float) or not math.isfinite(time_limit) or not 0<time_limit<=360 or max_work>450000000:
            raise ValueError('authorized total charged work/cooperative time ceiling')
        if any(type(v) is not int or v<1 for v in (max_rows,max_variables,max_work,max_preprocessing_operations,max_preprocessing_cells,max_cells,max_denominator,max_coefficient_bits,max_columns,max_monomials,max_operations,max_horizon,max_degree,max_checkpoint_bytes)):
            raise ValueError('positive strict resource limits')
        if (on_checkpoint is not None and not callable(on_checkpoint)) or (verification_callback is not None and not callable(verification_callback)):
            raise ValueError('optional checkpoint and independent verification callbacks')
        deadline=start+time_limit
        columns,lhs,monomials,shape,offset,blocks,specs=S.prepare(instances,gram_blocks,storage_blocks,
            gram_specs=gram_specs,deadline=deadline,max_columns=max_columns,max_monomials=max_monomials,
            max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,max_degree=max_degree)
        nonnegative,relations,layout=classify(columns,shape,offset,specs)
        if set(monomials)!=set(lhs)|{m for p in columns for m in p}:raise ValueError('complete affine full-Gram monomial domain')
        checkpoint=make_checkpoint(instances,blocks,specs,columns,lhs,monomials,shape,offset,nonnegative,relations,layout,
            dict(time_limit=time_limit,max_work=max_work,max_cells=max_cells,max_preprocessing_operations=max_preprocessing_operations,
                max_preprocessing_cells=max_preprocessing_cells,max_rows=max_rows,max_variables=max_variables,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits))
        checkpoint.update(storage_block_hashes=list(map(S.digest,storage_blocks)),grammar_hash=S.digest(A.SPEC))
        restricted,r_nonnegative,r_relations,keep,redundancy=restricted_columns(columns,offset,nonnegative,relations,layout)
        compilation_reserve=S.compilation_charge(instances,blocks,columns)+sum(map(len,columns))+1
        checkpoint.update(restricted_column_indices=keep,
            restricted_exact_columns_hash=S.digest([[[list(m),str(q)] for m,q in sorted(p.items())] for p in restricted]),
            storage_cross_redundancy=redundancy,compilation_work_reserve=compilation_reserve,
            restricted_nonnegative_indices=r_nonnegative,restricted_relation_indices=r_relations,
            dual_equation_order=[keep[i] for i in r_relations+r_nonnegative],native_receipts=[])
        emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
        if compilation_reserve>=max_work:raise OverflowError('total charged compilation/reconstruction work cap')
        support,numerical=support_proposal(restricted,lhs,monomials,r_nonnegative,r_relations,
            deadline=deadline,max_rows=max_rows,max_variables=max_variables,max_work=max_work)
        diagnostics['proposal_diagnostics']=numerical
        checkpoint.update(phase='LP_proposal',support=None if support is None else list(support),numerical_diagnostics=copy.deepcopy(numerical))
        emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
        if support is None:
            return dict(status='missing_resource' if numerical.get('solver_status')==1 else 'uncertified',certified=False,
                reason='floating solver did not propose support; no exact infeasibility conclusion',diagnostics=diagnostics,proposal_checkpoint=checkpoint,**FLAGS)
        remaining=deadline-time.monotonic()
        if remaining<=0:raise TimeoutError('native reconstruction deadline')
        def native_checkpoint(info):
            receipt=copy.deepcopy(info)
            checkpoint['native_receipts'].append(dict(origin='callback',status=receipt['status'],receipt_sha256=S.digest(receipt),
                total_work_proxy=receipt.get('total_work_proxy'),preprocessing_actual_work=receipt.get('preprocessing_actual_work')))
            checkpoint.update(phase='native_reconstruction',native_receipt=receipt)
            emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
        out=N.reconstruct_dual_fixed_support(restricted,lhs,monomials,r_nonnegative,r_relations,support,
            time_limit=remaining,max_rows=max_rows,max_variables=max_variables,max_work=max_work,max_cells=max_cells,
            max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits,
            max_preprocessing_operations=max_preprocessing_operations,max_preprocessing_cells=max_preprocessing_cells,
            max_receipt_bytes=max_checkpoint_bytes,compilation_work_reserve=compilation_reserve,on_checkpoint=native_checkpoint)
        out['proposal_diagnostics']=numerical
        diagnostics=out.get('diagnostics',{})
        native_summary={key:copy.deepcopy(value) for key,value in diagnostics.items() if key!='leaf_elimination'}
        if 'leaf_elimination' in diagnostics:
            checkpoint['native_receipt']=copy.deepcopy(diagnostics['leaf_elimination'])
            native_summary['leaf_receipt_sha256']=S.digest(checkpoint['native_receipt'])
            if not checkpoint['native_receipts'] or checkpoint['native_receipts'][-1]['receipt_sha256']!=native_summary['leaf_receipt_sha256']:
                receipt=checkpoint['native_receipt']
                checkpoint['native_receipts'].append(dict(origin='terminal_return',status=receipt['status'],receipt_sha256=S.digest(receipt),
                    total_work_proxy=receipt.get('total_work_proxy'),preprocessing_actual_work=receipt.get('preprocessing_actual_work')))
        checkpoint.update(phase='native_reconstruction',native_status=out['status'],native_diagnostics=native_summary,native_reason=out.get('reason'))
        emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
        out['proposal_checkpoint']=checkpoint
        if not out.get('certified'):return out
        y=dict(zip(monomials,map(F,out['weights'])));grams={}
        for name,n,entries in layout:
            matrix=[[F(0)]*n for _ in range(n)]
            for pos,a,b in entries:
                value=sum((q*y[m] for m,q in columns[pos].items()),F(0))
                matrix[a][b]=matrix[b][a]=value if a==b else value/2
                if a!=b and value:raise ValueError('restricted cross moment nonzero')
                if a==b and value<0:raise ValueError('negative Gram diagonal')
            matrix=[[str(q) for q in row] for row in matrix]
            grams[name]=dict(matrix=matrix,PSD_certificate=PSD.verify_psd(matrix))
        constants=[str(y.get((i,),F(0))) for i in range(len(instances))]
        restricted_dots=out['columns_dot_y']
        complete_dots=[str(sum((q*y[m] for m,q in p.items()),F(0))) for p in columns]
        if [complete_dots[i] for i in keep]!=restricted_dots:raise ValueError('restricted/full dual dot binding')
        out.update(monomials=[dict(instance=m[0],m=list(m[1:])) for m in monomials],
            columns_dot_y=complete_dots[:offset],gram_columns_dot_y=complete_dots[offset:],gram_duals=grams,gram_specs=specs,
            source_hashes=list(map(S.digest,instances)),gram_block_hashes=list(map(S.digest,blocks)),storage_block_hashes=list(map(S.digest,storage_blocks)),grammar_hash=S.digest(A.SPEC),
            restricted_columns_dot_y=restricted_dots,restricted_column_indices=keep,storage_cross_redundancy=redundancy,
            constant_coordinates=constants,all_C_q_extension_requires_zero_constant_coordinates=all(F(q)==0 for q in constants),
            restricted_dual_search='all offdiagonal moments zero; successful witness separates full declared affine PSD cone',**FLAGS)
        out['independent_check']=S.independent_admission('dual',instances,blocks,storage_blocks,specs,out,verification_callback)
        if time.monotonic()>deadline:raise TimeoutError('independent dual verification deadline')
        out['diagnostics']['elapsed_total_seconds']=time.monotonic()-start
        out['independent_full_Gram_check_passed']=True
        checkpoint.update(phase='independent_admission',independently_verified=True)
        emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
        return out
    except (OverflowError,TimeoutError,MemoryError,ImportError) as e:status='missing_resource';error=e
    except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError) as e:status='uncertified';error=e
    checkpoint=bounded_failure(checkpoint,error,max_checkpoint_bytes)
    return dict(status=status,certified=False,reason=str(error),diagnostics=diagnostics,proposal_checkpoint=checkpoint,**FLAGS)
