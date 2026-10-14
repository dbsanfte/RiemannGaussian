"""Versioned complete-Gram dual proposal with compressed exact admission.
Bounded synchronous proposal checkpoints precede native calls. No float result
is a theorem; process memory and hard elapsed limits belong to the runner.
"""
import math,time,copy,json
from fractions import Fraction as F
import cancellation_shared_gram_synthesis as S
import check_cancellation_shared_gram as I
import native_exact_support_compressed as N
from cancellation_shared_gram_dual import classify
from cancellation_native_gram_dual import support_proposal
FLAGS=dict(global_bound_proved=False,RH_proved=False)

def emit_checkpoint(checkpoint,callback,max_bytes):
 if len(json.dumps(checkpoint,sort_keys=True,separators=(',',':'),allow_nan=False).encode())>max_bytes:raise OverflowError('dual proposal checkpoint byte cap')
 if callback is not None:
  try:callback(copy.deepcopy(checkpoint))
  except Exception as e:raise RuntimeError('dual checkpoint callback failed: '+str(e))from e

def bounded_failure(checkpoint,error,max_bytes):
 if checkpoint is None:return None
 checkpoint['failure']=str(error)
 return checkpoint if len(json.dumps(checkpoint,sort_keys=True,separators=(',',':'),allow_nan=False).encode())<=max_bytes else None

def make_checkpoint(instances,blocks,specs,columns,lhs,monomials,shape,offset,nonnegative,relations,layout,limits):
 domain=[dict(instance=m[0],m=list(m[1:]))for m in monomials]
 scalar_layout=[dict(index=i,kind='scalar')for i in range(offset)]
 for name,n,entries in layout:
  for pos,a,b in entries:scalar_layout.append(dict(index=pos,kind='Gram',group=name,i=a,j=b))
 return dict(schema='shared-Gram-dual-proposal-v2',phase='prepared_domain',proposal_only=True,certified=False,**FLAGS,
  source_hashes=[S.digest(i)for i in instances],gram_block_hashes=[S.digest(b)for b in blocks],gram_specs=specs,
  monomials=domain,row_order_hash=S.digest(domain),scalar_shape=list(shape),scalar_offset=offset,
  exact_columns_hash=S.digest([[[list(m),str(q)]for m,q in sorted(p.items())]for p in columns]),
  exact_target_hash=S.digest([[list(m),str(q)]for m,q in sorted(lhs.items())]),column_layout=scalar_layout,layout_hash=S.digest(scalar_layout),
  nonnegative_indices=nonnegative,relation_indices=relations,dual_equation_order=relations+nonnegative,
  dual_variable_order='positive monomial coordinates; negative monomial coordinates; nonnegative column slacks',
  support=None,numerical_diagnostics={},numerical_options=dict(solver='HiGHS',threads=1,parallel=False,support_threshold='1e-8'),limits=limits,refitted=False)

def propose(instances, gram_blocks, *, gram_specs=None, on_checkpoint=None,max_checkpoint_bytes=8388608,time_limit=180,
            max_rows=2000, max_variables=60000, max_work=450000000,max_preprocessing_operations=200000000,max_preprocessing_cells=4000000,
            max_cells=4000000, max_denominator=2**4096,
            max_coefficient_bits=4096, max_columns=2048,
            max_monomials=30000, max_operations=200000000,
            max_horizon=80, max_degree=12):
    start = time.monotonic()
    diagnostics = {};checkpoint=None
    try:
        if type(time_limit) not in (int, float) or not math.isfinite(time_limit) or time_limit <= 0:
            raise ValueError('positive finite time limit')
        limits = (max_rows, max_variables, max_work, max_cells, max_denominator,
                  max_coefficient_bits, max_columns, max_monomials,
                  max_operations, max_horizon, max_degree,max_checkpoint_bytes,max_preprocessing_operations,max_preprocessing_cells)
        if any(type(v) is not int or v < 1 for v in limits):
            raise ValueError('positive integer resource limits')
        if on_checkpoint is not None and not callable(on_checkpoint):raise ValueError('optional checkpoint callback must be callable')
        deadline = start + time_limit
        columns, lhs, monomials, shape, offset, blocks, specs = S.prepare(
            instances, gram_blocks, gram_specs=gram_specs, deadline=deadline,
            max_columns=max_columns, max_monomials=max_monomials,
            max_operations=max_operations, max_coefficient_bits=max_coefficient_bits,
            max_horizon=max_horizon, max_degree=max_degree)
        nonnegative, relations, layout = classify(columns, shape, offset, specs)
        # Retain diagonals as well as all cross columns in the moment domain.
        if set(monomials) != set(lhs) | {m for p in columns for m in p}:
            raise ValueError('complete full-Gram monomial domain')
        checkpoint=make_checkpoint(instances,blocks,specs,columns,lhs,monomials,shape,offset,nonnegative,relations,layout,
         dict(time_limit=time_limit,max_work=max_work,max_cells=max_cells,max_preprocessing_operations=max_preprocessing_operations,max_preprocessing_cells=max_preprocessing_cells,max_rows=max_rows,max_variables=max_variables,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits))
        emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
        support, diagnostics = support_proposal(
            columns, lhs, monomials, nonnegative, relations,
            deadline=deadline, max_rows=max_rows,
            max_variables=max_variables, max_work=max_work)
        checkpoint.update(phase='LP_proposal',support=None if support is None else list(support),numerical_diagnostics=copy.deepcopy(diagnostics))
        emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
        if support is None:
            return dict(status='missing_resource' if diagnostics['solver_status'] == 1 else 'uncertified',
                        certified=False,
                        reason='floating solver did not propose support; no exact infeasibility conclusion',
                        diagnostics=diagnostics,proposal_checkpoint=checkpoint, **FLAGS)
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError('native reconstruction deadline')
        out = N.reconstruct_dual_fixed_support(
            columns, lhs, monomials, nonnegative, relations, support,
            time_limit=remaining, max_rows=max_rows, max_variables=max_variables,
            max_work=max_work, max_cells=max_cells,
            max_denominator=max_denominator, max_coefficient_bits=max_coefficient_bits,max_preprocessing_operations=max_preprocessing_operations,max_preprocessing_cells=max_preprocessing_cells)
        out['proposal_diagnostics'] = diagnostics
        checkpoint.update(phase='native_reconstruction',native_status=out['status'],native_diagnostics=copy.deepcopy(out.get('diagnostics',{})),native_reason=out.get('reason'))
        emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
        out['proposal_checkpoint']=checkpoint
        if not out.get('certified'):
            return out
        y = dict(zip(monomials, map(F, out['weights'])))
        grams = {}
        for name, n, entries in layout:
            H = [[F(0) for _ in range(n)] for _ in range(n)]
            for pos, a, b in entries:
                value = sum((F(q) * y[m] for m, q in columns[pos].items()), F(0))
                H[a][b] = H[b][a] = value if a == b else value / 2
                if a != b and value:
                    raise ValueError('restricted cross moment nonzero')
                if a == b and value < 0:
                    raise ValueError('negative Gram diagonal')
            matrix = [[str(q) for q in row] for row in H]
            grams[name] = dict(matrix=matrix, PSD_certificate=I.verify_psd(matrix))
        constants = [str(y.get((i,), F(0))) for i in range(len(instances))]
        complete_dots = out['columns_dot_y']
        out.update(
            monomials=[dict(instance=m[0], m=list(m[1:])) for m in monomials],
            columns_dot_y=complete_dots[:offset],
            gram_columns_dot_y=complete_dots[offset:],
            gram_duals=grams, gram_specs=specs,
            source_hashes=[S.digest(x) for x in instances],
            gram_block_hashes=[S.digest(x) for x in blocks],
            constant_coordinates=constants,
            all_C_q_extension_requires_zero_constant_coordinates=all(F(q) == 0 for q in constants),
            restricted_dual_search='all offdiagonal moments zero; successful witness separates full declared PSD cone',
            **FLAGS)
        out['independent_check'] = I.verify_dual(instances, blocks, specs, out)
        if time.monotonic() > deadline:
            raise TimeoutError('independent verification deadline')
        out['diagnostics']['elapsed_total_seconds'] = time.monotonic() - start
        out['independent_full_Gram_check_passed'] = True
        checkpoint.update(phase='independent_admission',independently_verified=True)
        emit_checkpoint(checkpoint,on_checkpoint,max_checkpoint_bytes)
        return out
    except (OverflowError, TimeoutError, MemoryError, ImportError) as e:
        checkpoint=bounded_failure(checkpoint,e,max_checkpoint_bytes)
        return dict(status='missing_resource', certified=False, reason=str(e), diagnostics=diagnostics,proposal_checkpoint=checkpoint, **FLAGS)
    except (ValueError, TypeError, KeyError, ZeroDivisionError, RuntimeError) as e:
        checkpoint=bounded_failure(checkpoint,e,max_checkpoint_bytes)
        return dict(status='uncertified', certified=False, reason=str(e), diagnostics=diagnostics,proposal_checkpoint=checkpoint, **FLAGS)
