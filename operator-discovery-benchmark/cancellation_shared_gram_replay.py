"""Reusable exact saved-support replay; no floating solver or new search.
A native C call needs an external worker timeout for a hard wall-clock bound.
"""
import math,time
from fractions import Fraction as F
import cancellation_shared_gram_synthesis as S
import cancellation_shared_gram_dual as D
import check_cancellation_shared_gram as I
import native_exact_support as N
FLAGS=dict(global_bound_proved=False,RH_proved=False)
classify=D.classify

def budget_check(rows,support_size,*,max_work=450000000,max_cells=4000000):
    """Pure preflight: no native allocation or invocation occurs here."""
    if any(type(n)is not int or n<1 for n in (rows,max_work,max_cells))or type(support_size)is not int or support_size<0:
        raise ValueError('positive dimensions/limits and nonnegative support size')
    work=rows*max(1,support_size)**2;cells=rows*(support_size+1)
    if work>max_work or cells>max_cells:raise OverflowError('saved support native dimension/work proxy')
    return dict(equation_rows=rows,support_size=support_size,work_proxy=work,cells_proxy=cells,max_work=max_work,max_cells=max_cells)

def replay(instances, gram_blocks, *, gram_specs, saved_support, time_limit=180,
            max_rows=2000, max_variables=60000, max_work=450000000,
            max_cells=4000000, max_denominator=2**4096,
            max_coefficient_bits=4096, max_columns=2048,
            max_monomials=30000, max_operations=200000000,
            max_horizon=80, max_degree=12):
    start = time.monotonic()
    diagnostics = {}
    try:
        if type(time_limit) not in (int, float) or not math.isfinite(time_limit) or time_limit <= 0:
            raise ValueError('positive finite time limit')
        limits = (max_rows, max_variables, max_work, max_cells, max_denominator,
                  max_coefficient_bits, max_columns, max_monomials,
                  max_operations, max_horizon, max_degree)
        if any(type(v) is not int or v < 1 for v in limits):
            raise ValueError('positive integer resource limits')
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
        variables=2*len(monomials)+len(nonnegative)
        if type(saved_support)is not list or any(type(i)is not int or not 0<=i<variables for i in saved_support)or len(set(saved_support))!=len(saved_support):
            raise ValueError('saved support unique valid indices')
        support=list(saved_support)
        diagnostics.update(budget_check(len(columns)+1,len(support),max_work=max_work,max_cells=max_cells))
        diagnostics.update(method='saved support only; no new floating proposal',support_hash=S.digest(support),refitted=False)
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError('native reconstruction deadline')
        out = N.reconstruct_dual_fixed_support(
            columns, lhs, monomials, nonnegative, relations, support,
            time_limit=remaining, max_rows=max_rows, max_variables=max_variables,
            max_work=max_work, max_cells=max_cells,
            max_denominator=max_denominator, max_coefficient_bits=max_coefficient_bits)
        out['replay_diagnostics'] = diagnostics
        out['refitted'] = False
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
        return out
    except (OverflowError, TimeoutError, MemoryError, ImportError) as e:
        return dict(status='missing_resource', certified=False, reason=str(e), diagnostics=diagnostics, **FLAGS)
    except (ValueError, TypeError, KeyError, ZeroDivisionError, RuntimeError) as e:
        return dict(status='uncertified', certified=False, reason=str(e), diagnostics=diagnostics, **FLAGS)
