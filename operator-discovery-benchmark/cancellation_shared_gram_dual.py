"""Restricted floating support proposal and exact arbitrary shared-Gram separator.

Every Gram diagonal is nonnegative and every cross moment is restricted to zero.
Success is independently admitted for the complete declared PSD cone; failure
is never a floating infeasibility theorem. Native RREF needs a worker deadline.
"""
import math
import time
from fractions import Fraction as F

import cancellation_shared_gram_synthesis as S
import check_cancellation_shared_gram as I
import native_exact_support as N
from cancellation_native_gram_dual import support_proposal

FLAGS = dict(global_bound_proved=False, RH_proved=False)


def classify(columns, shape, offset, specs):
    """Classify the complete scalar-plus-upper-Gram column domain."""
    ns, nr = shape
    if any(type(v) is not int or v < 0 for v in (ns, nr, offset)) or offset < ns + 2 * nr:
        raise ValueError('scalar column shape')
    if type(specs) is not dict or not specs or any(type(k) is not str or not k for k in specs):
        raise ValueError('named Gram dimensions')
    if any(type(n) is not int or not 1 <= n <= 64 for n in specs.values()):
        raise ValueError('bounded positive Gram dimensions')
    nonnegative = list(range(ns)) + list(range(ns + 2 * nr, offset))
    relations = list(range(ns, ns + 2 * nr))
    layout = []
    pos = offset
    for name in sorted(specs):
        n = specs[name]
        entries = []
        for a, b in S.upper(n):
            entries.append((pos, a, b))
            (nonnegative if a == b else relations).append(pos)
            pos += 1
        layout.append((name, n, entries))
    if pos != len(columns):
        raise ValueError('complete scalar and Gram column coverage')
    return nonnegative, relations, layout


def propose(instances, gram_blocks, *, gram_specs=None, time_limit=180,
            max_rows=2000, max_variables=60000, max_work=400000000,
            max_cells=2000000, max_denominator=2**4096,
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
        support, diagnostics = support_proposal(
            columns, lhs, monomials, nonnegative, relations,
            deadline=deadline, max_rows=max_rows,
            max_variables=max_variables, max_work=max_work)
        if support is None:
            return dict(status='missing_resource' if diagnostics['solver_status'] == 1 else 'uncertified',
                        certified=False,
                        reason='floating solver did not propose support; no exact infeasibility conclusion',
                        diagnostics=diagnostics, **FLAGS)
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError('native reconstruction deadline')
        out = N.reconstruct_dual_fixed_support(
            columns, lhs, monomials, nonnegative, relations, support,
            time_limit=remaining, max_rows=max_rows, max_variables=max_variables,
            max_work=max_work, max_cells=max_cells,
            max_denominator=max_denominator, max_coefficient_bits=max_coefficient_bits)
        out['proposal_diagnostics'] = diagnostics
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
