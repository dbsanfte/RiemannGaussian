"""Structural LP search using sparse matrices, bounded caches and native rationals.
The dictionary and structural L1 objective match cancellation_arithmetic_synthesis.
Every finite result still needs the separate independent arithmetic checker.
"""
from fractions import Fraction as F
import math
import time
import warnings
from cancellation_arithmetic_synthesis import objective_costs
from exact_polynomial_column_cache import ColumnCache
from grouped_arithmetic_sparse import instantiate_details
from native_exact_support import exact_support_solution
import grouped_arithmetic_synthesis as G
FLAGS = dict(global_bound_proved=False, RH_proved=False)


def sparse_matrix(columns, monomials):
    from scipy.sparse import csc_matrix
    row_index = {m: j for j,m in enumerate(monomials)}
    rows = []; values = []; offsets = [0]
    for column in columns:
        for m,q in column.items():
            value = float(q)
            if not math.isfinite(value): raise OverflowError('float proposal conversion')
            rows.append(row_index[m]); values.append(value)
        offsets.append(len(values))
    return csc_matrix((values, rows, offsets), shape=(len(monomials), len(columns)))


def synthesize(instances, *, allow_constant_slack=True, max_columns=1024,
               max_monomials=10000, max_operations=200000000,
               max_coefficient_bits=2048, max_horizon=4096, max_degree=12,
               max_denominator=1000000, time_limit=10, column_cache=None,
               max_exact_cells=2000000):
    start = time.monotonic()
    diagnostics = dict(objective='structural L1; zero-cost scalar slack',
                       lp_optimality_claim=False, proposal_matrix='CSC',
                       highs_threads=1, highs_parallel=False,
                       exact_backend='FLINT rational RREF',
                       native_call_interruptible=False)
    try:
        for v in (max_columns,max_monomials,max_operations,max_coefficient_bits,
                  max_horizon,max_degree,max_denominator,max_exact_cells):
            if type(v) is not int or v < 1: raise ValueError('positive resource limits')
        if type(allow_constant_slack) is not bool or type(time_limit) not in (int,float) or not math.isfinite(time_limit) or time_limit <= 0:
            raise ValueError('time/flag domain')
        deadline = start + time_limit
        limits = dict(max_columns=max_columns,max_monomials=max_monomials,
                      max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,
                      max_horizon=max_horizon,max_degree=max_degree)
        cache = column_cache if column_cache is not None else ColumnCache(max_entries=1)
        prepared = cache.prepare(instances, deadline=deadline, **limits)
        columns,lhs,monomials,shape = (prepared[k] for k in ('columns','lhs','monomials','shape'))
        diagnostics['column_cache'] = prepared['metadata']
        if allow_constant_slack:
            monomials = G._add_slacks(columns,lhs,monomials,len(instances),max_columns,max_monomials)
        costs = objective_costs(*shape,len(instances),allow_constant_slack)
        diagnostics.update(rows=len(monomials),columns=len(columns),nonzero_coefficients=sum(map(len,columns)))
        answer = [F(0)] * len(columns)
        if lhs:
            if not columns:
                return dict(status='no_certificate_found',reason='no columns',diagnostics=diagnostics,**FLAGS)
            from scipy.optimize import linprog, OptimizeWarning
            matrix = sparse_matrix(columns,monomials)
            b = [float(lhs.get(m,0)) for m in monomials]
            if any(not math.isfinite(v) for v in b): raise OverflowError('float target conversion')
            diagnostics.update(proposal_matrix_bytes=matrix.data.nbytes+matrix.indices.nbytes+matrix.indptr.nbytes,
                               dense_float64_equivalent_bytes=len(monomials)*len(columns)*8)
            # HiGHS uses its own scheduler; OMP/BLAS environment caps alone do
            # not constrain it. SciPy forwards these native options verbatim.
            with warnings.catch_warnings():
                warnings.filterwarnings('ignore',category=OptimizeWarning,
                    message=r"Unrecognized options detected: \{'threads': 1, 'parallel': False\}\. These will be passed to HiGHS verbatim\.")
                result = linprog(costs,A_eq=matrix,b_eq=b,bounds=(0,None),method='highs',
                    options={'time_limit':max(.001,deadline-time.monotonic()),
                             'threads':1,'parallel':False})
            diagnostics.update(lp_status=int(result.status),lp_message=str(result.message),
                               float_objective=None if result.fun is None else float(result.fun))
            if time.monotonic()>deadline: raise TimeoutError('proposal deadline')
            if not result.success:
                return dict(status='missing_resource' if result.status==1 else 'no_certificate_found',
                            reason='no float support; not mathematical infeasibility',diagnostics=diagnostics,**FLAGS)
            support = [j for j,v in enumerate(result.x) if v>1e-9]
            diagnostics['proposed_support'] = support
            exact = exact_support_solution(columns,lhs,support,deadline=deadline,
                max_rows=max_monomials,max_columns=max_columns,max_cells=max_exact_cells,
                max_work=max_operations,max_denominator=max_denominator,
                max_coefficient_bits=max_coefficient_bits)
            if exact is None or any(q<0 for q in exact):
                return dict(status='no_certificate_found',reason='support failed exact nonnegative reconstruction',diagnostics=diagnostics,**FLAGS)
            for j,q in zip(support,exact): answer[j]=q
        n,r=shape
        weights=dict(square_weights=list(map(str,answer[:n])),
                     relation_weights=[str(answer[n+2*j]-answer[n+2*j+1]) for j in range(r)])
        details=[instantiate_details(i,weights,**limits,max_denominator=max_denominator,
                    time_limit=time_limit,deadline=deadline,allow_constant_slack=allow_constant_slack)
                 for i in instances]
        slacks=list(map(str,answer[n+2*r:])) if allow_constant_slack else []
        if allow_constant_slack and slacks != [d['constant_slack'] for d in details]:
            raise ValueError('reconstructed scalar slack mismatch')
        diagnostics.update(exact_lp_weights=list(map(str,answer)),
                           exact_structural_objective=str(sum(F(c)*w for c,w in zip(costs,answer))),
                           instantiation=[d['diagnostics'] for d in details],
                           elapsed_seconds=time.monotonic()-start)
        return dict(status='finite_certificate',weights=weights,constant_slacks=slacks,
                    allow_constant_slack=allow_constant_slack,
                    certificates=[d['certificate'] for d in details],diagnostics=diagnostics,
                    scope='fixed finite shared scalar cone; Grams fixed zero; no global estimate',**FLAGS)
    except (OverflowError,TimeoutError,MemoryError,ImportError) as e:
        return dict(status='missing_resource',reason=str(e),diagnostics=diagnostics,**FLAGS)
    except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError) as e:
        return dict(status='no_certificate_found',reason='rejected: '+str(e),diagnostics=diagnostics,**FLAGS)
