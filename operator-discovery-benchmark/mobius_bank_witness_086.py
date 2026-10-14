"""Seek artificial anchored Boolean witnesses compatible with a typed bank.

Only exact bank compatibility and the full rational quadratic value admit a
lower certificate. HiGHS supplies proposals, never an infeasibility proof or
a proof of a global quadratic maximum. The actual unknown Mobius signs are
not queried. This finite witness bounds both unrestricted signed-bank and
mixed-bank positive-square grammars, and makes no all-scale or RH claim.
"""
from fractions import Fraction as Q
from math import gcd, isfinite
import os
import time
import warnings

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from flint import fmpq_mat

import mobius_arithmetic_bank_086 as BANK
import mobius_mixed_zero_086 as MIXED

B = MIXED.B
DEFAULT_SEED = 20261011086
MAX_ATTEMPTS = 16
MAX_LOCAL_STEPS = 16
MAX_INTEGER_BITS = 4096
MAX_FLOAT_INTEGER = 1 << 50
NATIVE_ENV_KEYS = ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS',
                   'NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS')


def _gate(model, m=0, bits=64, extra=0, work=0):
    MIXED._gate(model,m,bits,extra=extra,work=work)
    if not model['program']['prime_anchor']:
        raise ValueError('compatible witness requires the complete original unit/prime anchor')


def integer_system(model, bank):
    """Construct exact binary equations and literal elementary obstructions.

    For a bank numerator column c, anchor s0=1 and si=2xi-1 give
    sum(i>0) ci xi = (sum(i>0) ci-c0)/2. Column denominators cancel from
    this homogeneous equation. Parity, gcd and binary-range obstructions
    below are exact necessary conditions; their absence proves no existence.
    """
    BANK.parse_bank(bank)
    m,n = len(bank),model['price_dimension']
    _gate(model,m,extra=n*max(1,m)*4096,work=32*n*max(1,m))
    columns,rows,rhs,obstructions,diagnostics = [],[],[],[],[]
    for j,descriptor in enumerate(bank):
        rec = BANK.integer_column(model,descriptor)
        raw = rec['column']
        if len(raw) != n or type(rec['denominator']) is not int or rec['denominator'] < 1:
            raise ValueError('complete integer bank column and positive denominator required')
        if rec['denominator'].bit_length() > MAX_INTEGER_BITS:
            raise B.ResourceLimit('witness integer column denominator4096bit gate')
        column = []
        for value in raw:
            if type(value) is bool or not isinstance(value,(int,np.integer)):
                raise ValueError('exact bank numerator integers required')
            v = int(value)
            if abs(v).bit_length() > MAX_INTEGER_BITS:
                raise B.ResourceLimit('witness integer column4096bit gate')
            column.append(v)
        bits = max([1]+[abs(v).bit_length() for v in column])+max(1,n.bit_length())+32
        _gate(model,m,bits,work=16*max(1,n))
        columns.append(column)
        diagnostics.append(dict(bank_column=j,cut=rec['cut'],prime_pair_count=rec['prime_pair_count'],
                                denominator=str(rec['denominator'])))
        if not n:
            rows.append([]);rhs.append(0)
            continue
        total = sum(column[1:])-column[0]
        if total % 2:
            obstructions.append(dict(kind='ODD_BINARY_RIGHT_NUMERATOR',bank_column=j,
                                     numerator=str(total),proof='Twice an integer binary sum cannot equal this odd integer.'))
            rows.append(column[1:]);rhs.append(None)
            continue
        right = total//2
        divisor = 0
        for value in column[1:]:divisor = gcd(divisor,abs(value))
        if not divisor:
            if right:
                obstructions.append(dict(kind='ZERO_ROW_NONZERO_RIGHT',bank_column=j,
                                         right=str(right),proof='The binary sum is identically zero while its required right side is nonzero.'))
            reduced = column[1:]
        elif right % divisor:
            obstructions.append(dict(kind='GCD_DOES_NOT_DIVIDE_RIGHT',bank_column=j,
                                     gcd=str(divisor),right=str(right),proof='Every binary sum is a multiple of the displayed gcd.'))
            reduced = column[1:]
        else:
            reduced = [value//divisor for value in column[1:]]
            right //= divisor
        minimum = sum(min(0,value) for value in reduced)
        maximum = sum(max(0,value) for value in reduced)
        if not minimum <= right <= maximum and not any(o['bank_column'] == j for o in obstructions):
            obstructions.append(dict(kind='BINARY_INTERVAL_EXCLUDES_RIGHT',bank_column=j,
                                     minimum=str(minimum),maximum=str(maximum),right=str(right),
                                     proof='With xi in {0,1}, every signed binary sum lies in the displayed exact interval.'))
        rows.append(reduced);rhs.append(right)
    return dict(columns=columns,rows=rows,rhs=rhs,obstructions=obstructions,
                column_diagnostics=diagnostics,bank_size=m,effective_dimension=n)


def compatible(model, system, signs):
    n = model['price_dimension']
    if len(system['columns']) != system['bank_size'] or any(len(column) != n for column in system['columns']):
        raise ValueError('complete exact compatibility system required')
    if type(signs) is not list or len(signs) != n or any(type(s) is not int or s not in (-1,1) for s in signs):
        raise ValueError('complete literal Boolean witness signs required')
    if n and signs[0] != 1:
        raise ValueError('witness anchor must be exactly1')
    _gate(model,system['bank_size'],work=16*n*max(1,system['bank_size']))
    residuals = [sum(c*s for c,s in zip(column,signs)) for column in system['columns']]
    return all(value == 0 for value in residuals),list(map(str,residuals))


def quadratic_value(model, remainder, signs):
    n = model['price_dimension']
    if type(signs) is not list or len(signs) != n or any(type(s) is not int or s not in (-1,1) for s in signs):
        raise ValueError('complete literal Boolean quadratic signs required')
    if not isinstance(remainder,fmpq_mat) or (remainder.nrows(),remainder.ncols()) != (n,n):
        raise ValueError('complete original remainder shape required')
    MIXED._budget_matrices(model,remainder,terms=max(1,n*n),work=16*n*n)
    if not n:return Q(0)
    s = fmpq_mat([[v] for v in signs])
    return B.OLD.as_q((s.transpose()*remainder*s)[0,0])


def _certificate(model, system, remainder, signs):
    ok,residuals = compatible(model,system,signs)
    if not ok:
        raise ValueError('artificial Boolean witness violates exact bank: '+repr(residuals))
    value = quadratic_value(model,remainder,signs)
    return dict(squarefree_count=model['squarefree_count'],signs=list(signs),lower_bound=str(value))


def certificate(model, bank, signs):
    """Reconstruct and bind the exact typed bank and frozen complete remainder."""
    return _certificate(model,integer_system(model,bank),MIXED.original_remainder(model),signs)


def numeric_system(model, system):
    """Lossless integer conversion after row gcd reduction, before any MILP."""
    if system['obstructions']:
        raise ValueError('exact binary obstruction precedes numerical conversion')
    m,n = system['bank_size'],system['effective_dimension']
    _gate(model,m,extra=max(1,n*m)*4096,work=32*n*max(1,m))
    active_rows,active_rhs = [],[]
    for j,(row,right) in enumerate(zip(system['rows'],system['rhs'])):
        # Bound every binary dot product and rhs below2^50. All integer input
        # doubles are then exact; feasibility still requires exact admission.
        if sum(abs(value) for value in row)+abs(right) >= MAX_FLOAT_INTEGER:
            raise B.ResourceLimit('witness MILP exact-integer float conversion50bit gate')
        if any(row):active_rows.append(row);active_rhs.append(right)
    width = max(0,n-1)
    A = np.asarray(active_rows,dtype=float).reshape((len(active_rows),width))
    b = np.asarray(active_rhs,dtype=float)
    return A,b


def improve_compatible(model, system, remainder, signs, steps=4):
    """Exact improving flips, only zero columns or equal-column opposite pairs."""
    if type(steps) is not int or not 0 <= steps <= MAX_LOCAL_STEPS:
        raise ValueError('fixed exact local step count0..16 required')
    initial = _certificate(model,system,remainder,signs)
    n,m = model['price_dimension'],system['bank_size']
    _gate(model,m,extra=n*n*4096,work=(steps+1)*128*n*n*max(1,m))
    current = list(signs)
    profiles = [tuple(column[i] for column in system['columns']) for i in range(n)]
    values = [[B.OLD.as_q(remainder[i,j]) for j in range(n)] for i in range(n)]
    flips = []
    for _ in range(steps):
        field = [sum((values[i][j]*current[j] for j in range(n)),Q(0)) for i in range(n)]
        best_gain,best_indices = Q(0),None
        for i in range(1,n):
            if not any(profiles[i]):
                gain = -4*current[i]*field[i]+4*values[i][i]
                if gain > best_gain:best_gain,best_indices = gain,[i]
            for j in range(i+1,n):
                if profiles[i] != profiles[j] or current[i] == current[j]:continue
                gain = -4*(current[i]*field[i]+current[j]*field[j])+4*(values[i][i]+values[j][j])+8*current[i]*current[j]*values[i][j]
                if gain > best_gain:best_gain,best_indices = gain,[i,j]
        if best_indices is None:break
        for i in best_indices:current[i] = -current[i]
        ok,residuals = compatible(model,system,current)
        if not ok:raise ArithmeticError('constraint-preserving flip violated exact bank')
        flips.append(dict(indices=best_indices,exact_gain=str(best_gain)))
    result = _certificate(model,system,remainder,current)
    if Q(result['lower_bound']) < Q(initial['lower_bound']):
        raise ArithmeticError('exact local quadratic improvement decreased witness')
    return result,dict(flips=flips,initial_lower_bound=initial['lower_bound'],
                       final_lower_bound=result['lower_bound'],anchor_never_flipped=True)


def _native_environment():
    return {key:os.environ.get(key) for key in NATIVE_ENV_KEYS}


def _require_native_one(environment):
    if environment['OPENBLAS_NUM_THREADS'] != '1' or environment['OMP_NUM_THREADS'] != '1':
        raise B.ResourceLimit('witness numerical work requires OPENBLAS_NUM_THREADS=1 and OMP_NUM_THREADS=1 before process launch')
    if any(environment[key] not in (None,'1') for key in NATIVE_ENV_KEYS[2:]):
        raise B.ResourceLimit('witness optional native thread environment must be unset or1')


def _starts(model, remainder, seed, count):
    n = model['price_dimension']
    _gate(model,work=20*n**3+64*max(4,count)*n*n,extra=n*n*2048)
    A = np.array([[float(remainder[i,j]) for j in range(n)] for i in range(n)])
    if not np.isfinite(A).all():raise ValueError('finite full quadratic objective required')
    normalizer = max(1.,float(np.max(np.abs(A))))
    A /= normalizer
    _,vectors = np.linalg.eigh((A+A.T)/2)
    rng = np.random.default_rng(seed)
    raw = [('ALL_PLUS_GRADIENT',np.ones(n))]
    for label,k in [('TOP_EIGEN_SIGN_GRADIENT',n-1),('BOTTOM_EIGEN_SIGN_GRADIENT',0)]:
        s = np.where(vectors[:,k] >= 0,1.,-1.)
        s *= s[0]
        raw.append((label,s))
    for k in range(max(1,count-3)):
        s = rng.choice([-1.,1.],size=n)
        s[0] = 1.
        raw.append(('SEEDED_RANDOM_GRADIENT_'+str(k),s))
    return A,[(name,s.astype(int).tolist()) for name,s in raw],normalizer


def solve_model(model, bank, *, time_limit=10, attempts=4, seed=DEFAULT_SEED,
                node_limit=1000, local_steps=4):
    """Fixed bounded MILP proposals; no numerical failure proves infeasibility."""
    if type(time_limit) not in (int,float) or not isfinite(time_limit) or not 0 < time_limit <= 7200:
        raise ValueError('finite positive witness time_limit<=7200 required')
    if type(attempts) is not int or not 0 <= attempts <= MAX_ATTEMPTS:
        raise ValueError('fixed MILP attempt count0..16 required')
    if type(seed) is not int or not 0 <= seed < 2**63:
        raise ValueError('literal nonnegative seed below2^63 required')
    if type(node_limit) is not int or not 1 <= node_limit <= 100000:
        raise ValueError('fixed MILP node limit1..100000 required')
    if type(local_steps) is not int or not 0 <= local_steps <= MAX_LOCAL_STEPS:
        raise ValueError('fixed exact local step count0..16 required')
    started = time.monotonic()
    receipts,candidates = [],[]
    environment = _native_environment()
    report = dict(u=model['u'],effective_dimension=model['price_dimension'],bank_size=len(bank),
                  seed=seed,requested_milp_attempts=attempts,time_limit_per_milp=time_limit,
                  requested_node_limit=node_limit,local_steps=local_steps,
                  native_environment=environment,highs_threads_requested=1,attempts=receipts,
                  candidates=candidates,artificial_signs_not_actual_Mobius=True,
                  unknown_composite_signs_used=False,original_boolean_coordinates_retained=True,
                  global_quadratic_maximum_proved=False,numerical_infeasibility_is_proof=False,
                  uniform_obstruction_proved=False,uniform_remaining_bound_proved=False,RH_proved=False)
    best = None

    def finish():
        report.update(status='EXACT_COMPATIBLE_BANK_WITNESS_PROPOSAL' if best is not None else 'NO_EXACT_COMPATIBLE_WITNESS_FOUND',
                      certificate=best,elapsed_seconds=time.monotonic()-started,
                      ops=model['meter'].ops,prospective_peak_bytes=model['meter'].peak_bytes)
        return report

    def failure(name,exc,**details):
        receipts.append(dict(name=name,status='RESOURCE_LIMIT' if isinstance(exc,B.ResourceLimit) else 'PROPOSAL_FAILURE',
                             error_type=type(exc).__name__,reason=str(exc),**details))

    def admit(name,signs,**details):
        nonlocal best
        ok,residuals = compatible(model,system,signs)
        if not ok:
            receipts.append(dict(name=name,status='EXACT_BANK_INCOMPATIBLE',residuals=residuals,**details))
            return
        original = _certificate(model,system,remainder,signs)
        chosen = original
        local_diagnostics = None
        if local_steps:
            try:
                chosen,local_diagnostics = improve_compatible(model,system,remainder,signs,steps=local_steps)
            except (ValueError,ArithmeticError,OverflowError) as exc:
                # The already admitted compatible vector remains a valid
                # incumbent even when its optional improvement cannot run.
                local_diagnostics = dict(status='RESOURCE_LIMIT' if isinstance(exc,B.ResourceLimit) else 'PROPOSAL_FAILURE',reason=str(exc))
        receipts.append(dict(name=name,status='EXACT_COMPATIBLE_CERTIFICATE',certificate=chosen,
                             unrefined_certificate=original,local_search=local_diagnostics,**details))
        if not any(c['certificate']['signs'] == chosen['signs'] for c in candidates):
            candidates.append(dict(origin=name,certificate=chosen))
        if best is None or Q(chosen['lower_bound']) > Q(best['lower_bound']):best = chosen

    try:
        system = integer_system(model,bank)
        report['column_diagnostics'] = system['column_diagnostics']
        if system['obstructions']:
            receipts.append(dict(name='EXACT_INTEGER_PRECHECK',status='EXACT_BINARY_INFEASIBILITY_PROVED',proofs=system['obstructions']))
            result = finish()
            result.update(status='EXACT_BOOLEAN_BANK_INFEASIBLE',exact_infeasibility_proofs=system['obstructions'])
            return result
        remainder = MIXED.original_remainder(model)
    except (ValueError,ArithmeticError,OverflowError) as exc:
        failure('EXACT_MODEL_PREPARATION',exc)
        return finish()
    n,m = model['price_dimension'],len(bank)
    # Always seek the cheap exact all-plus incumbent before numerical work.
    try:admit('ALL_PLUS_EXACT_START',[1]*n)
    except (ValueError,ArithmeticError,OverflowError) as exc:failure('ALL_PLUS_EXACT_START',exc)
    if n <= 1:return finish()
    try:
        _require_native_one(environment)
        A,rhs = numeric_system(model,system)
        floating,starts,normalizer = _starts(model,remainder,seed,max(4,attempts))
        report['floating_remainder_normalizer'] = normalizer
        # Bound the proposed branch-node work and reserve half of remaining
        # charged work for exact admissions/local moves. This is a conservative
        # resource estimate, not a theorem about HiGHS instruction counts.
        per_node = 64*(n+m+1)**2*max(1,m+1)
        remaining_work = model['meter'].limit-model['meter'].ops
        actual_nodes = min(node_limit,max(0,remaining_work//(2*max(1,attempts)*per_node)))
        report.update(milp_node_limit=actual_nodes,milp_work_per_node=per_node,
                      predeclared_objectives=[name for name,_ in starts[:attempts]])
        for name,s in starts[1:4]:
            try:admit(name+'_EXACT_START',s)
            except (ValueError,ArithmeticError,OverflowError) as exc:failure(name+'_EXACT_START',exc)
        if attempts and actual_nodes < 1:
            raise B.ResourceLimit('witness prospective work cannot admit one MILP node per fixed attempt')
        constraints = LinearConstraint(A,rhs,rhs) if len(rhs) else None
        bounds = Bounds(np.zeros(n-1),np.ones(n-1))
        integrality = np.ones(n-1,dtype=np.uint8)
    except (ValueError,ArithmeticError,OverflowError,np.linalg.LinAlgError) as exc:
        failure('NUMERICAL_SEARCH_PREPARATION',exc)
        return finish()
    for index,(name,start) in enumerate(starts[:attempts]):
        objective = floating@np.asarray(start,dtype=float)
        weight = objective[1:]
        largest = max(1.,float(np.max(np.abs(weight))))
        cost = -weight/largest
        details = dict(milp_attempt=index,objective=name,start_signs=start,
                       objective_scale=largest,time_limit=time_limit,node_limit=actual_nodes,
                       highs_threads_requested=1)
        caught = []
        try:
            if not np.isfinite(cost).all():raise ValueError('finite MILP objective required')
            _gate(model,m,extra=64*1024**2+(n+m+1)**2*4096,work=actual_nodes*per_node)
            with warnings.catch_warnings(record=True) as caught:
                warnings.simplefilter('always')
                result = milp(cost,integrality=integrality,bounds=bounds,constraints=constraints,
                              options=dict(time_limit=float(time_limit),node_limit=actual_nodes,
                                           presolve=True,mip_rel_gap=0.0,threads=1))
            details.update(solver_status=int(result.status),solver_message=str(result.message),
                           warnings=[str(w.message) for w in caught])
            raw_nodes = getattr(result,'mip_node_count',None)
            raw_gap = getattr(result,'mip_gap',None)
            details['mip_node_count'] = int(raw_nodes) if raw_nodes is not None and isfinite(raw_nodes) else None
            details['mip_gap'] = float(raw_gap) if raw_gap is not None and isfinite(raw_gap) else None
            if result.x is None:
                receipts.append(dict(name='MILP_'+str(index),status='FLOAT_MILP_INFEASIBLE_UNPROVED' if result.status == 2 else 'NO_NUMERICAL_BOOLEAN_PROPOSAL',
                                     infeasibility_proved=False,**details))
                continue
            vector = np.asarray(result.x)
            if vector.shape != (n-1,) or not np.isfinite(vector).all():
                raise ValueError('finite complete MILP binary proposal required')
            rounded = np.rint(vector)
            if not np.isin(rounded,[0,1]).all():raise ValueError('rounded MILP proposal must be binary')
            signs = [1]+[2*int(x)-1 for x in rounded]
            details['max_integer_rounding_deviation'] = float(np.max(np.abs(vector-rounded)))
            admit('MILP_'+str(index),signs,**details)
        except (ValueError,ArithmeticError,OverflowError,RuntimeError) as exc:
            details.setdefault('warnings',[str(w.message) for w in caught])
            failure('MILP_'+str(index),exc,**details)
    return finish()


def solve(program, bank, u, **options):
    return solve_model(MIXED.build_model(program,u),bank,**options)
