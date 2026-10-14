"""Synthesize floor-annihilator bounds without reading Mobius signs.

The optimizer sees floor geometry and an unsigned squarefree mask. Every
floating proposal is rounded and replayed exactly; no solver optimum or
finite coefficient vector is declared a uniform arithmetic theorem.
"""
from fractions import Fraction as Q
from math import isqrt, isfinite
import warnings
import numpy as np
from scipy.optimize import linprog, OptimizeWarning
from scipy.sparse import csr_matrix, hstack, vstack, eye

from prime_transfer_algebra_058 import Meter

SCHEMA = 'mobius-floor-control-v1'
GRID = 2**20
MAX_N = 65536
MAX_HORIZONS = 512
DEFAULT_EXPONENTS = ['0', '1/257', '1/17', '1/9', '1/5', '1/3', '1/2', '2/3']


def parameters_checked(parameters, meter):
    if type(parameters) is not dict or set(parameters) not in (
            {'primes', 'p', 'q', 'alpha', 'gamma'},
            {'primes', 'p', 'q', 'alpha', 'gamma', 'tau'}):
        raise ValueError('source parameter schema; no signed data admitted')
    primes = parameters['primes']
    if type(primes) is not list or not 2 <= len(primes) <= 8:
        raise ValueError('bounded prime registration')
    for p in primes:
        if type(p) is not int or not 2 <= p <= 1000000:
            raise ValueError('actual bounded registered primes')
        for d in range(2, isqrt(p)+1):
            meter.charge(4)
            if p % d == 0: raise ValueError('actual registered prime')
    if primes != sorted(set(primes)):
        raise ValueError('canonical prime registration')
    p, q = parameters['p'], parameters['q']
    if type(p) is not int or type(q) is not int or p not in primes or q not in primes or p >= q:
        raise ValueError('ordered registered source primes')
    for field in ('alpha', 'gamma')+ (('tau',) if 'tau' in parameters else ()):
        value = parameters[field]
        if type(value) is not str or len(value) > 2500:
            raise ValueError('bounded canonical source fraction')
        fraction = Q(value)
        if str(fraction) != value or fraction <= 0 or (field != 'gamma' and fraction >= 1):
            raise ValueError('canonical source fractional gate')
        if max(abs(fraction.numerator).bit_length(), fraction.denominator.bit_length()) > 4096:
            raise OverflowError('source fraction bit capacity')
    return p, q


def power(N, text, meter):
    if type(N) is not int or not 2 <= N <= MAX_N or type(text) is not str:
        raise ValueError('integer scale and canonical exponent')
    a = Q(text)
    if str(a) != text or not 0 <= a <= 1:
        raise ValueError('canonical exponent in[0,1]')
    bits = N.bit_length()*max(a.numerator, a.denominator)
    if bits > 100000:
        raise OverflowError('integer-power bit capacity')
    target, lo, hi = N**a.numerator, 0, N+1
    while hi-lo > 1:
        mid = (lo+hi)//2
        meter.charge(1+bits*max(1, bits.bit_length()))
        if mid**a.denominator <= target: lo = mid
        else: hi = mid
    return lo


def squarefree_mask(D, meter):
    """All square divisors; no prime labels or Mobius parity are queried."""
    answer = bytearray([1])*(D+1)
    answer[0] = 0
    for a in range(2, isqrt(D)+1):
        for n in range(a*a, D+1, a*a):
            answer[n] = 0
            meter.charge(2)
    return answer


def source(N, y, p, q, ratio, meter):
    D, den = 4*N//p, ratio.denominator
    g = [0]*(D+2)
    for d in range(y+1, D+1):
        wp = 4*N//(p*d)-3*(2*N//(p*d))+2*(N//(p*d))
        wq = 4*N//(q*d)-3*(2*N//(q*d))+2*(N//(q*d))
        g[d] = -den*wp+ratio.numerator*wq
        meter.charge(24)
    floors = {}
    for b, scale in ((p, den), (q, -ratio.numerator)):
        for v, a in ((4, 1), (2, -3), (1, 2)):
            X = v*N//b
            if X: floors[X] = floors.get(X, 0)+scale*a
    steps = {T: g[T]-g[T+1] for T in range(1, D+1) if g[T] != g[T+1]}
    meter.charge(8*D)
    return g, floors, steps


def row_endpoints(steps, j):
    joined = {}
    for T, a in steps.items():
        for A, value in ((T//j, a), (T//(j+1), -a)):
            if A: joined[A] = joined.get(A, 0)+value
    return sorted((A for A, value in joined.items() if value), reverse=True)


def dictionary(anchors, depth, limit, meter):
    # Visit quotient blocks, then cover the whole depth range under a cap.
    # A prefix clip would eventually freeze the same rational horizons and
    # erase the intended scale growth of positive fractional exponents.
    horizons = set()
    for A in anchors:
        k, stop = 1, min(depth, A//2)
        while k <= stop:
            X = A//k
            horizons.add(X)
            k = A//X+1
            meter.charge(8)
    ordered = sorted(horizons)
    truncated = len(ordered) > limit
    if truncated:
        ordered = ([ordered[-1]] if limit == 1 else
                   [ordered[i*(len(ordered)-1)//(limit-1)] for i in range(limit)])
        horizons = set(ordered)
    complete = True
    for A in anchors:
        k = 1
        while k <= A//2:
            X = A//k
            if X not in horizons: complete = False
            k = A//X+1
            meter.charge(8)
    return ordered, truncated, complete


def quantize(value, bound):
    if not isfinite(float(value)):
        raise ValueError('finite optimization proposal')
    return max(-bound*GRID, min(bound*GRID, int(round(float(value)*GRID))))


def exact_replay(k, direct, den, ns, horizons, box, primal, eps, dual, matrix, meter):
    """Integer certificate, including a robust lower bound for the box LP."""
    center = GRID*(direct+k[1])+sum(a*(1-X) for a, X in zip(primal, horizons))
    max_product = sum(abs(a)*(X//2) for a, X in zip(primal, horizons))
    if matrix.size and max_product+GRID*max(map(abs, k), default=0) < 2**63:
        residual = np.array([GRID*k[n] for n in ns], dtype=np.int64)-matrix@np.array(primal, dtype=np.int64)
        residual_l1 = sum(abs(int(a)) for a in residual)
    else:
        residual_l1 = sum(abs(GRID*k[n]-sum(a*(X//n) for a, X in zip(primal, horizons))) for n in ns)
    defects = [eps*(1-X)-sum(z*(X//n) for n, z in zip(ns, dual)) for X in horizons]
    lower_num = eps*(direct+k[1])+sum(z*k[n] for n, z in zip(ns, dual))-box*sum(map(abs, defects))
    upper = Q(abs(center)+residual_l1, GRID*den)
    lower = Q(lower_num, GRID*den)
    if lower > upper:
        raise ArithmeticError('box dual lower cannot exceed feasible primal')
    meter.charge(16*max(1, len(ns))*max(1, len(horizons)))
    return {'center_numerator': center, 'residual_l1_numerator': residual_l1,
            'dual_defect_l1_numerator': sum(map(abs, defects)),
            'bound': str(upper), 'box_optimum_lower': str(lower), 'box_gap': str(upper-lower)}


def solve_row(k, direct, den, sf, horizons, meter):
    ns = [n for n in range(2, len(k)) if sf[n]]
    count, m = len(ns), len(horizons)
    box = 4*den*max(1, m)
    meter.reserve(32*1024**2+192*max(1, count)*max(1, m)+256*len(k))
    matrix = np.array([[X//n for X in horizons] for n in ns], dtype=np.int64).reshape((count, m))
    values = np.array([k[n] for n in ns], dtype=float)
    if not m:
        primal, eps = [], GRID*((direct+k[1] > 0)-(direct+k[1] < 0))
        dual = [GRID*((k[n] > 0)-(k[n] < 0)) for n in ns]
        solver = {'status': 'empty_dictionary_exact', 'iterations': 0, 'message': ''}
    else:
        b = np.array([1-X for X in horizons], dtype=float)
        A = csr_matrix(matrix, dtype=float)
        zero = csr_matrix((count, 1)); identity = eye(count, format='csr')
        top = csr_matrix(np.vstack([np.r_[b, -1, np.zeros(count)], np.r_[-b, -1, np.zeros(count)]]))
        constraints = vstack([top, hstack([-A, zero, -identity]), hstack([A, zero, -identity])], format='csr')
        rhs = np.r_[-(direct+k[1]), direct+k[1], -values, values]
        objective = np.r_[np.zeros(m), 1., np.ones(count)]
        # SciPy forwards this native HiGHS option, while warning that it is
        # outside SciPy's own option list. Set the native worker count too.
        with warnings.catch_warnings():
            warnings.filterwarnings('ignore', message="Unrecognized options detected:.*threads.*",
                                    category=OptimizeWarning)
            result = linprog(objective, A_ub=constraints, b_ub=rhs,
                bounds=[(-box, box)]*m+[(0, None)]*(count+1), method='highs-ds',
                options={'presolve': True, 'time_limit': 30.0, 'threads': 1,
                         'dual_feasibility_tolerance': 1e-9, 'primal_feasibility_tolerance': 1e-9})
        iterations = max(0, int(getattr(result, 'nit', 0) or 0))
        meter.charge(4*(iterations+1)*max(1, m)*max(1, count))
        solver = {'status': 'optimal_float_proposal' if result.success else 'failed_zero_fallback',
                  'iterations': iterations, 'message': str(result.message)}
        if result.success:
            primal = [quantize(x, box) for x in result.x[:m]]
            marginal = result.ineqlin.marginals
            eps = quantize(-marginal[0]+marginal[1], 1)
            dual = [quantize(-marginal[2+i]+marginal[2+count+i], 1) for i in range(count)]
        else:
            primal, eps, dual = [0]*m, 0, [0]*count
    proof = exact_replay(k, direct, den, ns, horizons, box, primal, eps, dual, matrix, meter)
    return {'horizons': horizons, 'coefficient_box': box, 'primal_numerators': primal,
            'dual_constant_numerator': eps, 'dual_weight_numerators': dual,
            **proof, 'solver': solver}


def construct(N, y, max_j, parameters, exponents=None, horizon_limit=MAX_HORIZONS, meter=None):
    meter = Meter(cap=300_000_000_000) if meter is None else meter
    exponents = list(DEFAULT_EXPONENTS) if exponents is None else exponents
    if any(type(v) is not int for v in (N, y, max_j)) or not 2 <= N <= MAX_N:
        raise ValueError('bounded integer source')
    p, q = parameters_checked(parameters, meter)
    D = 4*N//p
    if not 1 <= y <= D or not 0 <= max_j <= min(D, 4096):
        raise ValueError('complete source row range')
    if type(horizon_limit) is not int or not 1 <= horizon_limit <= MAX_HORIZONS:
        raise ValueError('floor dictionary capacity')
    if type(exponents) is not list or not 1 <= len(exponents) <= 128 or any(type(x) is not str for x in exponents) or len(set(exponents)) != len(exponents):
        raise ValueError('finite distinct exponent requests')
    depths = [power(N, e, meter) for e in exponents]
    sf = squarefree_mask(D, meter)
    endpoints = []
    for ratio in (Q(p, q), Q(1)):
        den = ratio.denominator
        g, floors, steps = source(N, y, p, q, ratio, meter)
        rows = []
        for j in range(1, max_j+1):
            size = D//j
            k = [0]+[g[j*n]-(g[(j+1)*n] if (j+1)*n <= D else 0) for n in range(1, size+1)]
            direct = floors.get(j, 0)
            anchors = row_endpoints(steps, j)
            cache, models, plans = {}, [], []
            for exponent, depth in [(None, 0)]+list(zip(exponents, depths)):
                hs, truncated, complete = dictionary(anchors, depth, horizon_limit, meter)
                key = tuple(hs)
                if key not in cache:
                    cache[key] = len(models)
                    models.append(solve_row(k, direct, den, sf, hs, meter))
                plans.append({'exponent': exponent, 'depth': depth, 'model_index': cache[key],
                              'dictionary_truncated': truncated, 'complete_endpoint_quotients': complete})
            best = min(range(len(models)), key=lambda a: (Q(models[a]['bound']),
                sum(v != 0 for v in models[a]['primal_numerators']), len(models[a]['horizons']), a))
            rows.append({'j': j, 'direct_scaled': direct, 'unit_kernel_scaled': k[1],
                         'anchors': anchors, 'models': models, 'plans': plans, 'selected_model': best})
        endpoints.append({'ratio': str(ratio), 'denominator': den, 'rows': rows})
    return {'schema': SCHEMA, 'N': N, 'y': y, 'max_j': max_j, 'parameters': parameters,
            'exponent_requests': exponents, 'horizon_limit': horizon_limit, 'coefficient_grid': GRID,
            'endpoints': endpoints, 'learner_mobius_signs_accessed': False,
            'uniform_head_bound_proved': False, 'RH_proved': False}
