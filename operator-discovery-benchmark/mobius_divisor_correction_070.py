"""Adaptive exact bounds from polynomial multiples of local divisor identities.

The optimizer receives a signed polynomial and geometry, never arithmetic
values. Numerical proposals are replayed over integers. Finite bounds are
unconditional; a uniform cost law for their coefficients remains open.
"""
from fractions import Fraction as Q
from heapq import heappush, heapreplace
from math import prod, isqrt, isfinite
import warnings
import numpy as np
from scipy.optimize import linprog, OptimizeWarning
from scipy.sparse import coo_matrix, eye, hstack, vstack
from prime_transfer_algebra_058 import Meter

SCHEMA = 'mobius-divisor-correction-v1'
GRID = 1 << 20
MAX_TERMS = 2_000_000
MAX_RADIUS = 131072
DEFAULT_OPTIONS = dict(rounds=3, batch=16, max_columns=48, pool_limit=192, lp_seconds=2.0)
DEFAULT_SIGMAS = ['1/2', '3/5', '2/3', '3/4', '1']


def rational(text):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded rational text')
    v = Q(text)
    if str(v) != text or max(abs(v.numerator).bit_length(), v.denominator.bit_length()) > 4096:
        raise ValueError('bounded canonical rational')
    return v


def pack(poly):
    return [dict(indices=list(k), numerator=v) for k, v in sorted(poly.items()) if v]


def unpack(terms, radius, degree):
    if type(terms) is not list or len(terms) > MAX_TERMS:
        raise ValueError('complete bounded sparse polynomial')
    result = {}; last = None
    for term in terms:
        if type(term) is not dict or set(term) != {'indices', 'numerator'}:
            raise ValueError('polynomial term schema')
        indices, value = term['indices'], term['numerator']
        if (type(indices) is not list or len(indices) > degree
                or any(type(i) is not int or not 2 <= i <= radius for i in indices)
                or indices != sorted(indices) or type(value) is not int or not value
                or abs(value).bit_length() > 4096):
            raise ValueError('canonical bounded polynomial term')
        key = tuple(indices)
        if last is not None and key <= last: raise ValueError('strict monomial order')
        result[key] = value; last = key
    return result


def input_from_model(model, denominator):
    p = {(): model['constant_scaled']}
    for term in model['terms']:
        p[tuple(term['indices'])] = term['coefficient_scaled']
    return dict(degree=model['degree'], U=model['mu_query_radius'],
                denominator=denominator, polynomial=pack(p))


def validate(source, T, options, sigmas):
    if type(source) is not dict or set(source) != {'degree', 'U', 'denominator', 'polynomial'}:
        raise ValueError('geometry and polynomial only; no signed evaluator input')
    d, U, den = source['degree'], source['U'], source['denominator']
    if (type(d) is not int or not 2 <= d <= 8 or type(U) is not int or not 1 <= U <= MAX_RADIUS
            or type(den) is not int or not 1 <= den <= 1000000
            or type(T) is not int or not U <= T <= MAX_RADIUS):
        raise ValueError('bounded degree, denominator and explicit arithmetic domain')
    if type(options) is not dict or set(options) != set(DEFAULT_OPTIONS):
        raise ValueError('declared search capacities')
    for name, low, high in (('rounds', 0, 8), ('batch', 1, 256), ('max_columns', 1, 256), ('pool_limit', 1, 4096)):
        if type(options[name]) is not int or not low <= options[name] <= high:
            raise ValueError('bounded '+name)
    if type(options['lp_seconds']) not in (int, float) or not isfinite(options['lp_seconds']) or not 0 < options['lp_seconds'] <= 30:
        raise ValueError('bounded solver time')
    if type(sigmas) is not list or not 1 <= len(sigmas) <= 32:
        raise ValueError('bounded distinct price exponents')
    values = [rational(s) for s in sigmas]
    if len(set(values)) != len(values) or any(not 0 <= s <= 1 for s in values):
        raise ValueError('distinct rational exponents in[0,1]')
    return unpack(source['polynomial'], U, d)


class Algebra:
    def __init__(self, meter):
        self.m = meter; self.defects = {}; self.weights = {}; self.radical_weights = {}

    def weight(self, key):
        if key not in self.weights:
            self.weights[key] = prod(key)
            self.m.charge(4*len(key)+1)
        return self.weights[key]

    def defect(self, n):
        if n not in self.defects:
            divisors = []
            for a in range(1, isqrt(n)+1):
                if n % a == 0:
                    divisors.append(a)
                    if a*a != n: divisors.append(n//a)
            p = {}
            for d in divisors:
                for s, sign in ((d, 1), (d-1, -1)):
                    if not s: continue
                    key = () if s == 1 else (s,)
                    p[key] = p.get(key, 0)+sign
            self.defects[n] = {k: v for k, v in p.items() if v}
            self.m.charge(8*isqrt(n)+8*len(divisors))
        return self.defects[n]

    def column(self, key):
        n, q = key
        return {tuple(sorted(q+s)): v for s, v in self.defect(n).items()}

    def upper_weight(self, key, text):
        value = self.weight(key); cache_key = (value, text)
        if cache_key in self.radical_weights: return self.radical_weights[cache_key]
        exponent = rational(text); a, b = exponent.numerator, exponent.denominator
        bits = value.bit_length()*a+GRID.bit_length()*b
        if max(bits, value.bit_length()*b) > 100000:
            raise OverflowError('exact radical intermediate capacity')
        if a == 0: result = GRID
        elif a == b: result = value*GRID
        else:
            target = value**a*GRID**b
            if b == 2: result = isqrt(target)
            else:
                lo, hi = 0, 1 << ((target.bit_length()+b-1)//b)
                while hi-lo > 1:
                    mid = (lo+hi)//2
                    if mid**b <= target: lo = mid
                    else: hi = mid
                    self.m.charge(1+bits*max(1, b.bit_length()))
                result = lo
            if result**b < target: result += 1
        self.radical_weights[cache_key] = result
        self.m.charge(4+bits)
        return result

    def reserve(self, terms=0, columns=0):
        self.m.reserve(32*1024**2+512*(len(self.weights)+len(self.radical_weights)+terms)
                       +256*sum(len(p) for p in self.defects.values())+1024*columns)


def rank_spread(T, limit=16):
    size = max(0, T-1)
    if size <= limit: return list(range(2, T+1))
    return [2+i*(size-1)//(limit-1) for i in range(limit)]


def scout(poly, dual, T, degree, active, limit, algebra):
    """Feedback expands identities at current monomials, never at measured mu."""
    prospective = T+(2*degree+16)*len(poly)
    if prospective > MAX_TERMS:
        raise MemoryError('complete candidate-enumeration capacity')
    algebra.reserve(terms=prospective+len(poly), columns=len(active))
    seen, heap = set(active), []
    landmarks = rank_spread(T)
    considered, positive = 0, 0

    def visit(n, q):
        nonlocal considered, positive
        key = (n, q)
        if not 2 <= n <= T or key in seen: return
        seen.add(key); considered += 1
        col = algebra.column(key)
        dot = abs(sum(dual.get(s, 0)*a for s, a in col.items()))
        norm = sum(algebra.weight(s)*abs(a) for s, a in col.items())
        algebra.m.charge(12*len(col)+8)
        if not dot: return
        positive += 1
        # All ranking decisions are exact. Prefer a large dual defect per
        # weighted column mass, then large defect, short multiplier, low n.
        rank = (Q(dot, norm), dot, -len(q), -n, tuple(-i for i in q))
        item = (rank, key)
        if len(heap) < limit: heappush(heap, item)
        elif item > heap[0]: heapreplace(heap, item)

    for n in range(2, T+1): visit(n, ())
    for monomial in sorted(poly):
        for i in sorted(set(monomial)):
            q = list(monomial); q.remove(i); q = tuple(q)
            visit(i, q); visit(i+1, q)
        if len(monomial) < degree:
            for n in landmarks: visit(n, monomial)
    return [item[1] for item in sorted(heap, reverse=True)], dict(
        considered_candidates=considered, positive_dual_scores=positive,
        retained_candidates=len(heap), pool_limit=limit, pool_limited=positive > limit,
        candidate_rule='constant multipliers; current monomial quotients at index and successor; rank-spread relations times current lower-degree monomials')


def quantize(x, bound):
    if not isfinite(float(x)): raise ValueError('finite optimizer proposal')
    return max(-bound*GRID, min(bound*GRID, int(round(float(x)*GRID))))


def replay(poly, columns, primal, dual, box, den, algebra):
    residual = {k: GRID*v for k, v in poly.items()}
    for key, coefficient in zip(columns, primal):
        for k, a in algebra.column(key).items():
            residual[k] = residual.get(k, 0)+coefficient*a
    residual = {k: v for k, v in residual.items() if v}
    if len(residual) > MAX_TERMS: raise MemoryError('complete corrected-polynomial capacity')
    upper = Q(sum(abs(v)*algebra.weight(k) for k, v in residual.items()), GRID*den)
    defect = sum(abs(sum(dual.get(k, 0)*a for k, a in algebra.column(key).items())) for key in columns)
    lower = Q(sum(dual.get(k, 0)*v for k, v in poly.items())-box*defect, GRID*den)
    if lower > upper: raise ArithmeticError('exact boxed dual exceeds feasible primal')
    algebra.m.charge(16*(len(poly)+len(residual)+sum(len(algebra.column(k)) for k in columns)))
    return residual, upper, lower


def solve(poly, columns, box, den, algebra, seconds):
    expanded = [algebra.column(k) for k in columns]
    monomials = sorted(set(poly).union(*(set(c) for c in expanded)))
    if len(monomials) > MAX_TERMS: raise MemoryError('complete optimizer support capacity')
    algebra.reserve(terms=8*len(monomials)+4*sum(map(len, expanded)), columns=len(columns))
    indices = {k: i for i, k in enumerate(monomials)}
    rows, cols, values = [], [], []
    for j, column in enumerate(expanded):
        for k, v in column.items(): rows.append(indices[k]); cols.append(j); values.append(v)
    m, count = len(columns), len(monomials)
    A = coo_matrix((values, (rows, cols)), shape=(count, m), dtype=float).tocsr()
    identity = eye(count, format='csr')
    constraints = vstack([hstack([A, -identity]), hstack([-A, -identity])], format='csr')
    p = np.array([poly.get(k, 0) for k in monomials], dtype=float)
    weights = [algebra.weight(k) for k in monomials]
    scale = max(weights, default=1)
    objective = np.r_[np.zeros(m), np.array(weights, dtype=float)/float(scale)]
    with warnings.catch_warnings():
        warnings.filterwarnings('ignore', message='Unrecognized options detected:.*threads.*', category=OptimizeWarning)
        result = linprog(objective, A_ub=constraints, b_ub=np.r_[-p, p],
            bounds=[(-box, box)]*m+[(0, None)]*count, method='highs-ds', options={
                'presolve': True, 'time_limit': seconds, 'threads': 1,
                'dual_feasibility_tolerance': 1e-9, 'primal_feasibility_tolerance': 1e-9})
    iterations = max(0, int(getattr(result, 'nit', 0) or 0))
    algebra.m.charge(4*(iterations+1)*max(1, len(values)+count)*max(1, m))
    if result.success:
        primal = [quantize(v, box) for v in result.x[:m]]
        marginals = result.ineqlin.marginals
        dual = {k: quantize((-marginals[i]+marginals[count+i])*float(scale), weights[i])
                for i, k in enumerate(monomials)}
    else:
        primal = [0]*m; dual = {}
    residual, upper, lower = replay(poly, columns, primal, dual, box, den, algebra)
    return dict(columns=[dict(n=n, multiplier_indices=list(q)) for n, q in columns],
        lambda_numerators=primal, residual=pack(residual), dual=pack(dual), box=box,
        primal_upper=str(upper), boxed_lower=str(lower), gap=str(upper-lower),
        solver=dict(status='optimal_float_proposal' if result.success else 'failed_zero_fallback',
                    iterations=iterations, message=str(result.message)))


def conditional_prices(poly_scaled, degree, den, sigmas, algebra):
    result = []
    for sigma in sigmas:
        coefficients = [0]*(degree+1)
        for key, value in poly_scaled.items():
            coefficients[len(key)] += abs(value)*algebra.upper_weight(key, sigma)
        result.append(dict(sigma=sigma, coefficients=[str(Q(v, GRID*GRID*den)) for v in coefficients]))
    return result


def construct(source, constraint_radius=None, options=None, price_exponents=None, meter=None, algebra=None):
    options = dict(DEFAULT_OPTIONS) if options is None else dict(options)
    sigmas = list(DEFAULT_SIGMAS) if price_exponents is None else list(price_exponents)
    T = source.get('U') if constraint_radius is None else constraint_radius
    poly = validate(source, T, options, sigmas)
    meter = Meter(cap=300_000_000_000) if meter is None else meter
    algebra = Algebra(meter) if algebra is None else algebra
    if algebra.m is not meter: raise ValueError('one accounted algebra context')
    degree, den = source['degree'], source['denominator']
    baseline = Q(sum(abs(v)*algebra.weight(k) for k, v in poly.items()), den)
    box = 4*max(1, max(map(abs, poly.values()), default=0))
    if max(box.bit_length(), max((abs(v).bit_length() for v in poly.values()), default=0)) > 1000:
        raise OverflowError('native optimization coefficient range')
    rounds, columns = [], []
    current = dict(poly)
    dual = {k: (1 if v > 0 else -1)*algebra.weight(k)*GRID for k, v in poly.items()}
    for _ in range(options['rounds']):
        if not any(current) or len(columns) >= options['max_columns']: break
        candidates, search = scout(current, dual, T, degree, columns, options['pool_limit'], algebra)
        count = min(options['batch'], options['max_columns']-len(columns), len(candidates))
        if not count: break
        columns.extend(candidates[:count])
        row = solve(poly, columns, box, den, algebra, options['lp_seconds'])
        row['search'] = search; rounds.append(row)
        current = unpack(row['residual'], T, degree)
        dual = unpack(row['dual'], T, degree)
    candidates = [(baseline, 0, -1)]+[(Q(r['primal_upper']), sum(v != 0 for v in r['lambda_numerators']), i)
                                    for i, r in enumerate(rounds)]
    selected = min(candidates)[2]
    if selected == -1:
        chosen = {k: GRID*v for k, v in poly.items()}; used = []
    else:
        row = rounds[selected]; chosen = unpack(row['residual'], T, degree)
        used = sorted({c['n'] for c, v in zip(row['columns'], row['lambda_numerators']) if v})
    algebra.reserve(terms=len(poly)+len(chosen)+sum(len(r['residual'])+len(r['dual']) for r in rounds), columns=len(columns))
    return dict(schema=SCHEMA, input=source, constraint_radius=T, coefficient_grid=GRID,
        price_exponents=sigmas, options=options, baseline_unconditional_bound=str(baseline),
        rounds=rounds, selected_round=selected, selected_polynomial=pack(chosen),
        selected_conditional_prices=conditional_prices(chosen, degree, den, sigmas, algebra),
        used_constraints=used, full_divisor_system_used=used == list(range(2, T+1)),
        constant_only_selected=not any(chosen), scalar_fake=dict(
            source_value=str(Q(poly.get((), 0), den)),
            corrected_value=str(Q(chosen.get((), 0), GRID*den)),
            violated_used_constraints=[n for n in used if n % 2], actual_mobius_assignment=False),
        conditional_prefix_bounds_paid=False, uniform_head_bound_proved=False, RH_proved=False,
        learner_mobius_signs_accessed=False)
