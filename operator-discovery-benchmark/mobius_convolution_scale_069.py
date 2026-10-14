"""Learn support-annihilating convolution laws and retain their signed cost.

No Mobius signs or target values are queried. Scalar prefix premises remain
explicitly conditional; lowering the sign-query radius does not pay growth.
"""
from fractions import Fraction as Q
from math import prod, isqrt
import numpy as np

from mobius_floor_control_068 import Meter, parameters_checked, source

SCHEMA = 'mobius-convolution-scale-v1'
GRID = 1 << 20
MAX_N = 65536
MAX_R = 131072
MAX_DEGREE = 8
MAX_CELLS = 2_000_000
MAX_TERMS = 2_000_000
DEFAULT_REQUESTS = [[str(Q(1, k))]*k for k in range(2, MAX_DEGREE+1)] + [
    [str(Q(a)), str(1-Q(a))] for a in ('1/257', '1/17', '1/9', '1/5', '2/7', '3/11', '3/7')]
DEFAULT_PRICE_EXPONENTS = ['1/2', '3/5', '2/3', '3/4', '1']


def rational(text):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded rational text')
    value = Q(text)
    if str(value) != text or max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > 4096:
        raise ValueError('bounded canonical rational')
    return value


def root_floor(value, degree, meter):
    if degree == 1: return value
    if degree == 2: return isqrt(value)
    lo, hi = 0, 1 << ((value.bit_length()+degree-1)//degree)
    while hi-lo > 1:
        mid = (lo+hi)//2
        meter.charge(1+value.bit_length()*max(1, degree.bit_length()))
        if mid**degree <= value: lo = mid
        else: hi = mid
    return lo


def power(R, text, meter, upper_grid=False):
    if type(R) is not int or not 1 <= R <= MAX_CELLS:
        raise ValueError('bounded positive arithmetic argument')
    theta = rational(text)
    if not 0 <= theta <= 1: raise ValueError('power exponent in[0,1]')
    bits = R.bit_length()*theta.numerator+(GRID.bit_length()*theta.denominator if upper_grid else 0)
    if max(bits, theta.denominator*R.bit_length()) > 100000:
        raise OverflowError('integer-power intermediate capacity')
    target = R**theta.numerator*(GRID**theta.denominator if upper_grid else 1)
    answer = root_floor(target, theta.denominator, meter)
    if upper_grid and answer**theta.denominator < target: answer += 1
    meter.charge(4+max(1, bits))
    return answer


def validate_requests(requests, sigmas):
    if type(requests) is not list or not 1 <= len(requests) <= 64:
        raise ValueError('bounded nonempty support programs')
    seen = set()
    for request in requests:
        if type(request) is not list or not 2 <= len(request) <= MAX_DEGREE:
            raise ValueError('degree2..8 support program')
        values = [rational(s) for s in request]
        if values != sorted(values) or any(not 0 <= x < 1 for x in values) or sum(values) < 1:
            raise ValueError('canonical ordered strict lower-scale exponents with total>=1')
        key = tuple(request)
        if key in seen: raise ValueError('distinct support programs')
        seen.add(key)
    if type(sigmas) is not list or not 1 <= len(sigmas) <= 32:
        raise ValueError('bounded conditional exponent requests')
    values = [rational(s) for s in sigmas]
    if len(set(values)) != len(values) or any(not 0 <= x <= 1 for x in values):
        raise ValueError('distinct conditional exponents in[0,1]')


def affine_solve(equations, variables, meter):
    """Generic sparse rational elimination; no expected law is supplied."""
    pivots = {}
    for coefficients, rhs in equations:
        row = {k: Q(v) for k, v in coefficients.items() if v}; rhs = Q(rhs)
        for col in sorted(pivots):
            if col not in row: continue
            old, value = pivots[col]; multiple = row[col]
            for j, v in old.items():
                row[j] = row.get(j, Q(0))-multiple*v
                if not row[j]: del row[j]
            rhs -= multiple*value
            meter.charge(8*len(old)+4)
        if not row:
            if rhs: raise ValueError('inconsistent coefficient synthesis')
            continue
        pivot = min(row); scale = row[pivot]
        pivots[pivot] = ({j: v/scale for j, v in row.items()}, rhs/scale)
        meter.charge(8*len(row))
    if len(pivots) != variables:
        raise ValueError('declared synthesis has unresolved free coefficients')
    answer = [Q(0)]*variables
    for col in sorted(pivots, reverse=True):
        row, rhs = pivots[col]
        answer[col] = rhs-sum((value*answer[j] for j, value in row.items() if j != col), Q(0))
        meter.charge(8*len(row))
    return answer, len(pivots)


def learn_annihilator(degree, meter):
    if type(degree) is not int or not 2 <= degree <= MAX_DEGREE:
        raise ValueError('bounded support-annihilator degree')
    count = 1 << degree
    equations = [({0: 1}, 1)]
    for i in range(degree):
        for mask in range(count):
            if not mask & (1 << i):
                equations.append(({mask: 1, mask | (1 << i): 1}, 0))
    coefficients, rank = affine_solve(equations, count, meter)
    if any(c.denominator != 1 for c in coefficients):
        raise ArithmeticError('integer normalized face-annihilating solution')
    return dict(degree=degree, coefficients=[c.numerator for c in coefficients], system_rank=rank)


def kernel_levels(k, degree, meter):
    """Transpose divisor summation; complete original support at every level."""
    R = len(k)-1; amplitude = max(map(abs, k), default=0)
    envelope = amplitude*R*(1+R.bit_length())**max(0, degree-2)
    if envelope*(1 << degree) >= 2**63:
        raise OverflowError('proved int64 divisor/tensor envelope capacity')
    meter.reserve(32*1024**2+16*(degree+1)*(R+1))
    levels = [None, np.array(k, dtype=np.int64)]
    for _ in range(2, degree+1):
        old = levels[-1]; new = np.zeros(R+1, dtype=np.int64)
        for v in range(1, R+1): new[v] = old[v::v].sum(dtype=np.int64)
        meter.charge(8*R*(1+R.bit_length()))
        levels.append(new)
    return levels


def prefix_polynomial(k, direct, cutoffs, law, levels, meter):
    R, degree = len(k)-1, len(cutoffs)
    if law['degree'] != degree or prod(u+1 for u in cutoffs) <= R:
        raise ValueError('matched learned law and exact support gate')
    if prod(cutoffs) > MAX_CELLS:
        raise MemoryError('complete tensor rectangle capacity')
    # Equal short factors coalesce before materializing tensors.
    factors = {}
    for mask, value in enumerate(law['coefficients']):
        if not mask: continue
        bounds = tuple(cutoffs[i] for i in range(degree) if mask & (1 << i))
        factors[bounds] = factors.get(bounds, 0)-value
    polynomial = {(): direct}
    for bounds, coefficient in factors.items():
        if not coefficient: continue
        m, cells = len(bounds), prod(bounds)
        meter.reserve(32*1024**2+256*cells+512*len(polynomial))
        index = np.ones(bounds, dtype=np.int64)
        for axis, u in enumerate(bounds):
            shape = [1]*m; shape[axis] = u
            index *= np.arange(1, u+1, dtype=np.int64).reshape(shape)
        tensor = levels[m][np.minimum(index, R)].copy()
        tensor[index > R] = 0
        for axis in range(m):
            shifted = np.zeros_like(tensor)
            take, put = [slice(None)]*m, [slice(None)]*m
            take[axis], put[axis] = slice(1, None), slice(None, -1)
            shifted[tuple(put)] = tensor[tuple(take)]
            tensor -= shifted
        for position in np.argwhere(tensor != 0):
            at = tuple(int(a) for a in position)
            monomial = tuple(sorted(a+1 for a in at if a >= 1))
            polynomial[monomial] = polynomial.get(monomial, 0)+coefficient*int(tensor[at])
        meter.charge(32*(m+1)*cells)
        if len(polynomial) > MAX_TERMS: raise MemoryError('complete signed polynomial capacity')
    return {key: value for key, value in polynomial.items() if value}


def conditional_prices(polynomial, degree, den, sigmas, weights, meter):
    answers = []
    for sigma in sigmas:
        numerators = [0]*(degree+1)
        for monomial, value in polynomial.items():
            d = len(monomial)
            if not d: numerators[0] += abs(value)*GRID; continue
            argument = prod(monomial); key = (argument, sigma)
            if key not in weights: weights[key] = power(argument, sigma, meter, upper_grid=True)
            numerators[d] += abs(value)*weights[key]
            meter.charge(8+4*d)
        answers.append(dict(sigma=sigma, coefficients=[str(Q(v, GRID*den)) for v in numerators]))
    return answers


def construct(N, y, max_j, parameters, requests=None, price_exponents=None, meter=None):
    meter = Meter(cap=300_000_000_000) if meter is None else meter
    requests = [list(v) for v in DEFAULT_REQUESTS] if requests is None else requests
    sigmas = list(DEFAULT_PRICE_EXPONENTS) if price_exponents is None else price_exponents
    if any(type(v) is not int for v in (N, y, max_j)) or not 2 <= N <= MAX_N:
        raise ValueError('bounded integer source')
    p, q = parameters_checked(parameters, meter); D = 4*N//p
    if not 1 <= y <= D or not 0 <= max_j <= min(D, 4096):
        raise ValueError('complete source row range')
    validate_requests(requests, sigmas)
    laws = [learn_annihilator(k, meter) for k in sorted({len(v) for v in requests})]
    by_degree = {law['degree']: law for law in laws}
    powers, weights = {}, {}
    retained_terms = 0
    endpoints = []
    for ratio in (Q(p, q), Q(1)):
        den = ratio.denominator; g, floors, _ = source(N, y, p, q, ratio, meter)
        rows = []
        for j in range(1, max_j+1):
            R = D//j
            k = [0]+[g[j*n]-(g[(j+1)*n] if (j+1)*n <= D else 0) for n in range(1, R+1)]
            direct = floors.get(j, 0)
            levels = kernel_levels(k, max(by_degree), meter)
            models, plans, cache = [], [], {}
            for exponents in requests:
                cutoffs = []
                for exponent in exponents:
                    key = (R, exponent)
                    if key not in powers: powers[key] = power(R, exponent, meter)
                    cutoffs.append(powers[key])
                key = tuple(cutoffs); degree = len(cutoffs)
                if prod(u+1 for u in cutoffs) <= R or (R > 1 and max(cutoffs) >= R):
                    raise ArithmeticError('exact strict smaller-scale support gate')
                if key not in cache:
                    cache[key] = len(models)
                    polynomial = prefix_polynomial(k, direct, cutoffs, by_degree[degree], levels, meter)
                    constant = polynomial.get((), 0)
                    retained_terms += len(polynomial)+1
                    if retained_terms > MAX_TERMS: raise MemoryError('retained complete polynomial capacity')
                    meter.reserve(32*1024**2+512*(retained_terms+len(weights))+256*prod(cutoffs)
                                  +16*(max(by_degree)+1)*(R+1))
                    models.append(dict(degree=degree, cutoffs=cutoffs,
                        support_min=prod(u+1 for u in cutoffs), mu_query_radius=max(cutoffs),
                        constant_scaled=constant,
                        terms=[dict(indices=list(key), coefficient_scaled=value)
                               for key, value in sorted(polynomial.items()) if key],
                        conditional_prices=conditional_prices(polynomial, degree, den, sigmas, weights, meter),
                        scalar_box_witness=dict(prefix_values='M(1)=1,M(s)=0 for s>=2',
                            value=str(Q(constant, den)), actual_mobius_assignment=False)))
                plans.append(dict(exponents=exponents, cutoffs=cutoffs, model_index=cache[key]))
            best = min(range(len(models)), key=lambda i: (
                sum(map(Q, models[i]['conditional_prices'][0]['coefficients'])),
                models[i]['mu_query_radius'], len(models[i]['terms']), i))
            rows.append(dict(j=j, R=R, direct_scaled=direct, unit_kernel_scaled=k[1],
                models=models, plans=plans, selected_model=best))
        endpoints.append(dict(ratio=str(ratio), denominator=den, rows=rows))
    return dict(schema=SCHEMA, N=N, y=y, max_j=max_j, parameters=parameters,
        requests=requests, price_exponents=sigmas, coefficient_grid=GRID, annihilators=laws,
        endpoints=endpoints, universal_convolution_identity_proved=True,
        smaller_mu_query_radius_verified=True, conditional_prefix_bounds_paid=False,
        uniform_head_bound_proved=False, RH_proved=False)
