"""Exact scale-dependent rational twists and generated signed moment mixtures.

These are coefficient primitives. No source arrays, norms or frozen compiler
are read. All range claims distinguish the raw profile from its rounding.
"""
from fractions import Fraction as Q
import math
import time

MAX_TERMS = 8
MAX_RATIONAL_BITS = 4096
MAX_POWER_BITS = 400_000
MAX_INTEGER_BITS = 4096


class Meter:
    def __init__(self, cap=200_000_000, seconds=600):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer work cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite time cap')
        self.cap, self.operations, self.deadline = cap, 0, time.monotonic()+seconds
        self.root_comparisons = self.ceil_comparisons = self.rational_operations = self.root_cache_hits = 0
        self.max_power_bits = self.total_power_bit_estimates = 0

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('drift work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('drift deadline')

    def power(self, bits):
        if bits > MAX_POWER_BITS:
            raise OverflowError('prospective exact power bit cap')
        self.max_power_bits = max(self.max_power_bits, bits)
        self.total_power_bit_estimates += bits
        self.charge(max(1, bits))

    def rational(self, value):
        _bounded(value)
        self.rational_operations += 1
        self.charge(1+abs(value.numerator).bit_length()+value.denominator.bit_length())
        return value

    def counts(self):
        return {name: getattr(self, name) for name in ('operations', 'root_comparisons',
                'ceil_comparisons', 'rational_operations', 'root_cache_hits', 'max_power_bits', 'total_power_bit_estimates')}


def _meter(meter):
    return meter if meter is not None else Meter()


def _bounded(value):
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_RATIONAL_BITS:
        raise OverflowError('rational coefficient bit cap')
    return value


def rational(text):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational string')
    value = Q(text)
    if str(value) != text:
        raise ValueError('canonical rational string')
    return _bounded(value)


def _integer(n, lower=1):
    if type(n) is not int or n < lower or n.bit_length() > MAX_INTEGER_BITS:
        raise ValueError('positive integer within implementation bit cap')
    return n


def _drift(a, theta):
    a, theta = rational(a), rational(theta)
    if a <= 0 or not 0 < theta < 1:
        raise ValueError('drift a>0 and0<theta<1')
    return a, theta


def beta_certificate(a, theta, N, meter=None):
    """Exact ceiling comparison; never approximate a rational power."""
    meter = _meter(meter)
    aq, tq = _drift(a, theta)
    _integer(N, 2)
    L, u, v = N.bit_length(), tq.numerator, tq.denominator
    # theta<1 gives a*L^theta <= a*L, an exact initial upper bound.
    hi = (aq.numerator*L+aq.denominator-1)//aq.denominator
    estimate = max(v*max(hi.bit_length(), aq.denominator.bit_length())+v*aq.denominator.bit_length(),
                   v*aq.numerator.bit_length()+u*L.bit_length())+4
    meter.power(estimate)
    rhs = pow(aq.numerator, v)*pow(L, u)
    factor = pow(aq.denominator, v)
    lo = 0
    while lo+1 < hi:
        mid = (lo+hi)//2
        meter.ceil_comparisons += 1
        meter.charge(max(1, estimate*(1+v.bit_length())//32))
        if pow(mid, v)*factor >= rhs:
            hi = mid
        else:
            lo = mid
    z = hi
    if not pow(z-1, v)*factor < rhs <= pow(z, v)*factor:
        raise ArithmeticError('exact ceiling witness failed')
    meter.ceil_comparisons += 2
    meter.charge(2*max(1, estimate*(1+v.bit_length())//32))
    return {'schema': 'floor-drift-beta-v1', 'a': a, 'theta': theta, 'N': N,
            'L': L, 'ceiling': str(z), 'beta': str(_bounded(Q(z, L))),
            'comparison': {'theta_numerator': str(u), 'theta_denominator': str(v),
                           'a_numerator': str(aq.numerator), 'a_denominator': str(aq.denominator),
                           'lower_is_strict': True, 'upper_is_nonstrict': True},
            'power_bit_estimate': estimate}


def beta(a, theta, N, meter=None):
    return Q(beta_certificate(a, theta, N, meter)['beta'])


def _spec(spec):
    if type(spec) is not dict or set(spec) != {'kind', 'a', 'theta', 'terms'} or spec['kind'] != 'drift_mixture':
        raise ValueError('exact drift mixture grammar')
    aq, tq = _drift(spec['a'], spec['theta'])
    if type(spec['terms']) is not list or not 1 <= len(spec['terms']) <= MAX_TERMS:
        raise ValueError('mixture1..8 terms')
    rates, weights, previous = [], [], Q(0)
    for term in spec['terms']:
        if type(term) is not dict or set(term) != {'rate', 'weight'}:
            raise ValueError('exact mixture term')
        r, w = rational(term['rate']), rational(term['weight'])
        if r <= previous or not w:
            raise ValueError('sorted distinct positive rates and nonzero signed weights')
        rates.append(r)
        weights.append(w)
        previous = r
    if _bounded(sum(weights)) != 1:
        raise ValueError('mixture unit normalization sumweights=1')
    return aq, tq, rates, weights


def synthesize_mixture(rates, a='1', theta='1/2', meter=None):
    """Solve the full moment system from any admitted distinct positive rates."""
    meter = _meter(meter)
    _drift(a, theta)
    if type(rates) is not list or not 1 <= len(rates) <= MAX_TERMS:
        raise ValueError('input rate set1..8')
    rr = sorted(rational(r) for r in rates)
    if rr[0] <= 0 or len(set(rr)) != len(rr):
        raise ValueError('distinct positive input rates')
    s = len(rr)
    matrix = [[meter.rational(r**k) for r in rr]+[Q(int(k == 0))] for k in range(s)]
    # Exact Gaussian elimination, not a fixed binomial or interpolation bank.
    for col in range(s):
        pivot = next((j for j in range(col, s) if matrix[j][col]), None)
        if pivot is None:
            raise ArithmeticError('distinct-rate Vandermonde unexpectedly singular')
        matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        divisor = matrix[col][col]
        matrix[col] = [meter.rational(x/divisor) for x in matrix[col]]
        for row in range(s):
            if row == col:
                continue
            multiplier = matrix[row][col]
            matrix[row] = [meter.rational(x-multiplier*y) for x, y in zip(matrix[row], matrix[col])]
    spec = {'kind': 'drift_mixture', 'a': a, 'theta': theta,
            'terms': [{'rate': str(r), 'weight': str(matrix[j][-1])} for j, r in enumerate(rr)]}
    _spec(spec)
    cert = mixture_certificate(spec, meter)
    if cert['order'] != s:
        raise ArithmeticError('generated moment order failed')
    return spec


def _poly_mul(a, b, meter):
    c = [Q(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] = meter.rational(c[i+j]+x*y)
    return c


def kernel_certificate(spec, meter=None):
    """Check the distinct-positive exponential-convolution identity exactly."""
    meter = _meter(meter)
    _, _, rates, weights = _spec(spec)
    denominator = [Q(1)]
    for r in rates:
        denominator = _poly_mul(denominator, [r, Q(1)], meter)
    numerator, summands = [Q(0)]*len(rates), []
    for i, (r, w) in enumerate(zip(rates, weights)):
        p = [w*r]
        for j, other in enumerate(rates):
            if i != j:
                p = _poly_mul(p, [other, Q(1)], meter)
        numerator = [meter.rational(x+y) for x, y in zip(numerator, p)]
        summands.append([str(x) for x in p])
    product = meter.rational(math.prod(rates))
    expected = [product]+[Q(0)]*(len(rates)-1)
    certified = numerator == expected
    return {'schema': 'floor-drift-exponential-kernel-v1',
            'status': 'certified' if certified else 'NOT_CERTIFIED',
            'denominator_polynomial_ascending': [str(x) for x in denominator],
            'numerator_summands_ascending': summands,
            'numerator_polynomial_ascending': [str(x) for x in numerator],
            'expected_numerator_ascending': [str(x) for x in expected],
            'rate_product': str(product), 'kernel_order': len(rates),
            'identity': 'sum_j w_j*r_j/(s+r_j)=product_j r_j/(s+r_j)',
            'raw_range': ['0', '1'] if certified else None,
            'raw_simplex_bound': '0<=1-P(u)<=product(r)*u^order/order!' if certified else None,
            'rounded_range_proved': False}


def mixture_certificate(spec, meter=None):
    meter = _meter(meter)
    aq, tq, rates, weights = _spec(spec)
    moments = [meter.rational(sum(w*r**k for w, r in zip(weights, rates))) for k in range(len(rates)+1)]
    m = next((k for k in range(1, len(moments)) if moments[k]), None)
    if m is None:
        raise ArithmeticError('unit-normalized distinct positive mixture has no first moment')
    abs_weights = meter.rational(sum(abs(w) for w in weights))
    abs_moment = meter.rational(sum(abs(w)*r**m for w, r in zip(weights, rates)))
    # Coefficient of log(n)^m L^(-m*(1-theta)) in 1-P(n,N).
    leading = meter.rational(Q((-1)**(m+1), math.factorial(m))*moments[m]*aq**m)
    rate = meter.rational(m*(1-tq))
    return {'schema': 'floor-drift-mixture-certificate-v1', 'spec': spec,
            'order': m, 'moments': [{'k': k, 'value': str(v)} for k, v in enumerate(moments)],
            'vanishing_orders': list(range(1, m)), 'leading_moment': str(moments[m]),
            'sum_abs_weights': str(abs_weights), 'weighted_abs_order_moment': str(abs_moment),
            'leading_error_coefficient': {'rational': str(leading), 'log_n_power': str(m)},
            'coefficient_rate': str(rate), 'energy_rate': str(2*rate),
            'local_expansion': '1-P(n,N)=leading_rational*log(n)^order*L^(-coefficient_rate)+o(L^(-coefficient_rate)), fixed n>=2',
            'beta_asymptotic': 'beta_N/(a*L^(theta-1))->1; beta_N->0; beta_N*log(N)->infinity',
            'rounding_policy': 'p=4*ceil(log2(N)); each n^(-rate*beta) rounded down independently',
            'rounding_error': 'abs(P_exact-P_rounded)<=2^(-p)*sum_abs_weights',
            'taylor_bound': 'abs(1-P_exact)<=u^order/order!*weighted_abs_order_moment, u=beta_N*log(n)>=0',
            'kernel_certificate': kernel_certificate(spec, meter),
            'coefficient_control_only': True, 'whole_signed_norm_proved': False,
            'uniform_forcing_bound_proved': False, 'norm_convergence_proved': False,
            'RH_proved': False, 'RH_refuted': False, 'additional_norms_evaluated': False,
            'source_arrays_read': False, 'counts': meter.counts()}


def _root_floor_inverse_integer(n, exponent, bits, meter):
    """Exact floor(2^bits*n^(-exponent))/2^bits, exponent rational>0."""
    u, v = exponent.numerator, exponent.denominator
    estimate = bits*v+u*n.bit_length()+4
    meter.power(estimate)
    D = 1 << bits
    if n == 1:
        return Q(1), estimate
    factor, rhs = pow(n, u), 1 << (bits*v)
    lo, hi = 0, D
    while lo+1 < hi:
        mid = (lo+hi)//2
        meter.root_comparisons += 1
        meter.charge(max(1, estimate*(1+v.bit_length())//32))
        if pow(mid, v)*factor <= rhs:
            lo = mid
        else:
            hi = mid
    return Q(lo, D), estimate


def _compile_prepared(spec, n, N, rates, weights, bc, meter, atom_cache=None):
    _integer(n)
    betaq, p = Q(bc['beta']), 4*(N-1).bit_length()
    rows, value = [], Q(0)
    for rate, weight in zip(rates, weights):
        exponent = _bounded(rate*betaq)
        key = (n, p, exponent.numerator, exponent.denominator)
        if atom_cache is not None and key in atom_cache:
            rounded, estimate = atom_cache[key]
            meter.root_cache_hits += 1
            meter.charge(1)
        else:
            rounded, estimate = _root_floor_inverse_integer(n, exponent, p, meter)
            if atom_cache is not None:
                atom_cache[key] = (rounded, estimate)
        value = meter.rational(value+weight*rounded)
        rows.append({'rate': str(rate), 'weight': str(weight), 'exponent': str(exponent),
                     'rounded_value': str(rounded), 'power_bit_estimate': estimate})
    rounding = meter.rational(sum(abs(w) for w in weights)/2**p)
    return {'schema': 'floor-drift-compilation-v1', 'spec': spec, 'n': n, 'N': N,
            'beta_certificate': bc, 'precision_bits': p, 'terms': rows, 'value': str(value),
            'rounding_error_bound': str(rounding), 'signs_retained': True,
            'exact_rounded_range_claim': None, 'counts': meter.counts()}


class CompilationContext:
    """One parsed spec and one beta per N, with explicitly owned per-n cache."""
    def __init__(self, spec, N, meter=None, _atom_cache=None):
        self.meter = _meter(meter)
        _, _, self.rates, self.weights = _spec(spec)
        self.spec = {'kind': 'drift_mixture', 'a': spec['a'], 'theta': spec['theta'],
                     'terms': [{'rate': str(r), 'weight': str(w)} for r, w in zip(self.rates, self.weights)]}
        self.N = _integer(N, 2)
        self.beta_certificate = beta_certificate(self.spec['a'], self.spec['theta'], N, self.meter)
        self._atom_cache = _atom_cache
        self.cache = {}

    def compile(self, n):
        _integer(n)
        if n not in self.cache:
            self.cache[n] = _compile_prepared(self.spec, n, self.N, self.rates, self.weights,
                                              self.beta_certificate, self.meter, self._atom_cache)
        return self.cache[n]

    def value(self, n):
        return Q(self.compile(n)['value'])

    def profile(self):
        if self.N > 1_048_576:
            raise OverflowError('explicit profile allocation cap')
        return tuple(self.value(n) for n in range(2, self.N+1))


class DriftCompiler:
    """Exact tuple-key context cache; no file hashes or source observations."""
    def __init__(self, meter=None):
        self.meter, self.contexts, self.atom_cache = _meter(meter), {}, {}

    def context(self, spec, N):
        # Validate before constructing a key, including exact unit normalization.
        _spec(spec)
        _integer(N, 2)
        key = (spec['a'], spec['theta'], tuple((t['rate'], t['weight']) for t in spec['terms']), N)
        if key not in self.contexts:
            self.contexts[key] = CompilationContext(spec, N, self.meter, self.atom_cache)
        return self.contexts[key]

    def profile(self, spec, N):
        return self.context(spec, N).profile()


def compile_mixture(spec, n, N, meter=None):
    return CompilationContext(spec, N, meter).compile(n)


compilation_certificate = compile_mixture


def mixture_value(spec, n, N, meter=None):
    return Q(compile_mixture(spec, n, N, meter)['value'])


def coefficient_error_bound(spec, n, N, meter=None):
    """All-positive-integer-n scalar bound; never a floor norm bound."""
    meter = _meter(meter)
    _integer(n)
    _integer(N, 2)
    cert = mixture_certificate(spec, meter)
    bc = beta_certificate(spec['a'], spec['theta'], N, meter)
    m, p = cert['order'], 4*(N-1).bit_length()
    log_upper = (n-1).bit_length()  # ln(n)<=ceil(log2(n)), including n=1.
    u = meter.rational(Q(bc['beta'])*log_upper)
    taylor = meter.rational(u**m*Q(cert['weighted_abs_order_moment'])/math.factorial(m))
    kernel = cert['kernel_certificate']
    simplex = meter.rational(u**m*Q(kernel['rate_product'])/math.factorial(m)) if kernel['status'] == 'certified' else None
    rounding = meter.rational(Q(cert['sum_abs_weights'])/2**p) if n != 1 else Q(0)
    raw_bound = min(taylor, simplex, Q(1)) if simplex is not None else taylor
    return {'schema': 'floor-drift-coefficient-bound-v1', 'spec': spec, 'n': n, 'N': N,
            'beta_certificate': bc, 'precision_bits': p, 'order': m,
            'log_upper_bound': str(log_upper), 'u_upper_bound': str(u),
            'taylor_error_bound': str(taylor), 'simplex_error_bound': None if simplex is None else str(simplex),
            'raw_error_bound': str(raw_bound),
            'rounding_error_bound': str(rounding), 'total_error_bound': str(meter.rational(raw_bound+rounding)),
            'bound': 'abs(1-P_rounded(n,N))<=total_error_bound',
            'coefficient_control_only': True, 'whole_signed_norm_proved': False,
            'uniform_forcing_bound_proved': False, 'norm_convergence_proved': False,
            'RH_proved': False, 'RH_refuted': False, 'counts': meter.counts()}
