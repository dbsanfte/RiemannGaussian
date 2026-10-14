"""Finite signed middle bands of the actual ordinary-mu E_R source.

No scientific values are evaluated at import. Gamma primitives are Arb
interval computations; this is finite evidence, never an all-scale bound.
"""
from fractions import Fraction as Q
import math
import time
from flint import arb, ctx

MAX_N = 32768
MAX_PRIMES = 8
MAX_PRODUCT = 1_000_000
MAX_TERMS = 2_000_000
MAX_PARAMETER_BITS = 4096
MAX_POWER_BITS = 400_000
MAX_ENDPOINT_BITS = 16384
OUTPUT_DYADIC_BITS = 80
MAX_CACHE_BYTES = 1024**3
MAX_WORKING_BYTES = 4*1024**3
PRECISIONS = (128, 192, 256, 384, 512)
COEFFICIENTS = (2, -3, 1)


class Meter:
    def __init__(self, cap=100_000_000_000, seconds=7200):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative work cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite deadline')
        self.cap, self.operations = cap, 0
        self.deadline = time.monotonic()+seconds
        self.peak_bytes_estimate = 0
        self.primitives = {name: 0 for name in ('prime_trial_divisions', 'mu_sieve_entries',
            'exact_power_bits', 'integer_weight_entries', 'exponential_terms',
            'log_atoms', 'power_atoms', 'gamma_upper_atoms', 'signed_sum_terms', 'cache_hits')}

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('middle-source work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('middle-source deadline')

    def reserve(self, amount):
        if type(amount) is not int or not 0 <= amount <= MAX_WORKING_BYTES:
            raise MemoryError('middle-source prospective working memory cap')
        self.peak_bytes_estimate = max(self.peak_bytes_estimate, amount)
        self.charge()

    def counts(self):
        return {'operations': self.operations, 'peak_bytes_estimate': self.peak_bytes_estimate,
                'total_primitive_counts': dict(self.primitives)}


def _meter(meter):
    return Meter() if meter is None else meter


def _q(text):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational string')
    try:
        value = Q(text)
    except (ValueError, ZeroDivisionError):
        raise ValueError('canonical rational string') from None
    if str(value) != text:
        raise ValueError('canonical rational string')
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_PARAMETER_BITS:
        raise OverflowError('rational parameter bit cap')
    return value


def _prime(p, meter):
    if type(p) is not int or not 2 <= p <= MAX_PRODUCT:
        raise ValueError('bounded actual prime')
    for d in range(2, math.isqrt(p)+1):
        meter.primitives['prime_trial_divisions'] += 1
        meter.charge(4)
        if p % d == 0:
            raise ValueError('actual prime required')
    return p


def _request(request, meter):
    if type(request) is not dict or set(request) != {
            'alpha', 'primes', 'N', 'gamma', 'lower_fraction', 'upper_fraction'}:
        raise ValueError('exact six-field middle request')
    alpha, gamma = _q(request['alpha']), _q(request['gamma'])
    lower, upper = _q(request['lower_fraction']), _q(request['upper_fraction'])
    if not 0 < alpha < 1 or gamma <= 0 or not 0 <= lower <= upper <= 1:
        raise ValueError('alpha/gamma/ordered band fractions domain')
    N, primes = request['N'], request['primes']
    if type(N) is not int or not 2 <= N <= MAX_N:
        raise ValueError('finite integer source support domain')
    if type(primes) is not list or len(primes) > MAX_PRIMES:
        raise ValueError('bounded canonical prime list')
    checked = tuple(_prime(p, meter) for p in primes)
    if list(sorted(set(checked))) != primes:
        raise ValueError('sorted distinct actual primes')
    if math.prod(checked) > MAX_PRODUCT:
        raise OverflowError('prime product resource cap')
    meter.charge(32+sum(abs(v.numerator).bit_length()+v.denominator.bit_length()
                        for v in (alpha, gamma, lower, upper)))
    return alpha, checked, N, gamma, lower, upper


def _aq(value):
    return arb(value.numerator)/value.denominator


def _integer_text(value):
    """Bounded local decimal formatting; no global Python guard changes."""
    if type(value) is not int or abs(value).bit_length() > MAX_ENDPOINT_BITS:
        raise OverflowError('endpoint integer bit cap')
    sign = '-' if value < 0 else ''
    value = abs(value)
    chunks = []
    while value >= 10**9:
        value, remainder = divmod(value, 10**9)
        chunks.append(remainder)
    return sign+str(value)+''.join(str(part).zfill(9) for part in reversed(chunks))


def _fraction_text(value):
    if value.denominator == 1:
        return _integer_text(value.numerator)
    return _integer_text(value.numerator)+'/'+_integer_text(value.denominator)


def _endpoint(value, meter, round_up=False):
    if not value.is_finite():
        raise ArithmeticError('nonfinite Arb enclosure')
    mantissa, exponent = value.man_exp()
    mantissa, exponent = int(mantissa), int(exponent)
    shift = exponent+OUTPUT_DYADIC_BITS
    estimated = abs(mantissa).bit_length()+max(0, shift)
    if estimated > MAX_ENDPOINT_BITS:
        raise OverflowError('exact dyadic endpoint bit cap')
    meter.charge(1+estimated)
    if shift >= 0:
        numerator = mantissa << shift
    else:
        numerator = -((-mantissa) >> -shift) if round_up else mantissa >> -shift
    exact = Q(numerator, 1 << OUTPUT_DYADIC_BITS)
    return _fraction_text(exact)


def _interval(value, meter):
    return {'lower': _endpoint(value.lower(), meter), 'upper': _endpoint(value.upper(), meter, True)}


def _delta(before, after):
    return {'operations': after['operations']-before['operations'],
            'peak_bytes_estimate': after['peak_bytes_estimate'],
            'total_primitive_counts': {k: after['total_primitive_counts'][k]-before['total_primitive_counts'][k]
                                      for k in after['total_primitive_counts']}}


class Context:
    def __init__(self, max_bytes=MAX_CACHE_BYTES):
        if type(max_bytes) is not int or not 0 <= max_bytes <= MAX_CACHE_BYTES:
            raise ValueError('bounded context cache bytes')
        self.max_bytes, self.bytes_estimate = max_bytes, 0
        self.kernels, self.logs, self.powers, self.endpoints, self.gamma_atoms = {}, {}, {}, {}, {}

    def get(self, table, key, meter):
        if key in table:
            meter.primitives['cache_hits'] += 1
            meter.charge()
            return table[key]
        return None

    def store(self, table, key, value, size, meter):
        meter.reserve(self.bytes_estimate+size)
        if size <= self.max_bytes-self.bytes_estimate:
            table[key] = value
            self.bytes_estimate += size
        return value


def prepare_context(meter=None, max_bytes=MAX_CACHE_BYTES):
    meter = _meter(meter)
    meter.reserve(1024)
    return Context(max_bytes)


def _compile(primes, N, context, meter):
    key = (primes, N)
    cached = context.get(context.kernels, key, meter)
    if cached is not None:
        return cached
    X, R = 4*N, math.prod(primes)
    meter.reserve(context.bytes_estimate+64*(X+1)+(1 << len(primes))*X*96)
    mu = [1]*(X+1)
    mu[0] = 0
    prime = [True]*(X+1)
    prime[0] = prime[1] = False
    for p in range(2, X+1):
        if prime[p]:
            for d in range(p, X+1, p):
                mu[d] = -mu[d]
                if d != p:
                    prime[d] = False
                meter.primitives['mu_sieve_entries'] += 1
                meter.charge(4)
            for d in range(p*p, X+1, p*p):
                mu[d] = 0
                meter.primitives['mu_sieve_entries'] += 1
                meter.charge(3)
    subsets = [(1, 1)]
    for p in primes:
        subsets += [(e*p, -sign) for e, sign in subsets]
        meter.charge(4*len(subsets))
    rows = []
    for d in range(1, X+1):
        weight = mu[d]*(2*(N//d)-3*((2*N)//d)+(X//d))
        meter.primitives['integer_weight_entries'] += 1
        meter.charge(8+d.bit_length())
        if weight and math.gcd(d, R) == 1:
            rows.extend((d*e, weight*sign) for e, sign in subsets)
            meter.primitives['exponential_terms'] += len(subsets)
            meter.charge(4*len(subsets))
            if len(rows) > MAX_TERMS:
                raise OverflowError('finite exponential term cap')
    rows.sort()
    if any(base <= 1 for base, _ in rows) or len({base for base, _ in rows}) != len(rows):
        raise ArithmeticError('unique nonunit Euler cofactor decomposition')
    if sum(weight for _, weight in rows) != 0:
        raise ArithmeticError('signed unit/constant coefficient cancellation')
    result = tuple(rows)
    return context.store(context.kernels, key, result, 1024+128*len(rows), meter)


def _epsilon(N, gamma, precision, context, meter):
    key = ('epsilon', N, gamma, precision)
    cached = context.get(context.endpoints, key, meter)
    if cached is not None:
        return cached
    estimate = max(N.bit_length()*gamma.numerator, gamma.denominator+1)
    if estimate > MAX_POWER_BITS:
        raise OverflowError('exact endpoint comparison power bit cap')
    meter.primitives['exact_power_bits'] += estimate
    meter.charge(estimate+N.bit_length()*gamma.numerator.bit_length())
    at_half = pow(N, gamma.numerator) <= (1 << gamma.denominator)
    value = arb(1)/2 if at_half else (-_aq(gamma)*arb(N).log()).exp()
    if not value.is_finite() or not value > 0:
        raise ArithmeticError('strictly positive endpoint enclosure')
    return context.store(context.endpoints, key, (value, at_half), 512+precision//4, meter)


def _log(base, precision, context, meter):
    key = (base, precision)
    cached = context.get(context.logs, key, meter)
    if cached is not None:
        return cached
    meter.primitives['log_atoms'] += 1
    meter.charge(precision*precision//16+base.bit_length()+32)
    return context.store(context.logs, key, arb(base).log(), 512+precision//4, meter)


def _atom(alpha, base, endpoint, endpoint_key, precision, context, meter):
    key = (alpha, base, endpoint_key, precision)
    cached = context.get(context.gamma_atoms, key, meter)
    if cached is not None:
        return cached
    logbase = _log(base, precision, context, meter)
    pkey = (alpha, base, precision)
    power = context.get(context.powers, pkey, meter)
    if power is None:
        meter.primitives['power_atoms'] += 1
        meter.charge(precision*precision//16+32)
        power = context.store(context.powers, pkey, logbase**_aq(alpha), 512+precision//4, meter)
    # d/dt [lambda^alpha Gamma(-alpha,lambda*t)]
    #     = -exp(-lambda*t)*t^(-alpha-1), t>0.
    value = power*(logbase*endpoint).gamma_upper(-_aq(alpha))
    meter.primitives['gamma_upper_atoms'] += 1
    meter.charge(precision*precision//8+64)
    if not value.is_finite():
        raise ArithmeticError('nonfinite upper incomplete gamma atom')
    return context.store(context.gamma_atoms, key, value, 640+precision//4, meter)


def band_decomposition(request, fractions=('0', '1/3', '2/3', '1'), meter=None):
    """Algebra only: closed adjacent bands partition the same full middle."""
    meter = _meter(meter)
    _request(request, meter)
    if type(fractions) not in (list, tuple) or not 2 <= len(fractions) <= 65:
        raise ValueError('bounded band partition')
    values = [_q(x) for x in fractions]
    if values[0] != 0 or values[-1] != 1 or any(a >= b for a, b in zip(values, values[1:])):
        raise ValueError('strict partition from0 to1')
    whole = dict(request, lower_fraction='0', upper_fraction='1')
    bands = [dict(request, lower_fraction=a, upper_fraction=b) for a, b in zip(fractions, fractions[1:])]
    return {'schema': 'prime-insertion-middle-partition-v1', 'whole_request': whole,
            'band_requests': bands, 'identity': 'J[epsilon,1/2]=sum adjacent J bands',
            'total_integral_identity': 'J[0,infinity]=J[0,epsilon]+J[epsilon,1/2]+J[1/2,infinity]',
            'endpoint_overlap_measure_zero': True, 'numeric_values_evaluated': False,
            'head_or_tail_bounded': False, 'all_scale': False}


def evaluate(request, precision=192, meter=None, context=None):
    """Certified normalized finite band; all signed source terms retained."""
    meter = _meter(meter)
    before = meter.counts()
    alpha, primes, N, gamma, lower, upper = _request(request, meter)
    if type(precision) is not int or precision not in PRECISIONS:
        raise ValueError('declared Arb precision bank')
    context = prepare_context(meter) if context is None else context
    if type(context) is not Context:
        raise ValueError('producer-owned literal cache context')
    old_precision = ctx.prec
    try:
        ctx.prec = precision
        epsilon, at_half = _epsilon(N, gamma, precision, context, meter)
        a = epsilon if lower == 0 else arb(1)/2 if lower == 1 else epsilon+(arb(1)/2-epsilon)*_aq(lower)
        b = epsilon if upper == 0 else arb(1)/2 if upper == 1 else epsilon+(arb(1)/2-epsilon)*_aq(upper)
        exact_zero = at_half or lower == upper
        rows = () if exact_zero else _compile(primes, N, context, meter)
        total = arb(0)
        for base, weight in rows:
            akey = ('fixed-half',) if lower == 1 else (N, gamma, lower)
            bkey = ('fixed-half',) if upper == 1 else (N, gamma, upper)
            avalue = _atom(alpha, base, a, akey, precision, context, meter)
            bvalue = _atom(alpha, base, b, bkey, precision, context, meter)
            total += weight*(avalue-bvalue)
            meter.primitives['signed_sum_terms'] += 1
            meter.charge(precision+abs(weight).bit_length()+32)
        if not exact_zero:
            total *= (arb(1)-_aq(alpha)).rgamma()
            meter.charge(precision*precision//8+64)
        interval = _interval(total, meter)
        endpoints = {name: _interval(value, meter) for name, value in
                     (('epsilon', epsilon), ('a', a), ('b', b))}
        result = {'schema': 'prime-insertion-middle-interval-v1', 'request': dict(request),
            'precision': precision, 'output_dyadic_bits': OUTPUT_DYADIC_BITS,
            **interval, 'endpoint_intervals': endpoints,
            'status': 'EXACT_ZERO_BAND' if exact_zero else 'FINITE_INTERVAL',
            'source': {'support': 4*N, 'prime_product': math.prod(primes),
                'coefficient_count': len(rows) if not exact_zero else None,
                'integer_coefficient_sum': sum(w for _, w in rows) if not exact_zero else None,
                'coefficient_l1': sum(abs(w) for _, w in rows) if not exact_zero else None,
                'formula': 'G_R(t)*sum_(d<=4N,gcd(d,R)=1)mu(d)*(2 floor(N/d)-3 floor(2N/d)+floor(4N/d))*d^-t',
                'ordinary_mu_provenance': 'integer Eratosthenes prime/multiple and square-multiple sieve',
                'unit_cancelled_exactly': True, 'filter_coefficients': [2, -3, 1],
                'normalization': '1/Gamma(1-alpha)',
                'source_kind': 'E_R K(n)=K(R*n), n>=2; no coprime mask on n',
                'all_valuations_retained': True,
                'arithmetic_skipped_for_exact_zero_band': exact_zero},
            'integration_method': 'signed exact exponential cofactor sum; Arb upper incomplete gamma at negative shape and positive argument',
            'source_chain_replayed_here': not exact_zero, 'whole_source_bound_proved': False,
            'all_scale': False, 'float_admission_used': False,
            'head_or_tail_evaluated': False, 'artifact_hashes_used': False,
            'counts': _delta(before, meter.counts())}
        return result
    finally:
        ctx.prec = old_precision
