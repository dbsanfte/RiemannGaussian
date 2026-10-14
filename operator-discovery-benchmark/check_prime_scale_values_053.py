"""Independent source reconstruction and joint signed filter evaluation.

Mobius values use sum_{d|n}mu(d)=delta_(n,1), not a prime sieve. Atoms use
higher-precision exp(alpha*log(log(n))). Final filters sum their combined
floor weights before taking interval magnitudes, retaining cancellation.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
import numpy as np
from flint import arb, ctx
from check_prime_scale_filter_053 import Meter, _parse, _expect

MAX_N = 2_000_000
INT64_MAX = 2**63-1


def _mobius(n, meter):
    mu = np.zeros(n+1, dtype=np.int64)
    mu[1] = 1
    for d in range(1, n+1):
        value = int(mu[d])
        if value not in (-1, 0, 1):
            raise ArithmeticError('independent divisor recurrence left Mobius range')
        if value:
            mu[2*d::d] -= value
            meter.charge(8*(n//d))
        else:
            meter.charge(4)
    return mu


def _floor(endpoint):
    mantissa, power = endpoint.man_exp()
    mantissa, power = int(mantissa), int(power)
    return mantissa << power if power >= 0 else mantissa >> -power


def _atom(n, alpha, bits, meter):
    for precision in (192, 256, 384):
        with ctx.workprec(precision):
            value = (arb(n).log().log()*alpha.numerator/alpha.denominator).exp()*(1 << bits)
            lo, hi = _floor(value.lower()), _floor(value.upper())
            meter.charge(precision**2+64)
            if lo == hi:
                return lo, precision
    raise ArithmeticError('independent atom floor unresolved at384bits')


@dataclass(frozen=True)
class VerifiedSource:
    alpha: str
    max_n: int
    bits: int
    mu: np.ndarray
    weights: np.ndarray
    metadata: dict

    def __post_init__(self):
        self.mu.setflags(write=False)
        self.weights.setflags(write=False)

    def __reduce__(self):
        return (VerifiedSource, (self.alpha, self.max_n, self.bits, self.mu, self.weights, self.metadata))


def verify_source(fields, meter=None, previous=None):
    meter = meter or Meter(cap=200_000_000_000, seconds=7200)
    if type(fields) is not dict or set(fields) != {'alpha', 'max_n', 'bits', 'mu', 'prefix_w', 'prefix_up', 'prefix_down'}:
        raise ValueError('exact finite source fields')
    text, n, bits = fields['alpha'], fields['max_n'], fields['bits']
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded rational alpha')
    alpha = Q(text)
    if str(alpha) != text or not 0 < alpha < 1 or max(alpha.numerator.bit_length(), alpha.denominator.bit_length()) > 4096:
        raise ValueError('canonical fractional source exponent')
    if type(n) is not int or not 2 <= n <= MAX_N or type(bits) is not int or not 16 <= bits <= 40:
        raise ValueError('finite source capacity')
    if previous is not None and (type(previous) is not VerifiedSource or
            previous.alpha != text or previous.bits != bits or previous.max_n >= n):
        raise ValueError('matching strictly smaller independently verified prefix')
    prefix_bound = (n-1)*n.bit_length()*(1 << bits)
    if prefix_bound > INT64_MAX:
        raise OverflowError('independent source int64 capacity')
    for name in ('mu', 'prefix_w', 'prefix_up', 'prefix_down'):
        array = fields[name]
        if type(array) is not np.ndarray or array.shape != (n+1,) or array.dtype.kind != 'i':
            raise ValueError('typed one-dimensional signed-integer source arrays')
        if name != 'mu' and array.dtype != np.dtype(np.int64):
            raise ValueError('int64 source prefixes')
    mu = _mobius(n, meter)
    if not np.array_equal(mu, fields['mu']):
        raise ValueError('ordinary Mobius source mismatch')
    weights = np.zeros(n+1, dtype=np.int64)
    old_max = 0 if previous is None else previous.max_n
    if previous is not None:
        if not np.array_equal(mu[:old_max+1], previous.mu):
            raise ValueError('independent extended Mobius prefix changed')
        weights[:old_max+1] = previous.weights
    refinement = {str(p): 0 for p in (192, 256, 384)}
    for d in range(max(2, old_max+1), n+1):
        if mu[d]:
            value, precision = _atom(d, alpha, bits, meter)
            weights[d] = -int(mu[d])*value
            refinement[str(precision)] += 1
    expected_w = np.cumsum(weights, dtype=np.int64)
    up, down = (mu == -1).astype(np.int64), (mu == 1).astype(np.int64)
    up[0:2] = 0; down[0:2] = 0
    for name, expected in (('prefix_w', expected_w),
                           ('prefix_up', np.cumsum(up, dtype=np.int64)),
                           ('prefix_down', np.cumsum(down, dtype=np.int64))):
        if not np.array_equal(expected, fields[name]):
            raise ValueError('source prefix mismatch: '+name)
        meter.charge(8*(n+1))
    mu.setflags(write=False); weights.setflags(write=False)
    metadata = {'verified': True, 'alpha': text, 'max_n': n, 'dyadic_bits': bits,
        'ordinary_mobius_method': 'independent divisor-sum recurrence',
        'atom_method': 'exp(alpha*log(log(n))),192/256/384-bit refinement',
        'atom_refinement_counts': refinement, 'prefix_int64_absolute_bound': prefix_bound,
        'reused_verified_prefix_through': old_max,
        'atom_counts_scope': 'new suffix only when extending; inherited atoms not reevaluated',
        'source_producer_imported': False, 'all_indices_checked': True,
        'finite_only': True, 'uniform_arithmetic_bound_proved': False, 'RH_proved': False}
    return VerifiedSource(text, n, bits, mu, weights, metadata)


def joint_filter(source, request, N, producer_interval=None, meter=None):
    meter = meter or Meter(cap=200_000_000_000, seconds=7200)
    if type(source) is not VerifiedSource:
        raise ValueError('independently verified immutable source required')
    alpha, q, coefficients, _, _, _ = _parse(request, meter)
    _expect(request['alpha'], source.alpha)
    if type(N) is not int or N < 2:
        raise ValueError('ordinary integer scaleN>=2')
    largest = q**(len(coefficients)-1)*N
    if largest > source.max_n:
        raise ValueError('filter exceeds independently verified source')
    l1 = sum(abs(c) for c in coefficients)
    # P(q)=0 makes each combined floor weight at most l1 in magnitude.
    # This pays int64 safety for the complete joint signed sum, rather than
    # trusting observed cancellation to prevent wraparound.
    absolute_capacity = l1*largest*largest.bit_length()*(1 << source.bits)
    if absolute_capacity > INT64_MAX:
        raise OverflowError('joint signed int64 resource capacity')
    d = np.arange(1, largest+1, dtype=np.int64)
    floor_weight = np.zeros(largest, dtype=np.int64)
    for j, c in enumerate(coefficients):
        # Each individual c*floor(...) must also fit before cancellation.
        if abs(c)*q**j*N > INT64_MAX:
            raise OverflowError('individual floor product capacity')
        floor_weight += c*((q**j*N)//d)
        meter.charge(16*largest)
    if np.any(np.abs(floor_weight) > l1):
        raise ArithmeticError('exact P(q) floor cancellation identity failed')
    center = int(np.sum(source.weights[1:largest+1]*floor_weight, dtype=np.int64))
    error_direction = -source.mu[1:largest+1]*floor_weight
    error_direction[0] = 0  # log(1)^alpha is exact0, with no floor uncertainty.
    down = int(np.sum(np.maximum(-error_direction, 0), dtype=np.int64))
    up = int(np.sum(np.maximum(error_direction, 0), dtype=np.int64))
    # Dividing by exact alpha retains exact rational source enclosures.
    denominator = (1 << source.bits)*alpha.numerator
    lo, hi = (center-down)*alpha.denominator, (center+up)*alpha.denominator
    lower, upper = Q(lo, denominator), Q(hi, denominator)
    if producer_interval is not None:
        if type(producer_interval) is not dict or set(producer_interval) != {'lower', 'upper'}:
            raise ValueError('exact producer interval')
        pl, pu = Q(producer_interval['lower']), Q(producer_interval['upper'])
        if str(pl) != producer_interval['lower'] or str(pu) != producer_interval['upper']:
            raise ValueError('canonical producer rational intervals')
        if not pl <= lower <= upper <= pu:
            raise ValueError('independent joint interval not contained in producer interval')
    meter.charge(64*largest)
    return {'verified': True, 'request': request, 'N': N, 'source_maximum_used': largest,
        'lower': str(lower), 'upper': str(upper), 'dyadic_bits': source.bits,
        'method': 'combined signed floor weights, independent full source, exact integer accumulation',
        'joint_floor_absolute_bound': l1, 'int64_absolute_capacity': absolute_capacity,
        'finite_only': True, 'uniform_arithmetic_bound_proved': False, 'RH_proved': False}


def check_bound(request, N, checked_filter, producer_target=None, meter=None):
    """Independent256-bit target and exact comparison at this integer only."""
    meter = meter or Meter()
    _, _, _, C, eta, _ = _parse(request, meter)
    _expect(checked_filter.get('verified'), True)
    _expect(checked_filter.get('request'), request)
    _expect(checked_filter.get('N'), N)
    if type(N) is not int or not 2 <= N <= MAX_N:
        raise ValueError('bounded integer target scale')
    def endpoint(value):
        m, e = value.man_exp(); m, e = int(m), int(e)
        return Q(m << e) if e >= 0 else Q(m, 1 << -e)
    with ctx.workprec(256):
        logarithmic = ((1+arb(N).log()).log()*eta.numerator/eta.denominator).exp()
        bound = arb(N).sqrt()*logarithmic*C.numerator/C.denominator
        blo, bhi = endpoint(bound.lower()), endpoint(bound.upper())
    if producer_target is not None:
        if not Q(producer_target['lower']) <= blo <= bhi <= Q(producer_target['upper']):
            raise ValueError('independent target interval not contained in producer bound')
    lo, hi = Q(checked_filter['lower']), Q(checked_filter['upper'])
    if lo > hi:
        raise ValueError('ordered independently checked source interval')
    lower_abs = Q(0) if lo <= 0 <= hi else min(abs(lo), abs(hi))
    upper_abs = max(abs(lo), abs(hi))
    status = 'FINITE_PASS' if upper_abs <= blo else 'FINITE_REFUTATION' if lower_abs > bhi else 'UNRESOLVED_INTERVAL'
    meter.charge(256**2)
    return {'verified': True, 'request': request, 'N': N, 'status': status,
        'target_lower': str(blo), 'target_upper': str(bhi),
        'absolute_source_lower': str(lower_abs), 'absolute_source_upper': str(upper_abs),
        'finite_only': True, 'uniform_arithmetic_bound_proved': False, 'RH_proved': False}
