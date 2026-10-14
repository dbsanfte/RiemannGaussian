"""Independent exact signed lag audit using direct integer correlations.

This module imports neither the lag producer nor its FLINT multiplication.
The current-scale lag cancellation and the full arithmetic growth bound remain
open. Finite correlations are certificates of identities, not those bounds.
"""
from fractions import Fraction as Q
from math import isqrt
import time
import numpy as np

SCHEMA = 'mobius-signed-head-lag-v1'
MAX_N = 65536
MAX_H = 4096
MAX_BITS = 4096
MAX_WORK = 300_000_000_000
MAX_MEMORY_BYTES = 512 * 1024 * 1024
MAX_ENTRIES = 4_000_000
INT64_MAX = (1 << 63)-1
MAX_POWER_BITS = 100000
ROUNDING_DENOMINATOR = 1 << 24


class Meter:
    def __init__(self, cap=MAX_WORK, seconds=7200):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative work cap')
        if type(seconds) not in (int, float) or not 0 < seconds <= 7200:
            raise ValueError('bounded positive deadline')
        self.cap, self.operations = cap, 0
        self.deadline = time.monotonic()+seconds

    def charge(self, n=1):
        if type(n) is not int or not 0 <= n <= self.cap-self.operations:
            raise OverflowError('signed lag work cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('signed lag deadline')


class _Context:
    def __init__(self, meter):
        self.m = meter
        self.work, self.entries, self.storage = 0, 0, 8192

    def charge(self, n=1):
        if type(n) is not int or not 0 <= n <= MAX_WORK-self.work:
            raise OverflowError('independent signed lag work capacity')
        self.work += n
        self.m.charge(n)

    def reserve(self, count, size=128):
        self.charge(count)
        self.entries += count
        self.storage += count*size
        if self.entries > MAX_ENTRIES:
            raise OverflowError('signed lag entry capacity')
        if self.storage > MAX_MEMORY_BYTES:
            raise MemoryError('signed lag storage capacity')

    def bounded(self, value):
        value = Q(value)
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        self.charge(bits+1)
        if bits > MAX_BITS:
            raise OverflowError('signed lag rational capacity')
        return value

    def q(self, value):
        if type(value) is not str or not 1 <= len(value) <= 2500:
            raise ValueError('bounded rational text')
        self.charge(len(value)+1)
        try:
            result = Q(value)
        except (ValueError, ZeroDivisionError):
            raise ValueError('rational text') from None
        if str(result) != value:
            raise ValueError('canonical rational required')
        return self.bounded(result)


def _fields(obj, names):
    if type(obj) is not dict or set(obj) != set(names):
        raise ValueError('exact signed lag schema')


def _integer(value, lo, hi, description):
    if type(value) is not int or not lo <= value <= hi:
        raise ValueError(description)
    return value


def _parameters(obj, c):
    if type(obj) is not dict or set(obj) not in (
            {'primes', 'p', 'q', 'alpha', 'gamma'},
            {'primes', 'p', 'q', 'alpha', 'gamma', 'tau'}):
        raise ValueError('source parameter schema')
    alpha, gamma = (c.q(obj[k]) for k in ('alpha', 'gamma'))
    if not 0 < alpha < 1 or gamma <= 0:
        raise ValueError('source fractional gates')
    if 'tau' in obj and not 0 < c.q(obj['tau']) < 1:
        raise ValueError('source tau gate')
    primes = obj['primes']
    if type(primes) is not list or not 2 <= len(primes) <= 8:
        raise ValueError('bounded prime registration')
    c.reserve(len(primes))
    for prime in primes:
        _integer(prime, 2, 1000000, 'actual bounded prime')
        for divisor in range(2, isqrt(prime)+1):
            c.charge(4)
            if prime % divisor == 0:
                raise ValueError('actual prime required')
    if primes != sorted(set(primes)):
        raise ValueError('canonical prime registration')
    p, q = obj['p'], obj['q']
    if type(p) is not int or type(q) is not int or p not in primes or q not in primes or p >= q:
        raise ValueError('ordered registered source primes')
    return p, q


def _ordinary_mu(D, c):
    """Sign sieve with explicit square divisors, including mu(1)=1."""
    c.reserve(2*(D+1), 40)
    mu, composite = [1]*(D+1), bytearray(D+1)
    mu[0] = 0
    for prime in range(2, D+1):
        c.charge()
        if composite[prime]:
            continue
        for n in range(prime, D+1, prime):
            c.charge(3)
            mu[n] = -mu[n]
            if n != prime:
                composite[n] = 1
        for n in range(prime*prime, D+1, prime*prime):
            c.charge(2)
            mu[n] = 0
    return mu


def _source(N, y, D, p, q, ratio, c):
    """Pointwise original source and correction jumps; no quotient blocks."""
    den, num = ratio.denominator, ratio.numerator
    c.reserve(2*(D+2), 40)
    f, g = [0]*(D+2), [0]*(D+2)
    for d in range(1, D+1):
        c.charge(24)
        Wp = 4*N//(p*d)-3*(2*N//(p*d))+2*(N//(p*d))
        Wq = 4*N//(q*d)-3*(2*N//(q*d))+2*(N//(q*d))
        if abs(Wp) > 1 or abs(Wq) > 1:
            raise ArithmeticError('elementary floor channel amplitude')
        joined = den*Wp-num*Wq
        if d <= y:
            f[d] = joined
        else:
            g[d] = -joined
    floors = {}
    for base, scale in ((p, den), (q, -num)):
        for v, a in ((4, 1), (2, -3), (1, 2)):
            Z = v*N//base
            if Z:
                floors[Z] = floors.get(Z, 0)+scale*a
                c.charge(8)
    floors = {Z: Q(a, den) for Z, a in floors.items() if a}
    steps = {}
    for T in range(1, D+1):
        c.charge(4)
        if g[T] != g[T+1]:
            steps[T] = Q(g[T]-g[T+1], den)
    c.reserve(len(floors)+len(steps))
    return f, g, floors, steps


def _correlate(values, c):
    """Native integer direct product sum, guarded before all arithmetic."""
    length = len(values)
    if not length:
        raise ValueError('nonempty lag row')
    maximum = max(map(abs, values))
    c.charge(length)
    if maximum > INT64_MAX or length*maximum*maximum > INT64_MAX:
        raise OverflowError('int64 correlation absolute product bound')
    c.charge(2*length*length)
    result = np.correlate(np.asarray(values, dtype=np.int64),
                          np.asarray(values, dtype=np.int64), mode='full')
    c.charge(length)
    return [int(v) for v in result[length-1:]]


def _sqrt_upper(value, c):
    """Unique least grid point with square at least the rational value."""
    value = c.bounded(value)
    if value < 0:
        raise ValueError('nonnegative radicand')
    target = value.numerator*ROUNDING_DENOMINATOR**2
    root = isqrt(target//value.denominator)
    if root*root*value.denominator < target:
        root += 1
    c.charge(64+target.bit_length()**2)
    return c.bounded(Q(root, ROUNDING_DENOMINATOR))


def _exponents(requests, N, c):
    if type(requests) is not list or not 1 <= len(requests) <= 128:
        raise ValueError('bounded nonempty exponent requests')
    result = []
    for text in requests:
        value = c.q(text)
        if not 0 <= value <= 1 or text in result:
            raise ValueError('distinct exponents in closed unit interval')
        bits = N.bit_length()*max(value.numerator, value.denominator)
        if bits > MAX_POWER_BITS:
            raise OverflowError('exact power intermediate bit capacity')
        result.append(text)
    return result


def _cutoff(N, exponent, claimed, c):
    if exponent is None:
        return _integer(claimed, 0, 0, 'baseline cutoff zero')
    delta = c.q(exponent)
    claimed = _integer(claimed, 1, N, 'bounded exact power cutoff')
    bits = N.bit_length()*max(delta.numerator, delta.denominator)
    c.charge(3*(1+bits*max(1, bits.bit_length())))
    target = N**delta.numerator
    if not claimed**delta.denominator <= target < (claimed+1)**delta.denominator:
        raise ValueError('exact rational power floor')
    return claimed


def _equal_q(obj, name, expected, c):
    if c.q(obj[name]) != c.bounded(expected):
        raise ValueError('exact signed lag field '+name)


def verify_lag(cert, meter=None):
    """Audit every finite lag, source coefficient, candidate and scope flag."""
    c = _Context(Meter() if meter is None else meter)
    _fields(cert, ('schema', 'N', 'y', 'H', 'parameters', 'head_stop',
                   'exponent_requests', 'rounding_denominator', 'endpoints',
                   'uniform_full_head_bound_proved', 'RH_proved'))
    if cert['schema'] != SCHEMA:
        raise ValueError('signed head lag schema')
    if cert['uniform_full_head_bound_proved'] is not False or cert['RH_proved'] is not False:
        raise ValueError('finite values do not prove a uniform bound or RH')
    p, q = _parameters(cert['parameters'], c)
    N = _integer(cert['N'], 2, MAX_N, 'bounded source scale')
    D = 4*N//p
    y = _integer(cert['y'], 1, D, 'bounded original prefix')
    H = _integer(cert['H'], 1, min(D, MAX_H), 'bounded raw short horizon')
    head_stop = (H+1)//2-1
    _integer(cert['head_stop'], head_stop, head_stop, 'complete head boundary')
    _integer(cert['rounding_denominator'], ROUNDING_DENOMINATOR,
             ROUNDING_DENOMINATOR, 'fixed exact square-root grid')
    requests = _exponents(cert['exponent_requests'], N, c)
    endpoints = cert['endpoints']
    if type(endpoints) is not list or len(endpoints) != 2:
        raise ValueError('both ratio endpoints required')
    mu = _ordinary_mu(D, c)
    c.reserve(D+1, 96)  # Peak live native correlation/vector scratch.
    checked_endpoints = []
    for endpoint, ratio in zip(endpoints, (Q(p, q), Q(1))):
        _fields(endpoint, ('ratio', 'denominator', 'step_first_moment', 'floor_l1', 'blocks'))
        if c.q(endpoint['ratio']) != ratio:
            raise ValueError('ordered exact ratio endpoints')
        den = ratio.denominator
        _integer(endpoint['denominator'], den, den, 'reduced common denominator')
        f, g, floors, steps = _source(N, y, D, p, q, ratio, c)
        M1 = sum((abs(a)*T for T, a in steps.items()), Q(0))
        floor_l1 = sum(map(abs, floors.values()), Q(0))
        _equal_q(endpoint, 'step_first_moment', M1, c)
        _equal_q(endpoint, 'floor_l1', floor_l1, c)
        starts, L = [], 1
        while L <= head_stop:
            starts.append(L)
            L *= 2
        blocks = endpoint['blocks']
        if type(blocks) is not list or len(blocks) != len(starts):
            raise ValueError('complete dyadic head block domain')
        checked_blocks = []
        for block, L in zip(blocks, starts):
            _fields(block, ('start', 'stop', 'correlation_numerators', 'row_sums_scaled',
                            'direct_coefficients', 'joined_kernel_l1', 'max_kernel',
                            'diagonal', 'signed_cross', 'moment', 'diagonal_upper',
                            'uniform_diagonal_upper', 'actual_head_variation',
                            'cauchy_upper', 'candidates'))
            stop = min(2*L-1, head_stop)
            _integer(block['start'], L, L, 'dyadic block start')
            _integer(block['stop'], stop, stop, 'complete dyadic block stop')
            count, length = stop-L+1, D//L
            total = [0]*length
            c.reserve(length, 80)
            row_sums, direct, kernel_l1, max_kernel = [], [], Q(0), Q(0)
            for j in range(L, stop+1):
                values = []
                row_sum, raw = 0, 0
                for n in range(1, D//j+1):
                    c.charge(32)
                    d, e = j*n, (j+1)*n
                    k = g[d]-(g[e] if e <= D else 0)
                    kernel_l1 += Q(abs(k), den)
                    max_kernel = max(max_kernel, Q(abs(k), den))
                    values.append(mu[n]*k)
                    row_sum += mu[n]*k
                    raw += mu[n]*(f[d]-(f[e] if e <= D else 0))
                d_j = floors.get(j, Q(0))
                if Q(raw, den) != d_j+Q(row_sum, den):
                    raise ArithmeticError('original source inverse identity')
                row_sums.append(row_sum)
                direct.append(d_j)
                for h, value in enumerate(_correlate(values, c)):
                    total[h] += value
                    c.charge(4)
            if max_kernel > 4:
                raise ArithmeticError('joined source jump bound')
            numerators = block['correlation_numerators']
            if type(numerators) is not list or len(numerators) != length:
                raise ValueError('complete nonnegative lag domain')
            c.reserve(len(numerators), 64)
            for actual, expected in zip(numerators, total):
                if type(actual) is not int or actual != expected:
                    raise ValueError('every exact lag correlation numerator')
                if Q(abs(actual), den*den) > 4*M1/L:
                    raise ArithmeticError('uniform individual lag majorant')
                c.charge(16)
            supplied_sums, supplied_direct = block['row_sums_scaled'], block['direct_coefficients']
            if type(supplied_sums) is not list or len(supplied_sums) != count or any(
                    type(a) is not int or a != b for a, b in zip(supplied_sums, row_sums)):
                raise ValueError('complete exact scaled row sums')
            if type(supplied_direct) is not list or len(supplied_direct) != count:
                raise ValueError('complete direct floor contributions')
            if any(c.q(a) != b for a, b in zip(supplied_direct, direct)):
                raise ValueError('direct six-floor atom coefficient')
            diag = Q(total[0], den*den)
            cross = Q(2*sum(total[1:]), den*den)
            moment = Q(sum(a*a for a in row_sums), den*den)
            diagonal_upper, universal = 4*kernel_l1, 4*M1/L
            absolute_direct = sum(map(abs, direct), Q(0))
            variation = sum((abs(d+Q(a, den)) for d, a in zip(direct, row_sums)), Q(0))
            if moment != diag+cross or not 0 <= diag <= diagonal_upper <= universal:
                raise ArithmeticError('diagonal and complete signed lag identity')
            for name, expected in (('joined_kernel_l1', kernel_l1), ('max_kernel', max_kernel),
                    ('diagonal', diag), ('signed_cross', cross), ('moment', moment),
                    ('diagonal_upper', diagonal_upper), ('uniform_diagonal_upper', universal),
                    ('actual_head_variation', variation),
                    ('cauchy_upper', absolute_direct+_sqrt_upper(count*moment, c))):
                _equal_q(block, name, expected, c)
            trials = block['candidates']
            if type(trials) is not list or len(trials) != len(requests)+1:
                raise ValueError('complete declared lag candidates')
            prefix = [0]
            for a in total[1:]:
                prefix.append(prefix[-1]+a)
                c.charge(4)
            for trial, exponent in zip(trials, [None]+requests):
                _fields(trial, ('exponent', 'requested_cutoff', 'used_cutoff', 'near_signed',
                                'far_signed', 'paid_moment_upper', 'finite_moment_upper',
                                'finite_head_upper', 'paid_head_upper', 'unpaid_risk_upper',
                                'far_nonpositive_observed', 'uniform_far_bound_proved'))
                if type(trial['exponent']) is not type(exponent) or trial['exponent'] != exponent:
                    raise ValueError('exact declared exponent order')
                requested = _cutoff(N, exponent, trial['requested_cutoff'], c)
                B = min(requested, length-1)
                _integer(trial['used_cutoff'], B, B, 'complete clipped near-lag domain')
                near = Q(2*prefix[B], den*den)
                far = cross-near
                paid = (4+8*B)*M1/L
                upper = paid+max(far, Q(0))
                if moment > upper or abs(near) > 8*B*M1/L:
                    raise ArithmeticError('short lag majorant and signed far transfer')
                for name, expected in (('near_signed', near), ('far_signed', far),
                        ('paid_moment_upper', paid), ('finite_moment_upper', upper),
                        ('finite_head_upper', absolute_direct+_sqrt_upper(count*upper, c)),
                        ('paid_head_upper', _sqrt_upper(count*paid, c)),
                        ('unpaid_risk_upper', _sqrt_upper(count*max(far, Q(0)), c))):
                    _equal_q(trial, name, expected, c)
                if trial['far_nonpositive_observed'] is not (far <= 0):
                    raise ValueError('finite signed far observation')
                if trial['uniform_far_bound_proved'] is not False:
                    raise ValueError('uniform far bound remains unpaid')
            checked_blocks.append(dict(start=L, stop=stop, lag_count=length,
                diagonal=str(diag), signed_cross=str(cross), moment=str(moment),
                actual_head_variation=str(variation), candidates=trials))
        checked_endpoints.append(dict(ratio=str(ratio), denominator=den,
            step_first_moment=str(M1), floor_l1=str(floor_l1), blocks=checked_blocks))
    return dict(verified=True, schema='verified-'+SCHEMA, parameters=cert['parameters'],
        N=N, y=y, H=H, D=D, head_stop=head_stop, endpoints=checked_endpoints,
        all_lags_independently_verified=True, original_source_inverse_identity_proved=True,
        ordinary_mu_unit_retained=True, squareful_mu_zero_retained=True,
        diagonal_and_individual_lag_rule_proved=True, endpoint_convexity_proved=True,
        independent_parent_066_admission_required=True, original_source_binding_proved=False,
        raw_short_head_only=True, arithmetic_query_horizon=D,
        uniform_far_bound_proved=False, uniform_full_head_bound_proved=False,
        uniform_N_growth_proved=False, whole_signed_target_bound_proved=False,
        RH_proved=False, masked_scientific_prefix_or_LP_evaluated=False,
        unmasked_original_source_inverse_evaluated=True,
        new_actual_mu_lag_correlations_evaluated=True,
        charged_work_units=c.work, prospective_peak_storage_bytes=c.storage)
