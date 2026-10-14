"""Finite rigorous fractional-Mobius floor sums, with integer hyperbola queries.

The source stores quantized atoms and sign-separated rounding uncertainties.
It proves neither an all-scale arithmetic bound nor a selected filter claim.
No source construction or numerical observation occurs at import.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
import math
import time
import numpy as np
from flint import arb, ctx

MAX_N = 2_000_000
MAX_INPUT_BITS = 4096
MAX_ROUND_BITS = 40
PRECISION_SCHEDULE = (128, 192, 256)
INT64_MAX = (1 << 63)-1
MAX_BUILD_BYTES = 4*1024**3


class Meter:
    def __init__(self, cap=30_000_000_000, seconds=7200):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer work cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite source deadline')
        self.cap, self.operations, self.deadline = cap, 0, time.monotonic()+seconds
        self.peak_bytes_estimate = self.max_parameter_bits = 0
        self.atom_attempt_counts = {str(p): 0 for p in PRECISION_SCHEDULE}
        self.atom_refinement_counts = {str(p): 0 for p in PRECISION_SCHEDULE}
        self.primitives = {name: 0 for name in (
            'sieve_candidates', 'sieve_prime_count', 'sieve_flip_entries',
            'sieve_square_zero_entries', 'sieve_composite_mark_entries',
            'log_evaluations', 'power_evaluations', 'directed_endpoint_floors',
            'quantized_atoms', 'prefix_entries_written', 'hyperbola_blocks',
            'integer_accumulations')}

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('prime-scale source work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('prime-scale source construction/query deadline')

    def reserve(self, amount):
        if type(amount) is not int or not 0 <= amount <= MAX_BUILD_BYTES:
            raise MemoryError('prime-scale source prospective memory cap')
        self.peak_bytes_estimate = max(self.peak_bytes_estimate, amount)
        self.charge()

    def counts(self):
        return {'operations': self.operations, 'max_parameter_bits': self.max_parameter_bits,
                'peak_bytes_estimate': self.peak_bytes_estimate,
                'atom_attempt_counts': dict(self.atom_attempt_counts),
                'atom_refinement_counts': dict(self.atom_refinement_counts),
                'total_primitive_counts': dict(self.primitives)}


def _meter(meter):
    return meter if meter is not None else Meter()


def _alpha(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational alpha string')
    try:
        value = Q(text)
    except (ValueError, ZeroDivisionError):
        raise ValueError('canonical rational alpha') from None
    if str(value) != text or not 0 < value < 1:
        raise ValueError('canonical rational alpha strictly between0 and1')
    bit_count = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
    if bit_count > MAX_INPUT_BITS:
        raise OverflowError('source alpha rational bit cap')
    meter.max_parameter_bits = max(meter.max_parameter_bits, bit_count)
    meter.charge(1+abs(value.numerator).bit_length()+value.denominator.bit_length())
    return value


def resource_preflight(alpha, max_n, bits=32, meter=None):
    """Prove int64 prefix safety before allocating or evaluating any atom.

    For2<=d<=X and0<alpha<1, (log d)^alpha<=max(1,log X)<=X.bit_length().
    The last inequality uses ln2<1. Sum of absolute integer atoms is bounded
    by (X-1)*X.bit_length()*2^bits, including every possible nonzero mu.
    """
    meter = _meter(meter)
    _alpha(alpha, meter)
    if type(max_n) is not int or not 1 <= max_n <= MAX_N:
        raise ValueError('integer finite source horizon1..2000000')
    if type(bits) is not int or not 1 <= bits <= MAX_ROUND_BITS:
        raise ValueError('integer dyadic rounding bits1..40')
    ell = max_n.bit_length()
    atom_bound = ell*(1 << bits)
    prefix_bound = (max_n-1)*atom_bound
    meter.charge(32+prefix_bound.bit_length())
    if prefix_bound > INT64_MAX:
        raise OverflowError('proved absolute prefix bound exceeds signed int64')
    estimate = 96*(max_n+1)+16*1024**2
    meter.reserve(estimate)
    return {'max_n': max_n, 'bits': bits, 'log_power_upper_integer': ell,
            'atom_abs_upper_integer': atom_bound,
            'prefix_abs_upper_integer': prefix_bound,
            'uncertainty_prefix_upper_integer': max_n-1,
            'int64_max': INT64_MAX, 'estimated_peak_bytes': estimate,
            'persistent_array_bytes': 25*(max_n+1),
            'overflow_preflight_proved': True,
            'overflow_proof': '(log d)^alpha<=max(1,log X)<=X.bit_length(); sum_abs<= (X-1)*ell*2^bits'}


def _sieve_mu(max_n, meter):
    mu = np.ones(max_n+1, dtype=np.int8)
    mu[0] = 0
    flags = np.ones(max_n+1, dtype=np.bool_)
    flags[:2] = False
    meter.charge(2*(max_n+1))
    for p in range(2, max_n+1):
        meter.primitives['sieve_candidates'] += 1
        meter.charge()
        if not flags[p]:
            continue
        meter.primitives['sieve_prime_count'] += 1
        flip_entries = max_n//p
        mu[p::p] *= -1
        meter.primitives['sieve_flip_entries'] += flip_entries
        meter.charge(16+flip_entries)
        square = p*p
        if square <= max_n:
            zeros = max_n//square
            marks = (max_n-square)//p+1
            mu[square::square] = 0
            flags[square::p] = False
            meter.primitives['sieve_square_zero_entries'] += zeros
            meter.primitives['sieve_composite_mark_entries'] += marks
            meter.charge(16+zeros+marks)
    return mu


def _exponents(alpha, meter):
    result = {}
    for precision in PRECISION_SCHEDULE:
        with ctx.workprec(precision):
            result[precision] = arb(alpha.numerator)/alpha.denominator
        meter.charge(16+2*precision+alpha.denominator.bit_length())
    return result


def _atom_ball(d, exponent, bits, precision, meter):
    with ctx.workprec(precision):
        meter.primitives['log_evaluations'] += 1
        meter.primitives['power_evaluations'] += 1
        meter.charge(64+precision*precision//4+d.bit_length())
        return (arb(d).log()**exponent)*(1 << bits)


def _endpoint_floor(endpoint, meter):
    mantissa, exponent = endpoint.man_exp()
    mantissa, exponent = int(mantissa), int(exponent)
    meter.primitives['directed_endpoint_floors'] += 1
    meter.charge(16+abs(mantissa).bit_length()+abs(exponent))
    return mantissa << exponent if exponent >= 0 else mantissa//(1 << -exponent)


def _quantized_atom(d, alpha, bits, meter, exponents=None):
    exponents = _exponents(alpha, meter) if exponents is None else exponents
    for precision in PRECISION_SCHEDULE:
        meter.atom_attempt_counts[str(precision)] += 1
        with ctx.workprec(precision):
            value = _atom_ball(d, exponents[precision], bits, precision, meter)
            if not value.is_finite():
                raise ArithmeticError('finite log-power atom enclosure required')
            lower = _endpoint_floor(value.lower(), meter)
            upper = _endpoint_floor(value.upper(), meter)
        if lower == upper:
            meter.atom_refinement_counts[str(precision)] += 1
            meter.primitives['quantized_atoms'] += 1
            return lower
    raise ArithmeticError('log-power integer floor unresolved after declared128/192/256 schedule')


@dataclass(frozen=True)
class Source:
    alpha: str
    max_n: int
    bits: int
    mu: np.ndarray
    prefix_w: np.ndarray
    prefix_up: np.ndarray
    prefix_down: np.ndarray
    overflow_certificate: dict
    construction_counts: dict
    atom_admission_counts: dict
    reused_prefix_through: int = 0

    def __post_init__(self):
        for name, dtype in (('mu', np.int8), ('prefix_w', np.int64),
                            ('prefix_up', np.int64), ('prefix_down', np.int64)):
            array = getattr(self, name)
            if not isinstance(array, np.ndarray) or array.dtype != dtype or array.shape != (self.max_n+1,):
                raise ValueError('source array exact dtype/domain')
            array.flags.writeable = False

    def __reduce__(self):
        # Worker IPC reconstructs through the constructor so NumPy pickle's
        # default writable flags cannot silently change the source contract.
        return (Source, (self.alpha, self.max_n, self.bits, self.mu,
                         self.prefix_w, self.prefix_up, self.prefix_down,
                         self.overflow_certificate, self.construction_counts,
                         self.atom_admission_counts, self.reused_prefix_through))

    def metadata(self):
        return {'schema': 'prime-scale-fractional-source-v1',
                'alpha': self.alpha, 'max_n': self.max_n, 'dyadic_bits': self.bits,
                'definition': 'A_alpha(N)=-sum_(d<=N)mu(d)*(log d)^alpha*floor(N/d)',
                'atom_definition': 'w_d=-mu(d)*floor(2^bits*(log d)^alpha), d>=2; w_0=w_1=0',
                'unit_convention': 'mu(0)=0; mu(1)=1; (log1)^alpha=0',
                'mu_provenance': 'exact Eratosthenes sieve; multiply by-1 on p multiples; zero p^2 multiples',
                'rounding_provenance': 'exact integer floor agreement of directed Arb endpoints',
                'precision_schedule': list(PRECISION_SCHEDULE),
                'atom_refinement_counts': dict(self.atom_admission_counts),
                'atom_refinement_counts_scope': 'all admitted stored atoms, including inherited prefix',
                'total_primitive_counts': dict(self.construction_counts['total_primitive_counts']),
                'counts_scope': 'latest construction or extension only',
                'reused_prefix_through': self.reused_prefix_through,
                'uncertainty_rule': 'mu=-1 permits upward atom error<1; mu=+1 permits downward atom error<1, in integer lattice units',
                'arrays': {'mu': {'dtype': 'int8', 'domain': [0, self.max_n], 'writeable': False},
                           **{name: {'dtype': 'int64', 'domain': [0, self.max_n], 'writeable': False,
                                     'prefix_includes_index': True} for name in
                              ('prefix_w', 'prefix_up', 'prefix_down')}},
                'persistent_array_bytes': sum(a.nbytes for a in (self.mu, self.prefix_w, self.prefix_up, self.prefix_down)),
                'overflow_certificate': dict(self.overflow_certificate),
                'counts': self.construction_counts,
                'independent_source_verified_here': False,
                'all_scale_bound_proved': False, 'RH_proved': False,
                'convolution_N_log_N_used': False, 'artifact_hashes_used': False}


def _count_delta(before, after):
    return {name: ({key: after[name][key]-before[name][key] for key in after[name]}
                   if type(after[name]) is dict else
                   after[name] if name in ('peak_bytes_estimate', 'max_parameter_bits')
                   else after[name]-before[name]) for name in after}


def _build_source(alpha, max_n, bits, meter, previous=None):
    before = meter.counts()
    overflow = resource_preflight(alpha, max_n, bits, meter)
    if previous is not None:
        meter.reserve(overflow['estimated_peak_bytes']+25*(previous.max_n+1))
    exponent = _alpha(alpha, meter)
    exponents = _exponents(exponent, meter)
    mu = _sieve_mu(max_n, meter)
    old_max = previous.max_n if previous is not None else 0
    if previous is not None:
        meter.charge(old_max+1)
        if not np.array_equal(mu[:old_max+1], previous.mu):
            raise ArithmeticError('extended exact mu sieve disagrees with retained prefix')
    weights = np.zeros(max_n+1, dtype=np.int64)
    for d in range(max(2, old_max+1), max_n+1):
        meter.charge()
        sign = int(mu[d])
        if sign:
            atom = _quantized_atom(d, exponent, bits, meter, exponents)
            if not 0 <= atom <= overflow['atom_abs_upper_integer']:
                raise ArithmeticError('quantized atom contradicts proved integer bound')
            weights[d] = -sign*atom
    up = np.asarray(mu == -1, dtype=np.int64)
    down = np.asarray(mu == 1, dtype=np.int64)
    down[1] = 0
    for name, array in (('prefix_w', weights), ('prefix_up', up), ('prefix_down', down)):
        start = old_max+1 if previous is not None else 0
        suffix = array[start:]
        np.cumsum(suffix, dtype=np.int64, out=suffix)
        if previous is not None:
            retained = getattr(previous, name)
            suffix += int(retained[-1])
            array[:start] = retained
        meter.primitives['prefix_entries_written'] += max_n+1
        meter.charge(2*(max_n+1))
        array.flags.writeable = False
    mu.flags.writeable = False
    counts = _count_delta(before, meter.counts())
    admission = {str(p): counts['atom_refinement_counts'][str(p)]+(
        previous.atom_admission_counts[str(p)] if previous is not None else 0)
        for p in PRECISION_SCHEDULE}
    return Source(alpha, max_n, bits, mu, weights, up, down, overflow, counts, admission, old_max)


def make_source(alpha, max_n, bits=32, meter=None):
    """Build one finite source, reusable for every integer filter/query.

    Fixed atom quantization is not a fitted identity: the error prefixes pay
    every nonzero atom's full possible rounding unit. The actual candidate
    mathematical expression remains unrounded.
    """
    meter = _meter(meter)
    return _build_source(alpha, max_n, bits, meter)


def extend_source(source, new_max_n, meter=None):
    """Copy old prefixes exactly; quantize only newly requested indices.

    The sieve is recomputed and its retained prefix checked. Old rounded atoms
    are never recomputed. Temporary coexistence of old/new arrays is included
    in prospective memory. The mathematical definition is unchanged.
    """
    if type(source) is not Source or type(new_max_n) is not int or new_max_n <= source.max_n:
        raise ValueError('extend a Source to a strictly larger integer horizon')
    return _build_source(source.alpha, new_max_n, source.bits, _meter(meter), source)


def evaluate_A(source, N, meter=None):
    """Exact endpoint numerators /2^bits, using grouped integer hyperbola sums.

    For every block[l,r] with floor(N/d)=q, accumulate q*(prefix[r]-prefix[l-1]).
    There are at most2*floor(sqrtN) blocks. Accumulators are Python integers;
    the proved int64 bound applies to stored prefixes only.
    """
    if type(source) is not Source or type(N) is not int or not 1 <= N <= source.max_n:
        raise ValueError('source query integer1..max_n')
    meter = _meter(meter)
    before = meter.operations
    center = up = down = blocks = 0
    left = 1
    while left <= N:
        quotient = N//left
        right = N//quotient
        center += quotient*(int(source.prefix_w[right])-int(source.prefix_w[left-1]))
        up += quotient*(int(source.prefix_up[right])-int(source.prefix_up[left-1]))
        down += quotient*(int(source.prefix_down[right])-int(source.prefix_down[left-1]))
        left = right+1
        blocks += 1
        meter.primitives['hyperbola_blocks'] += 1
        meter.primitives['integer_accumulations'] += 3
        meter.charge(32+abs(center).bit_length()+up.bit_length()+down.bit_length())
    if blocks > 2*math.isqrt(N):
        raise ArithmeticError('hyperbola block complexity invariant')
    return {'schema': 'prime-scale-A-dyadic-enclosure-v1', 'alpha': source.alpha,
            'N': N, 'dyadic_bits': source.bits, 'denominator': 1 << source.bits,
            'center_numerator': center,
            'downward_uncertainty_count': down, 'upward_uncertainty_count': up,
            'lower_numerator': center-down, 'upper_numerator': center+up,
            'hyperbola_blocks': blocks, 'work_operations': meter.operations-before,
            'endpoint_encoding': 'exact numerator /2^dyadic_bits; closed conservative enclosure',
            'integer_accumulator_type': 'Python int; stored prefixes int64 with proved preflight',
            'independent_source_verified_here': False,
            'unrounded_mathematical_sum_enclosed': True,
            'all_scale_bound_proved': False, 'float_admission_used': False}
