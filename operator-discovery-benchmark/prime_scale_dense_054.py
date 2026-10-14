"""Dense exact algebra on supplied, previously admitted 053 source prefixes.

No atom, logarithm or Mobius sieve is recomputed. Source quantization admission
is inherited from its external receipt; this layer checks representation and
convolution identities, and exposes finite witnesses for independent replay.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
import math
import time
import numpy as np

MAX_N = 2_000_000
MAX_BITS = 40
MAX_INPUT_BITS = 4096
INT64_MAX = (1 << 63)-1
MAX_BYTES = 4*1024**3


class Meter:
    def __init__(self, cap=20_000_000_000, seconds=7200):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer work cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite dense deadline')
        self.cap, self.operations, self.deadline = cap, 0, time.monotonic()+seconds
        self.peak_bytes_estimate = 0
        self.primitives = {name: 0 for name in (
            'source_prefix_entries_validated', 'recovered_difference_entries',
            'convolution_center_entries', 'convolution_up_entries',
            'convolution_down_entries', 'summatory_prefix_entries',
            'new_scales_tested', 'filter_terms', 'exact_squared_comparisons')}

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('dense scale audit work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('dense scale audit deadline')

    def reserve(self, amount):
        if type(amount) is not int or not 0 <= amount <= MAX_BYTES:
            raise MemoryError('dense scale audit prospective memory cap')
        self.peak_bytes_estimate = max(self.peak_bytes_estimate, amount)
        self.charge()

    def counts(self):
        return {'operations': self.operations, 'peak_bytes_estimate': self.peak_bytes_estimate,
                'total_primitive_counts': dict(self.primitives)}


def _meter(meter):
    return meter if meter is not None else Meter()


def _alpha(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational exponent string')
    try:
        value = Q(text)
    except (ValueError, ZeroDivisionError):
        raise ValueError('canonical rational exponent') from None
    if str(value) != text or not 0 < value < 1:
        raise ValueError('canonical alpha strictly between0 and1')
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_INPUT_BITS:
        raise OverflowError('dense exponent bit cap')
    meter.charge(1+abs(value.numerator).bit_length()+value.denominator.bit_length())
    return value


def resource_preflight(max_n, bits, meter=None):
    """Sufficient signed-int64 guard for every convolution partial sum.

    |w_d|<=ell*2^bits and sum_(d<=X)floor(X/d)<=X*(1+logX)
    <=X*(1+ell), ell=X.bit_length(). This also bounds every summatory
    prefix and arbitrary intermediate subset, retaining all signs.
    """
    meter = _meter(meter)
    if type(max_n) is not int or not 1 <= max_n <= MAX_N:
        raise ValueError('dense horizon1..2000000')
    if type(bits) is not int or not 1 <= bits <= MAX_BITS:
        raise ValueError('integer dyadic bits1..40')
    ell = max_n.bit_length()
    bound = max_n*ell*(1+ell)*(1 << bits)
    meter.charge(32+bound.bit_length())
    if bound > INT64_MAX:
        raise OverflowError('proved dense absolute summatory bound exceeds int64')
    estimate = 112*(max_n+1)+16*1024**2
    meter.reserve(estimate)
    return {'max_n': max_n, 'bits': bits, 'ell': ell,
            'center_abs_upper_integer': bound,
            'uncertainty_upper_integer': max_n*(1+ell),
            'int64_max': INT64_MAX, 'estimated_peak_bytes': estimate,
            'persistent_dense_array_bytes': 24*(max_n+1),
            'overflow_preflight_proved': True,
            'proof': 'sum_abs<=ell*2^bits*sum_floor<=X*ell*(1+ell)*2^bits<2^63'}


def _counts_delta(before, after):
    return {'operations': after['operations']-before['operations'],
            'peak_bytes_estimate': after['peak_bytes_estimate'],
            'total_primitive_counts': {key: after['total_primitive_counts'][key]-before['total_primitive_counts'][key]
                                      for key in after['total_primitive_counts']}}


@dataclass(frozen=True)
class DenseSource:
    alpha: str
    max_n: int
    bits: int
    Acenter: np.ndarray
    Adown: np.ndarray
    Aup: np.ndarray
    overflow_certificate: dict
    construction_counts: dict

    def __post_init__(self):
        for array in (self.Acenter, self.Adown, self.Aup):
            if not isinstance(array, np.ndarray) or array.dtype != np.int64 or array.shape != (self.max_n+1,):
                raise ValueError('dense int64 array exact domain')
            array.flags.writeable = False

    def __reduce__(self):
        return (DenseSource, (self.alpha, self.max_n, self.bits, self.Acenter,
                             self.Adown, self.Aup, self.overflow_certificate,
                             self.construction_counts))

    def metadata(self):
        return {'schema': 'prime-scale-dense-source-v1', 'alpha': self.alpha,
                'max_n': self.max_n, 'dyadic_bits': self.bits,
                'arrays': {name: {'dtype': 'int64', 'domain': [0, self.max_n], 'writeable': False}
                           for name in ('Acenter', 'Adown', 'Aup')},
                'center_identity': 'Acenter[N]=sum_(d<=N)w[d]*floor(N/d)',
                'uncertainty_identity': 'Adown/Aup[N]=sum_(d<=N)down/up[d]*floor(N/d)',
                'construction': 'exact stride Dirichlet convolution with1, then cumulative sum',
                'overflow_certificate': dict(self.overflow_certificate),
                'counts': self.construction_counts,
                'persistent_array_bytes': self.Acenter.nbytes+self.Adown.nbytes+self.Aup.nbytes,
                'source_chain_replayed_here': False,
                'source_admission': 'supplied053 prefix receipt; actual log/Mobius admission external',
                'new_atoms_evaluated': 0, 'artifact_hashes_used': False,
                'all_scale': False}


def _validate_fields(fields, meter):
    expected = {'alpha', 'max_n', 'bits', 'mu', 'prefix_w', 'prefix_up', 'prefix_down', 'metadata'}
    if type(fields) is not dict or set(fields) != expected:
        raise ValueError('dense source fields exactly alpha,max_n,bits,mu,prefix_w/up/down,metadata')
    _alpha(fields['alpha'], meter)
    X, bits = fields['max_n'], fields['bits']
    guard = resource_preflight(X, bits, meter)
    arrays = {}
    for name in ('mu', 'prefix_w', 'prefix_up', 'prefix_down'):
        array = fields[name]
        dtype = np.int8 if name == 'mu' else np.int64
        if not isinstance(array, np.ndarray) or array.dtype != dtype or array.shape != (X+1,):
            raise ValueError('supplied prefix binary dtype/domain')
        arrays[name] = array
    metadata = fields['metadata']
    if (type(metadata) is not dict or metadata.get('schema') != 'prime-scale-fractional-source-v1'
            or metadata.get('alpha') != fields['alpha'] or metadata.get('max_n') != X
            or metadata.get('dyadic_bits') != bits):
        raise ValueError('matching053 source metadata required')
    array_metadata = metadata.get('arrays')
    if type(array_metadata) is not dict:
        raise ValueError('source array metadata')
    for name in arrays:
        row = array_metadata.get(name)
        if (type(row) is not dict or row.get('dtype') != ('int8' if name == 'mu' else 'int64')
                or row.get('domain') != [0, X] or row.get('writeable') is not False
                or (name != 'mu' and row.get('prefix_includes_index') is not True)):
            raise ValueError('source array metadata dtype/domain')
    source_guard = metadata.get('overflow_certificate')
    ell = X.bit_length()
    prefix_bound = (X-1)*ell*(1 << bits)
    if (type(source_guard) is not dict or source_guard.get('max_n') != X
            or source_guard.get('bits') != bits or source_guard.get('int64_max') != INT64_MAX
            or source_guard.get('log_power_upper_integer') != ell
            or source_guard.get('atom_abs_upper_integer') != ell*(1 << bits)
            or source_guard.get('prefix_abs_upper_integer') != prefix_bound
            or source_guard.get('uncertainty_prefix_upper_integer') != X-1
            or source_guard.get('overflow_preflight_proved') is not True):
        raise ValueError('matching source int64 overflow certificate')
    mu = arrays['mu']
    if int(mu[0]) != 0 or int(mu[1]) != 1 or not np.all((mu >= -1) & (mu <= 1)):
        raise ValueError('source mu range/unit')
    for name in ('prefix_w', 'prefix_up', 'prefix_down'):
        array = arrays[name]
        if int(array[0]) or int(array[1]):
            raise ValueError('zero source unit atom/prefix')
        bound = prefix_bound if name == 'prefix_w' else X-1
        if np.any(array > bound) or np.any(array < (-bound if name == 'prefix_w' else 0)):
            raise ValueError('source prefix outside proved bounds')
    # The stronger dense guard also gives2*source prefix bound<int64max, so
    # differences themselves cannot overflow even on subsequently rejected data.
    weights = np.empty(X+1, dtype=np.int64)
    up = np.empty(X+1, dtype=np.int64)
    down = np.empty(X+1, dtype=np.int64)
    for name, out in (('prefix_w', weights), ('prefix_up', up), ('prefix_down', down)):
        out[0] = 0
        np.subtract(arrays[name][1:], arrays[name][:-1], out=out[1:])
    if np.any(up < 0) or np.any(up > 1) or np.any(down < 0) or np.any(down > 1):
        raise ValueError('binary uncertainty atom increments')
    expected_up, expected_down = mu == -1, mu == 1
    expected_up[:2] = expected_down[:2] = False
    if not np.array_equal(up != 0, expected_up) or not np.array_equal(down != 0, expected_down):
        raise ValueError('uncertainty increments disagree with supplied mu')
    if (np.any(weights > ell*(1 << bits)) or np.any(weights < -ell*(1 << bits))
            or np.any(weights[up != 0] < 0) or np.any(weights[down != 0] > 0)
            or np.any(weights[(up+down) == 0] != 0)):
        raise ValueError('signed source atom range/mu consistency')
    refinements = metadata.get('atom_refinement_counts')
    if (type(refinements) is not dict or set(refinements) != {'128', '192', '256'}
            or any(type(v) is not int or v < 0 for v in refinements.values())
            or sum(refinements.values()) != int(np.count_nonzero(mu[2:]))):
        raise ValueError('source atom admission counts')
    meter.primitives['source_prefix_entries_validated'] += 4*(X+1)
    meter.primitives['recovered_difference_entries'] += 3*(X+1)
    meter.charge(64*(X+1))
    return weights, up, down, guard


def dense_source(fields, meter=None):
    """Use existing quantized prefixes; recompute no atom or arithmetic source."""
    meter = _meter(meter)
    before = meter.counts()
    weights, up, down, guard = _validate_fields(fields, meter)
    X = fields['max_n']
    center_A, up_A, down_A = [np.zeros(X+1, dtype=np.int64) for _ in range(3)]
    for d in range(2, X+1):
        meter.charge(4)
        entries = X//d
        for input_array, output_array, counter in (
                (weights, center_A, 'convolution_center_entries'),
                (up, up_A, 'convolution_up_entries'),
                (down, down_A, 'convolution_down_entries')):
            value = int(input_array[d])
            if value:
                output_array[d::d] += value
                meter.primitives[counter] += entries
                meter.charge(8+entries)
    for array in (center_A, down_A, up_A):
        np.cumsum(array, dtype=np.int64, out=array)
        meter.primitives['summatory_prefix_entries'] += X+1
        meter.charge(2*(X+1))
    return DenseSource(fields['alpha'], X, fields['bits'], center_A, down_A, up_A,
                       guard, _counts_delta(before, meter.counts()))


def _selected(selected, dense, meter):
    if type(selected) is not dict or set(selected) != {'id', 'request'}:
        raise ValueError('selected entry exactly id,request')
    if type(selected['id']) is not str or not 1 <= len(selected['id']) <= 250:
        raise ValueError('bounded selected id')
    request = selected['request']
    if type(request) is not dict or set(request) != {'alpha', 'q', 'coefficients', 'bound'}:
        raise ValueError('request exactly alpha,q,coefficients,bound')
    alpha = _alpha(request['alpha'], meter)
    if request['alpha'] != dense.alpha:
        raise ValueError('filter alpha must match dense source')
    q, coefficients = request['q'], request['coefficients']
    if type(q) is not int or not 2 <= q <= MAX_N:
        raise ValueError('positive prime scale within resource domain')
    for divisor in range(2, math.isqrt(q)+1):
        meter.charge(4)
        if q % divisor == 0:
            raise ValueError('scale q must be prime')
    if (type(coefficients) is not list or not 1 <= len(coefficients) <= 4
            or any(type(c) is not int or abs(c) > 64 for c in coefficients)
            or coefficients[-1] == 0):
        raise ValueError('integer filter coefficients, degree<=3, absolute coefficients<=64, nonzero final coefficient')
    bound = request['bound']
    if (type(bound) is not dict or set(bound) != {'C', 'log_power', 'minimum', 'normalization'}
            or bound['C'] != '2' or bound['log_power'] != '0'
            or bound['normalization'] != 'divide_by_alpha'
            or type(bound['minimum']) is not int or not 2 <= bound['minimum'] <= MAX_N):
        raise ValueError('this exact squared evaluator requires C2,eta0,divide_by_alpha,integer minimum>=2')
    return request, alpha


def _filter_interval(request, dense, N, meter, include_rows=False):
    center = lower = upper = 0
    rows = []
    scale = N
    for j, c in enumerate(request['coefficients']):
        a = int(dense.Acenter[scale])
        down, up = int(dense.Adown[scale]), int(dense.Aup[scale])
        lo, hi = a-down, a+up
        center += c*a
        lower += c*(lo if c >= 0 else hi)
        upper += c*(hi if c >= 0 else lo)
        if include_rows:
            rows.append({'j': j, 'scale': scale, 'coefficient': c,
                         'Acenter': a, 'Adown': down, 'Aup': up,
                         'lower_numerator': lo, 'upper_numerator': hi})
        scale *= request['q']
        meter.primitives['filter_terms'] += 1
        meter.charge(32+abs(center).bit_length()+abs(lower).bit_length()+abs(upper).bit_length())
    if lower > upper:
        raise ArithmeticError('signed filter interval order')
    return center, lower, upper, rows


def first_counterexample(selected, dense, skip_scales, meter=None):
    """Scan all unobserved scales ascending; no floats or approximate roots.

    T endpoints are accumulated as Python integers, so no extra int64 filter
    assumption is introduced. Strict failure needs a positive absolute lower
    bound whose exact square exceeds4*N*alpha^2. A straddling interval remains
    unresolved unless its complete absolute upper bound passes the claim.
    """
    if type(dense) is not DenseSource:
        raise ValueError('DenseSource required')
    meter = _meter(meter)
    before = meter.counts()
    request, alpha = _selected(selected, dense, meter)
    if (type(skip_scales) not in (list, tuple, set, frozenset)
            or any(type(n) is not int or not 1 <= n <= MAX_N for n in skip_scales)):
        raise ValueError('declared skip scales: positive integer collection')
    skips = set(skip_scales)
    degree = len(request['coefficients'])-1
    minimum, maximum = request['bound']['minimum'], dense.max_n//(request['q']**degree)
    total = max(0, maximum-minimum+1)
    skipped = sum(minimum <= n <= maximum for n in skips)
    new_total = total-skipped
    tested = passes = unresolved = 0
    witness = None
    scale_factor = 4*alpha.numerator**2*(1 << (2*dense.bits))
    alpha_denominator_squared = alpha.denominator**2
    for N in range(minimum, maximum+1):
        if N in skips:
            continue
        center, lower, upper, _ = _filter_interval(request, dense, N, meter)
        lower_abs = lower if lower > 0 else -upper if upper < 0 else 0
        upper_abs = max(abs(lower), abs(upper))
        left = lower_abs**2*alpha_denominator_squared
        right = N*scale_factor
        meter.primitives['exact_squared_comparisons'] += 1
        meter.primitives['new_scales_tested'] += 1
        meter.charge(32+left.bit_length()+right.bit_length())
        tested += 1
        if left > right:
            _, _, _, rows = _filter_interval(request, dense, N, meter, include_rows=True)
            witness = {'schema': 'prime-scale-dense-counterexample-v1',
                       'id': selected['id'], 'request': request, 'N': N,
                       'source_max_n': dense.max_n,
                       'source_support_used': request['q']**degree*N,
                       'dyadic_bits': dense.bits, 'denominator': 1 << dense.bits,
                       'term_rows': rows,
                       'Tcenter': center, 'Tlower': lower, 'Tupper': upper,
                       'lower_abs_numerator': lower_abs,
                       'comparison': {'left': left, 'right': right, 'relation': '>',
                                      'formula': 'lower_abs^2*alpha_den^2 > 4*N*alpha_num^2*2^(2*bits)'},
                       'source_chain_replayed_here': False, 'all_scale': False,
                       'float_or_root_comparison_used': False}
            break
        upper_left = upper_abs**2*alpha_denominator_squared
        meter.primitives['exact_squared_comparisons'] += 1
        meter.charge(32+upper_left.bit_length()+right.bit_length())
        if upper_left <= right:
            passes += 1
        else:
            unresolved += 1
    return {'schema': 'prime-scale-dense-finite-audit-v1', 'id': selected['id'],
            'request': request, 'source_max_n': dense.max_n,
            'minimum': minimum, 'maximum': maximum,
            'domain_scale_count': total, 'skipped_preobserved_count': skipped,
            'new_scales_total': new_total, 'new_scales_tested': tested,
            'finite_pass_count': passes, 'unresolved_count': unresolved,
            'strict_counterexample_count': int(witness is not None),
            'untested_after_counterexample': new_total-tested,
            'first_counterexample': witness,
            'status': 'FINITE_COUNTEREXAMPLE' if witness else (
                'NO_NEW_SCALES' if new_total == 0 else
                'NO_COUNTEREXAMPLE_WITH_UNRESOLVED' if unresolved else 'FINITE_ALL_NEW_SCALES_PASS'),
            'counts': _counts_delta(before, meter.counts()),
            'skip_scales_in_domain': sorted(n for n in skips if minimum <= n <= maximum),
            'source_chain_replayed_here': False, 'all_scale': False,
            'observations_outside_declared_dense_domain': False,
            'exact_integer_squared_comparisons': True}
