"""Boolean prime-insertion prefixes from previously admitted dense K data.

No logarithm, Mobius atom, or saved scientific array is read at import. Actual
logarithmic-source admission is external. Exact integer subset cancellation
licenses the tighter correlated error rule, including the shifted unit atom.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
import math
import time
import numpy as np

MAX_N = 2_000_000
MAX_BITS = 40
MAX_PARAMETER_BITS = 4096
MAX_RESULT_BITS = 8192
MAX_PRIMES = 8
MAX_SETS = 128
MAX_FILTER_TERMS = 17
INT64_MAX = (1 << 63)-1
MAX_BYTES = 4*1024**3


class Meter:
    def __init__(self, cap=20_000_000_000, seconds=7200):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer work cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite insertion deadline')
        self.cap, self.operations, self.deadline = cap, 0, time.monotonic()+seconds
        self.peak_bytes_estimate = 0
        self.primitives = {name: 0 for name in (
            'prime_trial_divisions', 'source_entries_validated', 'difference_entries',
            'subset_vector_entries', 'mask_entries', 'prefix_entries',
            'boolean_product_pairs', 'source_cache_hits', 'filter_terms')}

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('prime insertion work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('prime insertion deadline')

    def reserve(self, amount):
        if type(amount) is not int or not 0 <= amount <= MAX_BYTES:
            raise MemoryError('prime insertion prospective memory cap')
        self.peak_bytes_estimate = max(self.peak_bytes_estimate, amount)
        self.charge()

    def counts(self):
        return {'operations': self.operations, 'peak_bytes_estimate': self.peak_bytes_estimate,
                'total_primitive_counts': dict(self.primitives)}


def _meter(meter):
    return meter if meter is not None else Meter()


def _alpha(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational alpha')
    try:
        value = Q(text)
    except (ValueError, ZeroDivisionError):
        raise ValueError('canonical rational alpha') from None
    if str(value) != text or not 0 < value < 1:
        raise ValueError('canonical alpha strictly between0 and1')
    if max(value.numerator.bit_length(), value.denominator.bit_length()) > MAX_PARAMETER_BITS:
        raise OverflowError('insertion alpha bit cap')
    meter.charge(1+value.numerator.bit_length()+value.denominator.bit_length())
    return value


def _prime(prime, meter):
    if type(prime) is not int or not 2 <= prime <= MAX_N:
        raise ValueError('actual integer prime within resource domain')
    for divisor in range(2, math.isqrt(prime)+1):
        meter.primitives['prime_trial_divisions'] += 1
        meter.charge(4)
        if prime % divisor == 0:
            raise ValueError('actual prime required')
    return prime


def normal_form(primes, meter=None):
    """Boolean operator normal form; repetitions collapse by D_p^2=D_p.

    Bank inputs themselves must already be sorted and distinct. This separate
    helper licenses syntactic reduction conditional on radical invariance.
    """
    meter = _meter(meter)
    if type(primes) not in (list, tuple) or len(primes) > 64:
        raise ValueError('bounded insertion word')
    out = tuple(sorted({_prime(p, meter) for p in primes}))
    if len(out) > MAX_PRIMES:
        raise ValueError('canonical prime set resource cap')
    return out


def _set(primes, meter):
    normalized = normal_form(primes, meter)
    if tuple(primes) != normalized:
        raise ValueError('input prime set must be canonical sorted/distinct')
    return normalized


def _subsets(primes):
    rows = []
    for mask in range(1 << len(primes)):
        subset = tuple(p for j, p in enumerate(primes) if mask & (1 << j))
        rows.append((mask, subset, math.prod(subset), (-1)**len(subset)))
    return rows


def boolean_certificate(alpha, primes, meter=None):
    """Checkable exact integer Boolean polynomial, conditional source identity."""
    meter = _meter(meter)
    _alpha(alpha, meter)
    primes = _set(primes, meter)
    product = math.prod(primes)
    if product > MAX_N:
        raise OverflowError('prime-set product resource cap')
    rows = _subsets(primes)
    square = [0]*len(rows)
    for mask, _, _, sign in rows:
        for other, _, _, other_sign in rows:
            square[mask | other] += sign*other_sign
            meter.primitives['boolean_product_pairs'] += 1
            meter.charge(4)
    cancellation = []
    for mask, subset, divisor, mu in rows:
        coefficient = sum(sign for upper, _, _, sign in rows if upper & mask == mask)
        meter.charge(4*len(rows))
        cancellation.append({'primes': list(subset), 'product': divisor, 'mu': mu,
                             'superset_sign_sum': coefficient,
                             'atom_coefficient': mu*coefficient})
    if any(square[mask] != sign for mask, _, _, sign in rows):
        raise ArithmeticError('Boolean idempotence polynomial')
    if any(v['atom_coefficient'] != int(v['product'] == product) for v in cancellation):
        raise ArithmeticError('common-atom subset cancellation polynomial')
    return {'schema': 'prime-insertion-boolean-certificate-v1',
            'alpha': alpha, 'primes': list(primes), 'product': product,
            'domain_minimum': 2,
            'subset_terms': [{'primes': list(subset), 'product': divisor, 'coefficient': sign}
                             for _, subset, divisor, sign in rows],
            'atom_cancellation_rows': cancellation,
            'square_reduction': [{'primes': list(subset), 'product': divisor, 'coefficient': square[mask]}
                                 for mask, subset, divisor, _ in rows],
            'source_kernel': 'K_alpha(n)=-sum_(d|n)mu(d)*(log d)^alpha',
            'source_condition': 'actual ordinary-mu common atom function; radical invariance',
            'operator': 'D_S=prod_(p in S)(I-E_p), E_p K(n)=K(p*n)',
            'boolean_relations': 'E_p^2=E_p; D_p^2=D_p; distinct prime operators commute',
            'shared_prime_zero': 'gcd(n,product)>1 implies D_S K(n)=0',
            'coprime_shift_identity': 'D_S K(n)=-sum_(d|n)mu(d)*(log(product*d))^alpha',
            'quantized_shift_identity': 'D_S K_center(n)=-sum_(d|n)mu(d)*floor(2^bits*(log(product*d))^alpha)',
            'coprime_upward_uncertainty': 'K_up(n)',
            'coprime_downward_uncertainty': 'K_down(n)+1_(product>1)',
            'prefix_definition': 'B_S(X)=sum_(2<=n<=X)D_S K(n)',
            'shifted_prefix_unit_correction': '+(log(product))^alpha; zero for empty set',
            'unit_n1_excluded': True, 'empty_set_identity': True,
            'normal_form': 'sorted distinct prime set; repeated insertions collapse',
            'source_chain_replayed_here': False, 'all_scale_bound_proved': False,
            'new_atoms_evaluated': 0}


def _delta(before, after):
    return {'operations': after['operations']-before['operations'],
            'peak_bytes_estimate': after['peak_bytes_estimate'],
            'total_primitive_counts': {k: after['total_primitive_counts'][k]-before['total_primitive_counts'][k]
                                      for k in after['total_primitive_counts']}}


def _fields(fields, meter):
    if type(fields) is not dict or set(fields) != {'alpha', 'max_n', 'bits', 'Acenter', 'Adown', 'Aup', 'metadata'}:
        raise ValueError('insertion fields exactly alpha,max_n,bits,Acenter,Adown,Aup,metadata')
    _alpha(fields['alpha'], meter)
    X, bits = fields['max_n'], fields['bits']
    if type(X) is not int or not 1 <= X <= MAX_N or type(bits) is not int or not 1 <= bits <= MAX_BITS:
        raise ValueError('source horizon/rounding resource domain')
    meter.reserve(112*(X+1)+16*1024**2)
    ell = X.bit_length()
    bound = X*ell*(1+ell)*(1 << bits)
    uncertainty_bound = X*(1+ell)
    if bound > INT64_MAX:
        raise OverflowError('dense source theoretical int64 bound')
    metadata = fields['metadata']
    if (type(metadata) is not dict or metadata.get('schema') != 'prime-scale-dense-source-v1'
            or metadata.get('alpha') != fields['alpha'] or metadata.get('max_n') != X
            or metadata.get('dyadic_bits') != bits):
        raise ValueError('matching dense source metadata')
    guard = metadata.get('overflow_certificate')
    if (type(guard) is not dict or guard.get('center_abs_upper_integer') != bound
            or guard.get('uncertainty_upper_integer') != uncertainty_bound
            or guard.get('max_n') != X or guard.get('bits') != bits or guard.get('ell') != ell
            or guard.get('int64_max') != INT64_MAX or guard.get('overflow_preflight_proved') is not True):
        raise ValueError('dense source overflow metadata')
    arrays = []
    if type(metadata.get('arrays')) is not dict:
        raise ValueError('dense source array metadata mapping')
    for name in ('Acenter', 'Adown', 'Aup'):
        array = fields[name]
        row = metadata.get('arrays', {}).get(name)
        if (not isinstance(array, np.ndarray) or array.dtype != np.int64 or array.shape != (X+1,)
                or type(row) is not dict or row.get('dtype') != 'int64'
                or row.get('domain') != [0, X] or row.get('writeable') is not False):
            raise ValueError('dense array binary dtype/domain')
        if int(array[0]) or int(array[1]):
            raise ValueError('zero dense source unit required')
        limit = bound if name == 'Acenter' else uncertainty_bound
        if np.any(array > limit) or np.any(array < (-limit if name == 'Acenter' else 0)):
            raise ValueError('dense source array bounds')
        arrays.append(array)
    difference_bound = int(np.max(arrays[0]))-int(np.min(arrays[0]))
    if difference_bound > INT64_MAX:
        raise OverflowError('exact observed range does not license int64 differences')
    recovered = []
    for array in arrays:
        values = np.empty(X+1, dtype=np.int64)
        values[0] = 0
        np.subtract(array[1:], array[:-1], out=values[1:])
        recovered.append(values)
    if np.any(recovered[1] < 0) or np.any(recovered[2] < 0):
        raise ValueError('nonnegative recovered uncertainty coefficients')
    meter.primitives['source_entries_validated'] += 3*(X+1)
    meter.primitives['difference_entries'] += 3*(X+1)
    meter.charge(48*(X+1))
    return tuple(arrays), tuple(recovered)


@dataclass(frozen=True)
class InsertionSource:
    alpha: str
    primes: tuple
    product: int
    max_n: int
    bits: int
    Bcenter: np.ndarray
    Bdown: np.ndarray
    Bup: np.ndarray
    certificate: dict
    overflow_certificate: dict

    def __post_init__(self):
        for array in (self.Bcenter, self.Bdown, self.Bup):
            if not isinstance(array, np.ndarray) or array.dtype != np.int64 or array.shape != (self.max_n+1,):
                raise ValueError('insertion int64 array domain')
            array.flags.writeable = False

    def __reduce__(self):
        return (InsertionSource, (self.alpha, self.primes, self.product, self.max_n, self.bits,
                                 self.Bcenter, self.Bdown, self.Bup, self.certificate,
                                 self.overflow_certificate))


@dataclass(frozen=True)
class InsertionBank:
    alpha: str
    max_n: int
    bits: int
    sources: dict
    construction_counts: dict

    def metadata(self):
        return {'schema': 'prime-insertion-bank-v1', 'alpha': self.alpha,
                'source_max_n': self.max_n, 'dyadic_bits': self.bits,
                'sources': [{'primes': list(S), 'product': src.product, 'max_n': src.max_n,
                             'overflow_certificate': src.overflow_certificate,
                             'unit_n1_excluded': True, 'correlated_error_rule_used': True}
                            for S, src in self.sources.items()],
                'counts': self.construction_counts, 'new_atoms_evaluated': 0,
                'source_chain_replayed_here': False, 'all_scale_bound_proved': False,
                'cache_key': 'literal canonical distinct prime tuple', 'artifact_hashes_used': False}


def build_insertion_sources(fields, prime_sets, meter=None):
    """Cache each canonical set once; share original arrays for the empty set.

    For coprime n, exact common-atom cancellation leaves only atoms at R*d.
    Their signs are -mu(d): old K_up/K_down count every nonunit error, and
    one extra downward unit pays log(R). Shared-prime values are exact zero.
    Integer preflight covers every signed subset intermediate and prefix.
    """
    meter = _meter(meter)
    before = meter.counts()
    if type(prime_sets) not in (list, tuple) or not 1 <= len(prime_sets) <= MAX_SETS:
        raise ValueError('bounded nonempty list of canonical prime sets')
    sets = [_set(primes, meter) for primes in prime_sets]
    unique = list(dict.fromkeys(sets))
    arrays, recovered = _fields(fields, meter)
    X, bits = fields['max_n'], fields['bits']
    for primes in unique:
        if math.prod(primes) > X:
            raise ValueError('prime-set product exceeds available source support')
    estimate = (112*(X+1)+24*sum(X//math.prod(S)+1 for S in unique)
                +4096*sum(1 << len(S) for S in unique)+16*1024**2)
    meter.reserve(estimate)
    Kcenter, Kdown, Kup = recovered
    center_abs = max(abs(int(np.min(Kcenter))), abs(int(np.max(Kcenter))))
    max_down, max_up = int(np.max(Kdown)), int(np.max(Kup))
    sources = {}
    for primes in sets:
        if primes in sources:
            meter.primitives['source_cache_hits'] += 1
            meter.charge()
            continue
        certificate = boolean_certificate(fields['alpha'], primes, meter)
        R, horizon = math.prod(primes), X//math.prod(primes)
        if not primes:
            sources[primes] = InsertionSource(fields['alpha'], primes, R, horizon, bits,
                                             *arrays, certificate,
                                             {'source_arrays_reused': True,
                                              'int64_admitted_by_dense_source': True})
            continue
        mask = np.ones(horizon+1, dtype=np.bool_)
        mask[:2] = False
        for prime in primes:
            mask[prime::prime] = False
        active = int(np.count_nonzero(mask))
        terms = 1 << len(primes)
        combo_bound = terms*center_abs
        prefix_bound = active*combo_bound
        down_bound, up_bound = active*(max_down+1), active*max_up
        if max(combo_bound, prefix_bound, down_bound, up_bound) > INT64_MAX:
            raise OverflowError('insertion subset/prefix int64 preflight')
        center = np.zeros(horizon+1, dtype=np.int64)
        for _, _, divisor, sign in _subsets(primes):
            center[2:] += sign*Kcenter[2*divisor:(horizon+1)*divisor:divisor]
            meter.primitives['subset_vector_entries'] += max(0, horizon-1)
            meter.charge(8+max(0, horizon-1))
        if np.any(center[~mask] != 0):
            raise ValueError('provided rounded source violates shared-prime zero identity')
        down = np.where(mask, Kdown[:horizon+1]+1, 0)
        up = np.where(mask, Kup[:horizon+1], 0)
        meter.primitives['mask_entries'] += horizon+1
        meter.charge(8*(horizon+1))
        for array in (center, down, up):
            np.cumsum(array, dtype=np.int64, out=array)
            meter.primitives['prefix_entries'] += horizon+1
            meter.charge(2*(horizon+1))
        sources[primes] = InsertionSource(fields['alpha'], primes, R, horizon, bits,
                                         center, down, up, certificate,
                                         {'source_arrays_reused': False,
                                          'recovered_K_abs_upper': center_abs,
                                          'subset_intermediate_abs_upper': combo_bound,
                                          'prefix_abs_upper': prefix_bound,
                                          'down_prefix_upper': down_bound, 'up_prefix_upper': up_bound,
                                          'coprime_indices_count': active,
                                          'int64_max': INT64_MAX, 'overflow_preflight_proved': True})
    return InsertionBank(fields['alpha'], X, bits, sources, _delta(before, meter.counts()))


def evaluate_filter(bank, S, q, coefficients, N, meter=None):
    """Exact normalized closed interval for sum c_j B_S(q^j*N)/alpha."""
    if type(bank) is not InsertionBank:
        raise ValueError('InsertionBank required')
    meter = _meter(meter)
    before = meter.counts()
    primes = _set(S, meter)
    if primes not in bank.sources:
        raise ValueError('prime set not built in this bank')
    source = bank.sources[primes]
    _prime(q, meter)
    if (type(coefficients) not in (list, tuple) or not 1 <= len(coefficients) <= MAX_FILTER_TERMS
            or any(type(c) is not int or abs(c) > 64 for c in coefficients)
            or coefficients[-1] == 0):
        raise ValueError('bounded signed integer filter with nonzero last coefficient')
    if type(N) is not int or N < 2 or q**(len(coefficients)-1)*N > source.max_n:
        raise ValueError('filter integer scale>=2 within complete insertion support')
    alpha = _alpha(bank.alpha, meter)
    center = lower = upper = 0
    rows, scale = [], N
    for j, coefficient in enumerate(coefficients):
        value = int(source.Bcenter[scale])
        down, up = int(source.Bdown[scale]), int(source.Bup[scale])
        lo, hi = value-down, value+up
        center += coefficient*value
        lower += coefficient*(lo if coefficient >= 0 else hi)
        upper += coefficient*(hi if coefficient >= 0 else lo)
        rows.append({'j': j, 'scale': scale, 'coefficient': coefficient,
                     'Bcenter': value, 'Bdown': down, 'Bup': up,
                     'lower_numerator': lo, 'upper_numerator': hi})
        meter.primitives['filter_terms'] += 1
        meter.charge(32+abs(center).bit_length()+abs(lower).bit_length()+abs(upper).bit_length())
        scale *= q
    denominator = 1 << source.bits
    normalized_lower = Q(lower*alpha.denominator, denominator*alpha.numerator)
    normalized_upper = Q(upper*alpha.denominator, denominator*alpha.numerator)
    for value in (normalized_lower, normalized_upper):
        if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_RESULT_BITS:
            raise OverflowError('normalized insertion interval bit cap')
        meter.charge(abs(value.numerator).bit_length()+value.denominator.bit_length()+1)
    return {'schema': 'prime-insertion-filter-interval-v1',
            'request': {'alpha': bank.alpha, 'primes': list(primes), 'q': q,
                        'coefficients': list(coefficients), 'N': N},
            'lower': str(normalized_lower), 'upper': str(normalized_upper),
            'normalization': 'divide_by_alpha',
            'center_numerator': center, 'lower_numerator': lower, 'upper_numerator': upper,
            'denominator': denominator, 'dyadic_bits': source.bits,
            'source_max_n': bank.max_n, 'insertion_max_n': source.max_n,
            'source_support_used': source.product*q**(len(coefficients)-1)*N,
            'term_rows': rows, 'counts': _delta(before, meter.counts()),
            'source_chain_replayed_here': False, 'all_scale_bound_proved': False,
            'new_atoms_evaluated': 0, 'float_admission_used': False}
