"""Finite Arb evidence for rational fractional logarithmic divisor kernels.

No all-scale sign theorem is implemented or imported. The ordinary Mobius
weights are derived from a trial factorization of each supplied integer.
Caches are literal functional tuples; no source arrays or artifact hashes.
"""
from fractions import Fraction as Q
import math
import time
from flint import arb, ctx

MAX_INPUT_BITS = 4096
MAX_N = 2**32-1
MAX_DIVISORS = 4096
MAX_CANDIDATES = 20000
MAX_DENOMINATOR = 4096
MAX_NUMBERS = 1024
MAX_CACHE_BYTES = 2*1024**3
MAX_SEARCH_BYTES = 8*1024**3
DEFAULT_GRAMMAR = {'a_denominator': 7, 'alpha_denominator': 11, 'max_candidates': 4000}


class Meter:
    def __init__(self, cap=20_000_000_000, seconds=7200):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer operation cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite time cap')
        self.cap, self.operations, self.deadline = cap, 0, time.monotonic()+seconds
        self.factor_divisions = self.divisor_rows = self.log_evaluations = 0
        self.power_evaluations = self.cache_hits = self.requests = 0
        self.max_parameter_bits = self.peak_bytes_estimate = 0

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('fractional kernel work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('fractional kernel deadline')

    def rational(self, value):
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        if bits > MAX_INPUT_BITS:
            raise OverflowError('fractional kernel rational input bit cap')
        self.max_parameter_bits = max(self.max_parameter_bits, bits)
        self.charge(1+abs(value.numerator).bit_length()+value.denominator.bit_length())
        return value

    def reserve(self, amount):
        if type(amount) is not int or not 0 <= amount <= MAX_SEARCH_BYTES:
            raise MemoryError('fractional kernel prospective memory cap')
        self.peak_bytes_estimate = max(self.peak_bytes_estimate, amount)
        self.charge()

    def counts(self):
        return {name: getattr(self, name) for name in (
            'operations', 'factor_divisions', 'divisor_rows', 'log_evaluations',
            'power_evaluations', 'cache_hits', 'requests', 'max_parameter_bits',
            'peak_bytes_estimate')}


def _meter(meter):
    return meter if meter is not None else Meter()


def _rational(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational string')
    try:
        value = Q(text)
    except (ValueError, ZeroDivisionError):
        raise ValueError('canonical rational string') from None
    if str(value) != text:
        raise ValueError('canonical rational string')
    return meter.rational(value)


def _request(request, meter):
    if type(request) is not dict or set(request) != {'a', 'b', 'alpha', 'sign'}:
        raise ValueError('request exactly a,b,alpha,sign')
    a, b, alpha = [_rational(request[name], meter) for name in ('a', 'b', 'alpha')]
    sign = request['sign']
    if type(sign) is not int or sign not in (-1, 1):
        raise ValueError('integer sign plus or minus1')
    if a < 0 or b < 0 or a+b != 1 or a == b or not 0 < alpha <= 2:
        raise ValueError('nonnegative unequal a,b summing1; exponent in(0,2]')
    return a, b, alpha, sign


def _precision(precision):
    if type(precision) is not int or not 128 <= precision <= 1024:
        raise ValueError('integer Arb precision128..1024')
    return precision


def _number(n):
    if type(n) is not int or not 1 <= n <= MAX_N:
        raise ValueError('positive integer n within32-bit resource domain')
    return n


class KernelCache:
    """Bounded literal caches of factorization, logarithms, bases and atoms."""
    def __init__(self, max_bytes=MAX_CACHE_BYTES):
        if type(max_bytes) is not int or not 0 <= max_bytes <= MAX_CACHE_BYTES:
            raise ValueError('kernel cache byte limit0..2GiB')
        self.max_bytes, self.bytes_estimate = max_bytes, 0
        self.factors, self.logs, self.bases, self.atoms = {}, {}, {}, {}

    def store(self, table, key, value, size, meter):
        if size <= self.max_bytes-self.bytes_estimate:
            table[key] = value
            self.bytes_estimate += size
            meter.reserve(self.bytes_estimate)
        else:
            meter.reserve(self.bytes_estimate+size)
        return value

    def factors_of(self, n, meter):
        if n in self.factors:
            meter.cache_hits += 1
            meter.charge()
            return self.factors[n]
        remaining, factors, candidate = n, [], 2
        while candidate*candidate <= remaining:
            meter.factor_divisions += 1
            meter.charge(4+remaining.bit_length())
            if remaining % candidate == 0:
                exponent = 0
                while remaining % candidate == 0:
                    remaining //= candidate
                    exponent += 1
                    meter.factor_divisions += 1
                    meter.charge(4+remaining.bit_length())
                factors.append((candidate, exponent))
            candidate = 3 if candidate == 2 else candidate+2
        if remaining > 1:
            factors.append((remaining, 1))
        divisors = [(1, 1)]
        for prime, _ in factors:
            divisors += [(d*prime, -mu) for d, mu in divisors]
            meter.charge(8*len(divisors))
            if len(divisors) > MAX_DIVISORS:
                raise OverflowError('squarefree divisor resource cap')
        divisors.sort()
        result = (tuple(factors), tuple(divisors))
        return self.store(self.factors, n, result, 512+128*len(factors)+128*len(divisors), meter)

    def log_of(self, integer, precision, meter):
        key = (integer, precision)
        if key in self.logs:
            meter.cache_hits += 1
            meter.charge()
            return self.logs[key]
        meter.log_evaluations += 1
        meter.charge(32+precision*precision//16+integer.bit_length())
        value = arb(0) if integer == 1 else arb(integer).log()
        return self.store(self.logs, key, value, 512+8*((precision+7)//8), meter)

    def atom(self, n, d, a, b, alpha, precision, meter):
        # a,b and alpha are literal reduced numerator/denominator pairs.
        base_key = (n, d, (a.numerator, a.denominator),
                    (b.numerator, b.denominator), precision)
        key = base_key+((alpha.numerator, alpha.denominator),)
        if key in self.atoms:
            meter.cache_hits += 1
            meter.charge()
            return self.atoms[key]
        if base_key in self.bases:
            meter.cache_hits += 1
            meter.charge()
            base = self.bases[base_key]
        else:
            left, right = self.log_of(d, precision, meter), self.log_of(n//d, precision, meter)
            base = (arb(a.numerator)/a.denominator)*left + (arb(b.numerator)/b.denominator)*right
            meter.charge(16+4*precision)
            key_bytes = sum(abs(v.numerator).bit_length()+v.denominator.bit_length() for v in (a, b))//8
            self.store(self.bases, base_key, base, 768+8*((precision+7)//8)+key_bytes, meter)
        zero = (not a or d == 1) and (not b or n//d == 1)
        meter.power_evaluations += 1
        meter.charge(32+precision*precision//8)
        if zero:
            value = arb(0)
        elif alpha.denominator == 1:
            value = base**alpha.numerator
        else:
            value = base**(arb(alpha.numerator)/alpha.denominator)
        if not value.is_finite():
            raise ArithmeticError('finite real fractional-logarithmic atom required')
        key_bytes = sum(abs(v.numerator).bit_length()+v.denominator.bit_length() for v in (a, b, alpha))//8
        return self.store(self.atoms, key, value, 960+8*((precision+7)//8)+key_bytes, meter)

    def metadata(self):
        return {'estimated_bytes': self.bytes_estimate, 'max_bytes': self.max_bytes,
                'factor_entries': len(self.factors), 'log_entries': len(self.logs),
                'base_entries': len(self.bases), 'atom_entries': len(self.atoms),
                'keys': 'literal(n,d,(a_num,a_den),(b_num,b_den),precision,(alpha_num,alpha_den))',
                'artifact_hashes_used': False}


CACHE = KernelCache()


def _endpoint(row):
    numerator, exponent = int(row[0]), row[1]
    return Q(numerator << exponent) if exponent >= 0 else Q(numerator, 1 << -exponent)


def _enclosure(value):
    if not value.is_finite():
        raise ArithmeticError('finite Arb enclosure required')
    lo, hi = value.lower().man_exp(), value.upper().man_exp()
    return {'lower_dyadic': [str(lo[0]), int(lo[1])],
            'upper_dyadic': [str(hi[0]), int(hi[1])], 'ball': value.str(65)}


def _interval(enclosure):
    return _endpoint(enclosure['lower_dyadic']), _endpoint(enclosure['upper_dyadic'])


def evaluate(request, n, precision=192, meter=None):
    """Finite rigorous sign evidence for one integer; no uniform sign admission."""
    meter = _meter(meter)
    a, b, alpha, sign = _request(request, meter)
    n, precision = _number(n), _precision(precision)
    meter.requests += 1
    before = meter.operations
    factors, divisors = CACHE.factors_of(n, meter)
    meter.reserve(CACHE.bytes_estimate+4096+512*len(divisors))
    with ctx.workprec(precision):
        total, absolute, terms = arb(0), arb(0), []
        for d, mu in divisors:
            atom = CACHE.atom(n, d, a, b, alpha, precision, meter)
            total += mu*atom
            absolute += atom
            meter.divisor_rows += 1
            meter.charge(16+4*precision)
            terms.append({'d': d, 'mu': mu, 'log_arguments': [d, n//d]})
        value = sign*total
        enclosure = _enclosure(value)
        lower, upper = _interval(enclosure)
        status = 'FINITE_NEGATIVE' if upper < 0 else (
            'FINITE_NONNEGATIVE' if lower >= 0 else 'UNRESOLVED_SIGN')
        normalized = None if n == 1 else _enclosure(value/CACHE.atom(
            n, 1, Q(0), Q(1), alpha, precision, meter))
        abs_enclosure = _enclosure(absolute)
        abs_lower, abs_upper = _interval(abs_enclosure)
        ratio = _enclosure(value/absolute) if abs_lower > 0 else None
        meter.charge(64+12*precision)
    ordinary_mu = 0 if any(e > 1 for _, e in factors) else (-1)**len(factors)
    return {'schema': 'fractional-prime-kernel-evaluation-v1', 'request': dict(request),
            'n': n, 'precision': precision, 'value': enclosure, 'finite_sign': status,
            'strict_positive': lower > 0, 'exact_zero_enclosure': lower == upper == 0,
            'normalized_by_log_n_alpha': normalized,
            'signed_over_absolute': ratio, 'absolute_divisor_sum': abs_enclosure,
            'factorization': [{'prime': p, 'exponent': e} for p, e in factors],
            'ordinary_mu_n': ordinary_mu, 'squarefree_divisors': terms,
            'prime': len(factors) == 1 and factors[0][1] == 1,
            'distinct_prime_count': len(factors),
            'arithmetic_provenance': 'ordinary Mobius from exact trial factorization; squarefree divisor subset parity',
            'primepowers_retained_via': 'log(n/d), with actual n and squarefree d',
            'zero_base_convention': '0^alpha=0 for alpha>0',
            'all_scale_sign_proved': False, 'uniform_bound_proved': False,
            'proof_provider_used': False, 'float_sign_admission_used': False,
            'work_operations': meter.operations-before}


def _grammar_spec(spec):
    if spec is None:
        return dict(DEFAULT_GRAMMAR)
    if type(spec) is not dict or set(spec)-set(DEFAULT_GRAMMAR):
        raise ValueError('grammar only denominator ceilings and candidate cap')
    out = dict(DEFAULT_GRAMMAR, **spec)
    for name in ('a_denominator', 'alpha_denominator'):
        if type(out[name]) is not int or not 1 <= out[name] <= MAX_DENOMINATOR:
            raise ValueError('positive declared denominator ceiling within resource cap')
    if type(out['max_candidates']) is not int or not 1 <= out['max_candidates'] <= MAX_CANDIDATES:
        raise ValueError('candidate cap1..20000')
    return out


def _fractions(ceiling, upper, meter, maximum):
    values = set()
    for denominator in range(1, ceiling+1):
        for numerator in range(0, upper*denominator+1):
            meter.charge(8+2*denominator.bit_length())
            if math.gcd(numerator, denominator) == 1:
                values.add(Q(numerator, denominator))
                if len(values) > maximum:
                    raise OverflowError('complete rational bank exceeds prospective candidate cap')
    return sorted(values)


def grammar(spec=None, meter=None):
    """Enumerate all admitted rationals under declared complexity ceilings."""
    meter, spec = _meter(meter), _grammar_spec(spec)
    avals = [a for a in _fractions(spec['a_denominator'], 1, meter,
                                  spec['max_candidates']//4+1) if a != Q(1, 2)]
    alphas = [v for v in _fractions(spec['alpha_denominator'], 2, meter,
                                   spec['max_candidates']//(2*len(avals))+1) if v > 0]
    count = 2*len(avals)*len(alphas)
    if count > spec['max_candidates']:
        raise OverflowError('declared complete rational bank exceeds candidate cap')
    meter.reserve(count*2048)
    discoveries, calibrations = [], []
    for a in avals:
        b = 1-a
        for alpha in alphas:
            for sign in (-1, 1):
                request = {'a': str(a), 'b': str(b), 'alpha': str(alpha), 'sign': sign}
                index = len(discoveries)+len(calibrations)
                entry = {'id': 'fractional_prime_kernel_%04d' % index, 'request': request,
                         'complexity': {'a_denominator': a.denominator,
                                        'alpha_denominator': alpha.denominator,
                                        'rational_height': sum(abs(v.numerator)+v.denominator for v in (a, b, alpha))},
                         'role': 'vonMangoldt_calibration' if alpha == 1 else 'discovery'}
                if alpha == 1:
                    entry['calibration_identity'] = 'K(n)=sign*(b-a)*Lambda(n), n>1; K(1)=0'
                    calibrations.append(entry)
                else:
                    discoveries.append(entry)
                meter.charge(64)
    return {'schema': 'fractional-prime-kernel-grammar-v1', 'limits': spec,
            'candidate_count': count, 'discovery': discoveries, 'calibrations': calibrations,
            'construction': 'sign*sum_(d|n)mu(d)*(a*log(d)+b*log(n/d))^alpha',
            'all_scale_proof_provider_used': False}


def _numbers(numbers, name):
    if type(numbers) is not list or not numbers or len(numbers) > MAX_NUMBERS:
        raise ValueError(name+' must be a nonempty bounded list')
    if any(type(n) is not int or not 2 <= n <= MAX_N for n in numbers) or len(set(numbers)) != len(numbers):
        raise ValueError(name+' requires distinct integers2..MAX_N')
    return list(numbers)


def _summary(entry, observations, numbers):
    negative = next((v for v in observations if v['finite_sign'] == 'FINITE_NEGATIVE'), None)
    complete = len(observations) == len(numbers)
    unresolved = sum(v['finite_sign'] == 'UNRESOLVED_SIGN' for v in observations)
    status = 'FINITE_NEGATIVE_COUNTEREXAMPLE' if negative else (
        'FINITE_NONNEGATIVE_ALL_TESTED' if not unresolved else 'NO_FINITE_NEGATIVE_WITH_UNRESOLVED')
    normalized = [(v['n'], _interval(v['normalized_by_log_n_alpha'])) for v in observations]
    maximum = {'lower': str(max(bounds[0] for _, bounds in normalized)),
               'upper': str(max(bounds[1] for _, bounds in normalized)),
               'scope': 'observed numbers only'}
    prime_responses = [v['n'] for v in observations if v['prime'] and v['strict_positive']]
    composite_responses = [v['n'] for v in observations if v['distinct_prime_count'] >= 2 and v['strict_positive']]
    return {**entry, 'finite_status': status, 'observations': observations,
            'requested_numbers': list(numbers), 'observed_count': len(observations),
            'full_training_coverage': complete,
            'skipped_after_counterexample': numbers[len(observations):] if negative else [],
            'finite_negative_witness': negative,
            'unresolved_zero_or_sign_count': unresolved,
            'exact_zero_enclosure_count': sum(v['exact_zero_enclosure'] for v in observations),
            'max_normalized': maximum,
            'strict_positive_prime_responses': prime_responses,
            'strict_positive_multiprime_responses': composite_responses,
            'nontrivial_two_distinct_prime_responses': len(prime_responses) >= 2,
            'eligible_for_finite_archive': entry['role'] == 'discovery' and complete and not negative and len(prime_responses) >= 2,
            'finite_evidence_only': True, 'uniform_sign_proved': False}


def search(spec, training_numbers, meter=None):
    """Observe a declared bank, stopping each row at its first strict negative.

    The caller freezes this spec and bank before scientific application.
    Irregular numbers are declared here; fresh final numbers never enter the
    selector through this API. Unresolved signs are retained, not tolerated.
    """
    if type(spec) is not dict or set(spec) != {'grammar', 'precision', 'irregular_numbers'}:
        raise ValueError('search spec exactly grammar,precision,irregular_numbers')
    meter = _meter(meter)
    training = _numbers(training_numbers, 'training_numbers')
    irregular = spec['irregular_numbers']
    if type(irregular) is not list or len(irregular) > MAX_NUMBERS:
        raise ValueError('bounded declared irregular list')
    if irregular:
        irregular = _numbers(irregular, 'irregular_numbers')
    numbers = training+[n for n in irregular if n not in training]
    if len(numbers) > MAX_NUMBERS:
        raise OverflowError('combined declared number cap')
    precision = _precision(spec['precision'])
    bank = grammar(spec['grammar'], meter)
    row_bytes = sum(8192+512*len(CACHE.factors_of(n, meter)[1]) for n in numbers)
    estimate = MAX_CACHE_BYTES+bank['candidate_count']*row_bytes
    meter.reserve(estimate)
    rows, calibrations = [], []
    for entry in bank['discovery']+bank['calibrations']:
        observations = []
        for n in numbers:
            value = evaluate(entry['request'], n, precision, meter)
            observations.append(value)
            if value['finite_sign'] == 'FINITE_NEGATIVE':
                break
        row = _summary(entry, observations, numbers)
        (calibrations if entry['role'] == 'vonMangoldt_calibration' else rows).append(row)
    return {'schema': 'fractional-prime-kernel-finite-search-v1',
            'spec': {'grammar': bank['limits'], 'precision': precision,
                     'irregular_numbers': list(irregular)},
            'training_numbers': training, 'observed_numbers': numbers,
            'grammar': bank, 'rows': rows, 'calibrations': calibrations,
            'counts': meter.counts(), 'cache': CACHE.metadata(),
            'fresh_final_numbers_seen_by_selector': False,
            'all_scale_sign_proved': False, 'uniform_bound_proved': False,
            'proof_provider_used': False, 'RH_proved': False}


def select(rows, limit=6):
    """Small finite-evidence archive, rational exponent and shape diversity.

    Strictly positive multiprime observations are preferred, followed by
    rational complexity. No proof-provider result or anticipated formula is
    consulted. An unresolved row stays explicitly unresolved if selected.
    """
    if type(rows) is not list or type(limit) is not int or not 0 <= limit <= 32:
        raise ValueError('row list and archive limit0..32')
    ids, eligible = set(), []
    for row in rows:
        if type(row) is not dict or type(row.get('id')) is not str or row['id'] in ids:
            raise ValueError('unique candidate rows')
        ids.add(row['id'])
        if (row['role'] == 'discovery' and row['full_training_coverage'] and
                row['finite_negative_witness'] is None and
                len(set(row['strict_positive_prime_responses'])) >= 2 and
                row['finite_status'] in ('FINITE_NONNEGATIVE_ALL_TESTED', 'NO_FINITE_NEGATIVE_WITH_UNRESOLVED')):
            eligible.append(row)
    def rank(row):
        complexity = row['complexity']
        return (not bool(row['strict_positive_multiprime_responses']),
                complexity['rational_height'], complexity['alpha_denominator'],
                complexity['a_denominator'], row['id'])
    eligible.sort(key=rank)
    selected, used_alphas, used_shapes = [], set(), set()
    # First reserve one representative per rational exponent, then per shape;
    # any remaining slots follow the same fixed complexity ordering.
    for phase in ('exponent', 'shape', 'remaining'):
        for row in eligible:
            if len(selected) >= limit:
                break
            if row['id'] in {v['id'] for v in selected}:
                continue
            alpha, shape = row['request']['alpha'], (row['request']['a'], row['request']['b'], row['request']['sign'])
            if phase == 'exponent' and alpha in used_alphas:
                continue
            if phase == 'shape' and shape in used_shapes:
                continue
            selected.append(row)
            used_alphas.add(alpha)
            used_shapes.add(shape)
    return {'schema': 'fractional-prime-kernel-finite-archive-v1', 'limit': limit,
            'eligible_count': len(eligible), 'selected': selected,
            'selection_rule': 'full coverage/no certified negative/two positive distinct primes; prefer positive multiprime response, lower rational height, exponent then shape diversity',
            'unresolved_sign_rows_may_be_selected': True,
            'vonMangoldt_calibrations_excluded': True,
            'finite_evidence_only': True, 'all_scale_sign_proved': False,
            'proof_provider_used': False, 'final_numbers_used': False}
