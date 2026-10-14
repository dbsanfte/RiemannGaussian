"""General signed floor/step vectors: exact events, global certified tails.

Montgomery--Vaughan's large sieve is an imported theorem. No actual program,
source coefficient or norm observation is made at import or in development.
"""
from fractions import Fraction as F
import math
import time
from flint import arb, ctx

MAX_SUPPORT = 2048
MAX_INDEX = 4096
MAX_PARAMETER_BITS = 4096
MAX_INTEGER_BITS = 8192
MAX_H = 8_388_608
LARGE_SIEVE_URL = 'https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf'


class Meter:
    def __init__(self, cap=1_000_000_000, seconds=3600):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer operation cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite time cap')
        self.cap, self.operations = cap, 0
        self.peak_integer_bits, self.peak_bytes_estimate = 0, 0
        self.deadline = time.monotonic()+seconds

    def charge(self, n=1):
        if type(n) is not int or n < 0 or n > self.cap-self.operations:
            raise OverflowError('signed floor norm work cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('signed floor norm deadline')

    def integer(self, value):
        bits = abs(value).bit_length()
        if bits > MAX_INTEGER_BITS:
            raise OverflowError('signed floor exact-integer cap')
        self.peak_integer_bits = max(self.peak_integer_bits, bits)
        self.charge(max(1, bits))
        return value

    def product(self, a, b):
        if a and b and abs(a).bit_length()+abs(b).bit_length() > MAX_INTEGER_BITS:
            raise OverflowError('signed floor multiplication preflight cap')
        return self.integer(a*b)

    def reserve(self, H, event_bits, support, kernel_bytes=0):
        estimate = (H+1)*(64+(event_bits+7)//8)+support*8192+65536+kernel_bytes
        if estimate > 15*1024**3:
            raise MemoryError('signed floor estimated memory cap')
        self.peak_bytes_estimate = max(self.peak_bytes_estimate, estimate)
        self.charge(H+1)

    def counts(self):
        return {'operations': self.operations, 'peak_integer_bits': self.peak_integer_bits,
                'peak_bytes_estimate': self.peak_bytes_estimate}


def _meter(meter):
    return meter if meter is not None else Meter()


class GCDKernel:
    """Bounded cache of exact factors of the rational covariance kernel."""
    def __init__(self, max_bytes=1024**3):
        if type(max_bytes) is not int or not 0 <= max_bytes <= 1024**3:
            raise ValueError('kernel cache byte cap0..1GiB')
        self.max_bytes, self.bytes_estimate, self.hits = max_bytes, 0, 0
        self.cache = {}

    def factor(self, m, n, meter=None):
        meter = _meter(meter)
        if type(m) is not int or type(n) is not int or not 2 <= m <= MAX_INDEX or not 2 <= n <= MAX_INDEX:
            raise ValueError('kernel floor indices2..4096')
        key = (min(m, n), max(m, n))
        meter.charge(16)
        if key in self.cache:
            self.hits += 1
            return self.cache[key]
        g = math.gcd(m, n)
        value = g*g-1
        size = 256+(m.bit_length()+n.bit_length()+value.bit_length()+7)//8
        if size <= self.max_bytes-self.bytes_estimate:
            self.cache[key] = value
            self.bytes_estimate += size
        return value

    def rational(self, m, n, meter=None):
        return F(self.factor(m, n, meter), 12*m*n)


class JordanKernel:
    """Coefficient-free exact Jordan2 sieve, retaining only largest cached K."""
    def __init__(self):
        self.maximum, self.values, self.hits, self.bytes_estimate = 1, [0, 1], 0, 128

    def get(self, K, meter=None):
        meter = _meter(meter)
        if type(K) is not int or not 1 <= K <= MAX_INDEX:
            raise ValueError('Jordan kernel index1..4096')
        if K <= self.maximum:
            self.hits += 1
            meter.charge()
            return self.values
        meter.charge(K+1)
        values = [n*n for n in range(K+1)]
        values[1] = 1
        for p in range(2, K+1):
            meter.charge(2)
            if values[p] != p*p:
                continue
            square = p*p
            for n in range(p, K+1, p):
                values[n] = values[n]//square*(square-1)
                meter.charge(8)
        self.maximum, self.values = K, values
        self.bytes_estimate = (K+1)*64
        return self.values


def _rational(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational required')
    meter.charge(len(text)+1)
    try:
        value = F(text)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError('canonical rational required') from exc
    if str(value) != text or max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_PARAMETER_BITS:
        raise ValueError('canonical rational within bit cap required')
    return value


def validate_program(program, meter=None):
    meter = _meter(meter)
    if type(program) is not dict or set(program) != {'id', 'constant', 'coefficients', 'steps'}:
        raise ValueError('exact general signed-vector schema required')
    if type(program['id']) is not str or not 1 <= len(program['id']) <= 250:
        raise ValueError('bounded nonempty vector id required')
    constant = _rational(program['constant'], meter)
    floors, steps = program['coefficients'], program['steps']
    if type(floors) is not list or type(steps) is not list or len(floors)+len(steps) > MAX_SUPPORT:
        raise ValueError('sorted floor/step lists with combined support<=2048')
    result = []
    for key, rows in (('n', floors), ('q', steps)):
        values, previous = [], 1
        for row in rows:
            if type(row) is not dict or set(row) != {key, 'value'}:
                raise ValueError('exact floor/step row schema')
            index = row[key]
            if type(index) is not int or not previous < index <= MAX_INDEX:
                raise ValueError('sorted distinct integer floor/step indices2..4096')
            value = _rational(row['value'], meter)
            if not value:
                raise ValueError('zero coefficients must be omitted')
            values.append((index, value))
            previous = index
            meter.charge(16+index.bit_length())
        result.append(values)
    return constant, result[0], result[1]


def integer_lattice(program, meter=None):
    meter = _meter(meter)
    constant, floors, steps = validate_program(program, meter)
    quotients = [(n, c/n) for n, c in floors]
    D = 1
    for value in [constant]+[c for _, c in quotients]+[d for _, d in steps]:
        factor = value.denominator//math.gcd(D, value.denominator)
        D = meter.product(D, factor)
        meter.charge(value.denominator.bit_length()+16)
    CD = meter.product(constant.numerator, D//constant.denominator)
    weights, periodic, one_time = [], [], []
    A, floor_abs, floor_signed, step_sum, step_abs, event_abs = 0, 0, 0, 0, 0, 0
    for n, value in quotients:
        w = meter.product(value.numerator, D//value.denominator)
        event = meter.product(w, n)
        weights.append((n, w))
        periodic.append((n, event))
        A += w
        floor_abs += meter.product(abs(w), n-1)
        floor_signed += meter.product(w, n-1)
        event_abs += abs(event)
        for integer in (A, floor_abs, floor_signed, event_abs):
            meter.integer(integer)
    for q, value in steps:
        weight = meter.product(value.numerator, D//value.denominator)
        one_time.append((q, -weight))
        step_sum += weight
        step_abs += abs(weight)
        event_abs += abs(weight)
        for integer in (step_sum, step_abs, event_abs):
            meter.integer(integer)
    Mnum = meter.integer(abs(CD-step_sum)+floor_abs)
    early = meter.integer(abs(CD)+step_abs+floor_abs)
    mean_num = meter.integer(2*(CD-step_sum)-floor_signed)
    return {'D': D, 'CD': CD, 'A': A, 'weights': weights, 'periodic': periodic,
            'one_time': one_time, 'Mnum': Mnum, 'M': F(Mnum, D),
            'early_bound_num': early, 'event_abs': event_abs,
            'mean_num': mean_num, 'constant': constant, 'floors': floors, 'steps': steps}


def periodic_energy(lattice, meter=None, kernel=None):
    """Exact complete periodic mean square after all steps have activated."""
    meter = _meter(meter)
    kernel = kernel if kernel is not None else JordanKernel()
    if type(kernel) is not JordanKernel:
        raise ValueError('JordanKernel cache required')
    weights, S = lattice['weights'], 0
    K = max((n for n, _ in weights), default=1)
    jordan = kernel.get(K, meter)
    work_bytes = kernel.bytes_estimate+(K+1)*(320+(lattice['early_bound_num'].bit_length()+7)//8)
    meter.reserve(0, lattice['event_abs'].bit_length(), len(weights)+len(lattice['one_time']), work_bytes)
    dense_weights, divisor_sums = [0]*(K+1), []
    for n, weight in weights:
        dense_weights[n] = weight
    for d in range(2, K+1):
        weighted_sum, occupied = 0, False
        for n in range(d, K+1, d):
            weighted_sum += dense_weights[n]
            occupied = occupied or bool(dense_weights[n])
            meter.charge(8)
        meter.integer(weighted_sum)
        term = meter.product(jordan[d], meter.product(weighted_sum, weighted_sum))
        S = meter.integer(S+term)
        if occupied:
            divisor_sums.append({'d': d, 'J2': str(jordan[d]), 'weighted_sum': str(weighted_sum)})
    D2 = meter.product(lattice['D'], lattice['D'])
    mean_square_num = meter.product(lattice['mean_num'], lattice['mean_num'])
    numerator = meter.integer(3*mean_square_num+S)
    denominator = meter.product(12, D2)
    if numerator < 0:
        raise ArithmeticError('exact periodic mean square is negative')
    V, variance, mean = F(numerator, denominator), F(S, denominator), F(lattice['mean_num'], 2*lattice['D'])
    if variance < 0:
        raise ArithmeticError('exact covariance quadratic form is negative')
    return {'K': K, 'mean': mean,
            'variance': variance, 'V': V, 'pair_count': len(weights)**2, 'kernel': kernel,
            'jordan_divisor_sums': divisor_sums,
            'work_bytes_estimate': work_bytes,
            'integer_variance_numerator': S, 'integer_V_numerator': numerator,
            'integer_common_denominator': denominator}


def head_from_lattice(lattice, H, precision=192, meter=None, kernel_bytes=0):
    meter = _meter(meter)
    if type(H) is not int or not 0 <= H <= MAX_H:
        raise ValueError('integer H0..8388608')
    if type(precision) is not int or not 128 <= precision <= 4096:
        raise ValueError('Arb precision128..4096')
    meter.reserve(H, lattice['event_abs'].bit_length(), len(lattice['weights'])+len(lattice['one_time']), kernel_bytes)
    meter.charge(6*sum(H//n for n, _ in lattice['periodic'])+48*H+6*len(lattice['one_time']))
    events = [0]*(H+1)
    for n, event in lattice['periodic']:
        for k in range(n, H+1, n):
            events[k] += event
        meter.charge()
    for q, event in lattice['one_time']:
        if q <= H:
            events[q] += event
    with ctx.workprec(precision):
        residue, total = lattice['CD'], arb(0)
        for k in range(1, H+1):
            residue += events[k]-lattice['A']
            if abs(residue) > lattice['early_bound_num']:
                raise ArithmeticError('exact early pointwise bound fails')
            total += arb(residue)*arb(residue)/(k*(k+1))
            if k % 4096 == 0:
                meter.charge()
        return total/(arb(lattice['D'])*arb(lattice['D']))


def enclosure(value):
    if not value.is_finite():
        raise ArithmeticError('finite output interval required')
    low, high = value.lower().man_exp(), value.upper().man_exp()
    return {'ball': value.str(65), 'lower_dyadic': [str(low[0]), int(low[1])],
            'upper_dyadic': [str(high[0]), int(high[1])]}


def certify(program, H=1_048_576, precision=192, meter=None, kernel=None):
    meter = _meter(meter)
    if type(H) is not int or not 0 <= H <= MAX_H:
        raise ValueError('integer H0..8388608')
    if type(precision) is not int or not 128 <= precision <= 4096:
        raise ValueError('Arb precision128..4096')
    lattice = integer_lattice(program, meter)
    if any(q > H for q, _ in lattice['one_time']):
        raise ValueError('H must cover all step thresholds')
    energy = periodic_energy(lattice, meter, kernel)
    a, K, M, V = H+1, energy['K'], lattice['M'], energy['V']
    pointwise = M*M/a
    sieve_factor = F(1, a)+F(K*K, a*(a+1))
    sieve = V*sieve_factor
    chosen = min(pointwise, sieve)
    for value in (pointwise, sieve_factor, sieve, chosen):
        meter.integer(value.numerator)
        meter.integer(value.denominator)
    with ctx.workprec(precision):
        head = head_from_lattice(lattice, H, precision, meter, energy['work_bytes_estimate'])
        tail_ball = arb(chosen.numerator)/chosen.denominator
        whole = head+arb(1, 1)*tail_ball/2
        meter.charge(256+8*precision)
        return {'schema': 'floor-signed-vector-norm-v1', 'program': program, 'H': H,
                'precision': precision,
                'basis': {'floor': 'f_n(cell k)=(k mod n)/n', 'step': 'I_q(cell k)=1_(k>=q)',
                          'residual': 'constant-sum c_n*f_n-sum d_q*I_q'},
                'lattice': {'D': str(lattice['D']), 'A': str(lattice['A']), 'R_zero': str(lattice['CD']),
                            'weights': [{'n': n, 'weight': str(w)} for n, w in lattice['weights']],
                            'periodic_events': [{'n': n, 'value': str(v)} for n, v in lattice['periodic']],
                            'step_events': [{'q': q, 'value': str(v)} for q, v in lattice['one_time']],
                            'early_abs_bound': str(F(lattice['early_bound_num'], lattice['D'])),
                            'update': 'R(k)-R(k-1)=-A+sum_(n|k)c_n*D-sum_(q=k)d_q*D'},
                'head': {'indices': [1, H], 'enclosure': enclosure(head)},
                'periodic_energy': {'K': K, 'mean': str(energy['mean']),
                                    'variance': str(energy['variance']), 'V': str(V),
                                    'formula': '(C-sum d-sum c*(n-1)/(2n))^2+sum_mn c_m*c_n*(gcd(m,n)^2-1)/(12mn)',
                                    'kernel_formula': '(gcd(m,n)^2-1)/(12mn)',
                                    'provider': 'Jordan2_divisor_squares',
                                    'jordan_identity': 'gcd(m,n)^2-1=sum_(d|m,n,d>1)J2(d)',
                                    'integer_mean_numerator': str(lattice['mean_num']),
                                    'jordan_divisor_sums': energy['jordan_divisor_sums'],
                                    'all_signed_pairs_retained': True, 'pair_count': energy['pair_count'],
                                    'integer_variance_numerator': str(energy['integer_variance_numerator']),
                                    'integer_V_numerator': str(energy['integer_V_numerator']),
                                    'integer_common_denominator': str(energy['integer_common_denominator'])},
                'tail': {'start': a, 'measure': str(F(1, a)), 'M': str(M),
                         'lower': '0', 'pointwise_upper': str(pointwise),
                         'large_sieve_upper': str(sieve), 'upper': str(chosen),
                         'chosen_provider': 'large_sieve' if sieve < pointwise else 'pointwise',
                         'steps_active': True, 'observations_used_to_infer_tail': False},
                'imported_large_sieve': {'authors': 'H. L. Montgomery and R. C. Vaughan',
                                         'title': 'The large sieve', 'year': 1973,
                                         'theorem': 'Theorem1(1.4) and matrix duality Lemma1',
                                         'url': LARGE_SIEVE_URL,
                                         'block_bound': '(L+K^2)*V',
                                         'frequency_spacing_lower': str(F(1, K*K)),
                                         'weighted_tail_factor': str(sieve_factor),
                                         'weighted_tail_formula': 'V*(1/a+K^2/(a*(a+1))), a=H+1',
                                         'minus_one_sharpening_used': False,
                                         'detector_discovered_theorem': False},
                'norm_squared': enclosure(whole), 'domain': '0<x<=1',
                'continuous_global_fixed_vector_bound': True,
                'float_norm_or_sign_admission_used': False,
                'target_role_requires_constant1_and_no_steps': True,
                'general_vector_is_automatically_RH_bearing': False,
                'convergence_as_support_increases_proved': False,
                'source_coefficient_recovery_claimed': False,
                'actual_source_data_read': False, 'RH_proved': False, 'RH_refuted': False,
                'coefficient_bit_count': sum(abs(c.numerator).bit_length()+c.denominator.bit_length()
                                             for c in [lattice['constant']]+[c for _, c in lattice['floors']]+[d for _, d in lattice['steps']]),
                'support': len(lattice['weights'])+len(lattice['one_time']),
                'kernel_cache_entries': len(energy['kernel'].values),
                'kernel_cache_hits': energy['kernel'].hits,
                'kernel_cache_bytes_estimate': energy['kernel'].bytes_estimate,
                'counts': meter.counts()}
