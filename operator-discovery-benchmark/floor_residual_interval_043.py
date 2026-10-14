"""Whole continuous L2 norm enclosure for a fixed integer-floor program.

All residues are exact integer event updates. The infinite tail is bounded
analytically, never inferred from a finite observation. No source data is read.
"""
from fractions import Fraction
import math
import time

from flint import arb, ctx

MAX_PARAMETER_BITS = 4096
MAX_INTEGER_BITS = 8192
MAX_SUPPORT = 256
MAX_H = 8_388_608


class Meter:
    def __init__(self, cap=500_000_000, seconds=3600):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer operation cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite time cap')
        self.cap, self.operations = cap, 0
        self.peak_integer_bits, self.peak_bytes_estimate = 0, 0
        self.deadline = time.monotonic()+seconds

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('floor residual work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('floor residual time cap')

    def integer(self, value):
        bits = abs(value).bit_length()
        if bits > MAX_INTEGER_BITS:
            raise OverflowError('floor residual exact-integer bit cap')
        self.peak_integer_bits = max(self.peak_integer_bits, bits)
        self.charge(max(1, bits))

    def product(self, a, b):
        if a and b and abs(a).bit_length()+abs(b).bit_length() > MAX_INTEGER_BITS:
            raise OverflowError('floor residual integer-product preflight cap')
        value = a*b
        self.integer(value)
        return value

    def reserve(self, H, event_bits, support):
        # One event-list pointer plus conservative Python int/limb overhead.
        estimated = (H+1)*(64+(event_bits+7)//8)+support*8192+65536
        if estimated > 15*1024**3:
            raise MemoryError('floor residual estimated memory cap')
        self.peak_bytes_estimate = max(self.peak_bytes_estimate, estimated)
        self.charge(H+1)

    def counts(self):
        return {'operations': self.operations,
                'peak_integer_bits': self.peak_integer_bits,
                'peak_bytes_estimate': self.peak_bytes_estimate}


def _meter(meter):
    return meter if meter is not None else Meter()


def _rational(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational coefficient required')
    meter.charge(len(text)+1)
    try:
        value = Fraction(text)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError('canonical rational coefficient required') from exc
    if str(value) != text or max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_PARAMETER_BITS:
        raise ValueError('canonical coefficient within bit cap required')
    return value


def validate_program(program, meter=None):
    meter = _meter(meter)
    if type(program) is not dict or set(program) != {'id', 'coefficients', 'steps'}:
        raise ValueError('exact floor program schema required')
    if type(program['id']) is not str or not 1 <= len(program['id']) <= 250:
        raise ValueError('bounded nonempty id required')
    rows, steps = program['coefficients'], program['steps']
    if type(rows) is not list or type(steps) is not list or len(rows)+len(steps) > MAX_SUPPORT:
        raise ValueError('floor/step lists with combined support<=256 required')
    results = []
    for key, entries in (('n', rows), ('q', steps)):
        result, previous = [], 1
        for row in entries:
            if type(row) is not dict or set(row) != {key, 'value'}:
                raise ValueError('exact floor/step row schema required')
            n = row[key]
            if type(n) is not int or n <= previous or n.bit_length() > MAX_PARAMETER_BITS:
                raise ValueError('sorted distinct integer floor/step>=2 within bit cap required')
            c = _rational(row['value'], meter)
            if c == 0:
                raise ValueError('zero coefficients must be omitted')
            result.append((n, c))
            previous = n
            meter.charge(n.bit_length()+16)
        results.append(result)
    return tuple(results)


def integer_lattice(program, meter=None):
    """Return exact D,A,weights/events and the rational pointwise bound M."""
    meter = _meter(meter)
    coefficients, step_coefficients = validate_program(program, meter)
    quotients = [(n, c/n) for n, c in coefficients]
    D = 1
    for _, value in quotients+step_coefficients:
        factor = value.denominator//math.gcd(D, value.denominator)
        D = meter.product(D, factor)
        meter.charge(value.denominator.bit_length()+16)
    weights, events, step_events, A, floor_abs, step_abs, step_sum, event_magnitude = [], [], [], 0, 0, 0, 0, 0
    for n, value in quotients:
        weight = meter.product(value.numerator, D//value.denominator)
        event = meter.product(weight, n)
        weights.append((n, weight))
        events.append((n, event))
        A += weight
        floor_abs += meter.product(abs(weight), n-1)
        event_magnitude += abs(event)
        meter.integer(A)
        meter.integer(floor_abs)
        meter.integer(event_magnitude)
        meter.charge(12)
    for q, value in step_coefficients:
        step_weight = meter.product(value.numerator, D//value.denominator)
        step_events.append((q, -step_weight))
        step_sum += step_weight
        step_abs += abs(step_weight)
        event_magnitude += abs(step_weight)
        meter.integer(step_sum)
        meter.integer(step_abs)
        meter.integer(event_magnitude)
    M_numerator = abs(D-step_sum)+floor_abs
    head_M_numerator = D+step_abs+floor_abs
    meter.integer(M_numerator)
    meter.integer(head_M_numerator)
    return {'D': D, 'A': A, 'weights': weights, 'events': events, 'step_events': step_events,
            'M_numerator': M_numerator, 'M': Fraction(M_numerator, D),
            'head_M_numerator': head_M_numerator,
            'event_magnitude': event_magnitude}


def head_from_lattice(lattice, H, precision=192, meter=None):
    """Event sieve plus one sequential exact residue/Arb head pass."""
    meter = _meter(meter)
    if type(H) is not int or not 0 <= H <= MAX_H:
        raise ValueError('integer H in0..8388608 required')
    if type(precision) is not int or not 128 <= precision <= 4096:
        raise ValueError('Arb precision128..4096 required')
    D, A = lattice['D'], lattice['A']
    meter.reserve(H, lattice['event_magnitude'].bit_length(), len(lattice['weights'])+len(lattice['step_events']))
    # Charge the entire prospective arithmetic pass before allocating memory.
    visits = sum(H//n for n, _ in lattice['events'])
    meter.charge(6*visits+48*H+6*len(lattice['step_events']))
    events = [0]*(H+1)
    for n, event in lattice['events']:
        for k in range(n, H+1, n):
            events[k] += event
        meter.charge()
    for q, event in lattice['step_events']:
        if q <= H:
            events[q] += event
    with ctx.workprec(precision):
        total, residue = arb(0), D
        for k in range(1, H+1):
            residue += events[k]-A
            if abs(residue) > lattice['head_M_numerator']:
                raise ArithmeticError('integer residue violates exact pointwise bound')
            total += arb(residue)*arb(residue)/(k*(k+1))
            if k % 4096 == 0:
                meter.charge()
        head = total/(arb(D)*arb(D))
        if not head.is_finite():
            raise ArithmeticError('nonfinite Arb head')
        return head


def enclosure(value):
    if not value.is_finite():
        raise ArithmeticError('nonfinite output enclosure')
    low, high = value.lower().man_exp(), value.upper().man_exp()
    return {'ball': value.str(65),
            'lower_dyadic': [str(low[0]), int(low[1])],
            'upper_dyadic': [str(high[0]), int(high[1])]}


def certify(program, H=1_048_576, precision=192, meter=None):
    """Certify the whole continuous norm for this one fixed exact program."""
    meter = _meter(meter)
    if type(H) is not int or not 0 <= H <= MAX_H:
        raise ValueError('integer H in0..8388608 required')
    if type(precision) is not int or not 128 <= precision <= 4096:
        raise ValueError('Arb precision128..4096 required')
    lattice = integer_lattice(program, meter)
    if any(q > H for q, _ in lattice['step_events']):
        raise ValueError('H must cover every step threshold q')
    M = lattice['M']
    tail = M*M/(H+1)
    meter.integer(tail.numerator)
    meter.integer(tail.denominator)
    with ctx.workprec(precision):
        head = head_from_lattice(lattice, H, precision, meter)
        tail_ball = arb(tail.numerator)/tail.denominator
        whole = head+arb(1, 1)*tail_ball/2
        meter.charge(256+8*precision)
        return {'schema': 'floor-residual-continuous-norm-v1', 'program': program,
                'H': H, 'precision': precision,
                'basis': {'definition': 'f_n(x)=floor(1/x)/n-floor(1/(n*x)) on0<x<=1; zero x>1',
                          'cell': 'x in(1/(k+1),1/k]',
                          'cell_value': '(k mod n)/n',
                          'step_value': '1_(x<=1/q)=1_(k>=q)',
                          'residual': 'e=1-sum c_n*f_n-sum d_q*1_(x<=1/q) on(0,1]'},
                'lattice': {'D': str(lattice['D']), 'A': str(lattice['A']),
                            'weights': [{'n': n, 'weight': str(weight)} for n, weight in lattice['weights']],
                            'events': [{'n': n, 'value': str(event)} for n, event in lattice['events']],
                            'step_events': [{'q': q, 'value': str(event)} for q, event in lattice['step_events']],
                            'residue_formula': 'R(k)=D-k*A+sum c_n*D*floor(k/n)-sum_(q<=k)d_q*D',
                            'update_formula': 'R(k)-R(k-1)=-A+sum_(n|k)c_n*D-sum_(q=k)d_q*D',
                            'R_zero': str(lattice['D'])},
                'head': {'indices': [1, H], 'formula': 'sum_(1<=k<=H)e(k)^2/(k*(k+1))',
                         'enclosure': enclosure(head)},
                'tail': {'indices': [H+1, 'infinity'], 'measure': str(Fraction(1, H+1)),
                         'pointwise_abs_bound': str(M),
                         'bound_formula': 'M=|1-sum d_q|+sum|c_n|*(n-1)/n; tail<=M^2/(H+1)',
                         'every_step_active_on_tail': True,
                         'lower': '0', 'upper': str(tail),
                         'observations_used_to_infer_tail': False},
                'norm_squared': enclosure(whole),
                'continuous_integral_domain': '0<x<=1',
                'continuous_global_fixed_program_bound': True,
                'head_arithmetic': 'exact integer residues and Arb interval accumulation',
                'tail_is_analytic_global_bound': True, 'float_sign_admission_used': False,
                'coefficient_bit_count': sum(abs(c.numerator).bit_length()+c.denominator.bit_length()
                                             for rows in validate_program(program, meter) for _, c in rows),
                'support': len(lattice['weights'])+len(lattice['step_events']),
                'convergence_as_support_increases_proved': False,
                'actual_source_coefficient_recovery_claimed': False,
                'RH_proved': False, 'RH_refuted': False,
                'counts': meter.counts()}
