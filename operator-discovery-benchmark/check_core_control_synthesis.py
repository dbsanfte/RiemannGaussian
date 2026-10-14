"""Independent complete transported-core storage and conditional control.

No producer import or source arithmetic. The source/prefix linkage and the
original pole witness must be verified outside this module. Finite recurrence
decisions never discharge the uniform premise in a recovery certificate.
"""
from copy import deepcopy
from fractions import Fraction
import re

from flint import arb, ctx

MAX_HORIZON = 524287
SCALAR_BITS = 4096
POWER_WORK = 64
KINDS = ('log_bank', 'half_delay', 'transport_error')


class _NoMeter:
    def charge(self, count=1): pass
    def live(self, cells): pass


def _rational(value, meter):
    if type(value) is not str or not 1 <= len(value) <= 2500:
        raise ValueError('bounded canonical rational string')
    meter.charge(len(value) + 1)
    if re.fullmatch(r'-?\d+(?:/\d+)?', value) is None:
        raise ValueError('canonical rational string')
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError('canonical rational string') from error
    if str(result) != value or max(abs(result.numerator).bit_length(), result.denominator.bit_length()) > SCALAR_BITS:
        raise ValueError('canonical rational with bounded scalar bits')
    return result


def validate(program, meter=None):
    if meter is None: meter = _NoMeter()
    meter.charge(4)
    if type(program) is not dict or set(program) != {'auxiliary', 'mix', 'reserve'}:
        raise ValueError('exact storage program schema')
    mix = _rational(program['mix'], meter)
    reserve = _rational(program['reserve'], meter)
    if reserve <= 0: raise ValueError('strictly positive reserve')
    auxiliary = program['auxiliary']
    if auxiliary is None:
        if mix != 0 or reserve != 1: raise ValueError('null auxiliary requires mix0 and reserve1')
    else:
        if type(auxiliary) is not dict or set(auxiliary) != {'kind', 'alpha'}:
            raise ValueError('exact auxiliary kind/alpha schema')
        if type(auxiliary['kind']) is not str or auxiliary['kind'] not in KINDS:
            raise ValueError('known complete auxiliary kind')
        if _rational(auxiliary['alpha'], meter) < 0:
            raise ValueError('nonnegative auxiliary exponent')
    return True


def _shape(shape, meter):
    meter.charge(3)
    if type(shape) is not dict or set(shape) != {'rho', 'log_power'}:
        raise ValueError('exact recurrence shape')
    rho = _rational(shape['rho'], meter)
    degree = _rational(shape['log_power'], meter)
    if rho not in (Fraction(1, 2), Fraction(1)) or degree < 0:
        raise ValueError('rho1/2 or1 and nonnegative log power')
    return rho, degree


def _transport(program, meter):
    expected = {'cofactor', 'theta', 'capacity_fraction', 'load_multiple', 'keep_failed_windows'}
    meter.charge(6)
    if type(program) is not dict or set(program) != expected:
        raise ValueError('exact fixed-global transport program')
    if type(program['cofactor']) is not int or not 2 <= program['cofactor'] <= 16:
        raise ValueError('strict cofactor2..16')
    theta = _rational(program['theta'], meter)
    if not 0 < theta <= 1: raise ValueError('theta in(0,1]')
    if type(program['capacity_fraction']) is not str or program['capacity_fraction'] != '1/2':
        raise ValueError('fixed half capacity')
    if type(program['load_multiple']) is not int or program['load_multiple'] != 4:
        raise ValueError('fixed load4m')
    if program['keep_failed_windows'] is not True:
        raise ValueError('complete failed windows retained')
    return theta


def _dyadic(value):
    if type(value) is not int or value < 1 or value & (value - 1):
        raise ValueError('strict positive dyadic integer')


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite():
        raise ArithmeticError('finite Arb scalar')
    return value


def _real(value, meter):
    meter.charge(2)
    return _finite(arb(value.numerator) / value.denominator, meter)


def _state(state, X, meter):
    if type(state) is not dict: raise ValueError('complete transported state dictionary')
    arrays = []
    for name in ('g', 'G', 'Bg', 'D'):
        values = state.get(name)
        meter.charge(2)
        if type(values) is not list or not 2 <= len(values) <= MAX_HORIZON + 1:
            raise ValueError('complete zero-based transported arrays')
        if not _finite(values[0], meter).is_zero(): raise ValueError('zero dummy coordinate')
        arrays.append(values)
    size = len(arrays[0])
    if any(len(values) != size for values in arrays): raise ValueError('matching full array horizons')
    if 'H' in state and (type(state['H']) is not int or state['H'] != size - 1):
        raise ValueError('strict matching state horizon')
    if 2 * X > size: raise ValueError('complete2X-1 measurement support')
    meter.live(60 * size + 4096)


def measure(state, program, X, meter):
    validate(program, meter)
    if ctx.prec != 192: raise ValueError('independent Arb precision192')
    _dyadic(X); _state(state, X, meter)
    auxiliary = program['auxiliary']
    mix = _real(_rational(program['mix'], meter), meter)
    reserve = _real(_rational(program['reserve'], meter), meter)
    alpha = Fraction(0) if auxiliary is None else _rational(auxiliary['alpha'], meter)
    exponent = _real(-alpha, meter) if alpha else None
    total = arb(0)
    for n in range(X, 2 * X):
        G = _finite(state['G'][n], meter)
        Q = arb(0)
        if auxiliary is not None:
            kind = auxiliary['kind']
            if kind == 'log_bank':
                meter.charge(POWER_WORK)
                logarithm = _finite(arb(2 * n).log(), meter)
                Q = _finite(_finite(state['Bg'][n], meter) / logarithm, meter)
            elif kind == 'half_delay':
                Q = _finite(state['G'][n // 2], meter)
            else:
                Q = _finite(state['D'][n], meter)
            if exponent is not None:
                meter.charge(POWER_WORK)
                factor = _finite(arb(n) ** exponent, meter)
                Q = _finite(Q * factor, meter)
        # Square the complete scalar before adding the reserve. No independent
        # squares of the target/auxiliary are substituted for their signed cross.
        mixed = _finite(G + _finite(mix * Q, meter), meter)
        cell = _finite(_finite(mixed * mixed, meter) +
                       _finite(reserve * _finite(Q * Q, meter), meter), meter)
        total = _finite(total + cell, meter)
        meter.charge(3)
    meter.charge(2)
    return _finite(total / (X * X), meter)


def certificate(program, shape, transport_program, pole_witness_verified=False, meter=None):
    if meter is None: meter = _NoMeter()
    validate(program, meter)
    rho, degree = _shape(shape, meter)
    theta = _transport(transport_program, meter)
    if type(pole_witness_verified) is not bool: raise ValueError('strict independently verified witness flag')
    mix = _rational(program['mix'], meter); reserve = _rational(program['reserve'], meter)
    domination = 1 + mix * mix / reserve
    error_power = 2 * theta - Fraction(5, 3)
    conditional_degree = degree + (1 if rho == 1 else 0)
    cofinal = error_power <= 0
    excluded = pole_witness_verified and cofinal and conditional_degree < 2
    meter.charge(36)
    meter.live(512 + sum(len(str(value)) for value in (program, shape, transport_program)))
    return dict(schema='core-control-synthesis-v1', program=deepcopy(program),
        shape=deepcopy(shape), transport_program=deepcopy(transport_program),
        domination_constant=str(domination), full_target_storage_constant=str(2 * domination),
        error_constant='50', error_power=str(error_power),
        conditional_log_degree=str(conditional_degree),
        pole_witness_verified=pole_witness_verified, pole_excluded=excluded,
        cofinal_recovery=cofinal,
        uniform_premise='For every dyadic X>=1, A(2X)<=rho*A(X)+C*(1+log2(X))^log_power '
            'for one fixed integer C>=1 and the complete fixed program/source, with finite base A(1).',
        uniform_premise_established=False, all_scale_storage_bound_proved=False,
        all_scale_target_bound_proved=False, RH_proved=False)


def check_test(storage_by_scale, parents, shape, C, meter):
    if ctx.prec != 192: raise ValueError('independent Arb precision192')
    rho, degree = _shape(shape, meter)
    if type(C) is not int or not 1 <= C or C.bit_length() > SCALAR_BITS:
        raise ValueError('strict frozen positive integer recurrence constant')
    if type(storage_by_scale) is not dict or type(parents) is not list or not parents:
        raise ValueError('storage dictionary and nonempty parent-scale list')
    for X, value in storage_by_scale.items():
        _dyadic(X); _finite(value, meter)
        if value < 0: raise ValueError('storage cannot be certified negative')
    last = 0
    for X in parents:
        _dyadic(X); meter.charge(3)
        if X <= last or X not in storage_by_scale or 2 * X not in storage_by_scale:
            raise ValueError('strict increasing complete parent/child scales')
        last = X
    meter.live(6 * len(storage_by_scale) + 8 * len(parents) + 4096)
    rho_ball = _real(rho, meter); degree_ball = _real(degree, meter)
    rows = []
    for X in parents:
        drift = _finite(storage_by_scale[2 * X] -
                        _finite(rho_ball * storage_by_scale[X], meter), meter)
        # 1+log2(X) is the exact integer bit_length for dyadic X.
        meter.charge(POWER_WORK)
        bound = _finite(C * _finite(arb(X.bit_length()) ** degree_ball, meter), meter)
        meter.charge(4)
        status = 'pass' if drift <= bound else 'fail' if drift > bound else 'unresolved'
        meter.charge(110)
        rows.append(dict(X=X, status=status, drift=drift.str(55), upper_bound=bound.str(55)))
    return rows
