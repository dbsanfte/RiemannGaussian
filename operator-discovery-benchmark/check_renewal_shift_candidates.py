"""Independent finite Arb checker for compiled renewal-shift quotients.

Local Euler factors are expanded by linear/geometric polynomial operations,
never the producer's logarithmic recurrence. Every source has the same complete
true-zeta centering; numerical enclosures carry no universal moment theorem.
"""
from fractions import Fraction as Q
from itertools import product
from math import isqrt, lcm
import re

from flint import arb, ctx

MAX_HORIZON = 262143
SOURCES = ('mu', 'one', 'partial_prime_13')
POWER_WORK = 64
ZETA_WORK = 256
FLAGS = dict(uniform_signed_bound_proved=False, RH_proved=False,
             finite_prefix_inverse_claimed=False, historical_novelty_claimed=False)


def validate(program):
    if type(program) is not dict or set(program) != {'shifts'}:
        raise ValueError('exact shifts-only program')
    items = program['shifts']
    if type(items) is not list or not 1 <= len(items) <= 4:
        raise ValueError('one through four rational shifts')
    shifts = []
    for text in items:
        if type(text) is not str or not 1 <= len(text) <= 32 or re.fullmatch(r'-?\d+(?:/\d+)?', text) is None:
            raise ValueError('bounded canonical rational text')
        try: b = Q(text)
        except (ValueError, ZeroDivisionError) as error: raise ValueError('rational shift') from error
        if str(b) != text or not 0 < b < 1:
            raise ValueError('canonical shift strictly between0and1')
        shifts.append(b)
    if any(a > b for a, b in zip(shifts, shifts[1:])):
        raise ValueError('nondecreasing shift multiset')
    if sum(shifts, Q(0)) >= 1 or lcm(*(b.denominator for b in shifts)) > 24:
        raise ValueError('sum shifts<1 and denominator LCM<=24')
    return tuple(shifts)


def stencil(program):
    """Enumerate all subset channels, retaining collisions by integer merging."""
    shifts = validate(program); merged = {}
    for included in product((0, 1), repeat=len(shifts)):
        t = sum((b for b, flag in zip(shifts, included) if flag), Q(0))
        c = 1 if sum(included) % 2 else -1
        merged[t] = merged.get(t, 0) + c
    return sorted((t, c) for t, c in merged.items() if c)


def _license(program):
    shifts = validate(program); compiled = stencil(program)
    if any(c > 0 and c != 1 for _, c in compiled):
        raise ValueError('unsupported higher real pole: positive merged exponent must equal1')
    L = Q(1)
    for b in shifts: L *= b
    return shifts, compiled, lcm(*(b.denominator for b in shifts)), L


def _precision():
    if type(ctx.prec) is not int or not 128 <= ctx.prec <= 256:
        raise ValueError('caller Arb precision128..256 bits')


def _horizon(H):
    if type(H) is not int or not 1 <= H <= MAX_HORIZON:
        raise ValueError('strict complete integer horizon1..262143')


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite():
        raise ArithmeticError('finite Arb enclosure required')
    return value


def _real(value, meter):
    meter.charge(2)
    return _finite(arb(value.numerator) / value.denominator, meter)


def _integer_power(value, exponent, meter):
    """Small integer powers by explicit charged multiplication, not real pow."""
    if type(exponent) is not int or exponent < 0:
        raise ValueError('nonnegative integer monomial exponent')
    result = arb(1); base = value
    while exponent:
        meter.charge()
        if exponent & 1: result = _finite(result * base, meter)
        exponent //= 2
        if exponent: base = _finite(base * base, meter)
    return result


def _spf(H, meter):
    meter.charge(H + 1); table = [0] * (H + 1)
    for p in range(2, isqrt(H) + 1):
        meter.charge()
        if table[p]: continue
        for n in range(p * p, H + 1, p):
            meter.charge()
            if not table[n]: table[n] = p
    return table


def _factor(n, table, meter):
    result = []
    while n > 1:
        meter.charge(); p = table[n] or n; exponent = 0
        while n % p == 0:
            meter.charge(2); n //= p; exponent += 1
        result.append((p, exponent))
    return result


def normalizer(program, meter):
    _, compiled, _, L = _license(program)  # Reject higher poles before Arb work.
    _precision(); result = []
    for t, exponent in compiled:
        if exponent <= 0: continue
        residue = _finite(1 / _real(L, meter), meter)
        for r, c in compiled:
            if r == t: continue
            argument = _real(1 - t + r, meter); meter.charge(ZETA_WORK)
            z = _finite(argument.zeta(), meter)
            factor = _integer_power(z, abs(c), meter)
            if c < 0:
                if factor.contains(0): raise ArithmeticError('zeta factor not separated from zero')
                factor = _finite(1 / factor, meter)
            residue = _finite(residue * factor, meter)
        coefficient = _finite(residue / _real(1 - t, meter), meter)
        result.append(dict(shift=str(t), residue=residue, coefficient=coefficient))
    return result


def _root_table(H, lcd, meter):
    roots = [arb(0), arb(1)]; meter.charge(2)
    for n in range(2, H + 1):
        meter.charge(POWER_WORK)
        roots.append(_finite(arb(n).root(lcd), meter))
    return roots


def _local(compiled, source_name, p, exponent, root, lcd, meter):
    """Truncated Euler rational function via repeated degree-one updates."""
    coefficients = [arb(1)] + [arb(0)] * exponent
    for t, c in compiled:
        integer = t * lcd
        if integer.denominator != 1: raise ValueError('compiled denominator binding')
        power = _integer_power(root, integer.numerator, meter)
        if power.contains(0): raise ArithmeticError('positive prime monomial')
        weight = _finite(1 / power, meter)
        if source_name == 'one':
            k, linear = c, -weight
        elif source_name == 'mu':
            k, linear = -c, -weight
        else:
            k = -c; linear = -weight if p <= 13 else weight
        for _ in range(abs(k)):
            meter.charge()
            if k > 0:
                # Multiply by1+linear*z. Descending order preserves old data.
                for e in range(exponent, 0, -1):
                    coefficients[e] = _finite(coefficients[e] + _finite(linear * coefficients[e - 1], meter), meter)
            else:
                # Divide by1+linear*z. Ascending order is geometric expansion.
                for e in range(1, exponent + 1):
                    coefficients[e] = _finite(coefficients[e] - _finite(linear * coefficients[e - 1], meter), meter)
    return coefficients


class State(dict):
    def __init__(self, *args, program=None, roots=None, lcd=1, **kwargs):
        super().__init__(*args, **kwargs)
        self._program = program; self._roots = roots; self._lcd = lcd


def _main(n, rows, roots, lcd, meter):
    signed = envelope = arb(0)
    if rows and roots is None:
        meter.charge(POWER_WORK); root = _finite(arb(n).root(lcd), meter)
    else:
        root = roots[n] if rows else arb(1)
    for row in rows:
        integer = (1 - Q(row['shift'])) * lcd
        if integer.denominator != 1: raise ValueError('normalizer denominator binding')
        power = _integer_power(root, integer.numerator, meter)
        signed = _finite(signed + _finite(row['coefficient'] * power, meter), meter)
        envelope = _finite(envelope + _finite(abs(row['coefficient']) * power, meter), meter)
    return signed, envelope


def evaluate(program, source_name, H, meter):
    _, compiled, lcd, L = _license(program)
    _precision(); _horizon(H)
    if type(source_name) is not str or source_name not in SOURCES:
        raise ValueError('declared actual/control source')
    meter.live(16 * (H + 1) + 4096)
    roots = _root_table(H, lcd, meter); table = _spf(H, meter); local = {}
    coefficients = [arb(0)] * (H + 1); scale = _real(L, meter)
    for n in range(2, H + 1):
        value = arb(1)
        for p, exponent in _factor(n, table, meter):
            if p not in local:
                maximum = 0; power = p
                while power <= H:
                    meter.charge(); maximum += 1; power *= p
                local[p] = _local(compiled, source_name, p, maximum, roots[p], lcd, meter)
            value = _finite(value * local[p][exponent], meter)
        coefficients[n] = _finite(value / scale, meter)
    rows = normalizer(program, meter)
    centered = [arb(0)] * (H + 1); absolute = [arb(0)] * (H + 1)
    prefix = abs_prefix = arb(0)
    for n in range(1, H + 1):
        prefix = _finite(prefix + coefficients[n], meter)
        abs_prefix = _finite(abs_prefix + abs(coefficients[n]), meter)
        main, abs_main = _main(n, rows, roots, lcd, meter)
        centered[n] = _finite(prefix - main, meter)
        absolute[n] = _finite(abs_prefix + abs_main, meter)
    return State(coefficients=coefficients, centered=centered, absolute=absolute, normalizer=rows,
                 program={'shifts': list(program['shifts'])}, roots=roots, lcd=lcd)


def baseline(H, meter):
    _precision(); _horizon(H); table = _spf(H, meter)
    integers = [0] * (H + 1)
    for n in range(2, H + 1):
        value = 1
        for _, exponent in _factor(n, table, meter):
            meter.charge()
            if exponent > 1: value = 0; break
            value = -value
        integers[n] = value
    coefficients = list(map(arb, integers)); meter.charge(H + 1)
    centered = [arb(0)] * (H + 1); absolute = [arb(0)] * (H + 1)
    prefix = abs_prefix = 0
    for n in range(1, H + 1):
        meter.charge(3); prefix += integers[n]; abs_prefix += abs(integers[n])
        centered[n] = arb(prefix); absolute[n] = arb(abs_prefix)
    meter.live(8 * (H + 1) + 4096)
    return State(coefficients=coefficients, centered=centered, absolute=absolute, normalizer=[])


def _state(state, meter):
    if not isinstance(state, dict) or not {'coefficients', 'centered', 'normalizer'} <= set(state) or set(state) - {'coefficients', 'centered', 'normalizer', 'absolute'}:
        raise ValueError('complete state with every normalizer channel')
    if type(state['coefficients']) is not list: raise ValueError('coefficient list')
    H = len(state['coefficients']) - 1; _horizon(H)
    for key in ('coefficients', 'centered') + (('absolute',) if 'absolute' in state else ()):
        vector = state[key]
        if type(vector) is not list or len(vector) != H + 1: raise ValueError('same complete state horizon')
        for value in vector: _finite(value, meter)
        if not vector[0].is_zero(): raise ValueError('state index0exactzero')
    rows = state['normalizer']
    if type(rows) is not list or len(rows) > 8: raise ValueError('bounded normalizer channel list')
    for row in rows:
        if type(row) is not dict or set(row) != {'shift', 'residue', 'coefficient'}:
            raise ValueError('exact normalizer row')
        text = row['shift']
        if type(text) is not str or not 1 <= len(text) <= 32: raise ValueError('canonical pole shift')
        try: t = Q(text)
        except (ValueError, ZeroDivisionError) as error: raise ValueError('pole shift') from error
        if str(t) != text or not 0 < t < 1: raise ValueError('pole inside0..1')
        _finite(row['residue'], meter); _finite(row['coefficient'], meter)
        expected = _finite(row['residue'] / _real(1 - t, meter), meter)
        if not expected.overlaps(row['coefficient']): raise ValueError('residue/main coefficient mismatch')
    if any(Q(a['shift']) >= Q(b['shift']) for a, b in zip(rows, rows[1:])):
        raise ValueError('distinct increasing normalizer poles')
    if isinstance(state, State) and state._program is not None:
        expected = normalizer(state._program, meter)
        if [r['shift'] for r in expected] != [r['shift'] for r in rows]:
            raise ValueError('all licensed pole channels retained')
        for actual, target in zip(rows, expected):
            if not all(actual[k].overlaps(target[k]) for k in ('residue', 'coefficient')):
                raise ValueError('whole true-zeta normalizer mismatch')
        rows = expected
    lcd = lcm(*(Q(r['shift']).denominator for r in rows)) if rows else 1
    if lcd > 24: raise ValueError('normalizer common denominator<=24')
    meter.live(16 * (H + 1) + 4096)
    return H, rows, lcd


def moments(state, scales, meter):
    _precision(); H, rows, lcd = _state(state, meter)
    if type(scales) is not list or len(scales) > H: raise ValueError('bounded scale list')
    seen = set()
    for X in scales:
        meter.charge()
        if type(X) is not int or X < 1 or X in seen or 2 * X - 1 > H:
            raise ValueError('distinct positive COMPLETE [X,2X) blocks')
        seen.add(X)
    if not scales: return []
    roots = state._roots if isinstance(state, State) else None
    if roots is not None: lcd = state._lcd
    wanted = [False] * (2 * max(scales))
    for X in scales:
        meter.charge(X)
        for n in range(X, 2 * X): wanted[n] = True
    prefix = abs_prefix = arb(0); signed = {}; envelope = {}
    for n in range(1, 2 * max(scales)):
        prefix = _finite(prefix + state['coefficients'][n], meter)
        abs_prefix = _finite(abs_prefix + abs(state['coefficients'][n]), meter)
        if not wanted[n]: continue
        main, abs_main = _main(n, rows, roots, lcd, meter)
        value = _finite(prefix - main, meter); path = _finite(abs_prefix + abs_main, meter)
        if not value.overlaps(state['centered'][n]): raise ValueError('complete signed center mismatch')
        if 'absolute' in state and not path.overlaps(state['absolute'][n]):
            raise ValueError('full absolute channels mismatch')
        signed[n] = value; envelope[n] = path
    result = []
    for X in scales:
        E = A = arb(0)
        for n in range(X, 2 * X):
            E = _finite(E + _finite(signed[n] ** 2, meter), meter)
            A = _finite(A + _finite(envelope[n] ** 2, meter), meter)
        result.append(dict(X=X, energy=_finite(E / (X * X), meter),
                           absolute_energy=_finite(A / (X * X), meter)))
    return result
