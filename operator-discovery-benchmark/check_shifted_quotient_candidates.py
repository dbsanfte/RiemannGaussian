"""Independent Arb reconstruction of complete shifted quotient candidates.

Sources are factored independently; each kernel and convolution output row
enumerates its complete divisors. No producer arithmetic is imported. Ball
enclosures verify finite evaluations, never a uniform signed moment theorem.
"""
from fractions import Fraction as Q
from math import comb, isqrt
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
    if type(items) is not list or not 1 <= len(items) <= 3:
        raise ValueError('one through three shifts')
    result = []
    for text in items:
        if type(text) is not str or not 1 <= len(text) <= 32 or re.fullmatch(r'-?\d+(?:/\d+)?', text) is None:
            raise ValueError('bounded canonical rational shift')
        try: value = Q(text)
        except (ValueError, ZeroDivisionError) as error: raise ValueError('rational shift') from error
        if str(value) != text or not 0 < value < 1 or value.denominator > 24:
            raise ValueError('canonical shift strictly between0and1, denominator<=24')
        result.append(value)
    if any(a >= b for a, b in zip(result, result[1:])):
        raise ValueError('strictly increasing distinct shifts')
    return tuple(result)


def _precision():
    if type(ctx.prec) is not int or not 128 <= ctx.prec <= 256:
        raise ValueError('caller must set Arb precision128..256 bits')


def _horizon(H):
    if type(H) is not int or not 1 <= H <= MAX_HORIZON:
        raise ValueError('strict integer complete horizon1..262143')


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite():
        raise ArithmeticError('finite Arb enclosure required')
    return value


def _real(value, meter):
    meter.charge(2)
    return _finite(arb(value.numerator) / value.denominator, meter)


def _spf(H, meter):
    """Smallest-prime sieve, independently used for full row factorization."""
    _horizon(H); meter.charge(H + 1)
    table = [0] * (H + 1)
    for p in range(2, isqrt(H) + 1):
        meter.charge()
        if table[p]: continue
        for n in range(p * p, H + 1, p):
            meter.charge()
            if not table[n]: table[n] = p
    meter.live(2 * (H + 1) + 256)
    return table


def _factor(n, spf, meter):
    factors = []
    while n > 1:
        meter.charge()
        p = spf[n] or n; exponent = 0
        while n % p == 0:
            meter.charge(2); n //= p; exponent += 1
        factors.append((p, exponent))
    return factors


def _divisors(n, spf, meter):
    result = [1]
    for p, exponent in _factor(n, spf, meter):
        old = list(result); power = 1
        for _ in range(exponent):
            meter.charge(); power *= p
            for d in old:
                meter.charge(); result.append(d * power)
    return result


def source(name, H, meter):
    _horizon(H)
    if type(name) is not str or name not in SOURCES:
        raise ValueError('declared actual/control source')
    spf = _spf(H, meter); values = [0] * (H + 1); values[1] = 1
    for n in range(2, H + 1):
        meter.charge()
        if name == 'one': values[n] = 1; continue
        factors = _factor(n, spf, meter)
        sign = 1
        for p, exponent in factors:
            meter.charge()
            if exponent > 1: sign = 0; break
            if name == 'mu' or p <= 13: sign = -sign
        values[n] = sign
    meter.live(2 * (H + 1) + 512)
    return values


def normalizer(program, meter):
    _precision(); shifts = validate(program); meter.charge(len(shifts))
    result = []
    for b in shifts:
        arg = _real(1 - b, meter); meter.charge(ZETA_WORK)
        z = _finite(arg.zeta(), meter)
        if z.contains(0): raise ArithmeticError('normalizing zeta not separated from zero')
        residue = _finite(1 / _finite(_real(b, meter) * z, meter), meter)
        for other in shifts:
            if other == b: continue
            argument = _real(1 - b + other, meter); meter.charge(ZETA_WORK)
            ratio = _finite(_finite(argument.zeta(), meter) / z, meter)
            factor = _finite(_finite(ratio - 1, meter) / _real(other, meter), meter)
            residue = _finite(residue * factor, meter)
        coefficient = _finite(residue / _real(1 - b, meter), meter)
        result.append(dict(shift=str(b), residue=residue, coefficient=coefficient))
    return result


class State(dict):
    """Four public fields; private power memo lasts only for this evaluation."""
    def __init__(self, *args, powers=None, **kwargs):
        super().__init__(*args, **kwargs)
        self._powers = {} if powers is None else powers


def _powers(b, H, meter):
    exponent = _real(-b, meter)
    out = [arb(0), arb(1)]
    meter.charge(2)
    for n in range(2, H + 1):
        meter.charge(POWER_WORK)
        out.append(_finite(arb(n) ** exponent, meter))
    return out


def _kernel(b, values, spf, powers, meter):
    H = len(values) - 1; result = [arb(0)] * (H + 1)
    divisor = _real(b, meter)
    for n in range(2, H + 1):
        total = arb(0)
        for d in _divisors(n, spf, meter):
            meter.charge(2)
            total = _finite(total + _finite(values[d] * powers[n // d], meter), meter)
        result[n] = _finite(total / divisor, meter)
    # This zero is structural, not the generic divisor formula at n=1.
    result[1] = arb(0)
    return result


def _convolution(left, right, spf, meter):
    H = len(left) - 1; result = [arb(0)] * (H + 1)
    meter.charge(H + 1)
    for n in range(2, H + 1):
        total = arb(0)
        for d in _divisors(n, spf, meter):
            meter.charge()
            if d == 1 or d == n: continue  # Both unit coefficients are exactly0.
            total = _finite(total + _finite(left[d] * right[n // d], meter), meter)
        result[n] = total
    return result


def _mainterms(n, rows, powers, meter):
    signed = arb(0); envelope = arb(0)
    for row in rows:
        b = Q(row['shift'])
        if row['shift'] in powers:
            # n^(1-b)=n*n^(-b), saving a second charged real power.
            power = _finite(n * powers[row['shift']][n], meter)
        else:
            meter.charge(POWER_WORK)
            power = _finite(arb(n) ** _real(1 - b, meter), meter)
        signed = _finite(signed + _finite(row['coefficient'] * power, meter), meter)
        envelope = _finite(envelope + _finite(abs(row['coefficient']) * power, meter), meter)
    return signed, envelope


def evaluate(program, values, meter):
    _precision(); shifts = validate(program)
    if type(values) is not list:
        raise ValueError('complete integer source vector')
    H = len(values) - 1; _horizon(H)
    for value in values:
        meter.charge()
        if type(value) is not int or value not in (-1, 0, 1):
            raise ValueError('strict integer source values{-1,0,1}')
    if values[0] != 0 or values[1] != 1:
        raise ValueError('source index0zero and unit1one')
    meter.live(18 * (H + 1) + 4096)
    spf = _spf(H, meter); tables = {}; coeff = None
    for b in shifts:
        table = _powers(b, H, meter); tables[str(b)] = table
        atom = _kernel(b, values, spf, table, meter)
        coeff = atom if coeff is None else _convolution(coeff, atom, spf, meter)
    rows = normalizer(program, meter)
    centered = [arb(0)] * (H + 1); absolute = [arb(0)] * (H + 1)
    prefix = abs_prefix = arb(0)
    for n in range(1, H + 1):
        prefix = _finite(prefix + coeff[n], meter)
        abs_prefix = _finite(abs_prefix + abs(coeff[n]), meter)
        main, abs_main = _mainterms(n, rows, tables, meter)
        centered[n] = _finite(prefix - main, meter)
        absolute[n] = _finite(abs_prefix + abs_main, meter)
    meter.live(18 * (H + 1) + 4096)
    return State(coefficients=coeff, centered=centered, absolute=absolute, normalizer=rows, powers=tables)


def baseline(degree, H, meter):
    """Complete (mu-delta_1) convolution power, not mu^degree-delta_1."""
    _precision(); _horizon(H)
    if type(degree) is not int or not 1 <= degree <= 3:
        raise ValueError('strict baseline degree1..3')
    spf = _spf(H, meter); integers = [0] * (H + 1)
    for n in range(1, H + 1):
        factors = _factor(n, spf, meter); value = 0
        for j in range(degree + 1):
            term = int(n == 1) if j == 0 else 1
            if j:
                for _, exponent in factors:
                    meter.charge(2)
                    term *= (-1) ** exponent * comb(j, exponent) if exponent <= j else 0
            meter.charge(2)
            value += comb(degree, j) * (-1) ** (degree - j) * term
        integers[n] = value
    cumulative = absolute = 0
    centered = [arb(0)] * (H + 1); envelope = [arb(0)] * (H + 1)
    for n in range(1, H + 1):
        meter.charge(3)
        # Baseline coefficient balls are exact integers.
        cumulative += integers[n]; absolute += abs(integers[n])
        centered[n] = arb(cumulative); envelope[n] = arb(absolute)
    meter.live(8 * (H + 1) + 4096)
    meter.charge(H + 1); coeff = list(map(arb, integers))
    return State(coefficients=coeff, centered=centered, absolute=envelope, normalizer=[])


def _state(state, meter):
    if not isinstance(state, dict) or not {'coefficients', 'centered', 'normalizer'} <= set(state) or set(state) - {'coefficients', 'centered', 'normalizer', 'absolute'}:
        raise ValueError('complete state with explicit normalizer channels')
    if type(state['coefficients']) is not list:
        raise ValueError('complete coefficient list')
    H = len(state['coefficients']) - 1; _horizon(H)
    for key in ('coefficients', 'centered') + (('absolute',) if 'absolute' in state else ()):
        vector = state[key]
        if type(vector) is not list or len(vector) != H + 1:
            raise ValueError('same complete state horizon')
        for value in vector:
            _finite(value, meter)
        if not vector[0].is_zero(): raise ValueError('state index0exactzero')
    rows = state['normalizer']
    if type(rows) is not list: raise ValueError('explicit normalizer row list')
    if rows:
        if any(type(r) is not dict or set(r) != {'shift', 'residue', 'coefficient'} for r in rows):
            raise ValueError('normalizer exact channels')
        expected = normalizer({'shifts': [r['shift'] for r in rows]}, meter)
        for old, new in zip(rows, expected):
            for key in ('residue', 'coefficient'):
                _finite(old[key], meter); meter.charge()
                if not old[key].overlaps(new[key]):
                    raise ValueError('whole true-zeta normalizer mismatch')
        rows = expected
    meter.live(18 * (H + 1) + 4096)
    return H, rows


def moments(state, scales, meter):
    _precision(); H, rows = _state(state, meter)
    if type(scales) is not list or len(scales) > H:
        raise ValueError('bounded full-block scale list')
    seen = set()
    for X in scales:
        meter.charge()
        if type(X) is not int or X < 1 or X in seen or 2 * X - 1 > H:
            raise ValueError('distinct positive scales with COMPLETE [X,2X)')
        seen.add(X)
    if not scales: return []
    tables = state._powers if isinstance(state, State) else {}
    requested = [False] * (2 * max(scales))
    for X in scales:
        meter.charge(X)
        for n in range(X, 2 * X): requested[n] = True
    prefix = abs_prefix = arb(0); signed = {}; absolute = {}
    # Prefix coefficients outside requested blocks are still required, while
    # no mainterm power is evaluated beyond the last requested complete block.
    for n in range(1, 2 * max(scales)):
        prefix = _finite(prefix + state['coefficients'][n], meter)
        abs_prefix = _finite(abs_prefix + abs(state['coefficients'][n]), meter)
        if not requested[n]: continue
        main, abs_main = _mainterms(n, rows, tables, meter)
        value = _finite(prefix - main, meter)
        path = _finite(abs_prefix + abs_main, meter)
        meter.charge()
        if not value.overlaps(state['centered'][n]): raise ValueError('centered prefix/mainterm mismatch')
        if 'absolute' in state:
            meter.charge()
            if not path.overlaps(state['absolute'][n]): raise ValueError('all-channel absolute envelope mismatch')
        signed[n] = value; absolute[n] = path
    result = []
    for X in scales:
        energy = envelope = arb(0)
        for n in range(X, 2 * X):
            energy = _finite(energy + _finite(signed[n] ** 2, meter), meter)
            envelope = _finite(envelope + _finite(absolute[n] ** 2, meter), meter)
        result.append(dict(X=X, energy=_finite(energy / (X * X), meter),
                           absolute_energy=_finite(envelope / (X * X), meter)))
    return result
