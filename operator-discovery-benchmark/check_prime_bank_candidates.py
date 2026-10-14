"""Independent complete actual-mu prime-bank arithmetic, with Arb enclosures.

Coefficient rows use factorization/divisor enumeration. Smooth prefixes use
an offline dominance query; prime banks use weighted prime-index Fenwick trees.
No producer arithmetic, numerical responses, or universal-bound claims enter.
"""
from fractions import Fraction
from math import isqrt
import re
from flint import arb, ctx

MAX_HORIZON = 1048575
POWER_WORK = 64
ZETA_WORK = 256
SOURCE_KEYS = ('p', 'a_u', 'a_v', 'd', 'a', 'z0', 'zu', 'zv', 'R', 'main')
OUTPUT_KEYS = ('K', 'L0', 'Lu', 'Lv', 'reduced', 'R', 'main')


def _precision():
    if type(ctx.prec) is not int or not 128 <= ctx.prec <= 256:
        raise ValueError('Arb precision128..256 required')


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite():
        raise ArithmeticError('finite Arb enclosure required')
    return value


def validate(theta_text):
    if type(theta_text) is not str or len(theta_text) > 32 or re.fullmatch(r'\d+(?:/\d+)?', theta_text) is None:
        raise ValueError('canonical bounded rational theta')
    try: theta = Fraction(theta_text)
    except (ValueError, ZeroDivisionError) as error: raise ValueError('rational theta') from error
    if str(theta) != theta_text or not Fraction(1, 2) <= theta < 1 or theta.denominator > 12:
        raise ValueError('canonical theta in[1/2,1), denominator<=12')
    return theta


def _spf(H, meter):
    table = [0] * (H + 1); meter.charge(H + 1)
    for p in range(2, isqrt(H) + 1):
        meter.charge()
        if table[p]: continue
        for n in range(p * p, H + 1, p):
            meter.charge()
            if not table[n]: table[n] = p
    return table


def _factors(n, table, meter):
    factors = []
    while n > 1:
        meter.charge(); p = table[n] or n; exponent = 0
        while n % p == 0:
            meter.charge(2); n //= p; exponent += 1
        factors.append((p, exponent))
    return factors


def _divisors(factors, meter):
    divisors = [1]
    for p, exponent in factors:
        old = list(divisors); power = 1; meter.charge(len(old))
        for _ in range(exponent):
            meter.charge(); power *= p
            for d in old:
                meter.charge(); divisors.append(d * power)
    return divisors


def _integer_power(n, exponent, meter):
    # Exact cutoff comparisons: no real-ball equality decisions.
    meter.charge(max(1, 2 * exponent.bit_length()))
    return n ** exponent


def main_coefficient(meter):
    _precision(); meter.charge(4)
    u = arb(2) / 3; argument = arb(4) / 3
    meter.charge(2 * ZETA_WORK)
    z = _finite(u.zeta(), meter); w = _finite(argument.zeta(), meter)
    if z.contains(0): raise ArithmeticError('zeta(2/3) separated fromzero')
    meter.charge(6)
    return _finite(arb(27) / 4 * (w / (z * z) - 1 / z), meter)


class SourceState(dict):
    """Own complete source; private index tables retained with explicit residency."""
    pass


def source_state(H, meter):
    _precision()
    if type(H) is not int or not 1 <= H <= MAX_HORIZON:
        raise ValueError('strict positive complete horizon<=1048575')
    meter.live(32 * (H + 1) + 4096)
    table = _spf(H, meter)
    result = SourceState({key: [arb(0)] * (H + 1) for key in SOURCE_KEYS})
    result['a_u'][1] = arb(1); result['a_v'][1] = arb(1)
    largest = [0] * (H + 1); prime_index = [0] * (H + 1)
    primes = []; wu = [arb(0)]; wv = [arb(0)]; local = {}
    m = main_coefficient(meter); prefix = arb(0); beta = arb(9) / 2; meter.charge(2)
    for n in range(1, H + 1):
        meter.charge(POWER_WORK)
        root = _finite(arb(n).root(3), meter)
        result['main'][n] = _finite(m * _finite(root * root, meter), meter)
        if n >= 2:
            factors = _factors(n, table, meter); largest[n] = factors[-1][0]
            if len(factors) == 1 and factors[0][1] == 1:
                primes.append(n); prime_index[n] = len(primes)
                u = _finite(1 / root, meter); v = _finite(u * u, meter)
                wu.append(u); wv.append(v)
                # Local a_b(p^e)=p^(-eb)-p^(-(e-1)b).
                local[n] = ([arb(1), _finite(u - 1, meter)], [arb(1), _finite(v - 1, meter)], u, v)
            au = av = arb(1)
            for p, exponent in factors:
                left, right, u, v = local[p]
                while len(left) <= exponent:
                    left.append(_finite(left[-1] * u, meter)); right.append(_finite(right[-1] * v, meter))
                au = _finite(au * left[exponent], meter); av = _finite(av * right[exponent], meter)
            result['a_u'][n] = au; result['a_v'][n] = av
            total = arb(0)
            for d in _divisors(factors, meter):
                meter.charge()
                if d == 1 or d == n: continue
                total = _finite(total + _finite(result['a_u'][d] * result['a_v'][n // d], meter), meter)
            result['p'][n] = _finite(beta * total, meter)
            # Complete same-prime overlap equals p on EVERY prime power.
            result['d'][n] = result['p'][n] if len(factors) == 1 else arb(0)
            result['a'][n] = arb(0) if len(factors) == 1 else result['p'][n]
            result['zu'][n] = _finite(result['p'][n] + _finite(beta * av, meter), meter)
            result['zv'][n] = _finite(result['p'][n] + _finite(beta * au, meter), meter)
            result['z0'][n] = _finite(result['zu'][n] + result['zv'][n], meter)
        prefix = _finite(prefix + result['a'][n], meter)
        result['R'][n] = _finite(prefix - result['main'][n], meter)
    result._H = H; result._table = table; result._largest = largest
    result._primes = primes; result._prime_index = prime_index
    result._wu = wu; result._wv = wv; result._precision = ctx.prec
    result.update(H=H, horizon=H, precision=ctx.prec, m_u=m, spf=table, lpf=largest, primes=primes,
                  prime_u={p: wu[j] for j, p in enumerate(primes, 1)},
                  prime_v={p: wv[j] for j, p in enumerate(primes, 1)})
    meter.charge(2 * len(primes))
    return result


class _Fenwick:
    def __init__(self, length, meter):
        self.tree = [arb(0)] * (length + 1); self.meter = meter
        meter.charge(length + 1)

    def add(self, index, value):
        while index < len(self.tree):
            self.tree[index] = _finite(self.tree[index] + value, self.meter)
            self.meter.charge(); index += index & -index

    def prefix(self, index):
        total = arb(0)
        while index:
            total = _finite(total + self.tree[index], self.meter)
            self.meter.charge(); index -= index & -index
        return total


def evaluate(theta_text, state, meter):
    theta = validate(theta_text); _precision()
    if not isinstance(state, SourceState) or state._precision != ctx.prec:
        raise ValueError('own complete source state at current precision required')
    H = state._H
    if any(type(state[key]) is not list or len(state[key]) != H + 1 for key in SOURCE_KEYS):
        raise ValueError('complete source array dimensions')
    primes = state._primes; largest = state._largest
    meter.live(38 * (H + 1) + 8 * (len(primes) + 1) + 4096)
    # Prime powers are bounded exact integers; comparing p^den <= n^num
    # includes equality in the smooth sector, enforcing the strict bank cutoff.
    threshold_powers = [_integer_power(p, theta.denominator, meter) for p in primes]
    smooth = _Fenwick(H, meter)
    banks = [_Fenwick(len(primes), meter) for _ in range(3)]
    out = {key: [arb(0)] * (H + 1) for key in OUTPUT_KEYS[:5]}
    out['R'] = state['R']; out['main'] = state['main']
    out['theta'] = theta_text; out['H'] = H; out['horizon'] = H
    cutoff = 0; totals = [arb(0)] * 3
    channels = (state['z0'], state['zu'], state['zv'])
    for n in range(1, H + 1):
        power = _integer_power(n, theta.numerator, meter)
        while cutoff < len(primes) and threshold_powers[cutoff] <= power:
            p = primes[cutoff]
            # Offline dominance: add every a(t) with largest prime p, even
            # future t; query below n restores the ORIGINAL prefix endpoint.
            for t in range(p, H + 1, p):
                meter.charge()
                if largest[t] == p:
                    smooth.add(t, state['a'][t])
            cutoff += 1; meter.charge()
        out['K'][n] = smooth.prefix(n)
        q = largest[n]
        if q and q * q > n and n // q > 1:
            k = n // q; index = state._prime_index[q]
            weights = (arb(1), state._wu[index], state._wv[index])
            for j in range(3):
                value = _finite(channels[j][k] * weights[j], meter)
                banks[j].add(index, value); totals[j] = _finite(totals[j] + value, meter)
        for j, key in enumerate(('L0', 'Lu', 'Lv')):
            out[key][n] = _finite(totals[j] - banks[j].prefix(cutoff), meter)
        out['reduced'][n] = _finite(out['K'][n] - out['L0'][n] + out['Lu'][n] - state['main'][n], meter)
        meter.charge(2)  # intermediate subtraction/addition above
    return out
