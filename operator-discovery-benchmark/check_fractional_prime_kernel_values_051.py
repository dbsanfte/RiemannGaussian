"""Independent higher-precision finite audit via all positive divisors.

No search-producer import, prime-subset evaluator or all-scale admission. Exact
dyadic bounds, factorization and Mobius provenance are checked against the
bound request. Arb remains the shared trusted real-ball arithmetic library.
"""
from fractions import Fraction as Q
from flint import arb, ctx
from check_fractional_prime_kernel_051 import Meter, _request, _expect


def _dyadic(row):
    if type(row) is not list or len(row) != 2:
        raise ValueError('dyadic pair')
    text, power = row
    if type(text) is not str or not 1 <= len(text) <= 1300:
        raise ValueError('bounded dyadic mantissa')
    number = int(text)
    if str(number) != text or number.bit_length() > 4096:
        raise ValueError('canonical bounded dyadic mantissa')
    if type(power) is not int or abs(power) > 16384:
        raise ValueError('bounded typed dyadic exponent')
    return Q(number << power) if power >= 0 else Q(number, 1 << -power)


def bounds(row):
    if type(row) is not dict or set(row) != {'lower_dyadic', 'upper_dyadic', 'ball'}:
        raise ValueError('exact finite enclosure schema')
    if type(row['ball']) is not str or len(row['ball']) > 2048:
        raise ValueError('bounded diagnostic ball text')
    lo, hi = _dyadic(row['lower_dyadic']), _dyadic(row['upper_dyadic'])
    if lo > hi:
        raise ValueError('ordered finite interval')
    return lo, hi


def _enclose(value):
    if not value.is_finite():
        raise ArithmeticError('finite independent Arb value')
    lo, hi = value.lower().man_exp(), value.upper().man_exp()
    return {'lower_dyadic': [str(lo[0]), int(lo[1])],
            'upper_dyadic': [str(hi[0]), int(hi[1])], 'ball': value.str(65)}


def _factor(n, meter):
    rest, p, factors = n, 2, []
    while p*p <= rest:
        exponent = 0
        while rest % p == 0:
            rest //= p
            exponent += 1
            meter.charge(16)
        if exponent:
            factors.append((p, exponent))
        p += 1
        meter.charge(16)
    if rest > 1:
        factors.append((rest, 1))
    return factors


def _all_divisors(factors, meter):
    rows = [(1, 1)]
    for p, e in factors:
        if len(rows)*(e+1) > 4096:
            raise OverflowError('all-positive-divisor resource cap')
        rows = [(d*p**j, mu if j == 0 else -mu if j == 1 else 0)
                for d, mu in rows for j in range(e+1)]
        meter.charge(32*len(rows))
    return sorted(rows)


def _power(base, alpha, exact_zero):
    if exact_zero:
        return arb(0)
    if alpha.denominator == 1:
        return base**alpha.numerator
    return (base.log()*arb(alpha.numerator)/alpha.denominator).exp()


def verify_value(request, n, row, meter=None):
    meter = meter or Meter(cap=100_000_000, seconds=180)
    a, b, alpha, sign = _request(request, meter)
    if type(n) is not int or not 1 <= n < 2**32:
        raise ValueError('typed32-bit ordinary integer')
    if type(row) is not dict:
        raise ValueError('finite producer row')
    _expect(row.get('schema'), 'fractional-prime-kernel-evaluation-v1')
    _expect(row.get('request'), request)
    _expect(row.get('n'), n)
    _expect(row.get('precision'), 192)
    for name in ('all_scale_sign_proved', 'uniform_bound_proved',
                 'proof_provider_used', 'float_sign_admission_used'):
        _expect(row.get(name), False)
    _expect(row.get('arithmetic_provenance'),
            'ordinary Mobius from exact trial factorization; squarefree divisor subset parity')
    _expect(row.get('primepowers_retained_via'), 'log(n/d), with actual n and squarefree d')
    _expect(row.get('zero_base_convention'), '0^alpha=0 for alpha>0')
    factors = _factor(n, meter)
    divisors = _all_divisors(factors, meter)
    _expect(row.get('factorization'), [{'prime': p, 'exponent': e} for p, e in factors])
    _expect(row.get('ordinary_mu_n'), 0 if any(e > 1 for _, e in factors) else (-1)**len(factors))
    _expect(row.get('prime'), len(factors) == 1 and factors[0][1] == 1)
    _expect(row.get('distinct_prime_count'), len(factors))
    _expect(row.get('squarefree_divisors'), [{'d': d, 'mu': mu, 'log_arguments': [d, n//d]}
                                           for d, mu in divisors if mu])
    with ctx.workprec(256):
        total, absolute = arb(0), arb(0)
        for d, mu in divisors:
            meter.charge(32)
            if mu == 0:
                continue
            left, right = arb(d).log(), arb(n//d).log()
            base = left*a.numerator/a.denominator+right*b.numerator/b.denominator
            value = _power(base, alpha, (a == 0 or d == 1) and (b == 0 or d == n))
            total += sign*mu*value
            absolute += value
            meter.charge(256*256)
        fresh = {'value': _enclose(total), 'absolute_divisor_sum': _enclose(absolute)}
        fresh['normalized_by_log_n_alpha'] = (None if n == 1 else _enclose(
            total/_power(arb(n).log(), alpha, False)))
        fresh['signed_over_absolute'] = None if n == 1 else _enclose(total/absolute)
        for name, independent in fresh.items():
            if independent is None:
                _expect(row.get(name), None)
                continue
            old_lo, old_hi = bounds(row.get(name))
            new_lo, new_hi = bounds(independent)
            if not old_lo <= new_lo <= new_hi <= old_hi:
                raise ValueError('independent256-bit result not contained in bound192-bit producer interval: '+name)
    lo, hi = bounds(row['value'])
    status = 'FINITE_NEGATIVE' if hi < 0 else 'FINITE_NONNEGATIVE' if lo >= 0 else 'UNRESOLVED_SIGN'
    _expect(row.get('finite_sign'), status)
    _expect(row.get('strict_positive'), lo > 0)
    _expect(row.get('exact_zero_enclosure'), lo == hi == 0)
    return {'verified': True, 'request': request, 'n': n, 'precision': 256,
            'method': 'independent all-positive-divisor enumeration; exp(alpha*log(base))',
            'producer_intervals_contain_independent_intervals': True,
            'ordinary_arithmetic_source_verified': True, 'independent_intervals': fresh,
            'finite_only': True, 'uniform_bound_proved': False, 'RH_proved': False}
