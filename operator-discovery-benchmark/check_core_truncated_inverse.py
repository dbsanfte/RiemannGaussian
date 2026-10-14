"""Independent truncated Dirichlet-inverse identities, not signed bounds.

Polynomial verification uses literal multiplication by the two finite binomial
factors. Numerical reconstruction uses complete divisor convolutions and an
exact integer Mobius-inverse check. Strict cutoff complements, units and prime
powers are retained. No generator or source producer is imported.
"""
from copy import deepcopy
from fractions import Fraction as Q
from math import comb
import re
from flint import arb, ctx

MAX_HORIZON = 524287
SCALAR_BITS = 4096


def _rational(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 2500 or re.fullmatch(r'-?\d+(?:/\d+)?', text) is None:
        raise ValueError('bounded canonical rational string')
    meter.charge(len(text) + 1)
    try: value = Q(text)
    except (ValueError, ZeroDivisionError) as error: raise ValueError('rational string') from error
    if str(value) != text or max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > SCALAR_BITS:
        raise ValueError('bounded canonical rational')
    return value


def _validate(program, meter):
    if type(program) is not dict or set(program) != {'alpha', 'gamma', 'p', 'q', 'terms'}:
        raise ValueError('exact truncated inverse program')
    alpha = _rational(program['alpha'], meter); gamma = _rational(program['gamma'], meter)
    if not 0 < alpha < 1 or not 0 < gamma < 1: raise ValueError('alpha,gamma strictly between0and1')
    p = program['p']; q = program['q']
    if type(p) is not int or type(q) is not int or not 0 <= p <= 2 or not 0 <= q <= 2 or p + q < 1:
        raise ValueError('integer inverse powers0..2 with nonzero total')
    terms = program['terms']
    if type(terms) is not list or not terms: raise ValueError('nonempty sparse inverse polynomial')
    meter.live(64 * len(terms) + 4096)
    decoded = {}; last = None
    for term in terms:
        if type(term) is not dict or set(term) != {'a', 'b', 'coefficient'}: raise ValueError('exact sparse term schema')
        a = term['a']; b = term['b']
        if type(a) is not int or type(b) is not int or min(a, b) < 0 or max(a.bit_length(), b.bit_length()) > SCALAR_BITS:
            raise ValueError('bounded nonnegative integer powers')
        coefficient = _rational(term['coefficient'], meter); key = (a, b)
        if coefficient == 0 or key in decoded: raise ValueError('unique nonzero sparse terms')
        if alpha * a + gamma * b >= 1: raise ValueError('inverse terms strictly below support boundary')
        decoded[key] = coefficient; meter.charge(8)
    return alpha, gamma, p, q, decoded


def verify_certificate(program, meter):
    alpha, gamma, p, q, polynomial = _validate(program, meter)
    residual = {}
    for (a, b), coefficient in polynomial.items():
        for i in range(p + 1):
            for j in range(q + 1):
                key = (a + i, b + j)
                value = coefficient * (-1) ** (i + j) * comb(p, i) * comb(q, j)
                residual[key] = residual.get(key, Q(0)) + value; meter.charge(8)
    residual[(0, 0)] = residual.get((0, 0), Q(0)) - 1; meter.charge()
    residual = {key: coefficient for key, coefficient in residual.items() if coefficient}
    for (a, b), coefficient in residual.items():
        meter.charge(6)
        if alpha * a + gamma * b < 1:
            raise ValueError('inverse residual survives inside the downward-closed region')
        if max(abs(coefficient.numerator).bit_length(), coefficient.denominator.bit_length()) > SCALAR_BITS:
            raise RuntimeError('residual rational bit cap')
    rows = [dict(a=a, b=b, coefficient=str(coefficient), weight=str(alpha * a + gamma * b))
            for (a, b), coefficient in sorted(residual.items())]
    return dict(verified=True, program=deepcopy(program), residual=rows,
        identity='mu^(*p)*mu_v^(*q)=A^(*p)*B^(*q)*P(R,S) on every n<=N',
        support='U=floor(N^alpha),V=floor(N^gamma); R vanishes on1..U,S on1..V; every omitted monomial has (U+1)^a*(V+1)^b>N',
        domain='every integer N>=1; all units, prime powers and cutoff complements',
        exact_all_scale_identity_verified=True, actual_mu_inverse_required=True,
        full_signed_bound_proved=False, core_recurrence_proved=False, RH_proved=False)


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite(): raise ArithmeticError('finite Arb scalar')
    return value


def _real(value, meter):
    meter.charge(2)
    return _finite(arb(value.numerator) / value.denominator, meter)


def _cutoff(N, exponent, meter):
    """Exact floor(N^(a/b)) with pre-allocation integer-bit guards."""
    a = exponent.numerator; b = exponent.denominator; meter.charge(3)
    if max(a, b) * max(1, N.bit_length()) > SCALAR_BITS:
        raise RuntimeError('exact cutoff integer-power bit cap')
    meter.charge(a * max(1, N.bit_length()))
    target = N ** a; lower = 1; upper = N + 1
    while lower + 1 < upper:
        middle = (lower + upper) // 2; meter.charge(b * max(1, middle.bit_length()) + 3)
        if middle ** b <= target: lower = middle
        else: upper = middle
    return lower


def _delta(H):
    result = [arb(0)] * (H + 1); result[1] = arb(1); return result


def _convolve(left, right, meter):
    H = len(left) - 1; result = [arb(0)] * (H + 1)
    for d in range(1, H + 1):
        for k in range(1, H // d + 1):
            result[d * k] = _finite(result[d * k] + _finite(left[d] * right[k], meter), meter); meter.charge(2)
    return result


def _power(values, exponent, H, meter, vanishing_below=None):
    # For R and S, the least possible nonzero coordinate is>=2, so very
    # large formal exponents can be discarded without allocating huge powers.
    if vanishing_below is not None and exponent >= H.bit_length():
        meter.charge(); return [arb(0)] * (H + 1)
    result = _delta(H)
    if exponent == 0: return result
    current = values; remaining = exponent
    while remaining:
        meter.charge(2)
        if remaining & 1: result = _convolve(result, current, meter)
        remaining //= 2
        if remaining: current = _convolve(current, current, meter)
    return result


def evaluate(mu, program, H, meter):
    if ctx.prec != 192: raise ValueError('independent Arb precision192')
    certificate = verify_certificate(program, meter)
    alpha, gamma, p, q, polynomial = _validate(program, meter)
    if type(H) is not int or not 1 <= H <= MAX_HORIZON or type(mu) is not list or len(mu) != H + 1:
        raise ValueError('complete strict horizon and Mobius list')
    if any(type(value) is not int or value not in (-1, 0, 1) for value in mu) or mu[0] != 0 or mu[1] != 1:
        raise ValueError('strict Mobius coefficients,dummy0,unit1')
    meter.live((30 + 3 * len(polynomial)) * (H + 1) + 4096)
    # Exact integer divisor sums characterize mu uniquely; no source labels or
    # numerical Mobius responses can bypass the square/power checks.
    divisor_sums = [0] * (H + 1); meter.charge(H + 1)
    for d in range(1, H + 1):
        for n in range(d, H + 1, d): divisor_sums[n] += mu[d]; meter.charge()
    for n in range(1, H + 1):
        meter.charge()
        if divisor_sums[n] != (1 if n == 1 else 0): raise ValueError('complete integer Mobius inverse identity fails')
    U = _cutoff(H, alpha, meter); V = _cutoff(H, gamma, meter)
    mu_ball = list(map(arb, mu)); kernel_v = [arb(0)] * (H + 1); mu_v = [arb(0)] * (H + 1)
    for n in range(1, H + 1):
        meter.charge(64); root = _finite(arb(n).root(3), meter)
        kernel_v[n] = _finite(1 / _finite(root * root, meter), meter)
        mu_v[n] = _finite(mu_ball[n] * kernel_v[n], meter)
    A = [mu_ball[n] if 1 <= n <= U else arb(0) for n in range(H + 1)]
    B = [mu_v[n] if 1 <= n <= V else arb(0) for n in range(H + 1)]
    delta = _delta(H); one = [arb(0)] + [arb(1)] * H
    inverse_a = _convolve(one, A, meter); inverse_b = _convolve(kernel_v, B, meter)
    R = [_finite(delta[n] - inverse_a[n], meter) for n in range(H + 1)]
    S = [_finite(delta[n] - inverse_b[n], meter) for n in range(H + 1)]
    # Weighted inverse zeroes are exact algebraic identities even if Arb root
    # multiplication leaves tiny zero-containing enclosures. Canonicalize only
    # the certified cutoff support, after independently checking containment.
    for n in range(1, U + 1):
        if not R[n].contains(0): raise ArithmeticError('R cutoff inverse support fails')
        R[n] = arb(0); meter.charge()
    for n in range(1, V + 1):
        if not S[n].contains(0): raise ArithmeticError('S cutoff inverse support fails')
        S[n] = arb(0); meter.charge()
    prefactor = _convolve(_power(A, p, H, meter), _power(B, q, H, meter), meter)
    R_powers = {0: delta}; S_powers = {0: delta}; components = []; reconstructed = [arb(0)] * (H + 1)
    for (a, b), coefficient in sorted(polynomial.items()):
        if a not in R_powers: R_powers[a] = _power(R, a, H, meter, U)
        if b not in S_powers: S_powers[b] = _power(S, b, H, meter, V)
        monomial = _convolve(R_powers[a], S_powers[b], meter)
        component = _convolve(prefactor, monomial, meter)
        components.append(dict(a=a, b=b, coefficient=str(coefficient), values=component))
        scalar = _real(coefficient, meter)
        for n in range(1, H + 1):
            reconstructed[n] = _finite(reconstructed[n] + _finite(scalar * component[n], meter), meter)
    reference = _convolve(_power(mu_ball, p, H, meter), _power(mu_v, q, H, meter), meter)
    for left, right in zip(reconstructed, reference):
        meter.charge()
        if not left.overlaps(right): raise ArithmeticError('complete finite truncated inverse reconstruction fails')
    return dict(H=H, U=U, V=V, A=A, B=B, R=R, S=S, terms=components,
                reconstructed=reconstructed, reference=reference, certificate=certificate,
                exact_finite_identity_verified=True, full_signed_bound_proved=False,
                core_recurrence_proved=False, RH_proved=False)
