"""Independent exact 16-mask occupancy eigenmode and prefix-kernel checks.

The scalar bulk envelope is algebraic. Neither it nor kernel recomposition
proves energy contraction or recovers the full arithmetic target.
"""
from fractions import Fraction as Q
from math import isqrt, comb
import re

MAX_KERNEL_X = 256
MAX_KERNEL_INDEX = 1048575


def _rational(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 128 or re.fullmatch(r'-?\d+(?:/\d+)?', text) is None:
        raise ValueError('bounded canonical rational string')
    try: value = Q(text)
    except (ValueError, ZeroDivisionError) as error: raise ValueError('rational value') from error
    if str(value) != text: raise ValueError('canonical rational string')
    meter.charge()
    return value


def _potential(values, meter):
    if type(values) is not list or len(values) != 16:
        raise ValueError('all16 exactly occupied masks required')
    return [_rational(value, meter) for value in values]


def _poly(values, meter):
    meter.charge(len(values))
    return [str(value) for value in values]


def verify_mode(potential, eigen_u, eigen_v, meter):
    f = _potential(potential, meter)
    if not any(f): raise ValueError('nonzero discovery mode required')
    a = _rational(eigen_u, meter); b = _rational(eigen_v, meter)
    Nu = []; Nv = []
    for mask in range(16):
        meter.charge(8)
        u = f[mask | 1] + f[mask | 4]
        v = f[mask | 2] + f[mask | 8]
        if u != a * f[mask] or v != b * f[mask]:
            raise ValueError('exact occupancy eigenrelation failed')
        Nu.append(u); Nv.append(v)
    meter.charge(10)
    endpoints = (1 - a - b, 1 - a - b + Q(4, 5) * a + Q(16, 25) * b)
    envelope = max(abs(value) for value in endpoints) if a >= 0 and b >= 0 else None
    stable = envelope is not None and envelope <= 1
    # This consequence uses mask15 in BOTH eigenrelations, not a rank fit.
    if stable and f[15] != 0:
        raise AssertionError('stable-mode final-mask obstruction failed')
    return dict(potential=potential, eigen_u=str(a), eigen_v=str(b),
                Nu=[str(value) for value in Nu], Nv=[str(value) for value in Nv],
                bulk_polynomial=_poly([1 - a - b, a, b], meter),
                bulk_envelope=None if envelope is None else str(envelope),
                envelope_domain='0<t=q^(-1/3)<4/5',
                envelope_hypothesis='nonnegative eigen_u and eigen_v',
                stable=stable, zero_mode=not any(f), final_mask_value=str(f[15]),
                stable_final_mask_zero=stable and f[15] == 0,
                algebraic_envelope_only=True, energy_contraction_proved=False,
                full_target_recovered=False, whole_signed_bound_proved=False, RH_proved=False)


def _index(value, name, upper):
    if type(value) is not int or not 1 <= value <= upper:
        raise ValueError('strict bounded positive integer ' + name)


def _fresh_prime(q, h, k, meter):
    if q < 2: raise ValueError('fresh prime>=2')
    for d in range(2, isqrt(q) + 1):
        meter.charge()
        if q % d == 0: raise ValueError('prime-adjunction index must be prime')
    meter.charge(2)
    if h % q == 0 or k % q == 0: raise ValueError('prime must be fresh for BOTH argument indices')


def verify_kernel(potential, X, q, h, k, mask, meter):
    f = _potential(potential, meter)
    _index(X, 'tiny fixture X', MAX_KERNEL_X)
    for value, name in ((q, 'q'), (h, 'h'), (k, 'k')): _index(value, name, MAX_KERNEL_INDEX)
    if type(mask) is not int or not 0 <= mask < 16: raise ValueError('occupancy mask0..15')
    _fresh_prime(q, h, k, meter)
    W = WL = WR = 0
    # Literal original integer prefixes, including n=X and n=2X-1, with
    # units and OUTSIDE/zero-support indices retained. No closed kernel used.
    for n in range(X, 2 * X):
        meter.charge(10)
        W += int(h <= n and k <= n)
        WL += int(q * h <= n and k <= n)
        WR += int(h <= n and q * k <= n)
    uL, vL, uR, vR = f[mask | 1], f[mask | 2], f[mask | 4], f[mask | 8]
    left = [uL + vL, -uL, -vL]; right = [uR + vR, -uR, -vR]
    bulk = [f[mask] - uL - vL - uR - vR, uL + uR, vL + vR]
    formal = [f[mask] * W - left[0] * WL - right[0] * WR,
              -left[1] * WL - right[1] * WR,
              -left[2] * WL - right[2] * WR]
    bulk_part = [value * W for value in bulk]
    left_exit = [value * (W - WL) for value in left]
    right_exit = [value * (W - WR) for value in right]
    meter.charge(42)
    recomposed = [sum(values, Q(0)) for values in zip(bulk_part, left_exit, right_exit)]
    if formal != recomposed: raise AssertionError('full formal transfer kernel identity')
    return dict(X=X, q=q, h=h, k=k, mask=mask,
                W=W, W_L=WL, W_R=WR, left_exit_count=W - WL, right_exit_count=W - WR,
                polynomial_basis=['1', 'z^2', 'z^4'], z='q^(-1/6)',
                formal_pair=_poly(formal, meter), bulk_multiplier=_poly(bulk, meter),
                left_transfer=_poly(left, meter), right_transfer=_poly(right, meter),
                bulk_part=_poly(bulk_part, meter), left_exit=_poly(left_exit, meter),
                right_exit=_poly(right_exit, meter), recomposed=_poly(recomposed, meter),
                exact_identity_verified=True, domain='q prime and coprime to h,k; all16 masks',
                energy_contraction_proved=False, full_target_recovered=False, whole_signed_bound_proved=False, RH_proved=False)


def verify_recovery(rows, coefficients, target, meter):
    if type(rows) is not list or type(coefficients) is not list or len(rows) != len(coefficients) or len(rows) > 256:
        raise ValueError('bounded matching mode/coordinate lists')
    goal = _potential(target, meter)
    modes = [_potential(row, meter) for row in rows]
    weights = [_rational(coefficient, meter) for coefficient in coefficients]
    reconstructed = [Q(0)] * 16
    for row, weight in zip(modes, weights):
        for mask in range(16):
            meter.charge(2); reconstructed[mask] += weight * row[mask]
    if reconstructed != goal: raise ValueError('complete16-coordinate recovery failed')
    return dict(reconstructed=[str(value) for value in reconstructed], target=target,
                exact_linear_recovery_verified=True,
                scope='literal occupancy coordinates only',
                energy_contraction_proved=False, whole_signed_bound_proved=False, RH_proved=False)


def _bounded(value, meter):
    meter.charge()
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > 4096:
        raise OverflowError('Bernstein rational bit cap')
    return value


def verify_bernstein(poly, segments, meter):
    """Literal exact Bernstein-basis expansion on each certified segment."""
    if type(poly) is not list or len(poly) > 25:
        raise ValueError('bounded sparse univariate polynomial')
    original = {}; previous = -1
    for row in poly:
        if type(row) is not list or len(row) != 2:
            raise ValueError('power/coefficient row')
        power, text = row
        if type(power) is not int or not previous < power <= 24:
            raise ValueError('strict ascending integer powers0..24')
        coefficient = _rational(text, meter)
        if not coefficient: raise ValueError('omit zero sparse coefficients')
        original[power] = coefficient; previous = power
    degree = max(original, default=0)
    if type(segments) is not list or not 1 <= len(segments) <= 256:
        raise ValueError('bounded complete segment partition')
    endpoint = Q(0)
    for segment in segments:
        if type(segment) is not dict or set(segment) != {'left', 'right', 'coefficients'}:
            raise ValueError('exact Bernstein segment schema')
        left = _rational(segment['left'], meter); right = _rational(segment['right'], meter)
        if left != endpoint or not left < right <= Q(9, 10):
            raise ValueError('consecutive increasing partition of[0,9/10]')
        supplied = segment['coefficients']
        if type(supplied) is not list or len(supplied) != degree + 1:
            raise ValueError('degree+1 Bernstein coefficients')
        coefficients = [_rational(text, meter) for text in supplied]
        if any(not -1 <= coefficient <= 1 for coefficient in coefficients):
            raise ValueError('Bernstein coefficients must lie in[-1,1]')
        expanded = [Q(0)] * (degree + 1)
        width_power = _bounded((right - left) ** degree, meter)
        for j, coefficient in enumerate(coefficients):
            scalar = _bounded(coefficient * comb(degree, j) / width_power, meter)
            for k in range(j + 1):
                for l in range(degree - j + 1):
                    meter.charge(6 + 2 * degree)
                    # Expand (z-left)^j*(right-z)^(degree-j) literally.
                    term = _bounded(scalar * comb(j, k) * (-left) ** (j - k) *
                                    comb(degree - j, l) * right ** (degree - j - l) * (-1) ** l, meter)
                    expanded[k + l] = _bounded(expanded[k + l] + term, meter)
        if any(value != original.get(power, Q(0)) for power, value in enumerate(expanded)):
            raise ValueError('exact Bernstein polynomial recomposition failed')
        endpoint = right
    if endpoint != Q(9, 10): raise ValueError('incomplete Bernstein domain coverage')
    meter.charge(10)
    if 2 * Q(9, 10) ** 6 <= 1: raise AssertionError('prime root domain inclusion')
    return dict(verified=True, polynomial=poly, segments=segments,
                domain='0<=z<=9/10', absolute_bound='1',
                prime_root_domain_included=True, algebraic_envelope_only=True,
                energy_contraction_proved=False, whole_signed_bound_proved=False,
                full_target_recovered=False, RH_proved=False)
