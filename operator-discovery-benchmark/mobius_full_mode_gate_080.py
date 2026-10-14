"""Postrun full-channel and second-log obstruction proposals, without mu queries."""
from fractions import Fraction as Q
from functools import lru_cache

import mobius_symbolic_cover_080 as S


@lru_cache(maxsize=1)
def rho_envelope():
    bits, mesh = 40, 64
    scale = 1 << bits
    lower = Q(S.log_spec('3')['lower'])
    lower = Q((lower*scale).numerator//(lower*scale).denominator, scale)
    summands = []
    for i in range(1, mesh+1):
        v = 1+Q(i, mesh)
        upper = Q(S.log_spec(str(v))['upper'])/(mesh*(v+1))
        summands.append(S.OLD.round_up(upper, bits))
    upper = 1-lower+sum(summands, Q(0))
    if not 0 < upper < Q(1, 16):
        raise ArithmeticError('rho3 envelope construction failed')
    return dict(mesh=mesh, bits=bits, log_terms=32, lower_log_three=str(lower),
        upper_riemann_summands=list(map(str, summands)), rho_three_upper=str(upper))


def source_mass(kernel, primes):
    mass = sum((Q(x['weight'])/x['divisor'] for x in kernel), Q(0))
    delta = Q(1)
    for p in primes:
        delta *= Q(p-1, p)
    return mass, delta


def full_polynomial(ray, r):
    a = S.ray_key(ray)
    return (-a[1][0]+a[8][0]+r*(a[7][0]-a[8][0]),
            -a[1][1]+a[8][1]+a[9][0]-a[8][0]+r*(a[7][1]-a[8][1]),
            a[9][1]-a[8][1])


def propose_full_mode(kernel, primes, gamma, ray, logspec, rho=None):
    a, g = S.ray_key(ray), Q(gamma)
    if not Q(1, 2) < g <= Q(2, 3) or any(any(x) for i, x in enumerate(a) if i not in (1, 7, 8, 9)):
        return dict(status='UNSUPPORTED_FULL_MODE_DOMAIN')
    if Q(logspec['argument']) != (3-2*g)/(2*g):
        raise ValueError('log argument not bound to cutoff')
    rho = rho or rho_envelope()
    mass, delta = source_mass(kernel, primes)
    scale = mass*delta/2
    ranges = [S.polynomial_range(S.poly_scale(full_polynomial(ray, r), scale), logspec)
              for r in (Q(0), Q(rho['rho_three_upper']))]
    lo, hi = min(x[0] for x in ranges), max(x[1] for x in ranges)
    base = full_polynomial(ray, Q(0))
    multiplier = S.poly_scale((a[7][0]-a[8][0], a[7][1]-a[8][1]), scale)
    ml, mh = S.polynomial_range(multiplier, logspec)
    strict = not any(base) and not ml <= 0 <= mh
    proved = not lo <= 0 <= hi or strict
    return dict(status='FULL_MODE_OBSTRUCTION_PROPOSAL' if proved else 'UNPAID_ZERO_CONTAINING_MODE',
        certificate=dict(mass=str(mass), delta=str(delta), leading_lower=str(lo), leading_upper=str(hi)),
        strict_rho_positivity_used=strict, uniform_signed_target_refuted=False)


def add_interval(total, weight, lower, upper):
    a, b = weight*lower, weight*upper
    return total[0]+min(a, b), total[1]+max(a, b)


def propose_second_mode(kernel, primes, gamma, ray, logspec):
    a, g = S.ray_key(ray), Q(gamma)
    if (not Q(1, 2) < g <= Q(2, 3) or any(any(x) for i, x in enumerate(a) if i not in (1, 9))
            or a[9][1] or not a[9][0] or a[1] != (Q(0), a[9][0])):
        return dict(status='UNSUPPORTED_SECOND_MODE_DOMAIN')
    if Q(logspec['argument']) != (3-2*g)/(2*g):
        raise ValueError('log argument not bound to cutoff')
    if any(not Q(1, 16) <= Q(x['divisor'], 4) <= 16 for x in kernel) or any(not 2 <= p <= 16 for p in primes):
        return dict(status='UNSUPPORTED_LOG_ARGUMENT_DOMAIN')
    mass, delta = source_mass(kernel, primes)
    moment = (mass, mass)
    for entry in kernel:
        bounds = S.log_spec(str(Q(entry['divisor'], 4)))
        moment = add_interval(moment, Q(entry['weight'])/entry['divisor'], Q(bounds['lower']), Q(bounds['upper']))
    for p in primes:
        bounds = S.log_spec(str(p))
        moment = add_interval(moment, -mass/Q(p-1), Q(bounds['lower']), Q(bounds['upper']))
    moment = moment[0]*delta, moment[1]*delta
    scale = -a[9][0]/(2*(1-2*g/3))
    lo, hi = sorted([scale*moment[0], scale*moment[1]])
    return dict(status='SECOND_MODE_OBSTRUCTION_PROPOSAL' if not lo <= 0 <= hi else 'UNPAID_ZERO_CONTAINING_SECOND_MODE',
        certificate=dict(mass=str(mass), delta=str(delta), moment_lower=str(moment[0]), moment_upper=str(moment[1]),
            leading_lower=str(lo), leading_upper=str(hi)), uniform_signed_target_refuted=False)
