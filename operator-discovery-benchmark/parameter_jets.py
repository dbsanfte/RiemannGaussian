"""General coefficient-power jets and one-sided logarithmic-kernel jets.

A jet contains Taylor coefficients, not unnormalised derivatives. These
operations expose parameter dependence; they do not assert a growth bound.
The zero-kernel extension has a declared strict endpoint and x>1 domain.
"""
from fractions import Fraction as Q
from math import factorial
import flint
from exact_arithmetic import convolve, formal_log, normalized_power

VERSION = "dirichlet-parameter-and-log-kernel-jets-v1"


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def power_parameter_jet(f, centre, order):
    """[h^j] f**(centre+h), finite at every arithmetic index.

    Accepts any rational sequence with f(1)=1, any rational centre and any
    nonnegative integer order. No multiplicativity or prime labels required.
    """
    if type(order) is not int or order < 0:
        raise ValueError("A nonnegative integer jet order is required")
    if len(f) < 2 or Q(f[1]) != 1:
        raise ValueError("A coefficient power requires f(1)=1")
    f = list(map(Q, f))
    logarithm = formal_log(f)
    term = normalized_power(f, Q(centre))
    result = [term]
    for j in range(1, order + 1):
        term = [c / j for c in convolve(term, logarithm)]
        result.append(term)
    return result


def _exp_jet(logarithm):
    result = [logarithm[0].exp()]
    for j in range(1, len(logarithm)):
        result.append(sum((k * logarithm[k] * result[j-k]
                           for k in range(1, j+1)), flint.arb(0)) / j)
    return result


def logarithmic_kernel_zero_jet(u, order, kappa=1, terms=160):
    """[a^j] K_(a,kappa)(u) at a=0+, for fixed u>0.

    K(a,u)=u**a/Gamma(1+a)*(1+sum a/(a+k)*(kappa*u)**k/k!).
    Every omitted scalar series receives an explicit geometric tail ball.
    There is no extension at u=0: K(a,0)=0 for a>0 but the u>0
    constant coefficient equals one. Fixed-u jets are not uniform-u bounds.
    """
    if type(order) is not int or order < 0:
        raise ValueError("A nonnegative integer jet order is required")
    if type(terms) is not int or terms < 1:
        raise ValueError("A positive series budget is required")
    if not u.is_finite() or not u > 0:
        raise ValueError("The one-sided zero-kernel jet requires u>0")
    z = real(kappa) * u
    magnitude = abs(z).upper()
    ratio = magnitude / (terms + 2)
    if not ratio < 1:
        raise ValueError("Increase the series budget to certify its tail")
    logarithm = [flint.arb(0)] * (order + 1)
    if order:
        logarithm[1] = u.log() + flint.arb.const_euler()
    for j in range(2, order + 1):
        logarithm[j] = (-1)**(j+1) * flint.arb(j).zeta() / j
    prefactor = _exp_jet(logarithm)
    hypergeometric = [flint.arb(1)] + [flint.arb(0)] * order
    term = flint.arb(1)
    for k in range(1, terms + 1):
        term *= z / k
        for j in range(1, order + 1):
            hypergeometric[j] += (-1)**(j-1) * term / k**j
    next_term = magnitude**(terms+1) / factorial(terms+1)
    for j in range(1, order + 1):
        radius = (next_term / (terms+1)**j / (1-ratio)).upper()
        hypergeometric[j] += flint.arb(0, radius)
    return [sum((prefactor[j-k] * hypergeometric[k] for k in range(j+1)),
                flint.arb(0)) for j in range(order+1)]


def strict_cutoff(x):
    x = Q(x)
    if x <= 1:
        raise ValueError("The one-sided arithmetic family requires x>1")
    return (x.numerator - 1) // x.denominator


def family_zero_jet(f, x, order, coefficient_slope=1, kernel_slope=1,
                    kappa=1):
    """[h^j] sum_(n<x) (f**(q*h))(n) K_(r*h,kappa)(log(x/n)).

    q is rational; r must be positive. Thus nearby coefficient and kernel
    powers may vary independently. A matched path is not assumed here.
    """
    x, q, r = map(Q, (x, coefficient_slope, kernel_slope))
    if r <= 0:
        raise ValueError("The one-sided kernel slope must be positive")
    top = strict_cutoff(x)
    if top >= len(f):
        raise ValueError("The complete coefficient prefix is too short")
    coefficients = power_parameter_jet(f, 0, order)
    result = [flint.arb(0) for _ in range(order+1)]
    for n in range(1, top+1):
        if not any(row[n] for row in coefficients):
            continue
        weights = logarithmic_kernel_zero_jet(real(x / n).log(), order, kappa)
        for j in range(order+1):
            for k in range(j+1):
                result[j] += real(coefficients[k][n] * q**k * r**(j-k)) * weights[j-k]
    return result


def root_count_decode(log_coefficients, inversion_coefficients, x):
    """Finite root-count inversion using exact n**k<x endpoint comparisons.

    For lambda=log_D(1) and mu=inverse_D(1), this equals pi_<(x).
    The routine accepts the supplied sequences; it has no prime oracle.
    """
    x = Q(x)
    top = strict_cutoff(x)
    if top >= len(log_coefficients):
        raise ValueError("The complete logarithmic prefix is too short")
    result, k = Q(0), 1
    while Q(2**k) < x:
        if k >= len(inversion_coefficients):
            raise ValueError("The complete inversion prefix is too short")
        count = sum((Q(log_coefficients[n]) for n in range(2, top+1)
                     if Q(n**k) < x), Q(0))
        result += Q(inversion_coefficients[k]) * count / k
        k += 1
    return result
