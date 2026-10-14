"""Signed first-jet prime errors with unrestricted finite dilation filters.

The logarithmic bridge needs a multiplier that is not identically zero.
Isolated multiplier zeros are allowed. No uniform arithmetic bound is given.
"""
from fractions import Fraction as Q
from math import ceil, comb, factorial
import flint
from exact_arithmetic import formal_log
from estimate_grammar import inverse_one_prefix

VERSION = "signed-first-jet-prime-errors-and-logarithmic-faithfulness-v1"


def real(x):
    x = Q(x)
    return flint.arb(x.numerator)/x.denominator


def logarithmic_coefficients(N):
    """Negative first coefficient-power jet, without primes or factorisation."""
    return [-v for v in formal_log(list(map(Q, inverse_one_prefix(N))))]


def prefix(f):
    result = [Q(0)]
    for v in f[1:]:
        result.append(result[-1]+Q(v))
    return result


def canonical_atoms(atoms):
    grouped = {}
    for delay, coefficient in atoms:
        d,c = Q(delay),Q(coefficient)
        if d < 1:
            raise ValueError("A dilation delay must be at least one")
        grouped[d] = grouped.get(d,Q(0))+c
    result = [(d,c) for d,c in sorted(grouped.items()) if c]
    if not result or result[0] != (Q(1),Q(1)):
        raise ValueError("The normalized smallest-delay coefficient must be one")
    return [[str(d),str(c)] for d,c in result]


def value(count_prefix,x,beta=1):
    """Truncated first jet li(x)-beta*Pi_<(x) for x>=2; zero for x<2.

    This bounded-interval truncation removes the log-log singularity near
    one. It changes the Mellin transform by an entire function only.
    """
    x,beta = Q(x),Q(beta)
    if x <= 0:
        raise ValueError("A positive real scale is required")
    if x < 2:
        return flint.arb(0)
    top = (x.numerator-1)//x.denominator
    if top >= len(count_prefix):
        raise ValueError("A complete logarithmic coefficient prefix is required")
    return real(x).log().ei()-real(beta*count_prefix[top])


def response(program,count_prefix,points):
    atoms = canonical_atoms(program["atoms"])
    return {str(x): sum((real(c)*value(count_prefix,Q(x)/Q(d),program["beta"])
                        for d,c in atoms),flint.arb(0)) for x in points}


def multiplier(program,s):
    return sum((real(c)*(-s*real(d).log()).exp() for d,c in program["atoms"]),flint.acb(0))


def increment_cost(program):
    """Uniform whole-unit increment cost, including actual prime-power jumps."""
    beta = Q(program["beta"])
    li2, log2 = real(2).log().ei(),real(2).log()
    return sum((real(abs(Q(c)))*(real(abs(beta))+1/(real(d)*log2)+
                (abs(li2) if Q(d).denominator!=1 else real(0)))
                for d,c in program["atoms"]),real(0))


def transfer(program,theta,log_power,C,offset):
    theta,log_power,C,offset = map(Q,(theta,log_power,C,offset))
    if theta < 0 or log_power < 0 or C <= 0:
        raise ValueError("Nonnegative growth powers and a positive constant are required")
    atoms = canonical_atoms(program["atoms"])
    beta = Q(program["beta"])
    pole_obstruction = beta!=1 and theta<1
    return {"theta":str(theta),"log_power":str(log_power),"constant":str(C),"offset":str(offset),
            "integer_premise":"For every integer n>=1, |R(n)-offset|<=C*n^theta*log(e+n)^log_power",
            "real_extension":"|R(t)-offset|<=C*t^theta*log(e+t)^log_power+B for every real t>=1",
            "increment_cost_ball":serialize(increment_cost(program)),
            "mellin_exponent":str(theta),
            "multiplier_not_identically_zero":True,
            "all_height_multiplier_nonvanishing_required":False,
            "every_ordinary_zero_multiplicity_retained":beta!=0,
            "uncancelled_pole_logarithm_at_one":pole_obstruction,
            "RH_sufficient_if_uniform":beta==1 and theta<=Q(1,2),
            "uniform_signed_premise_proved":False,"RH_proved":False}


def cost(program,cert,sigma,height):
    """Full conditional reciprocal cost at a declared point away from D=0.

    A quantitative all-height inverse bound is NOT claimed. Isolated zeros
    of D are qualitatively harmless, but their removable division needs its
    own quantitative certificate. The logarithmic reconstruction is charged
    its exponential cost, not confused with a direct 1/zeta bound.
    """
    if Q(program["beta"])!=1:
        return None
    theta,ell,C,A = map(Q,(cert[k] for k in ("theta","log_power","constant","offset")))
    sigma,height = Q(sigma),Q(height)
    if sigma <= theta or sigma <= 0:
        raise ValueError("The cost point must lie inside the conditional Mellin domain")
    p = ceil(ell)
    l = (real(1)+flint.arb.const_e()).log()
    integral = sum((comb(p,j)*l**(p-j)*factorial(j)/real(sigma-theta)**(j+1)
                    for j in range(p+1)),real(0))
    H = real(C)*integral+flint.arb(cert["increment_cost_ball"])/real(sigma)
    s = flint.acb(real(sigma),real(height))
    D = multiplier(program,s)
    if not D.abs_lower()>0:
        return None
    log2 = real(2).log()
    compact = log2*(2+flint.arb.const_euler()-log2.log())
    logarithmic_bound = (abs(s)*H+real(abs(A)))/D.abs_lower()+abs(s)*compact
    return abs(s-real(1)).log()+logarithmic_bound


def serialize(v):
    return (v+flint.arb(0,(real(Q(1,2**180))*(1+abs(v))).upper())).str(45)
