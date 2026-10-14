"""Typed ball-valued arithmetic logarithms and their triangular inverses.

The formal laws apply to complete finite prefixes of normalized units.
Prime bounds apply specifically to the constant-one zeta coefficients.
No prime indicator or factorization of the coefficient index is an input.
"""

from fractions import Fraction as Q
from functools import lru_cache

import flint


def real(value):
    value=Q(value)
    return flint.arb(value.numerator)/value.denominator


def complete_prefix(values,normalized):
    if not isinstance(values,(list,tuple)) or len(values)<2:
        raise ValueError('A complete prefix with unused index zero is required')
    out=[]
    for value in values:
        if isinstance(value,(flint.arb,flint.acb)):
            ball=value
        elif isinstance(value,complex):
            ball=flint.acb(value.real,value.imag)
        else:
            ball=real(value)
        if not ball.is_finite():
            raise ValueError('All coefficient balls must be finite')
        out.append(ball)
    # Ball comparisons are three-valued: both == and != can be false
    # for overlapping intervals. Require an affirmative exact equality.
    if not out[0]==0 or not out[1]==(1 if normalized else 0):
        raise ValueError('The input must have unused index zero and the declared normalization')
    return out


@lru_cache(maxsize=None)
def proper_divisors(cutoff):
    result=[[] for _ in range(cutoff+1)]
    for d in range(2,cutoff+1):
        for n in range(2*d,cutoff+1,d):
            result[n].append(d)
    return tuple(tuple(row) for row in result)


@lru_cache(maxsize=None)
def mobius_exponent(k):
    """Factor only the small perfect-power exponent, never the input index."""
    sign=1;d=2
    while d*d<=k:
        if k%d==0:
            k//=d;sign=-sign
            if k%d==0:return 0
        d+=1
    return -sign if k>1 else sign


def power_placement(values,inverse):
    result=[flint.arb(0)]*len(values)
    for n in range(2,len(values)):
        image=n;k=1
        while image<len(values):
            weight=mobius_exponent(k) if inverse else 1
            if weight:result[image]+=real(Q(weight,k))*values[n]
            image*=n;k+=1
    return result


def forward(values,alpha):
    weights=[flint.arb(0),flint.arb(0)]+[
        flint.arb(n).log()**real(alpha) for n in range(2,len(values))]
    L=[flint.arb(0)]*len(values);R=L.copy()
    for n,divisors in enumerate(proper_divisors(len(values)-1)):
        if n<2:continue
        L[n]=weights[n]*values[n]-sum(
            (values[n//d]*L[d] for d in divisors),flint.arb(0))
        R[n]=L[n]/weights[n]
    return L,R


def recover(decoder,alpha):
    R=power_placement(decoder,False)
    weights=[flint.arb(0),flint.arb(0)]+[
        flint.arb(n).log()**real(alpha) for n in range(2,len(R))]
    values=[flint.arb(0)]*len(R);values[1]=flint.arb(1)
    for n,divisors in enumerate(proper_divisors(len(R)-1)):
        if n<2:continue
        values[n]=R[n]+sum(
            (values[n//d]*weights[d]*R[d] for d in divisors),flint.arb(0))/weights[n]
    return values


def program_value(program,inputs):
    family=program['family'];alpha=Q(program['alpha'])
    if not 0<alpha<=1:
        raise ValueError('This fractional-prime production requires 0 < alpha <= 1')
    if family not in ('fractional_arithmetic_log','normalized_fractional_log',
                      'fractional_prime_decoder','fractional_prime_decoder_inverse'):
        raise ValueError('Unknown fractional-prime production '+family)
    inverse=family=='fractional_prime_decoder_inverse'
    values=complete_prefix(inputs[program['input']],normalized=not inverse)
    if inverse:return recover(values,alpha)
    L,R=forward(values,alpha)
    if family=='fractional_arithmetic_log':return L
    if family=='normalized_fractional_log':return R
    return power_placement(R,True)


PRODUCTION_CATALOGUE={
    'sort':'complete ball-valued arithmetic-function prefix',
    'families':['fractional_arithmetic_log','normalized_fractional_log',
                'fractional_prime_decoder','fractional_prime_decoder_inverse'],
    'parameters':'rational 0 < alpha <= 1; alpha=1 is classical calibration',
    'strict_sign_domain':'0 < alpha < 1; at alpha=1 all composite coefficients vanish',
    'universal_laws':['coefficient-local triangular inverse','perfect-power placement inverse'],
    'zeta_laws':['prime value one','sharp composite bound 2^(1-alpha)-1',
                 'strict factor-count sign law','uniform coefficient limit as alpha tends to one'],
    'ordinary_zeta_gate':'Fractional branch retention requires a nonzero numerator and certified corridors; only two old simple zeros are certified',
    'new_uniform_prime_distribution_estimate_proved':False,
    'historical_novelty_established':False,
}
