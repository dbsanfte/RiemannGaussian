"""Compose learned prime rows into exact, zero-preserving proof attempts.

Finite squarefree conditioning preserves the original smoothed Mobius sum.
Bernstein envelopes and elementary finite-sieve discrepancy certify affine
bounds. Those bounds do not discharge square-root cancellation obligations.
"""

from fractions import Fraction as Q
from math import comb, gcd
from functools import lru_cache
import flint


def parameters(primes):
    if not isinstance(primes,(list,tuple)) or not 1<=len(primes)<=8:
        raise ValueError('Declare between one and eight distinct prime multipliers')
    if any(type(p) is not int or p<2 or not flint.fmpz(p).is_prime() for p in primes):
        raise ValueError('Every declared multiplier must be a prime integer')
    if len(set(primes))!=len(primes):
        raise ValueError('The multiplier set must be squarefree')
    return tuple(sorted(primes))


def divisors_with_sign(primes):
    out = [(1,1)]
    for p in primes:
        out += [(p*d,-sign) for d,sign in out]
    return tuple(sorted(out))


def kernel(coefficients):
    if not isinstance(coefficients,(list,tuple)) or not 2<=len(coefficients)<=9:
        raise ValueError('A polynomial kernel of degree one through eight is required')
    c = tuple(Q(x) for x in coefficients)
    if c[0]!=1 or sum(c)!=0:
        raise ValueError('The kernel must have W(0)=1 and W(1)=0')
    while len(c)>2 and c[-1]==0:
        c = c[:-1]
    return c


def bernstein_on_interval(coefficients,left,right):
    degree = len(coefficients)-1
    monomial = [sum((coefficients[j]*comb(j,i)*left**(j-i)*(right-left)**i
                     for j in range(i,degree+1)),Q(0)) for i in range(degree+1)]
    return tuple(sum((monomial[i]*Q(comb(k,i),comb(degree,i)) for i in range(k+1)),Q(0))
                 for k in range(degree+1))


@lru_cache(maxsize=None)
def _certificate(primes,c):
    ds = divisors_with_sign(primes)
    degree = len(c)-1
    endpoints = sorted({Q(0)}|{Q(1,d) for d,sign in ds})
    density = sum((Q(sign,d) for d,sign in ds),Q(0))
    assert density>0
    cells = []
    integral = variation = Q(0)
    previous = Q(0)
    for left,right in zip(endpoints,endpoints[1:]):
        middle = (left+right)/2
        active = [(d,sign) for d,sign in ds if d*middle<1]
        poly = tuple(c[j]*sum(sign*d**j for d,sign in active) for j in range(degree+1))
        bern = bernstein_on_interval(poly,left,right)
        envelope = tuple(map(abs,bern))
        assert envelope[0]==previous
        previous = envelope[-1]
        cell_integral = (right-left)*sum(envelope)/(degree+1)
        cell_variation = sum(abs(b-a) for a,b in zip(envelope,envelope[1:]))
        integral += cell_integral
        variation += cell_variation
        cells.append({'left':str(left),'right':str(right),
            'active_divisors_with_sign':[[d,sign] for d,sign in active],
            'polynomial_coefficients':list(map(str,poly)),
            'Bernstein_coefficients':list(map(str,bern)),
            'positive_envelope_Bernstein_coefficients':list(map(str,envelope)),
            'envelope_integral':str(cell_integral),'variation_upper':str(cell_variation)})
    assert previous==0
    discrepancy = 2**(len(primes)-1)
    return {'primes':list(primes),'kernel':list(map(str,c)),
        'target':'sum_(n<=X)mu(n)*W(n/X)',
        'coefficient_requirement':'the Dirichlet inverse of the constant-one arithmetic function (Mobius), not an arbitrary integer sequence',
        'divisors_with_sign':[[d,sign] for d,sign in ds],
        'identity':'S_W(X)=sum_(gcd(n,P)=1) mu(n)*sum_(d|P) mu(d)*W(d*n/X), W=0 beyond one',
        'arithmetic_target_preserved_exactly':True,
        'ordinary_zeta_Mellin_transform_preserved_exactly':True,
        'cells':cells,'rough_row_density':str(density),
        'finite_sieve_discrepancy_upper':discrepancy,
        'envelope_integral':str(integral),'envelope_variation_upper':str(variation),
        'linear_constant':str(density*integral),'boundary_cost':str(discrepancy*variation),
        'bound':'|S_W(X)| <= linear_constant*X + boundary_cost',
        'domain':'every real X >= 1, for the declared finite prime set and kernel',
        'status':'proved_all_scale_elementary_known_Euler_factor_consequence',
        'external_prime_distribution_theorem_used':False,
        'square_root_cancellation_obligation_discharged':False,
        'historical_novelty_established':False}


def certificate(primes,coefficients):
    return _certificate(parameters(primes),kernel(coefficients)).copy()


def rewrite_value(values,primes,coefficients,X):
    primes,c = parameters(primes),kernel(coefficients)
    if type(X) is not int or X<1:
        raise ValueError('The finite evaluation requires an integer X >= 1')
    if not isinstance(values,(list,tuple)) or len(values)<=X or values[0]!=0:
        raise ValueError('A complete coefficient prefix through X is required')
    if any(type(a) is not int for a in values[:X+1]):
        raise ValueError('An integer coefficient prefix is required')
    # Check the defining inverse law on the complete supplied prefix.
    # An arbitrary sequence must not inherit a Mobius-specific certificate.
    totals = [0]*(X+1)
    for d in range(1,X+1):
        if values[d]:
            for n in range(d,X+1,d):
                totals[n] += values[d]
    if totals[1]!=1 or any(totals[n] for n in range(2,X+1)):
        raise ValueError('The supplied prefix must be the Dirichlet inverse of constant one')
    P = 1
    for p in primes:
        P *= p
    ds = divisors_with_sign(primes)
    out = Q(0)
    for n in range(1,X+1):
        if gcd(n,P)!=1 or not values[n]:
            continue
        for d,sign in ds:
            if d*n>X:
                continue
            u = Q(d*n,X)
            weight = sum((a*u**j for j,a in enumerate(c)),Q(0))
            out += values[n]*sign*weight
    return out


def program_value(program,inputs):
    family = program['family']
    if family=='rough_row_rewrite_certificate':
        return certificate(program['primes'],program['kernel'])
    if family=='rough_row_rewrite_value':
        return rewrite_value(inputs[program['input']],program['primes'],program['kernel'],program['X'])
    raise ValueError('Unknown cancellation-rewrite production '+family)


PRODUCTION_CATALOGUE = {'kind':'estimate_feedback_program',
    'families':['rough_row_rewrite_certificate','rough_row_rewrite_value'],
    'parameters':'one through eight distinct prime integers and a rational kernel of degree one through eight with W(0)=1,W(1)=0',
    'grammar_operations':['compose learned prime cancellation rows','squarefree divisor dilation',
                          'piecewise polynomial support partition','Bernstein absolute envelope',
                          'finite-sieve discrepancy and integration by parts'],
    'target_and_ordinary_zeta_zero_signature_preserved':True,
    'identity_coefficient_domain':'the actual Mobius function; finite evaluations check the constant-one inverse law',
    'new_uniform_signed_cancellation_estimate_available':False}
