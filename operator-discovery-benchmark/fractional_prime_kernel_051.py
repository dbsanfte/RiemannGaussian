"""Uniform proof rules for a general divisor/logarithmic-power grammar.

These rules pay pointwise arithmetic kernel bounds, not an RH norm estimate.
The calculus and Euler-product arguments are recorded in the051 review. This
producer does not evaluate candidates, primes, zeta values or numerical fits.
"""
from copy import deepcopy
from fractions import Fraction as Q
import math
import time

SCHEMA = 'fractional-prime-kernel-proof-v1'
FORMULA = 'K(n)=sign*sum_{d|n}mu(d)*(a*log(d)+b*log(n/d))^alpha'


class Meter:
    def __init__(self, cap=1_000_000, seconds=60):
        self.cap, self.operations = cap, 0
        self.deadline = time.monotonic()+seconds

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('kernel proof work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('kernel proof time cap')

    def number(self, value):
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        if bits > 4096:
            raise OverflowError('kernel proof rational bit cap')
        self.charge(1+2*bits)
        return value


def rational(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational string')
    try:
        value = Q(text)
    except (ValueError, ZeroDivisionError):
        raise ValueError('rational parameter') from None
    if str(value) != text:
        raise ValueError('canonical rational parameter')
    return meter.number(value)


def parse(request, meter):
    if type(request) is not dict or set(request) != {'a', 'b', 'alpha', 'sign'}:
        raise ValueError('exact fractional kernel grammar')
    a, b, alpha = (rational(request[key], meter) for key in ('a', 'b', 'alpha'))
    sign = request['sign']
    if a < 0 or b < 0 or a+b != 1 or a == b or not 0 < alpha <= 2:
        raise ValueError('nonnegative distinct a,b summing to1 and0<alpha<=2')
    if type(sign) is not int or sign not in (-1, 1):
        raise ValueError('typed orientation sign')
    return a, b, alpha, sign


def derivative_coefficient(alpha, k, meter=None):
    """Positive coefficient alpha*(1-alpha)*...*(k-1-alpha),0<alpha<1."""
    meter = meter or Meter()
    alpha = rational(alpha, meter)
    if not 0 < alpha < 1 or type(k) is not int or not 1 <= k <= 4096:
        raise ValueError('concave exponent and bounded evaluation order')
    value = alpha
    for j in range(1, k):
        value = meter.number(value*(j-alpha))
    return str(value)


def _common(request):
    return dict(schema=SCHEMA, request=deepcopy(request), formula=FORMULA,
        domain=dict(n='every ordinary integer n>=2', extension_at_one='K(1)=0',
            parameters='fixed exact request; theorem holds for every admitted parameter in its licensed branch',
            rounding='none; exact real logarithms and powers;0^alpha=0'),
        divisor_reduction=dict(kind='squarefree_divisor_boolean_cube',
            variables='C=b*log(n), h_p=(a-b)*log(p), for every distinct ordinary prime p|n',
            identity='sum_{d|n}mu(d)*f(C+(a-b)*log(d))=sum_{S subset primes(n)}(-1)^|S|*f(C+sum_{p in S}h_p)',
            prime_powers_retained_in='C=b*log(n)', all_distinct_prime_factors_retained=True),
        proof_backend='reviewed exact calculus and finite divisor identities; no proof-assistant formalization',
        arithmetic_source='ordinary Mobius function and actual ordinary prime divisors',
        source_values_evaluated=False, numerical_evidence_used=False,
        prime_distribution_bound_proved=False, uniform_mobius_partial_sum_bound_proved=False,
        original_floor_energy_bound_proved=False, analytic_continuation_proved=False,
        RH_proved=False, RH_refuted=False)


def build_certificate(request, meter=None):
    meter = meter or Meter()
    a, b, alpha, sign = parse(request, meter)
    result = _common(request)
    prime_response = meter.number(sign*(b-a))
    if prime_response < 0:
        branch, witness, reason = 'negative_prime', 2, 'sign*(b^alpha-a^alpha)<0 since alpha>0'
    elif alpha == 1:
        c = abs(a-b)
        result.update(status='PAID_UNIFORM_POINTWISE_CONTROL', branch='linear_endpoint',
            nonnegative_for_all_n=True, strict_positive_scope='exactly the ordinary prime powers',
            exact_zero_scope='integers with at least two distinct prime factors',
            identity=dict(kind='von_mangoldt', coefficient=str(c), formula='K(n)=c*Lambda(n)'),
            upper_bound=dict(kind='minimum_prime_logarithm', coefficient=str(c), power='1'),
            proof=dict(kind='boolean_difference_of_linear_function',
                unit_cancellation=True, mixed_differences_order_two_or_more_zero=True),
            zeta_bridge=dict(kind='logarithmic_derivative', coefficient=str(c),
                formula='sum K(n)/n^s=-c*zeta_prime(s)/zeta(s)', domain='Re(s)>1',
                absolute_convergence_proved=True))
        meter.charge(30)
        return result
    elif a > b and alpha < 1:
        c = a-b
        result.update(status='PAID_UNIFORM_POINTWISE_CONTROL', branch='fractional_forward',
            nonnegative_for_all_n=True, strict_positive_scope='every integer n>=2', exact_zero_scope='none for n>=2',
            identity=dict(kind='normalized_positive_laplace_prime_product', c=str(c),
                normalizer='I_alpha=integral_0^infinity (1-exp(-u))*u^(-alpha-1) du',
                normalizer_finite_positive=True,
                formula='K(n)=I_alpha^(-1)*integral_0^infinity n^(-b*t)*prod_{p|n}(1-p^(-c*t))*t^(-alpha-1) dt'),
            upper_bound=dict(kind='minimum_prime_increment', offset_coefficient=str(b),
                step_coefficient=str(c), power=str(alpha),
                formula='K(n)<=min_{p|n}[(b*log(n)+c*log(p))^alpha-(b*log(n))^alpha]',
                weaker_bound='K(n)<=(c*log(p_min))^alpha'),
            product_bound=(dict(kind='mixed_derivative_product', k='omega(n)',
                coefficient='alpha*prod_{j=1}^{k-1}(j-alpha)',
                formula='K(n)<=alpha*prod_{j=1}^{k-1}(j-alpha)*c^k*prod_{p|n}log(p)/(b*log(n))^(k-alpha)',
                factor_count_bound='K(n)/log(n)^alpha<=alpha*prod_{j=1}^{k-1}(j-alpha)*c^k*b^(alpha-k)/k^k',
                omega_upper='K(n)/log(n)^alpha<=2*alpha*b^alpha*(c/(2*b))^k/k',
                omega_ratio=str(meter.number(c/(2*b))), exponential_omega_decay=c < 2*b,
                b_strictly_positive=True) if b > 0 else None),
            proof=dict(kind='concave_power_laplace_and_boolean_product',
                finite_difference_constant_cancels=True, one_factor_dominance=True,
                all_factors_between_zero_and_one=True, upper_bound_includes_all_prime_powers=True),
            zeta_bridge=dict(kind='fractional_zeta_quotient_integral', numerator_shift=str(b),
                denominator_shift=str(a), subtracted_constant='1',
                formula='sum K(n)/n^s=I_alpha^(-1)*integral_0^infinity [zeta(s+b*t)/zeta(s+a*t)-1]*t^(-alpha-1) dt',
                domain='Re(s)>1', absolute_convergence_proved=True,
                justification='K(n)<=(c*log(n))^alpha; absolute Dirichlet convergence, positive real Tonelli and complex domination'))
        meter.charge(50)
        return result
    elif a < b and alpha == 2:
        c = b-a
        result.update(status='PAID_UNIFORM_POINTWISE_CONTROL', branch='quadratic_backward',
            nonnegative_for_all_n=True, strict_positive_scope='exactly omega(n)=1 or2',
            exact_zero_scope='omega(n)>=3',
            identity=dict(kind='positive_mangoldt_convolution', c=str(c),
                formula='K(n)=c*Lambda(n)*log(n)+c^2*(Lambda*Lambda)(n)',
                prime_power='K(p^e)=c*(2*b*e-c)*log(p)^2',
                two_distinct_primes='K(p^e*q^f)=2*c^2*log(p)*log(q), e,f>=1'),
            upper_bound=dict(kind='full_logarithmic_power', coefficient=str(c), power='2',
                formula='K(n)<=c*log(n)^2'),
            proof=dict(kind='boolean_difference_of_quadratic_function',
                cubic_mixed_differences_zero=True, prime_power_coefficient_positive=True,
                pair_coefficient_positive=True, a_plus_b_equals_one=True),
            zeta_bridge=dict(kind='quadratic_logarithmic_derivative', coefficient=str(c),
                formula='sum K(n)/n^s=c*(zeta_prime/zeta)_prime(s)+c^2*(zeta_prime(s)/zeta(s))^2',
                domain='Re(s)>1', absolute_convergence_proved=True))
        meter.charge(40)
        return result
    elif a > b:
        branch, witness, reason = 'negative_two_prime_convex', 6, 'sign=-1 and strictly positive second difference of x^alpha for alpha>1'
    elif alpha < 1:
        branch, witness, reason = 'negative_two_prime_concave', 6, 'sign=+1 and strictly negative backward second difference of x^alpha for0<alpha<1'
    else:
        branch, witness, reason = 'negative_three_prime', 30, 'sign=+1 and strictly negative backward third difference of x^alpha for1<alpha<2'
    result.update(status='REFUTED_UNIFORM_NONNEGATIVITY', branch=branch,
        nonnegative_for_all_n=False, witness=dict(n=witness, primes=([2] if witness == 2 else [2, 3] if witness == 6 else [2, 3, 5]),
            conclusion='K(n)<0', proof=reason, exact_sign_proved=True, numerical_evaluation_required=False),
        scope='refutes nonnegativity of this kernel, not any original RH bound',
        uniform_pointwise_upper_bound_claimed=False)
    meter.charge(20)
    return result
