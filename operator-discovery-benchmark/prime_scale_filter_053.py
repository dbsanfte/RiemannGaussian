"""Exact finite-scale arithmetic reductions with an OPEN square-root bound.

All nonzero polynomial scale filters retain the noninteger zero singularity;
their root locations need not be restricted. This licenses a conditional RH
implication, never the missing all-integer arithmetic inequality itself.
"""
from copy import deepcopy
from fractions import Fraction as Q
from functools import reduce
from math import gcd
import math
import time

SCHEMA = 'fractional-prime-scale-filter-proof-v1'


class Meter:
    def __init__(self, cap=50_000_000, seconds=180):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative work cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('finite positive time cap')
        self.cap, self.operations, self.deadline = cap, 0, time.monotonic()+seconds

    def charge(self, n=1):
        if type(n) is not int or n < 0 or n > self.cap-self.operations:
            raise OverflowError('scale proof work cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('scale proof deadline')


def rational(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational text')
    value = Q(text)
    if str(value) != text or max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > 4096:
        raise ValueError('canonical rational input capacity')
    meter.charge(4*len(text)+1)
    return value


def parse(request, meter):
    if type(request) is not dict or set(request) != {'alpha', 'q', 'coefficients', 'bound'}:
        raise ValueError('exact scale-filter request')
    alpha = rational(request['alpha'], meter)
    q, coefficients, bound = request['q'], request['coefficients'], request['bound']
    if not 0 < alpha < 1 or type(q) is not int or not 2 <= q <= 64:
        raise ValueError('fractional exponent0<alpha<1 and integer scale2..64')
    if type(coefficients) is not list or not 2 <= len(coefficients) <= 17:
        raise ValueError('finite degree1..16 polynomial')
    if any(type(c) is not int or abs(c).bit_length() > 1024 for c in coefficients):
        raise ValueError('typed bounded integer coefficients')
    if coefficients[0] == 0 or coefficients[-1] <= 0 or reduce(gcd, coefficients) != 1:
        raise ValueError('primitive polynomial with positive leading and nonzero constant coefficient')
    value = 0
    for c in reversed(coefficients):
        value = q*value+c
        meter.charge(16+value.bit_length())
    if value != 0:
        raise ValueError('exact linear-main-term annihilation P(q)=0')
    if type(bound) is not dict or set(bound) != {'C', 'log_power', 'minimum', 'normalization'}:
        raise ValueError('exact uniform-bound request')
    C, eta = rational(bound['C'], meter), rational(bound['log_power'], meter)
    if C <= 0 or eta < 0 or type(bound['minimum']) is not int or bound['minimum'] != 2:
        raise ValueError('positiveC, nonnegative log power, every integerN>=2')
    if type(bound['normalization']) is not str or bound['normalization'] != 'divide_by_alpha':
        raise ValueError('fixed alpha normalization')
    return alpha, q, coefficients, C, eta


def build_certificate(request, meter=None):
    meter = meter or Meter()
    alpha, q, coefficients, C, eta = parse(request, meter)
    degree = len(coefficients)-1
    jumps = sum(abs(c)*q**j for j, c in enumerate(coefficients))
    p1 = sum(coefficients)
    meter.charge(300+len(coefficients)*64)
    return {
        'schema': SCHEMA, 'request': deepcopy(request),
        'status': 'PAID_ARITHMETIC_REDUCTION_AND_CONDITIONAL_RH_BOUND_OPEN',
        'kernel': {'a': '1', 'b': '0', 'alpha': str(alpha), 'sign': -1},
        'polynomial': {'ascending_coefficients': list(coefficients), 'degree': degree,
            'P_at_q': 0, 'P_at_one': p1, 'nonzero': True,
            'no_annulus_root_exclusion_required': True},
        'source': {
            'K': 'K_alpha(n)=-sum_{d|n}mu(d)*(log d)^alpha; K_alpha(1)=0',
            'A': 'A_alpha(x)=sum_{2<=n<=x}K_alpha(n), every real x>=1',
            'T': 'T_P(x)=sum_{j=0}^degree c_j*A_alpha(q^j*x)',
            'normalized_target': 'T_P(x)/alpha',
            'finite_divisor_identity': 'T_P(N)=-sum_{d<=q^degree*N}mu(d)*(log d)^alpha*sum_j c_j*floor(q^j*N/d)',
            'ordinary_mobius': True, 'all_prime_and_composite_terms_retained': True,
            'rounding': 'none in mathematical source; numerical enclosures must retain their error'},
        'main_term_cancellation': {
            'full_center': 'M_alpha(x)=kappa_alpha*(x-1)',
            'kappa_definition': 'kappa_alpha=I_alpha^(-1)*integral_0^infinity t^(-alpha-1)/zeta(1+t) dt',
            'filtered_center': '-kappa_alpha*P(1), since P(q)=0',
            'affine_center_annihilated': p1 == 0,
            'kappa_evaluation_or_fitting_required': False},
        'open_premise': {
            'status': 'OPEN', 'C': str(C), 'log_power': str(eta),
            'expression': '|T_P(N)|/alpha<=C*sqrt(N)*(1+log(N))^eta',
            'quantifiers': 'for every ordinary integer N>=2; fixed alpha,q,P,C,eta',
            'finite_samples_can_pay': False, 'pointwise_K_bound_can_pay': False,
            'polynomial_cancellation_can_pay': False, 'arithmetic_bound_proved': False},
        'integer_to_real': {
            'integer_jump_budget': jumps,
            'formula': '|T_P(x)-T_P(floor(x))|<=sum_j |c_j|*q^j*(log(q^j*(x+1)))^alpha',
            'pointwise_dependency': '0<K_alpha(n)<=(log(n))^alpha, for all n>=2',
            'conclusion': 'OPEN integer premise implies T_P(x)=O_epsilon(x^(1/2+epsilon)) for every epsilon>0'},
        'mellin_identity': {
            'initial_domain': 'Re(s)>1',
            'F': 'F_alpha(s)=sum_{n>=2}K_alpha(n)/n^s',
            'head': 'B_P(s)=sum_j c_j*q^(j*s)*integral_1^(q^j) A_alpha(u)*u^(-s-1) du',
            'head_entire': True,
            'formula': 'integral_1^infinity T_P(x)*x^(-s-1) dx=P(q^s)*F_alpha(s)/s-B_P(s)',
            'conditional_holomorphy': 'OPEN premise implies P(q^s)*F_alpha(s)/s holomorphic on Re(s)>1/2'},
        'fractional_zero_survival': {
            'dependency': 'reviewed052 fixed-height rightmost-zero asymptotic, b=0, every zeta zero multiplicity',
            'F_asymptotic': 'F_alpha(rho+delta)=C_rho*delta^(-alpha)+O(1), C_rho!=0, delta>0 tending to0',
            'multiplier_order': 'P(q^s)/s has a finite integer zero order k>=0 at nonreal rho',
            'reason_finite': 'P is nonzero finite polynomial; q^s has nonzero derivative; rho!=0',
            'product_asymptotic': 'P(q^(rho+delta))*F_alpha(rho+delta)/(rho+delta)=C_prime*delta^(k-alpha)+O(delta^k), C_prime!=0',
            'k_zero': 'the expression diverges, contradicting holomorphy',
            'k_positive': 'k-1<k-alpha<k forces all Taylor coefficients through k-1 to vanish; holomorphy would imply O(delta^k), a contradiction',
            'all_polynomial_root_locations_allowed': True},
        'conclusion': 'the exact OPEN integer arithmetic bound implies RH',
        'conditional_RH_implication_proved': True,
        'uniform_arithmetic_bound_proved': False, 'centered_error_bound_proved': False,
        'original_floor_energy_bound_proved': False,
        'converse_proved': False, 'RH_proved': False, 'RH_refuted': False,
        'numerical_evidence_used': False,
        'proof_backend': 'independently reviewed analytic and finite-divisor rules; not proof-assistant formalization'}
