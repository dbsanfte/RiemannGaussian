"""Exact finite-prime proof-grammar obstruction, not an actual-source model.

No actual source coefficient, analytic normalization, Arb ball, archive or
numerical study is evaluated here. The positive scalar bounds are assumptions.
"""
from fractions import Fraction
import math
import time

MAX_PARAMETER_BITS = 4096
MAX_RESULT_BITS = 8192
MAX_PRIMES = 1024


class Meter:
    def __init__(self, cap=10_000_000, seconds=60):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer operation cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite time cap')
        self.cap, self.operations, self.peak_integer_bits = cap, 0, 0
        self.deadline = time.monotonic()+seconds

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('finite-prime obstruction work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('finite-prime obstruction time cap')

    def reserve_bits(self, bits):
        if type(bits) is not int or not 0 <= bits <= MAX_RESULT_BITS:
            raise OverflowError('exact integer result bit cap')
        self.peak_integer_bits = max(self.peak_integer_bits, bits)
        self.charge(max(1, bits))

    def counts(self):
        return {'operations': self.operations, 'peak_integer_bits': self.peak_integer_bits}


def _meter(meter):
    return meter if meter is not None else Meter()


def rational(text, name='parameter', meter=None):
    meter = _meter(meter)
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational '+name)
    meter.charge(len(text)+1)
    try:
        value = Fraction(text)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError('canonical rational '+name) from exc
    if str(value) != text or max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_PARAMETER_BITS:
        raise ValueError('canonical rational within bit cap '+name)
    return value


def is_prime(n, meter=None):
    meter = _meter(meter)
    if type(n) is not int or n < 2 or n.bit_length() > MAX_PARAMETER_BITS:
        return False
    meter.charge(n.bit_length()+1)
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    limit = math.isqrt(n)
    # This preflight is a resource bound, not a semantic prime-size cutoff.
    meter.charge(max(0, (limit-1)//2))
    for divisor in range(3, limit+1, 2):
        if n % divisor == 0:
            return False
    return True


def validate_primes(primes, meter=None):
    meter = _meter(meter)
    if type(primes) not in (list, tuple) or len(primes) > MAX_PRIMES:
        raise ValueError('finite prime list within resource cap')
    if any(type(p) is not int for p in primes) or len(set(primes)) != len(primes):
        raise ValueError('distinct integer primes required')
    for p in primes:
        if not is_prime(p, meter):
            raise ValueError('every registered value must be an actual prime')
    meter.charge(len(primes)+1)
    return sorted(primes)


def first_missing_prime(primes, meter=None):
    meter = _meter(meter)
    registered = set(validate_primes(primes, meter))
    candidate = 2
    while True:
        meter.charge()
        if candidate not in registered and is_prime(candidate, meter):
            return candidate
        candidate += 1


def _exact_power(base, exponent, meter):
    if type(base) is not int or base < 1 or type(exponent) is not int or exponent < 1:
        raise ValueError('positive exact integer power')
    meter.reserve_bits(1 if base == 1 else base.bit_length()*exponent)
    meter.charge(exponent.bit_length()+1)
    return pow(base, exponent)


def dyadic_threshold(theta_text, k_text, L, meter=None):
    """Minimal dyadic X with (k/(2L))^den(theta)*X^num(theta)>=1."""
    meter = _meter(meter)
    theta, k = rational(theta_text, 'theta', meter), rational(k_text, 'k', meter)
    if not 0 < theta < 1 or not k > 0 or type(L) is not int or L < 1:
        raise ValueError('0<theta<1, k>0 and positive integer L required')
    ratio = k/(2*L)
    numerator = _exact_power(ratio.numerator, theta.denominator, meter)
    denominator = _exact_power(ratio.denominator, theta.denominator, meter)
    j = max(0, (denominator.bit_length()-numerator.bit_length())//theta.numerator)
    while True:
        meter.reserve_bits(numerator.bit_length()+j*theta.numerator)
        lhs = numerator << (j*theta.numerator)
        meter.charge(4)
        if lhs >= denominator:
            break
        j += 1
    meter.reserve_bits(j+1)
    X = 1 << j
    if j and numerator << ((j-1)*theta.numerator) >= denominator:
        raise ArithmeticError('dyadic threshold is not minimal')
    return {'X': str(X), 'j': j, 'ratio': str(ratio),
            'theta_numerator': theta.numerator, 'theta_denominator': theta.denominator,
            'powered_numerator': str(numerator), 'powered_denominator': str(denominator),
            'lhs': str(lhs), 'rhs': str(denominator), 'comparison': '>=',
            'minimal_dyadic': True}


def synthetic_local_h(v, e, meter=None):
    """Exact injected rational local coefficient, never actual p^-r."""
    meter = _meter(meter)
    if type(v) is not Fraction or not 0 < v < 1 or type(e) is not int or e < 0:
        raise ValueError('rational 0<v<1 and integer e>=0 required')
    meter.charge(8)
    if e == 0:
        return Fraction(1)
    if e == 1:
        return v-2
    meter.reserve_bits(max(v.numerator.bit_length(), v.denominator.bit_length())*e+4)
    return (1-v)**2*v**(e-2)


def _synthetic_multiplicative(n, local_values, h, meter):
    if type(n) is not int or n < 1 or n.bit_length() > MAX_PARAMETER_BITS:
        raise ValueError('positive bounded integer n required')
    if type(local_values) is not dict:
        raise ValueError('injected prime to rational-local-value map required')
    primes = validate_primes(list(local_values), meter)
    value = Fraction(1)
    for p in primes:
        v = local_values[p]
        if type(v) is not Fraction or not 0 < v < 1:
            raise ValueError('injected rational local values required')
        e = 0
        while n % p == 0:
            meter.charge(4)
            n //= p
            e += 1
        if e:
            if h:
                value *= synthetic_local_h(v, e, meter)
            else:
                meter.reserve_bits(max(v.numerator.bit_length(), v.denominator.bit_length())*e+4)
                value *= (v-1)*v**(e-1)
        meter.charge(8)
        meter.reserve_bits(max(abs(value.numerator).bit_length(), value.denominator.bit_length()))
    return Fraction(0) if h and n != 1 else value


def synthetic_u(n, local_values, meter=None):
    return _synthetic_multiplicative(n, local_values, False, _meter(meter))


def synthetic_h(n, local_values, meter=None):
    return _synthetic_multiplicative(n, local_values, True, _meter(meter))


def generate_certificate(primes, r_text='1/3', q=2, k_text='1/10', K=1, meter=None):
    """Produce a scoped symbolic certificate with externally assumed scalar bounds."""
    meter = _meter(meter)
    P = validate_primes(primes, meter)
    r, k = rational(r_text, 'r', meter), rational(k_text, 'k', meter)
    if not 0 < r < Fraction(1, 2):
        raise ValueError('r must satisfy 0<r<1/2')
    if type(q) is not int or q < 2 or q.bit_length() > MAX_PARAMETER_BITS:
        raise ValueError('bounded integer q>=2 required')
    if type(K) is not int or K < 1 or K.bit_length() > MAX_PARAMETER_BITS or not 0 < k <= K:
        raise ValueError('positive rational k<=positive integer K required')
    theta = 1-r
    h_bound = _exact_power(4, max(1, len(P)), meter) if P else 1
    L = (q+1)*h_bound
    meter.reserve_bits(L.bit_length())
    threshold = dyadic_threshold(str(theta), k_text, L, meter)
    missing = first_missing_prime(P, meter)
    registered = []
    for p in P:
        meter.charge(96)
        registered.append({
            'prime': p, 'v': {'kind': 'prime_power', 'prime': p, 'exponent': str(-r)},
            'v_domain': '0<v<1',
            'u_numerator': ['1', '-1'], 'u_denominator': ['1', '-v'],
            'h_numerator': ['1', '-2', '1'], 'h_denominator': ['1', '-v'],
            'u_e0': '1', 'u_e_ge1': '(v-1)*v^(e-1)',
            'h_e0': '1', 'h_e1': 'v-2', 'h_e_ge2': '(1-v)^2*v^(e-2)',
            'h_l1': '4-2*v', 'h_l1_upper': '4'})
    meter.charge(512)
    return {
        'schema': 'finite-prime-obstruction-v1',
        'parameters': {'primes': P, 'r': r_text, 'theta': str(theta), 'q': q,
                       'k_lower': k_text, 'K_upper': K},
        'quantifier': 'for any fixed finite set P of distinct actual primes',
        'assumptions': {'analytic_scalar': '(1-q^r)/(theta*zeta(theta))',
                        'scalar_bounds': '0<k<=kappa<=K',
                        'scalar_bounds_require_independent_verification': True,
                        'ordinary_mu_theta_series_convergence_used': False},
        'definitions': {'u_unit': '1',
                        'u_registered': '(p^-r-1)*p^(-r*(e-1)), e>=1, p in P',
                        'u_unregistered': '1, e>=1, p not in P',
                        'u_multiplicative': True, 'u_coefficient_abs_bound': '1',
                        'divisor_identity': 'u=One*h_P',
                        'g': '(delta-q*delta_q)*h_P',
                        'c': '(delta-q*delta_q)*u=One*g',
                        'J': 'prefix(c)(x)-kappa*x^theta',
                        'J_zero': '0', 'c_unit': '1',
                        'energy': 'X^-2*sum_(X<=n<2X)J(n)^2'},
        'local_laws': {'registered': registered,
                       'unregistered': {'u_e_ge0': '1', 'h_e0': '1', 'h_e_ge1': '0'}},
        'norms': {'h_l1_upper': str(h_bound), 'g_l1_upper': str(L),
                  'factorization': 'sum|h_P|=product_(p in P)(4-2*p^-r)<=4^|P|',
                  'g_triangle': 'sum|g|<=(q+1)*sum|h_P|'},
        'periodic': {'q': q, 'multiplier_coefficients': ['1', str(-q)],
                     'harmonic_multiplier': '0',
                     'harmonic_identity': 'sum g(d)/d=(1-q/q)*sum h_P(d)/d=0',
                     'prefix_identity': 'prefix(c)(x)=sum g(d)*(floor(x/d)-x/d)',
                     'prefix_abs_bound': str(L), 'prefix_domain': 'every real x>=0',
                     'absolute_series_justifies_interchange': True},
        'first_missing_prime': {'prime': missing, 'u_value': '1',
                                'required_value': 'p^-r-1',
                                'required_value_range': '(-1,0)',
                                'signed_gap': '2-p^-r', 'signed_gap_strict_lower': '1',
                                'registered_prime_laws_retained': True},
        'threshold': threshold,
        'energy_obstruction': {'lower_constant': str(k*k/4), 'exponent': str(1-2*r),
                               'domain': 'every integer X>=threshold.X',
                               'centered_abs_lower': '(k/2)*n^theta for every integer n>=threshold.X',
                               'energy_lower': '(k^2/4)*X^(1-2*r)',
                               'energy_exponent_strictly_positive': True,
                               'growth_disproves_uniform_subpower_for_fake': True,
                               'upper_centered_bound': 'K*x^theta+L'},
        'source_scope': {'fake_dirichlet_series': 'zeta(s)*H_P(s)',
                         'H_P': 'product_(p in P)(1-p^-s)^2/(1-p^(-(s+r)))',
                         'fake_periodic_dirichlet_series': '(1-q^(1-s))*zeta(s)*H_P(s)',
                         'fake_periodic_has_theta_pole': False,
                         'retains_actual_global_meromorphic_identity': False,
                         'retains_actual_center_as_its_own_residue': False,
                         'excluded_by_actual_all_prime_source_binding': True,
                         'grammar_scope': 'only finitely many registered prime laws plus unit and coefficient bound',
                         'purpose': 'negative calibration of insufficient proof grammars'},
        'source_counterexample': False, 'covariance_bound_proved': False,
        'actual_all_prime_bound_proved': False, 'RH_proved': False, 'RH_refuted': False,
        'actual_source_values_generated': False, 'actual_normalization_evaluated': False,
        'counts': meter.counts()}
