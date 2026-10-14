"""Complete centered K_r*mu source; numerical arrays are proposals, not proofs.

No source values are computed at import. All-prime bounds are symbolic. Actual
normalization is evaluated lazily by normalization_certificate/build_state.
"""
from fractions import Fraction
import math
import time
import numpy as np
from flint import arb, ctx

MAX_BITS = 4096
MAX_CELLS = 200_000_000


class Meter:
    def __init__(self, cap=500_000_000, seconds=600):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer operation cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite time cap')
        self.cap, self.operations, self.peak_cells = cap, 0, 0
        self.deadline = time.monotonic() + seconds

    def charge(self, n=1):
        if type(n) is not int or n < 0:
            raise ValueError('nonnegative integer charge')
        if n > self.cap - self.operations:
            raise OverflowError('centered-Mobius work cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('centered-Mobius time cap')

    def live(self, cells):
        if type(cells) is not int or cells < 0:
            raise ValueError('nonnegative integer live cells')
        self.charge()
        self.peak_cells = max(self.peak_cells, cells)
        if cells > MAX_CELLS:
            raise MemoryError('centered-Mobius scalar-cell cap')

    def counts(self):
        return {'operations': self.operations, 'peak_cells': self.peak_cells}


def _meter(meter):
    return meter if meter is not None else Meter()


def _parameters(r_text, q, meter):
    if type(r_text) is not str or not 1 <= len(r_text) <= 2500:
        raise ValueError('bounded canonical rational r')
    meter.charge(len(r_text) + 8)
    try:
        r = Fraction(r_text)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError('canonical rational r') from exc
    if str(r) != r_text or not 0 < r < Fraction(1, 2):
        raise ValueError('canonical rational 0<r<1/2')
    if max(abs(r.numerator).bit_length(), r.denominator.bit_length()) > MAX_BITS:
        raise ValueError('r parameter bit cap')
    if type(q) is not int or q < 2 or q.bit_length() > MAX_BITS:
        raise ValueError('integer q>=2 within bit cap')
    meter.charge(q.bit_length() + r.numerator.bit_length() + r.denominator.bit_length())
    return r, 1-r


def _ceiling(value):
    if type(value) is not str or len(value) > 1300:
        raise ValueError('canonical nonnegative integer kappa ceiling')
    try:
        result = int(value)
    except ValueError as exc:
        raise ValueError('canonical integer ceiling') from exc
    if str(result) != value or result < 0 or result.bit_length() > MAX_BITS:
        raise ValueError('canonical nonnegative ceiling within bit cap')
    return result


def symbolic_certificate(r_text, q, kappa_ceiling=None, meter=None):
    """Exact parameter/local-law certificate; no zeta or source evaluation."""
    meter = _meter(meter)
    r, theta = _parameters(r_text, q, meter)
    ceiling = None if kappa_ceiling is None else _ceiling(kappa_ceiling)
    meter.charge(80 + (0 if ceiling is None else ceiling.bit_length()))
    return {
        'schema': 'centered-mobius-bound-v1', 'r': str(r), 'theta': str(theta), 'q': q,
        'source': {'convolution': [{'kind': 'power', 'exponent': str(-r)}, {'kind': 'mu', 'exponent': '0'}]},
        'unit': '1',
        'local': {'variable': 't', 'parameter': 'p^-r',
                  'numerator': ['1', '-1'], 'denominator': ['1', '-p^-r'],
                  'prime': 'p^-r-1', 'higher_prime_power_multiplier': 'p^-r',
                  'higher_prime_power_domain': 'e>=2',
                  'divisible_multiplier': 'p^-r', 'coprime_multiplier': 'p^-r-1',
                  'divisibility_domain': 'p prime,n>=1; divisible iff p divides n',
                  'prime_power_abs_bound': '1'},
        'coefficient_abs_bound': '1',
        'periodic': {
            'definition': 'c_q=b_r-q*(delta_q*b_r)', 'coefficient_abs_bound': str(q+1),
            'conditional_prime_laws': {
                'hypothesis': 'q is prime; no primality claim is made by this certificate',
                'q_local_numerator': ['1', '-(q+1)', 'q'],
                'q_local_denominator': ['1', '-q^-r'],
                'q_divisibility': 'c_q(q*n)=q^-r*c_q(n)-(q+1)*1_(q does not divide n)*b_r(n)+q*1_(valuation_q(n)=1)*b_r(n/q)',
                'other_prime': 'c_q(p*n)=p^-r*c_q(n)-1_(p does not divide n)*c_q(n), p prime distinct from q',
                'higher_q_prime_power_multiplier': 'q^-r, e>=3',
            },
        },
        'normalization': {'definition': '(1-q^r)/(theta*zeta(theta))',
                          'interpretation': 'analytic; no ordinary mu(theta) moment asserted',
                          'absolute_ceiling': None if ceiling is None else str(ceiling),
                          'ceiling_requires_independent_verification': True},
        'increment': {'definition': 'a(n)=c_q(n)-kappa*(n^theta-(n-1)^theta)',
                      'domain': 'every integer n>=1', 'unit': '1-kappa',
                      'power_increment_abs_bound': '1',
                      'absolute_bound': None if ceiling is None else str(q+1+ceiling)},
        'prefix_energy_bound_proved': False, 'RH_proved': False,
    }


def normalization_certificate(r_text, q, precision=192, meter=None):
    """Arb enclosure of the analytic scalar, with certified rational ceiling.

    The enclosure is not an ordinary coefficient-moment convergence claim.
    Precision insufficiency raises rather than substituting a float value.
    """
    meter = _meter(meter)
    r, theta = _parameters(r_text, q, meter)
    if type(precision) is not int or not 128 <= precision <= 4096:
        raise ValueError('Arb precision128..4096')
    meter.charge(4096 + 16*precision + q.bit_length())
    with ctx.workprec(precision):
        ar = arb(r.numerator)/r.denominator
        at = arb(theta.numerator)/theta.denominator
        zeta = at.zeta()
        kappa = (1-arb(q)**ar)/(at*zeta)
        if not kappa.is_finite() or not kappa > 0:
            raise ArithmeticError('normalization enclosure is not finite strictly positive')
        rounded = abs(kappa).upper().ceil().unique_fmpz()
        if rounded is None:
            raise ArithmeticError('normalization ceiling is not an exact integer')
        ceiling = int(rounded)
        if ceiling.bit_length() > MAX_BITS:
            raise OverflowError('normalization ceiling bit cap')
        certificate = symbolic_certificate(r_text, q, str(ceiling), meter)
        return {'schema': 'centered-mobius-normalization-v1', 'r': r_text, 'q': q,
                'theta': str(theta), 'precision': precision, 'kappa': str(kappa),
                'absolute_ceiling': str(ceiling), 'certificate': certificate,
                'ordinary_mu_theta_series_convergence_used': False}


def _finite_float(value, name):
    if type(value) not in (int, float) or not math.isfinite(value):
        raise ArithmeticError(name+' must be a finite real scalar')
    return float(value)


def smallest_prime_factors(H, meter=None):
    """Metered complete SPF; caller retains its source arrays separately."""
    meter = _meter(meter)
    if type(H) is not int or H < 1:
        raise ValueError('integer horizon>=1')
    meter.live(9*(H+1)+128)
    meter.charge(H+1)
    spf = np.zeros(H+1, dtype=np.int64)
    for p in range(2, H+1):
        meter.charge(2)
        if spf[p]:
            continue
        meter.charge(3*(H//p))
        for n in range(p, H+1, p):
            if not spf[n]:
                spf[n] = p
    return spf


def multiplicative_coefficients(spf, prime_values, meter=None):
    """Generic synthetic-testable recurrence with values0<power(p)<1.

    prime_values(p) supplies p^-r in production; this helper has no source
    normalization. SPF is validated structurally without rebuilding a sieve.
    """
    meter = _meter(meter)
    if type(spf) is not np.ndarray or spf.ndim != 1 or spf.dtype.kind not in 'iu' or len(spf) < 2:
        raise ValueError('one-dimensional integer SPF array')
    H = len(spf)-1
    meter.live(9*(H+1)+128)
    meter.charge(H+1)
    b = np.zeros(H+1, dtype=np.float64)
    b[1] = 1.0
    cache = {}
    for n in range(2, H+1):
        meter.charge(14)
        p = int(spf[n])
        if p < 2 or p > n or n % p or int(spf[p]) != p:
            raise ValueError('invalid SPF divisibility')
        m = n//p
        if p not in cache:
            meter.charge(64)
            v = _finite_float(prime_values(p), 'prime power parameter')
            if not 0 < v < 1:
                raise ArithmeticError('prime power parameter outside(0,1)')
            cache[p] = v
        v = cache[p]
        b[n] = b[m]*(v if m % p == 0 else v-1)
        if not math.isfinite(b[n]) or abs(b[n]) > 1:
            raise ArithmeticError('coefficient finite/local-bound failure')
    return b


def center_coefficients(b, q, theta_text, kappa, meter=None):
    """Complete generic centering helper; injected scalar supports toy tests.

    Returns indices0..H, including n1 and periodic multiples of q. Numerical
    prefixes are compensated; exact formula remains in the symbolic cert.
    """
    meter = _meter(meter)
    if type(b) is not np.ndarray or b.ndim != 1 or b.dtype.kind != 'f' or len(b) < 2:
        raise ValueError('one-dimensional float coefficient array')
    if type(q) is not int or q < 2 or q.bit_length() > MAX_BITS:
        raise ValueError('integer q>=2')
    if type(theta_text) is not str:
        raise ValueError('canonical theta')
    theta = Fraction(theta_text)
    if str(theta) != theta_text or not 0 < theta < 1:
        raise ValueError('canonical theta in(0,1)')
    kt = _finite_float(kappa, 'kappa')
    tf = float(theta)
    if not 0 < tf < 1:
        raise ArithmeticError('theta float resolution insufficient')
    H = len(b)-1
    meter.live(9*(H+1)+128)
    meter.charge(8*(H+1))
    if b[0] != 0 or not np.isfinite(b).all():
        raise ValueError('finite coefficient array with index0zero')
    c = b.copy()
    if q <= H:
        qf = _finite_float(q, 'q')
        c[q::q] -= qf*b[1:H//q+1]
    prefix = np.zeros(H+1)
    main = np.zeros(H+1)
    J = np.zeros(H+1)
    a = np.zeros(H+1)
    running, compensation = 0.0, 0.0
    for n in range(1, H+1):
        meter.charge(48)
        # Neumaier prefix; all earlier terms retained, no block restart.
        item = float(c[n])
        total = running + item
        compensation += ((running-total)+item if abs(running) >= abs(item)
                         else (item-total)+running)
        running = total
        prefix[n] = running + compensation
        power = math.exp(tf*math.log(n))
        delta = 1.0 if n == 1 else power*(-math.expm1(tf*math.log1p(-1.0/n)))
        main[n] = kt*power
        J[n] = prefix[n]-main[n]
        a[n] = item-kt*delta
        if not all(math.isfinite(v) for v in (prefix[n], main[n], J[n], a[n])):
            raise ArithmeticError('nonfinite centered source arithmetic')
    return {'c': c, 'prefix': prefix, 'main': main, 'J': J, 'a': a}


def build_state(H, r_text='1/3', q=2, normalization=None, meter=None):
    """Generate complete float source only when the authorized runner calls.

    The returned normalization ball/ceiling is rigorous; float arrays are
    numerical observations. Passing a normalization requires parameter match
    and strict equality with an independently recomputed certificate.
    """
    meter = _meter(meter)
    r, theta = _parameters(r_text, q, meter)
    if type(H) is not int or H < 1:
        raise ValueError('integer horizon>=1')
    meter.live(9*(H+1)+128)
    norm = normalization_certificate(r_text, q, meter=meter)
    if normalization is not None:
        if type(normalization) is not dict or normalization != norm:
            raise ValueError('normalization must match fresh complete certificate')
    with ctx.workprec(norm['precision']):
        ball = arb(norm['kappa'])
        kt = float(ball.mid())
        width = float(ball.rad())
    if not math.isfinite(kt) or not math.isfinite(width):
        raise ArithmeticError('normalization float representation failure')
    rf = float(r)
    if not 0 < rf < 0.5:
        raise ArithmeticError('r float resolution insufficient')
    spf = smallest_prime_factors(H, meter)
    b = multiplicative_coefficients(spf, lambda p: math.exp(-rf*math.log(p)), meter)
    arrays = center_coefficients(b, q, str(theta), kt, meter)
    arrays.update({'b': b, 'H': H, 'r': r_text, 'theta': str(theta), 'q': q,
                   'kappa': kt, 'normalization': norm, 'certificate': norm['certificate']})
    arrays['metadata'] = {
        **meter.counts(), 'complete_index_range': [0,H], 'index0zero': True,
        'unit_retained': True, 'normalization_radius': width,
        'normalization_error_J_bound': width*math.exp(float(theta)*math.log(H)),
                  'arrays_are_float_observations': True,
        'float_roundoff_is_interval_certified': False,
        'ordinary_mu_theta_series_convergence_used': False,
        'prefix_energy_bound_proved': False, 'RH_proved': False,
    }
    return arrays
