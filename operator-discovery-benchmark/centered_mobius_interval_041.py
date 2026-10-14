"""Independent finite Arb replay of centered Mobius/Haar covariance programs.

Import and synthetic helpers do not evaluate source normalization. Actual source
generation is an explicit build_state call, to be made only after program freeze.
No producer import, SPF recurrence, float coefficient or theorem claim is used.
"""
from fractions import Fraction
import math
import time

from flint import arb, ctx

MAX_H = 8_388_607
MAX_BITS = 4096


class Meter:
    def __init__(self, cap=1_000_000_000, seconds=7200):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer operation cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite time cap')
        self.cap, self.operations, self.peak_bytes_estimate = cap, 0, 0
        self.deadline = time.monotonic() + seconds

    def charge(self, n=1):
        if type(n) is not int or n < 0 or n > self.cap-self.operations:
            raise OverflowError('independent interval work cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('independent interval time cap')

    def reserve(self, H, precision):
        # Deliberately conservative allowance for three full Python Arb arrays,
        # intermediate limbs, sieve, pointers and allocation overhead.
        self.peak_bytes_estimate = max(self.peak_bytes_estimate,
                                      (H+1)*(1500+3*((precision+7)//8)))
        if self.peak_bytes_estimate > 15*1024**3:
            raise MemoryError('independent interval estimated memory cap')
        self.charge()

    def counts(self):
        return {'operations': self.operations,
                'peak_bytes_estimate': self.peak_bytes_estimate}


def _meter(meter):
    return meter if meter is not None else Meter()


def _rational(text, name):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational '+name)
    try:
        value = Fraction(text)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError('canonical rational '+name) from exc
    if str(value) != text or max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_BITS:
        raise ValueError('canonical rational within bit cap '+name)
    return value


def _ball(value):
    if type(value) is Fraction:
        return arb(value.numerator)/value.denominator
    if type(value) is int or type(value) is arb:
        result = arb(value)
    elif type(value) is str:
        return _ball(_rational(value, 'coefficient'))
    else:
        raise ValueError('exact rational or Arb scalar required')
    if not result.is_finite():
        raise ArithmeticError('finite interval scalar required')
    return result


def _precision(precision):
    if type(precision) is not int or not 128 <= precision <= 4096:
        raise ValueError('Arb precision 128..4096')


def _horizon(H):
    if type(H) is not int or not 1 <= H <= MAX_H:
        raise ValueError('integer horizon 1..8388607')


def _period(q):
    if type(q) is not int or not 2 <= q or q.bit_length() > MAX_BITS:
        raise ValueError('integer period q>=2 within bit cap')


def independent_coefficients(H, r_text, precision=192, meter=None,
                             prime_power=None):
    """Distinct-prime sieve product; optional exact local powers are for toys.

    b(n)=n^-r product_(p|n)(1-p^r). For injected local values v(p), the
    equivalent product v(p)^(valuation_p(n)-1)*(v(p)-1) is computed directly
    from divisibility, never from b(n/p) or an SPF recursion.
    """
    _horizon(H)
    _precision(precision)
    r = _rational(r_text, 'r')
    if not 0 < r < Fraction(1, 2):
        raise ValueError('r must satisfy 0<r<1/2')
    meter = _meter(meter)
    meter.reserve(H, precision)
    with ctx.workprec(precision):
        b = [arb(1)]*(H+1)
        b[0] = arb(0)
        composite = bytearray(H+1)
        exponent = _ball(r)
        for p in range(2, H+1):
            meter.charge(2)
            if composite[p]:
                continue
            if prime_power is None:
                factor = 1-arb(p)**exponent
            else:
                v = _ball(prime_power(p))
                if not 0 < v < 1:
                    raise ValueError('toy local power must lie in (0,1)')
                factor = v-1
            meter.charge(16)
            for n in range(p, H+1, p):
                meter.charge(6)
                composite[n] = 1
                if prime_power is None:
                    b[n] = b[n]*factor
                else:
                    local = factor
                    divisor = n//p
                    while divisor % p == 0:
                        meter.charge(4)
                        local = local*v
                        divisor //= p
                    b[n] = b[n]*local
        if prime_power is None:
            for n in range(2, H+1):
                meter.charge(24)
                b[n] = b[n]*(arb(n)**(-exponent))
        return b


def center_from_coefficients(b, q, theta_text, kappa, precision=192, meter=None):
    """Complete centered source from exact toy coefficients/injected scalar.

    Running c_q prefixes equal B(n)-q B(floor(n/q)); the analytic main is
    kappa*n^theta, without rounding the continuous dilated main.
    """
    if type(b) not in (list, tuple) or len(b) < 2:
        raise ValueError('complete coefficient list including index zero')
    H = len(b)-1
    _horizon(H)
    _period(q)
    _precision(precision)
    theta = _rational(theta_text, 'theta')
    if not 0 < theta < 1:
        raise ValueError('theta must lie in (0,1)')
    meter = _meter(meter)
    meter.reserve(H, precision)
    with ctx.workprec(precision):
        if _ball(b[0]) != 0 or _ball(b[1]) != 1:
            raise ValueError('source index zero must vanish and unit must be one')
        kt, exponent = _ball(kappa), _ball(theta)
        J, Dprefix = [arb(0)]*(H+1), [arb(0)]*(H+1)
        running, square_prefix = arb(0), arb(0)
        for n in range(1, H+1):
            meter.charge(40)
            cn = _ball(b[n])
            if n % q == 0:
                cn -= q*_ball(b[n//q])
            running += cn
            J[n] = running-kt*(arb(n)**exponent)
            increment = J[n]-J[n-1]
            square_prefix += increment*increment
            Dprefix[n] = square_prefix
            if not J[n].is_finite() or not square_prefix.is_finite():
                raise ArithmeticError('nonfinite centered interval arithmetic')
        return {'H': H, 'q': q, 'r': str(1-theta), 'theta': theta_text,
                'precision': precision, 'kappa': kt, 'J': J,
                'Dprefix': Dprefix, '_gram_cache': {}, 'meter': meter,
                'metadata': {'complete_index_range': [0, H],
                             'unit_retained': True, 'index0zero': True,
                             'arithmetic': 'Arb', 'precision': precision,
                             'prefix_energy_bound_proved': False,
                             'RH_proved': False, **meter.counts()}}


def build_state(H, r_text='1/3', q=2, precision=192, meter=None):
    """Explicit actual source generation; call only after candidate freeze."""
    _horizon(H)
    _period(q)
    _precision(precision)
    r = _rational(r_text, 'r')
    if not 0 < r < Fraction(1, 2):
        raise ValueError('r must satisfy 0<r<1/2')
    meter = _meter(meter)
    meter.reserve(H, precision)
    theta = 1-r
    with ctx.workprec(precision):
        rt, tt = _ball(r), _ball(theta)
        meter.charge(4096+16*precision)
        zeta = tt.zeta()
        kappa = (1-arb(q)**rt)/(tt*zeta)
        if not kappa.is_finite() or not kappa > 0:
            raise ArithmeticError('finite positive independent normalization required')
        b = independent_coefficients(H, r_text, precision, meter)
        state = center_from_coefficients(b, q, str(theta), kappa, precision, meter)
        state['normalization'] = {'definition': '(1-q^(1-theta))/(theta*zeta(theta))',
                                  'r': r_text, 'theta': str(theta), 'q': q,
                                  'precision': precision, 'kappa': enclosure(kappa),
                                  'zeta_theta': enclosure(zeta),
                                  'ordinary_mu_theta_series_convergence_used': False}
        state['metadata']['coefficient_construction'] = 'distinct-prime product sieve'
        state['metadata']['source_kind'] = 'actual complete centered Mobius source'
        return state


def _is_prime(n, meter):
    if n < 2:
        return False
    for divisor in range(2, math.isqrt(n)+1):
        meter.charge()
        if n % divisor == 0:
            return False
    return True


def validate_program(program, r_text, meter=None):
    meter = _meter(meter)
    if type(program) is not dict or set(program) != {'id', 'm', 'lambda', 'rho', 'delta', 'C'}:
        raise ValueError('complete exact program schema required')
    if type(program['id']) is not str or not 1 <= len(program['id']) <= 250:
        raise ValueError('bounded program id required')
    m = program['m']
    if type(m) is not int or not 2 <= m <= MAX_H:
        raise ValueError('bounded integer m>=2')
    spec = program['lambda']
    if type(spec) is not dict:
        raise ValueError('exact lambda specification required')
    if spec.get('kind') == 'rational' and set(spec) == {'kind', 'value'}:
        lam = _ball(_rational(spec['value'], 'lambda'))
    elif spec.get('kind') == 'prime_power' and set(spec) == {'kind', 'prime', 'exponent'}:
        if type(spec['prime']) is not int or spec['prime'] != m or not _is_prime(m, meter):
            raise ValueError('source lambda requires prime=m')
        exponent = _rational(spec['exponent'], 'lambda exponent')
        if exponent != -_rational(r_text, 'r'):
            raise ValueError('source lambda exponent must equal -r')
        lam = arb(m)**_ball(exponent)
    else:
        raise ValueError('unsupported lambda schema')
    rho, delta, C = (_rational(program[key], key) for key in ('rho', 'delta', 'C'))
    if not 0 <= rho <= 1 or delta < 0 or C < 0:
        raise ValueError('0<=rho<=1, delta>=0, C>=0 required')
    meter.charge(48)
    return m, lam, _ball(rho), _ball(delta), _ball(C)


def enclosure(value):
    """Readable ball plus exact enclosing dyadic endpoints for lossless replay."""
    if not value.is_finite():
        raise ArithmeticError('nonfinite output enclosure')
    low, high = value.lower().man_exp(), value.upper().man_exp()
    return {'ball': value.str(65),
            'lower_dyadic': [str(low[0]), int(low[1])],
            'upper_dyadic': [str(high[0]), int(high[1])]}


def base_gram(state, m, X):
    """Cache complete two-channel Gram and direct complete child variance."""
    if type(m) is not int or m < 2 or type(X) is not int or X < 1:
        raise ValueError('integer m>=2 and X>=1 required')
    if 2*m*X-1 > state['H']:
        raise ValueError('complete child range exceeds source horizon')
    key = (m, X)
    if key in state['_gram_cache']:
        return state['_gram_cache'][key]
    meter = state['meter']
    with ctx.workprec(state['precision']):
        J = state['J']
        sjj, saa, sja, child_squares, variance_squares = (arb(0) for _ in range(5))
        for n in range(X, 2*X):
            meter.charge(20+12*m)
            A = sum(J[m*n+j] for j in range(m))/m
            sjj += J[n]*J[n]
            saa += A*A
            sja += J[n]*A
            for j in range(m):
                child = J[m*n+j]
                child_squares += child*child
                difference = child-A
                variance_squares += difference*difference
        scale = X*X
        gram = {'E_J': sjj/scale, 'E_A': saa/scale, 'C_JA': sja/scale,
                'E_child': child_squares/(m*m*scale),
                'V': variance_squares/(m*m*scale),
                'D': state['Dprefix'][2*m*X-1]/X}
        gram['variance_identity_residual'] = gram['E_child']-gram['E_A']/m-gram['V']
        if not gram['variance_identity_residual'].contains(0):
            raise ArithmeticError('complete child variance identity failed')
        state['_gram_cache'][key] = gram
        return gram


def audit(state, programs, scales_by_m):
    """Return finite pass/fail/unresolved for every requested exact program/scale.

    Q<=0 is a finite observation only. No scalar, scale, covariance, increment
    head or child term is dropped, and no sign is inferred from midpoint floats.
    """
    if type(programs) not in (list, tuple) or not programs:
        raise ValueError('nonempty program list required')
    if type(scales_by_m) is not dict:
        raise ValueError('scale map required')
    meter = state['meter']
    rows, ids = [], set()
    with ctx.workprec(state['precision']):
        for program in programs:
            m, lam, rho, delta, C = validate_program(program, state['r'], meter)
            if program['id'] in ids:
                raise ValueError('unique program ids required')
            ids.add(program['id'])
            scales = scales_by_m.get(m, scales_by_m.get(str(m)))
            if type(scales) not in (list, tuple) or not scales or len(set(scales)) != len(scales):
                raise ValueError('nonempty unique complete scales required per m')
            for X in scales:
                gram = base_gram(state, m, X)
                E_I = gram['E_A']-2*lam*gram['C_JA']+lam*lam*gram['E_J']
                C_JI = gram['C_JA']-lam*gram['E_J']
                Q = 2*lam*C_JI+(1+delta)*E_I-(m*rho-lam*lam)*gram['E_J']-C*gram['D']
                status = 'pass' if Q <= 0 else ('fail' if Q > 0 else 'unresolved')
                moments = {**gram, 'lambda': lam, 'E_I': E_I, 'C_JI': C_JI, 'Q': Q}
                rows.append({'id': program['id'], 'm': m, 'X': X,
                             'source_indices': [X, 2*X-1],
                             'complete_child_indices': [m*X, 2*m*X-1],
                             'increment_indices': [1, 2*m*X-1],
                             'status': status,
                             'moments': {name: enclosure(value) for name, value in moments.items()},
                             'complete_child_variance_identity_checked': True})
                meter.charge(96)
        return {'schema': 'centered-mobius-interval-audit-v1',
                'source': {'H': state['H'], 'r': state['r'], 'theta': state['theta'],
                           'q': state['q'], 'precision': state['precision']},
                'programs': programs, 'scales_by_m': scales_by_m, 'rows': rows,
                'normalization': state.get('normalization'),
                'cached_base_grams': len(state['_gram_cache']),
                'counts': meter.counts(),
                'finite_evidence_only': True,
                'uniform_signed_bound_proved': False, 'RH_proved': False}
