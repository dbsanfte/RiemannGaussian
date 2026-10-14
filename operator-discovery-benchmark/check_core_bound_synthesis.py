"""Independent actual-source modes and complete generated auxiliary energies.

All signed Gram crosses are retained by forming the scalar expressions before
squaring. Delay/log-Abel filters and positive storage expose finite evidence;
no uniform bound, recovery premise, or RH conclusion is discharged here.
"""
from fractions import Fraction as Q
import re
from flint import arb, ctx

MAX_HORIZON = 262143
MODES = ('nu0', 'nu1', 'nu2', 'mu')
POWER_WORK = 64
ZETA_WORK = 256
LOG_CUTOFF = 64


def _rational(text):
    if type(text) is not str or not 1 <= len(text) <= 128 or re.fullmatch(r'-?\d+(?:/\d+)?', text) is None:
        raise ValueError('bounded canonical rational string')
    try: value = Q(text)
    except (ValueError, ZeroDivisionError) as error: raise ValueError('rational text') from error
    if str(value) != text: raise ValueError('canonical rational string')
    return value


def _exponent(text):
    value = _rational(text)
    if not 0 <= value <= 1 or value.denominator > 12: raise ValueError('rational exponent0..1, denominator<=12')
    return value


def validate(program):
    if type(program) is not dict or set(program) != {'target_filter', 'auxiliary'}:
        raise ValueError('exact target_filter/auxiliary program')
    target = program['target_filter']
    if type(target) is not dict: raise ValueError('target filter object')
    kind = target.get('kind', 'delay')
    if kind == 'delay':
        if set(target) not in ({'sign', 'theta'}, {'kind', 'sign', 'theta'}): raise ValueError('exact delay filter')
        if type(target['sign']) is not int or target['sign'] not in (-1, 0, 1): raise ValueError('delay sign -1,0,1')
        _exponent(target['theta'])
    elif kind == 'log_abel':
        if set(target) != {'kind', 'cutoff'} or type(target['cutoff']) is not int or target['cutoff'] != LOG_CUTOFF:
            raise ValueError('fixed log-Abel cutoff64')
    else: raise ValueError('known filter kind')
    auxiliary = program['auxiliary']
    if auxiliary is not None:
        if type(auxiliary) is not dict or set(auxiliary) != {'coefficients', 'theta', 'alpha', 'weight'}: raise ValueError('exact auxiliary schema')
        vector = auxiliary['coefficients']
        if type(vector) is not list or len(vector) != 4: raise ValueError('all4 auxiliary mode coordinates')
        for coefficient in vector: _rational(coefficient)
        if auxiliary['theta'] is not None: _exponent(auxiliary['theta'])
        _exponent(auxiliary['alpha'])
        if _rational(auxiliary['weight']) <= 0: raise ValueError('strictly positive storage weight')
    return program


def _precision():
    if ctx.prec != 192: raise ValueError('independent Arb precision192')


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite(): raise ArithmeticError('finite Arb value')
    return value


def _real(value, meter):
    meter.charge(2); return _finite(arb(value.numerator) / value.denominator, meter)


def _power(base, exponent, meter):
    meter.charge(POWER_WORK)
    return _finite(arb(base) ** _real(exponent, meter), meter)


def _convolve(left, right, meter):
    result = [arb(0)] * len(left)
    for d in range(1, len(left)):
        for k in range(1, (len(left) - 1) // d + 1):
            result[d * k] = _finite(result[d * k] + _finite(left[d] * right[k], meter), meter); meter.charge(2)
    return result


def _prefix(values, meter):
    result = [arb(0)] * len(values)
    for n in range(1, len(values)): result[n] = _finite(result[n - 1] + values[n], meter)
    return result


class State(dict):
    pass


def source(H, meter):
    _precision()
    if type(H) is not int or not 1 <= H <= MAX_HORIZON: raise ValueError('strictH1..262143')
    meter.live(20 * (H + 1) + 4096)
    mu_int = [1] * (H + 1); mu_int[0] = 0; composite = [False] * (H + 1); meter.charge(2 * (H + 1))
    for p in range(2, H + 1):
        meter.charge()
        if composite[p]: continue
        for n in range(p, H + 1, p):
            meter.charge(2); mu_int[n] = -mu_int[n]
            if n != p: composite[n] = True
        for n in range(p * p, H + 1, p * p): mu_int[n] = 0; meter.charge()
    mu = list(map(arb, mu_int)); ku = [arb(0)] * (H + 1); mu_v = [arb(0)] * (H + 1); meter.charge(H + 1)
    for n in range(1, H + 1):
        meter.charge(POWER_WORK); root = _finite(arb(n).root(3), meter)
        ku[n] = _finite(1 / root, meter); mu_v[n] = _finite(mu[n] * _finite(ku[n] * ku[n], meter), meter)
    # Complete direct convolutions, not the producer's prime-local modes.
    mu_square = _convolve(mu, mu, meter); mixed = _convolve(mu, mu_v, meter)
    modes = dict(nu0=_convolve(ku, mu_square, meter), nu1=_convolve(ku, mixed, meter),
                 nu2=_convolve(ku, mu_v, meter), mu=mu)
    prefixes = {name: _prefix(modes[name], meter) for name in MODES}
    meter.charge(2 * ZETA_WORK + 8)
    z = _finite((arb(2) / 3).zeta(), meter); w = _finite((arb(4) / 3).zeta(), meter)
    if z.contains(0): raise ArithmeticError('zeta denominator separated fromzero')
    beta = arb(9) / 2; R_u = _finite(beta * (w / (z * z) - 1 / z), meter); meter.charge(6)
    coefficients = [beta, -beta, -R_u, -beta]
    core = [arb(0)] * (H + 1)
    for n in range(1, H + 1):
        total = arb(0)
        for coefficient, name in zip(coefficients, MODES): total = _finite(total + _finite(coefficient * modes[name][n], meter), meter)
        core[n] = total
    F = _prefix(core, meter); log_prefix = [arb(0)] * (H + 1); log_abel = [arb(0)] * (H + 1)
    running = arb(0)
    for n in range(1, H + 1):
        if n == 1: logarithm = arb(0); meter.charge()
        else: meter.charge(POWER_WORK); logarithm = _finite(arb(n).log(), meter)
        running = _finite(running + _finite(core[n] * logarithm, meter), meter); log_prefix[n] = running
        log_abel[n] = F[n] if n < LOG_CUTOFF else _finite(running / logarithm, meter)
    result = State(H=H, precision=192, modes=modes, prefixes=prefixes, R_u=R_u, c=coefficients,
                   core=core, F=F, log_prefix=log_prefix, log_abel=log_abel, mu_int=mu_int)
    result.update({name: modes[name] for name in MODES})
    return result


def measure(program, X, state, meter):
    validate(program); _precision()
    if type(X) is not int or X < 1 or not isinstance(state, State) or state.get('precision') != 192:
        raise ValueError('positive integerX and own192-bit State')
    H = state.get('H'); N = 2 * X - 1
    if type(H) is not int or not 1 <= H <= MAX_HORIZON or N > H: raise ValueError('complete2X-1 support')
    for key in ('F', 'log_abel'):
        if type(state.get(key)) is not list or len(state[key]) != H + 1 or not state[key][0].is_zero(): raise ValueError('completezero-based prefix arrays')
    prefixes = state.get('prefixes')
    if type(prefixes) is not dict or set(prefixes) != set(MODES) or any(type(prefixes[name]) is not list or len(prefixes[name]) != H + 1 or not prefixes[name][0].is_zero() for name in MODES):
        raise ValueError('all4 full mode prefixes')
    meter.live(20 * (H + 1) + 4096)
    target = program['target_filter']; kind = target.get('kind', 'delay')
    a = arb(0) if kind != 'delay' or target['sign'] == 0 else _finite(target['sign'] * _power(2, _rational(target['theta']), meter), meter)
    auxiliary = program['auxiliary']
    if auxiliary is None: vector = None; b = weight = arb(0); alpha = Q(0)
    else:
        vector = [_real(_rational(c), meter) for c in auxiliary['coefficients']]
        b = arb(0) if auxiliary['theta'] is None else _power(2, _rational(auxiliary['theta']), meter)
        weight = _real(_rational(auxiliary['weight']), meter)
        alpha = _rational(auxiliary['alpha'])
    E_F = E_G = E_H = arb(0)
    for n in range(X, N + 1):
        current = state['F'][n]
        filtered = state['log_abel'][n] if kind == 'log_abel' else _finite(current - _finite(a * state['F'][n // 2], meter), meter)
        storage = arb(0)
        if vector is not None:
            for coefficient, name in zip(vector, MODES):
                value = _finite(prefixes[name][n] - _finite(b * prefixes[name][n // 2], meter), meter)
                storage = _finite(storage + _finite(coefficient * value, meter), meter)
            if alpha: storage = _finite(storage * _power(n, -alpha, meter), meter)
        E_F = _finite(E_F + _finite(current * current, meter), meter)
        E_G = _finite(E_G + _finite(filtered * filtered, meter), meter)
        E_H = _finite(E_H + _finite(storage * storage, meter), meter)
    denominator = X * X; meter.charge()
    E_F = _finite(E_F / denominator, meter); E_G = _finite(E_G / denominator, meter); E_H = _finite(E_H / denominator, meter)
    majorant = _finite(E_G + _finite(weight * E_H, meter), meter)
    return dict(X=X, energy_target=E_F, energy_filtered=E_G, energy_auxiliary=E_H, majorant=majorant,
                uniform_signed_bound_proved=False, RH_proved=False, recovery_premise_established=False,
                signed_credit_proved=False)


def verify_coarse(certificate, R_u, meter):
    """Verify the reviewed weak universal reference, never a critical bound.

Pointwise mode majorants give K=3*beta+R_u. Complete delay/log-Abel and
auxiliary prefix estimates give Ct and Ch. On [2X,4X), squaring and summing
costs8X; (1+ln(4X))^2<=9(1+log2X)^2 gives the exact constant72.
Nonnegative rho permits A(2X)-rho*A(X)<=A(2X).
"""
    _precision()
    fields = {'rule', 'source', 'imports', 'program', 'residue_ceiling', 'constant',
              'gamma', 'log_power', 'statement', 'independently_rh_sufficient',
              'whole_signed_bound_proved', 'RH_proved'}
    if type(certificate) is not dict or set(certificate) != fields:
        raise ValueError('exact universal coarse-reference schema')
    validate(certificate['program'])
    ceiling = certificate['residue_ceiling']
    if type(ceiling) is not int or not 1 <= ceiling <= 1048575:
        raise ValueError('bounded positive integer residue ceiling')
    _finite(R_u, meter)
    if not R_u > 0 or not R_u <= arb(ceiling):
        raise ValueError('complete residue enclosure must satisfy0<R_u<=ceiling')
    program = certificate['program']; target = program['target_filter']
    K = Q(27, 2) + ceiling
    Ct = K if target.get('kind', 'delay') == 'log_abel' else 2 * K
    auxiliary = program['auxiliary']; Ch = weight = Q(0)
    if auxiliary is not None:
        Ch = 2 * sum((abs(_rational(v)) for v in auxiliary['coefficients']), Q(0))
        weight = _rational(auxiliary['weight'])
    constant = 72 * (Ct * Ct + weight * Ch * Ch); meter.charge(30)
    imports = ['|nu0(n)|<=d2(n); |nu1(n)|,|nu2(n)|,|mu(n)|<=1',
               'sum_(n<=x) d2(n)<=x*(1+log x)', '0<R_u<=residue_ceiling']
    expected = dict(rule='absolute_prefix_majorants', source='actual_mu_candidate10_four_mode_core',
                    imports=imports, program=program, residue_ceiling=ceiling, constant=str(constant),
                    gamma='1', log_power=2,
                    statement='for every dyadic X>=1 and rho>=0: A(2X)-rho*A(X)<=constant*X*(1+log2 X)^2',
                    independently_rh_sufficient=False, whole_signed_bound_proved=False, RH_proved=False)
    # Strict scalar/list/dict typing prevents bool/int equality accepting forged metadata.
    def same(left, right):
        if type(left) is not type(right): return False
        if type(left) is dict: return set(left) == set(right) and all(same(left[k], right[k]) for k in left)
        if type(left) is list: return len(left) == len(right) and all(same(a, b) for a, b in zip(left, right))
        return left == right
    if not same(certificate, expected): raise ValueError('universal reference constant/domain/import/proof metadata mismatch')
    return dict(verified=True, universal_reference_verified=True, constant=str(constant), gamma='1', log_power=2,
                domain='all dyadic integers X>=1 and rho>=0',
                independently_rh_sufficient=False, whole_signed_bound_proved=False, RH_proved=False,
                cofinal_critical_bound_proved=False)
