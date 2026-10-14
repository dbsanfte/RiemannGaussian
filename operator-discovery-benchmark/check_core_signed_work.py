"""Independent complete core source, all-prime log bank and signed shells.

Direct Mobius convolutions differ from prime-local source reconstruction. Shell
weights use Ei at exact logarithmic endpoints; no endpoint approximation or
positive clipping of signed work occurs. Finite evidence proves no uniform gate.
"""
from fractions import Fraction as Q
import re
from flint import arb, ctx

MAX_HORIZON = 524287
MODES = ('nu0', 'nu1', 'nu2', 'mu')
POWER_WORK = 64
SPECIAL_WORK = 256
CUTOFF = 1024


def _rational(text):
    if type(text) is not str or not 1 <= len(text) <= 128 or re.fullmatch(r'-?\d+(?:/\d+)?', text) is None:
        raise ValueError('bounded canonical rational string')
    try: value = Q(text)
    except (ValueError, ZeroDivisionError) as error: raise ValueError('rational text') from error
    if str(value) != text: raise ValueError('canonical rational string')
    return value


def validate(program):
    if type(program) is not dict or set(program) != {'target_filter', 'eta', 'cutoff'}:
        raise ValueError('exact target_filter/eta/cutoff program')
    target = program['target_filter']
    if type(target) is not dict or set(target) != {'kind', 'sign', 'theta'} or target['kind'] != 'delay':
        raise ValueError('exact delay filter schema')
    if type(target['sign']) is not int or target['sign'] not in (-1, 0, 1): raise ValueError('strict delay sign')
    theta = _rational(target['theta'])
    if not 0 <= theta <= 1 or theta.denominator > 12: raise ValueError('delay exponent0..1, denominator<=12')
    eta = _rational(program['eta'])
    if not -2 <= eta <= 2: raise ValueError('signed eta in[-2,2]')
    if type(program['cutoff']) is not int or program['cutoff'] != CUTOFF: raise ValueError('fixed cutoff1024')
    return program


def _precision():
    if ctx.prec != 192: raise ValueError('independent Arb precision192')


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite(): raise ArithmeticError('finite Arb value')
    return value


def _real(value, meter):
    meter.charge(2)
    return _finite(arb(value.numerator) / value.denominator, meter)


def _convolve(left, right, meter):
    result = [arb(0)] * len(left)
    for d in range(1, len(left)):
        for k in range(1, (len(left) - 1) // d + 1):
            result[d * k] = _finite(result[d * k] + _finite(left[d] * right[k], meter), meter)
            meter.charge(2)
    return result


def _prefix(values, meter):
    result = [arb(0)] * len(values)
    for n in range(1, len(values)): result[n] = _finite(result[n - 1] + values[n], meter)
    return result


class State(dict):
    """Per-evaluation workspace; cached endpoints and filters remain metered."""
    pass


def _live(state, meter):
    H = state['H']
    meter.live(22 * (H + 1) + 4096 + 2 * len(state.get('_ei', {})) + 12 * len(state.get('_shells', {})))


def source(H, meter):
    _precision()
    if type(H) is not int or not 1 <= H <= MAX_HORIZON: raise ValueError('strictH1..524287')
    meter.live(22 * (H + 1) + 4096)
    mu_int = [1] * (H + 1); mu_int[0] = 0
    composite = [False] * (H + 1); primes = []; meter.charge(2 * (H + 1))
    for p in range(2, H + 1):
        meter.charge()
        if composite[p]: continue
        primes.append(p)
        for n in range(p, H + 1, p):
            meter.charge(2); mu_int[n] = -mu_int[n]
            if n != p: composite[n] = True
        for n in range(p * p, H + 1, p * p): mu_int[n] = 0; meter.charge()
    mu = list(map(arb, mu_int)); ku = [arb(0)] * (H + 1); mu_v = [arb(0)] * (H + 1)
    meter.charge(H + 1)
    for n in range(1, H + 1):
        meter.charge(POWER_WORK); root = _finite(arb(n).root(3), meter)
        ku[n] = _finite(1 / root, meter)
        mu_v[n] = _finite(mu[n] * _finite(ku[n] * ku[n], meter), meter)
    mu_square = _convolve(mu, mu, meter); mixed = _convolve(mu, mu_v, meter)
    modes = dict(nu0=_convolve(ku, mu_square, meter), nu1=_convolve(ku, mixed, meter),
                 nu2=_convolve(ku, mu_v, meter), mu=mu)
    prefixes = {name: _prefix(modes[name], meter) for name in MODES}
    meter.charge(2 * SPECIAL_WORK + 8)
    z = _finite((arb(2) / 3).zeta(), meter); w = _finite((arb(4) / 3).zeta(), meter)
    if z.contains(0): raise ArithmeticError('zeta denominator separated fromzero')
    beta = arb(9) / 2; R_u = _finite(beta * (w / (z * z) - 1 / z), meter); meter.charge(6)
    coefficients = [beta, -beta, -R_u, -beta]
    core = [arb(0)] * (H + 1)
    for n in range(1, H + 1):
        total = arb(0)
        for coefficient, name in zip(coefficients, MODES):
            total = _finite(total + _finite(coefficient * modes[name][n], meter), meter)
        core[n] = total
    F = _prefix(core, meter); log_prefix = [arb(0)] * (H + 1); running = arb(0)
    for n in range(1, H + 1):
        if n == 1: logarithm = arb(0); meter.charge()
        else: meter.charge(POWER_WORK); logarithm = _finite(arb(n).log(), meter)
        running = _finite(running + _finite(core[n] * logarithm, meter), meter)
        log_prefix[n] = running
    result = State(H=H, precision=192, modes=modes, prefixes=prefixes, core=core, F=F,
                   log_prefix=log_prefix, B=log_prefix, R_u=R_u, c=coefficients,
                   mu_int=mu_int, primes=primes, ku=ku, _ei={}, _shells={}, _cache_meter=meter)
    result.update({name: modes[name] for name in MODES})
    return result


def _state(state):
    if not isinstance(state, State) or state.get('precision') != 192: raise ValueError('own192-bit State')
    H = state.get('H')
    if type(H) is not int or not 1 <= H <= MAX_HORIZON: raise ValueError('bounded complete horizon')
    for key in ('F', 'log_prefix'):
        values = state.get(key)
        if type(values) is not list or len(values) != H + 1 or type(values[0]) is not arb or not values[0].is_zero():
            raise ValueError('complete zero-based prefix arrays')
    return H


def _cache(state, meter):
    # Cache use under a different audit meter cannot make prior work disappear.
    if state.get('_cache_meter') is not meter:
        state['_ei'] = {}; state['_shells'] = {}; state['_cache_meter'] = meter
    _live(state, meter)


def _ell(n, state, meter):
    if n == 1: return arb(0)  # Only used with the exactly zero unit log bank.
    cache = state['_ei']
    for endpoint in (n, n + 1):
        if endpoint not in cache:
            meter.charge(POWER_WORK + SPECIAL_WORK)
            logarithm = _finite(arb(endpoint).log(), meter)
            cache[endpoint] = _finite((-logarithm).ei(), meter)
            _live(state, meter)
    value = _finite(cache[n + 1] - cache[n], meter)
    if not value > 0: raise ArithmeticError('positive complete integral weight')
    return value


def measure(program, X, state, meter):
    validate(program); _precision(); H = _state(state)
    if type(X) is not int or X < 1 or 2 * X - 1 > H: raise ValueError('complete positive integer block')
    _cache(state, meter)
    target = program['target_filter']; key = (target['sign'], target['theta'], X)
    if key not in state['_shells']:
        if target['sign'] == 0: a = arb(0)
        else:
            meter.charge(POWER_WORK)
            a = _finite(target['sign'] * arb(2) ** _real(_rational(target['theta']), meter), meter)
        meter.charge(POWER_WORK); log2 = _finite(arb(2).log(), meter)
        E = critical = prime = arb(0)
        for n in range(X, 2 * X):
            half = n // 2
            G = _finite(_finite(state['F'][n], meter) - _finite(a * _finite(state['F'][half], meter), meter), meter)
            BG = _finite(_finite(state['log_prefix'][n], meter) - _finite(a * _finite(state['log_prefix'][half], meter), meter)
                         - _finite(_finite(a * log2, meter) * state['F'][half], meter), meter)
            if n == 1 and not BG.is_zero(): raise ValueError('unit log bank must be exactlyzero')
            square = _finite(G * G, meter)
            E = _finite(E + square, meter)
            critical = _finite(critical + _finite(square / (n * (n + 1)), meter), meter); meter.charge(2)
            prime = _finite(prime + _finite(_finite(G * BG, meter) * _ell(n, state, meter), meter), meter)
        E = _finite(E / (X * X), meter); meter.charge()
        state['_shells'][key] = (E, critical, prime)
        _live(state, meter)
    E, critical, prime = state['_shells'][key]
    eta = _real(_rational(program['eta']), meter)
    work = _finite(_finite((1 - eta) * critical, meter) + _finite(eta * prime, meter), meter); meter.charge()
    memory = _finite(critical - prime, meter)
    return dict(X=X, energy_filtered=E, critical_energy=critical, prime_log_work=prime,
                memory_cross=memory, work=work, dyadic_domain=(X >= CUTOFF and X & (X - 1) == 0),
                uniform_signed_bound_proved=False, all_scale_work_bound_proved=False,
                whole_signed_bound_proved=False, recovery_premise_established=False, RH_proved=False)


def verify_logbank(state, meter):
    """All-prime-power logarithmic derivatives, checked against every coefficient.

Lambda(p^e)=log(p), while lambda_i(p^e) retains the full prime-power
argument. Each complete cofactor and the unit are present in the convolution.
"""
    _precision(); H = _state(state); _live(state, meter)
    modes = state.get('modes'); c = state.get('c'); core = state.get('core')
    if type(modes) is not dict or set(modes) != set(MODES) or type(c) is not list or len(c) != 4 or type(core) is not list or len(core) != H + 1:
        raise ValueError('complete core mode data')
    if any(type(modes[name]) is not list or len(modes[name]) != H + 1 for name in MODES): raise ValueError('complete mode coefficients')
    # Independently recover primes; do not trust caller-supplied source metadata.
    composite = [False] * (H + 1); primes = []; meter.charge(H + 1)
    for p in range(2, H + 1):
        meter.charge()
        if composite[p]: continue
        primes.append(p)
        for n in range(p * p, H + 1, p): composite[n] = True; meter.charge()
    bank = [arb(0)] * (H + 1); meter.live(27 * (H + 1) + 4096 + 2 * len(state.get('_ei', {})) + 12 * len(state.get('_shells', {})))
    for p in primes:
        meter.charge(POWER_WORK); logarithm = _finite(arb(p).log(), meter)
        d = p
        while d <= H:
            meter.charge(POWER_WORK); inverse_root = _finite(1 / arb(d).root(3), meter)
            inverse_square = _finite(inverse_root * inverse_root, meter)
            lambdas = (inverse_root - 2, inverse_root - 1 - inverse_square, inverse_root - inverse_square, arb(-1))
            meter.charge(6)
            multipliers = [_finite(_finite(logarithm * lam, meter) * coefficient, meter) for lam, coefficient in zip(lambdas, c)]
            for k in range(1, H // d + 1):
                summand = arb(0)
                for multiplier, name in zip(multipliers, MODES):
                    summand = _finite(summand + _finite(multiplier * modes[name][k], meter), meter)
                bank[d * k] = _finite(bank[d * k] + summand, meter)
            d *= p; meter.charge()
    residual = [arb(0)] * (H + 1)
    for n in range(1, H + 1):
        if n == 1: direct = arb(0)
        else:
            meter.charge(POWER_WORK); direct = _finite(core[n] * _finite(arb(n).log(), meter), meter)
        residual[n] = _finite(bank[n] - direct, meter)
        if not residual[n].contains(0): raise ValueError('all-prime coefficient log-bank identity fails')
    prefix = _prefix(bank, meter)
    prefix_residual = [_finite(prefix[n] - state['log_prefix'][n], meter) for n in range(H + 1)]
    if any(not value.contains(0) for value in prefix_residual): raise ValueError('complete prefix log-bank identity fails')
    return dict(verified=True, coefficients=bank, prefix=prefix, coefficient_residual=residual,
                prefix_residual=prefix_residual, all_prime_powers_retained=True,
                uniform_signed_bound_proved=False, RH_proved=False)


def _same(left, right):
    if type(left) is not type(right): return False
    if type(left) is dict: return set(left) == set(right) and all(_same(left[k], right[k]) for k in left)
    if type(left) is list: return len(left) == len(right) and all(_same(a, b) for a, b in zip(left, right))
    return left == right


def _inverse(target):
    theta = _rational(target['theta']) if target['sign'] else Q(0)
    if not target['sign']:
        return dict(cofinal=True, extra_log_degree=0, kind='identity', uniform_core_bound_proved=False)
    if theta < Q(1, 2):
        return dict(cofinal=True, extra_log_degree=0, kind='bounded_causal_inverse',
                    cost='(1-2^(theta-1/2))^-1 in critical prefix norm', uniform_core_bound_proved=False)
    if theta == Q(1, 2):
        return dict(cofinal=True, extra_log_degree=2, kind='critical_polylog_causal_inverse',
                    cost='at most1+floor(log2 H) in truncated critical norm', uniform_core_bound_proved=False)
    return dict(cofinal=False, extra_log_degree=None, kind='unpaid_inverse_power',
                energy_power_loss=str(2 * theta - 1), uniform_core_bound_proved=False)


def verify_recovery(certificate, meter):
    """Verify conditional history absorption and its paid causal inverse.

The proof checks are rational. log2>69/100 follows from three positive
atanh-series terms. 7/5<sqrt2<3/2 gives 2-sqrt2<3/5 and
(1+sqrt2)^2<6. No supplied finite work rows discharge the uniform premise.
"""
    if type(certificate) is not dict or 'program' not in certificate: raise ValueError('recovery certificate object')
    program = validate(certificate['program'])
    expected = dict(rule='signed_shell_volterra_history', program=program,
        work='integral_X^(2X) ((1-eta)*G(x)^2+eta*G(x)*B_G(x)/log(x))/x^2 dx',
        exact_filtered_log_bank='B_G(x)=B_F(x)-a*B_F(x/2)-a*log(2)*F(x/2)',
        domain='every dyadic X>=1024; full unit-cell integrals; zero prefixes below1',
        eta_absolute_ceiling='2', log2_lower='69/100', local_volterra_upper='3/5',
        history_geometric_sum_square_upper='6', gap_lower='4/5', history_mass_upper='2/5',
        history='N_G(X)<=2W_eta(X)/g_eta(X)+eta^2*(1+sqrt2)/(2*g_eta(X)^2*log(X)^2)*sum_(k=1)^log2X 2^(-k/2)*N_G(X/2^k)',
        gap='g_eta(X)=1-|eta|*(2-sqrt2)/log(X)',
        assumption='W_eta(X)<=K*(1+log2X)^p for every dyadic X>=1024; K>=0,p>=0',
        head='H0=max_(dyadic Y<1024) E_G(Y), all finite units and delayed heads retained',
        conclusion='E_G(X)<=4*max(H0,5K)*(1+log2X)^p for all dyadic X>=1',
        strict_smaller_scale_dependencies=True, filtered_energy_log_loss=0,
        target_recovery=_inverse(program['target_filter']), all_scale_work_bound_proved=False,
        whole_signed_bound_proved=False, RH_proved=False)
    meter.charge(120)
    lower_log2 = 2 * sum((Q(1, 3) ** (2 * j + 1) / (2 * j + 1) for j in range(3)), Q(0))
    logX_lower = 10 * Q(69, 100)
    gap = 1 - 2 * Q(3, 5) / logX_lower
    mass = 4 * 6 / (2 * Q(4, 5) ** 2 * logX_lower ** 2)
    if not (lower_log2 > Q(69, 100) and Q(7, 5) ** 2 < 2 < Q(3, 2) ** 2 and gap > Q(4, 5) and mass < Q(2, 5)):
        raise ArithmeticError('strict rational history absorption conditions')
    if not _same(certificate, expected): raise ValueError('history scope/constants/inverse/premise certificate mismatch')
    return dict(verified=True, conditional_recovery_verified=True, strict_smaller_scale_dependencies=True,
                target_recovery=expected['target_recovery'], uniform_premise_discharged=False,
                all_scale_work_bound_proved=False, whole_signed_bound_proved=False, RH_proved=False)


def verify_weak(certificate, R_u, meter):
    """Weak gamma1 reference bounds signed work in absolute value, both scales.

|g_n|<=3*(3*beta+R_u)*d2(n). Summation bounds both G and
B_G/log by Cg*n*(1+log n). Complete cell integrals give a shell
constant4*(|1-eta|+|eta|)*Cg^2. The signed step requires child AND
parent absolute bounds; their scale/log comparison contributes9.
"""
    _precision()
    if type(certificate) is not dict or 'program' not in certificate: raise ValueError('weak certificate object')
    program = validate(certificate['program']); _finite(R_u, meter)
    if not R_u > 0 or not R_u <= arb(5): raise ValueError('complete0<R_u<=5 enclosure')
    eta = _rational(program['eta']); Cg = 3 * Q(37, 2)
    constant = 4 * (abs(1 - eta) + abs(eta)) * Cg * Cg; meter.charge(35)
    expected = dict(rule='complete_absolute_shell_reference', program=program, source_residue_ceiling=5,
                    source_coefficient_ceiling='37/2', filtered_coefficient_ceiling=str(Cg),
                    shell_constant=str(constant), step_constant=str(9 * constant), gamma='1', log_power=2,
                    scope='all dyadic X>=1024 and0<=rho<=1; |W(X)|<=shell_constant*X*(1+log2X)^2',
                    critical_control_proved=False, whole_signed_bound_proved=False, RH_proved=False)
    if not _same(certificate, expected): raise ValueError('weak full signed step/reference scope mismatch')
    return dict(verified=True, universal_weak_reference_verified=True, gamma='1', log_power=2,
                shell_constant=str(constant), step_constant=str(9 * constant),
                critical_control_proved=False, whole_signed_bound_proved=False, RH_proved=False)


def verify_recurrence(certificate, meter):
    """Conditional upper induction on signed work; neither base nor step assumed proven."""
    if type(certificate) is not dict: raise ValueError('recurrence certificate object')
    fields = {'rule', 'program', 'rho', 'log_power', 'constant', 'base_scale', 'base_upper',
              'head_energy_upper', 'base_requirement', 'premise', 'work_upper_constant',
              'filtered_log_degree', 'filtered_energy_constant', 'conclusion', 'recovery',
              'uniform_step_proved', 'whole_signed_bound_proved', 'RH_proved'}
    if set(certificate) != fields: raise ValueError('exact recurrence certificate schema')
    program = validate(certificate['program'])
    rho = _rational(certificate['rho']); constant = _rational(certificate['constant'])
    base = _rational(certificate['base_upper']); head = _rational(certificate['head_energy_upper'])
    k = certificate['log_power']
    if not 0 <= rho <= 1 or min(constant, base, head) < 0 or type(k) is not int or not 0 <= k <= 4096:
        raise ValueError('nonnegative rational forcing/base/head, rho0..1 and bounded integer log power')
    if constant == 0: K = base; p = 0
    elif rho < 1: K = base + constant / (1 - rho); p = k
    else: K = base + constant; p = k + 1
    if not _same(certificate['recovery'].get('program') if type(certificate['recovery']) is dict else None, program):
        raise ValueError('recovery must bind identical program')
    recovery_result = verify_recovery(certificate['recovery'], meter)
    meter.charge(40)
    expected = dict(rule='signed_upper_dyadic_recurrence', program=program, rho=str(rho), log_power=k,
        constant=str(constant), base_scale=CUTOFF, base_upper=str(base), head_energy_upper=str(head),
        base_requirement='W(1024)<=base_upper; all dyadic E_G(Y)<=head_energy_upper for1<=Y<1024',
        premise='W(2X)<=rho*W(X)+constant*(1+log2X)^log_power for every dyadic X>=1024',
        work_upper_constant=str(K), filtered_log_degree=p, filtered_energy_constant=str(4 * max(head, 5 * K)),
        conclusion='E_G(X)<=filtered_energy_constant*(1+log2X)^filtered_log_degree for every dyadic X>=1',
        recovery=certificate['recovery'], uniform_step_proved=False, whole_signed_bound_proved=False, RH_proved=False)
    if not _same(certificate, expected): raise ValueError('conditional signed recurrence/base/head/growth scope mismatch')
    return dict(verified=True, conditional_induction_verified=True, work_upper_constant=str(K),
                filtered_log_degree=p, filtered_energy_constant=expected['filtered_energy_constant'],
                target_recovery=recovery_result['target_recovery'], base_and_head_verified=False,
                uniform_step_proved=False, whole_signed_bound_proved=False, RH_proved=False)
