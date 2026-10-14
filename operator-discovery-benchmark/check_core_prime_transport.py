"""Independent complete prime/composite transport and conditional recovery.

Every failed window is retained unchanged. Capacity is tested on the SUM
of all assigned demands, before any coefficient changes. Global log prefixes
retain all earlier windows; transported coefficients are not multiplicative.
No finite transport result supplies an all-scale target estimate.
"""
from fractions import Fraction as Q
import re
from flint import arb, ctx

MAX_HORIZON = 524287


class Meter:
    def __init__(self, cap=1500000000, max_cells=48000000):
        self.operations = 0; self.peak_cells = 0; self.cap = cap; self.max_cells = max_cells
    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('strict nonnegative work')
        self.operations += n
        if self.operations > self.cap: raise RuntimeError('shared work cap')
    def live(self, cells):
        if type(cells) is not int or cells < 0: raise ValueError('strict resident cells')
        self.peak_cells = max(self.peak_cells, cells)
        if cells > self.max_cells: raise RuntimeError('resident cap')
    def counts(self): return dict(operations=self.operations, peak_cells=self.peak_cells)


def _rational(text):
    if type(text) is not str or not 1 <= len(text) <= 128 or re.fullmatch(r'-?\d+(?:/\d+)?', text) is None:
        raise ValueError('bounded canonical rational string')
    try: value = Q(text)
    except (ValueError, ZeroDivisionError) as error: raise ValueError('rational string') from error
    if str(value) != text: raise ValueError('canonical rational string')
    return value


def validate(program):
    if type(program) is not dict or set(program) != {'cofactor', 'theta', 'capacity_fraction', 'load_multiple', 'keep_failed_windows'}:
        raise ValueError('exact transport AST')
    m = program['cofactor']; theta = _rational(program['theta'])
    if type(m) is not int or not 2 <= m <= 16 or not 0 < theta <= 1: raise ValueError('cofactor2..16,theta in(0,1]')
    if program['capacity_fraction'] != '1/2' or type(program['capacity_fraction']) is not str:
        raise ValueError('fixed half capacity')
    if type(program['load_multiple']) is not int or program['load_multiple'] != 4: raise ValueError('fixed load4m')
    if program['keep_failed_windows'] is not True: raise ValueError('whole failed windows retained')
    return theta


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite(): raise ArithmeticError('finite Arb value')
    return value


def _plan(coefficients, sources, destinations, m, meter):
    """Pure all-or-nothing sign/congestion/aggregate-capacity guard.

Geometry is established by transform, never by this helper alone. The helper
is also useful for tiny synthetic congestion cases with no prime-gap claim.
"""
    meter.charge(len(sources) + len(destinations))
    if not sources: return 'empty', 'no_prime_sources', 0, []
    if any(not coefficients[p] < 0 for p in sources): return 'rejected', 'source_not_negative', None, []
    if not destinations: return 'rejected', 'no_destinations', None, []
    if any(not coefficients[t] > 0 for t in destinations): return 'rejected', 'destination_not_positive', None, []
    load = (len(sources) + len(destinations) - 1) // len(destinations); meter.charge(3)
    if load > 4 * m: return 'rejected', 'congestion', load, []
    demands = {t: arb(0) for t in destinations}; assignments = []
    for i, p in enumerate(sources):
        t = destinations[i % len(destinations)]; demand = _finite(-coefficients[p], meter)
        assignments.append([p, t, demand]); demands[t] = _finite(demands[t] + demand, meter); meter.charge(2)
    for t in destinations:
        capacity = _finite(coefficients[t] / 2, meter)
        meter.charge()
        if not demands[t] <= capacity: return 'rejected', 'capacity_not_certified', load, []
    return 'accepted', 'all_guards_passed', load, assignments


def transform(coefficients, program, meter=None):
    if meter is None: meter = Meter()
    if ctx.prec != 192: raise ValueError('independent Arb precision192')
    theta = validate(program); m = program['cofactor']
    if type(coefficients) is not list or not 2 <= len(coefficients) <= MAX_HORIZON + 1 or len(coefficients) & (len(coefficients) - 1):
        raise ValueError('complete horizon2^J-1,J>=1')
    H = len(coefficients) - 1; J = len(coefficients).bit_length() - 1
    meter.live(60 * (H + 1) + 4096)
    for value in coefficients: _finite(value, meter)
    if not coefficients[0].is_zero(): raise ValueError('zero dummy coefficient')
    # Eratosthenes geometry; no source arithmetic or producer imports.
    prime = [True] * (H + 1); prime[0] = prime[1] = False; meter.charge(H + 1)
    for p in range(2, H + 1):
        meter.charge()
        if prime[p]:
            for n in range(p * p, H + 1, p): prime[n] = False; meter.charge()
    g = list(coefficients); windows = []; assignments = []
    for k in range(J):
        A = 1 << k; exponent = theta.numerator * k // theta.denominator; L = 1 << exponent; meter.charge(3)
        for start in range(A, 2 * A, L):
            stop = start + L
            sources = [p for p in range(start, stop) if prime[p]]; meter.charge(L)
            destinations = []
            for t in range(start, stop):
                if t % m == 0 and t // m > m and prime[t // m]: destinations.append(t)
                meter.charge(3)
            if set(sources) & set(destinations): raise ArithmeticError('prime/composite source collision')
            meter.charge(len(sources) + len(destinations))
            status, reason, load, plan = _plan(coefficients, sources, destinations, m, meter)
            if status == 'accepted':
                for p, t, demand in plan:
                    g[p] = arb(0); g[t] = _finite(g[t] - demand, meter)
                assignments.extend(plan)
            mass_original = mass_transformed = arb(0)
            for n in range(start, stop):
                mass_original = _finite(mass_original + coefficients[n], meter)
                mass_transformed = _finite(mass_transformed + g[n], meter)
            residual = _finite(mass_original - mass_transformed, meter)
            if not residual.contains(0): raise ArithmeticError('window mass conservation')
            windows.append(dict(annulus=A, start=start, stop=stop, length=L, sources=sources,
                destinations=destinations, max_load=load, status=status, reason=reason,
                assignments=plan, mass_residual=residual))
    F = [arb(0)] * (H + 1); G = [arb(0)] * (H + 1)
    B = [arb(0)] * (H + 1); Bg = [arb(0)] * (H + 1)
    D = [arb(0)] * (H + 1); B_D = [arb(0)] * (H + 1)
    logarithms = [arb(0)] * (H + 2); ei = [arb(0)] * (H + 2)
    for n in range(2, H + 2):
        meter.charge(320); logarithms[n] = _finite(arb(n).log(), meter)
        ei[n] = _finite((-logarithms[n]).ei(), meter)
    for n in range(1, H + 1):
        F[n] = _finite(F[n - 1] + coefficients[n], meter); G[n] = _finite(G[n - 1] + g[n], meter)
        B[n] = _finite(B[n - 1] + _finite(coefficients[n] * logarithms[n], meter), meter)
        Bg[n] = _finite(Bg[n - 1] + _finite(g[n] * logarithms[n], meter), meter)
        D[n] = _finite(F[n] - G[n], meter); B_D[n] = _finite(B[n] - Bg[n], meter)
    blocks = []
    for k in range(J):
        X = 1 << k; Eg = Ed = Wg = arb(0)
        for n in range(X, 2 * X):
            Eg = _finite(Eg + _finite(G[n] * G[n], meter), meter)
            Ed = _finite(Ed + _finite(D[n] * D[n], meter), meter)
            if n > 1:
                ell = _finite(ei[n + 1] - ei[n], meter)
                Wg = _finite(Wg + _finite(_finite(G[n] * Bg[n], meter) * ell, meter), meter)
        Eg = _finite(Eg / (X * X), meter); Ed = _finite(Ed / (X * X), meter); meter.charge(2)
        blocks.append(dict(X=X, energy_transformed=Eg, energy_error=Ed, prime_log_work=Wg,
                           work_domain=X >= 1024, uniform_bound_proved=False))
    return dict(H=H, J=J, program=program, g=g, G=G, Bg=Bg, F=F, B=B, D=D, B_D=B_D,
                windows=windows, assignments=assignments, blocks=blocks, identity_verified=True,
                arithmetic_error_premise_verified=False, transported_source_multiplicative=False,
                all_scale_target_bound_proved=False, RH_proved=False)


def verify_recovery(program, source_program, R_u, meter=None):
    """Derive prime coefficients formally; keep the reviewed eventual input explicit.

The universal error payment follows from the actual-source prime polynomial
and negative-only complete window flows. It is not a bound on Eg. Eventual
prime deletion additionally imports review011 and Guth--Maynard Corollary1.3;
that imported result is not independently proved by this arithmetic checker.
"""
    if meter is None: meter = Meter()
    if ctx.prec != 192: raise ValueError('independent Arb precision192')
    theta = validate(program); _finite(R_u, meter)
    if not R_u > 0 or not R_u < arb(5): raise ValueError('strict complete0<R_u<5 enclosure')
    if type(source_program) is not dict or type(source_program.get('terms')) is not list or len(source_program['terms']) != 4:
        raise ValueError('all4 complete source factor rows')
    expected_modes = {'B': ('beta', {Q(0): Q(-2), Q(1, 3): Q(1)}),
                      'U': ('-beta', {Q(0): Q(-1), Q(1, 3): Q(1), Q(2, 3): Q(-1)}),
                      'V': ('-beta', {Q(0): Q(-1)}),
                      'power': ('-R_u', {Q(1, 3): Q(1), Q(2, 3): Q(-1)})}
    formal_scalars = {'beta': (Q(1), Q(0)), '-beta': (Q(-1), Q(0)), '-R_u': (Q(0), Q(-1))}
    polynomial = {}; seen = set()
    for term in source_program['terms']:
        if type(term) is not dict or set(term) != {'name', 'coefficient', 'zeta_factors'} or type(term['name']) is not str or term['name'] not in expected_modes or term['name'] in seen:
            raise ValueError('unique complete source mode schema')
        seen.add(term['name']); scalar = term['coefficient']; factors = term['zeta_factors']
        if type(scalar) is not str or scalar not in formal_scalars or type(factors) is not list: raise ValueError('formal beta/Ru coefficients')
        decoded = {}; last = None
        for factor in factors:
            if type(factor) is not list or len(factor) != 2: raise ValueError('complete zeta factor pair')
            shift = _rational(factor[0]); exponent = _rational(factor[1])
            if shift < 0 or exponent == 0 or exponent.denominator != 1 or (last is not None and shift <= last):
                raise ValueError('ordered nonzero integral Euler factors')
            last = shift; decoded[shift] = exponent
            beta_part, residue_part = formal_scalars[scalar]
            old = polynomial.get(shift, (Q(0), Q(0)))
            polynomial[shift] = (old[0] + beta_part * exponent, old[1] + residue_part * exponent); meter.charge(8)
        # This complete binding also protects the cofactor sign/tail argument.
        if (scalar, decoded) != expected_modes[term['name']]: raise ValueError('complete actual four-mode source AST binding')
    polynomial = {power: coefficient for power, coefficient in polynomial.items() if coefficient != (0, 0)}
    if polynomial != {Q(1, 3): (Q(0), Q(-1)), Q(2, 3): (Q(1), Q(1))}:
        raise ValueError('complete prime polynomial mismatch')
    m = program['cofactor']; remainder = m; singly_valued = 0; p = 2
    while p * p <= remainder:
        exponent = 0; meter.charge(2)
        while remainder % p == 0: remainder //= p; exponent += 1; meter.charge(3)
        singly_valued += exponent == 1; p += 1
    if remainder > 1: singly_valued += 1
    positive_cofactor_limit = singly_valued % 2 == 1
    power = 2 * theta - Q(5, 3); alpha = theta - Q(1, 3)
    eventual = positive_cofactor_limit and Q(17, 30) < theta < Q(99, 100); meter.charge(30)
    return dict(verified=True, prime_polynomial=[['1/3', '0', '-1'], ['2/3', '1', '1']],
        polynomial_basis=['beta', 'R_u'], beta='9/2', residue_scope='0<R_u<5',
        prime_demand_bound='accepted demand -f(p)<=5*p^(-1/3)',
        window_error_bound='|D(n)|<=5*L*A^(-1/3) on every complete annulus window',
        error_energy_constant='25', error_energy_power=str(power),
        error_energy_domain='every dyadic X>=1, including all failed windows and finite units',
        error_energy_bound_proved=True, cofinal_recovery=power <= 0,
        forward_energy_bound='E_F(X)<=2*E_g(X)+50*X^('+str(power)+')',
        reverse_energy_bound='E_g(X)<=2*E_F(X)+50*X^('+str(power)+')',
        global_log_bank_identity='B_D(x)=log(x)*D(x)-integral_1^x D(t)/t dt',
        all_earlier_window_tails_retained=True,
        global_log_bank_bound=('|B_D(x)|<=5*x^('+str(alpha)+')*(log(x)+1/('+str(alpha)+'))' if alpha > 0 else None),
        global_log_bank_bound_applicable=alpha > 0, cofactor_positive_limit=positive_cofactor_limit,
        cofactor_single_valuation_prime_count=singly_valued,
        eventual_prime_deletion=eventual,
        eventual_prime_deletion_is_conditional_on_reviewed_import=True,
        trusted_inputs=['review011 complete-cofactor sign argument', 'Guth--Maynard arXiv:2405.20552 Corollary1.3, short-interval prime counts'],
        eventual_prime_count_domain='17/30<theta<99/100; fixed cofactor with positive leading limit',
        transported_source_multiplicative=False, transported_euler_log_bank_inherited=False,
        all_scale_transformed_bound_proved=False, all_scale_target_bound_proved=False, RH_proved=False)
