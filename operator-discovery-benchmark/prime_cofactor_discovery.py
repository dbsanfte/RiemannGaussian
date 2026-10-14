"""Generate prime/cofactor states and prove elementary frontier bounds.

The input is an arithmetic source expression, not a bank of companion states.
Exact coefficient jets generate the states. Rational generating functions
describe every prime valuation. The bound grammar currently contains power
summation and a prime-only rough-frontier lower bound, not a proof of the joined
prefix estimate. Finite observations never change a certificate's scope.
"""
from fractions import Fraction
import time

import sympy as S

Q, T, R = S.symbols('q t R')
SPEC = dict(max_states=12, valuations=[1, 2, 3], max_degree=24,
            operation_cap=10000000, seconds=300,
            residue_interval=['1', '5'], lattice=6)


class Budget:
    def __init__(self, spec=None):
        self.spec = dict(SPEC, **(spec or {}))
        self.operations = 0
        self.started = time.monotonic()

    def charge(self, n=1):
        self.operations += n
        if self.operations > self.spec['operation_cap']:
            raise RuntimeError('symbolic work cap')
        if time.monotonic() - self.started > self.spec['seconds']:
            raise RuntimeError('symbolic time cap')


def rat(x):
    return S.Rational(str(x))


def core_source():
    """Original four signed Dirichlet products; no companion supplied."""
    def a(kind, shift):
        return dict(kind=kind, shift=shift)
    return dict(lattice=6, channels=[
        dict(atoms=[a('power', 2), a('mu', 0), a('mu', 0)], weight=['9/2', '0']),
        dict(atoms=[a('power', 2), a('mu', 0), a('mu', 4)], weight=['-9/2', '0']),
        dict(atoms=[a('power', 2), a('mu', 4)], weight=['0', '-1']),
        dict(atoms=[a('mu', 0)], weight=['-9/2', '0'])])


def compile_source(source):
    if source['lattice'] != 6 or not 1 <= len(source['channels']) <= 12:
        raise ValueError('sixth-root lattice and at most12 channels')
    factors, weights = [], []
    for channel in source['channels']:
        if not 1 <= len(channel['atoms']) <= 8:
            raise ValueError('one to eight source atoms per channel')
        factor = S.Integer(1)
        for atom in channel['atoms']:
            shift = atom['shift']
            if type(shift) is not int or not 0 <= shift <= 24:
                raise ValueError('bounded nonnegative atom shift')
            if atom['kind'] == 'mu':
                factor *= 1-Q**shift*T
            elif atom['kind'] == 'power':
                factor /= 1-Q**shift*T
            else:
                raise ValueError('source atom kind')
        factors.append(S.cancel(factor))
        weights.append(rat(channel['weight'][0])+rat(channel['weight'][1])*R)
    return factors, weights


def coefficients(factor, count):
    """Finite jets for proposing states; the closure proof uses full factors."""
    num, den = map(lambda z: S.Poly(z, T), S.fraction(S.cancel(factor)))
    out = []
    for e in range(count+1):
        value = num.nth(e)-sum(den.nth(j)*out[e-j] for j in range(1, e+1))
        out.append(S.cancel(value/den.nth(0)))
    return out


def terms(poly):
    return [[int(i), int(j), str(c)] for (i, j), c in
            sorted(S.Poly(poly, Q, T).terms()) if c != 0]


def encode_function(expr):
    num, den = S.fraction(S.cancel(expr))
    # Normalize a constant formal-series denominator coefficient to one.
    constant = S.expand(den).subs(T, 0)
    if constant != 0 and not constant.has(Q):
        num, den = S.expand(num/constant), S.expand(den/constant)
    return dict(numerator=terms(num), denominator=terms(den))


def encode_matrix(matrix):
    return [[str(x) for x in row] for row in matrix.tolist()]


def affine_interval(value):
    """Exact enclosure over the fixed source parameter domain 1<=R<=5."""
    p = S.Poly(S.expand(value), R)
    if p.degree() > 1:
        raise ValueError('affine source constant required')
    a, b = p.nth(0), p.nth(1)
    values = (a+b, a+5*b)
    return min(values), max(values)


def abs_ceiling(value):
    return max(map(abs, affine_interval(value)))


def prime_polynomial(row, local, weights):
    return S.Poly(S.expand(sum(row[j]*coefficients(local[j], 1)[1]*weights[j]
                              for j in range(len(local)))), Q)


def frontier_bound(index, row, local, weights, meter):
    """Synthesize a power bound and, when possible, a cofinal lower bound.

    Scope: H(n;y), y=ceil(sqrt(2X)), X<=n<2X. The support is just
    the unit and primes. It is not the complete integer prefix of the source.
    """
    poly = prime_polynomial(row, local, weights)
    unit = S.expand(sum(a*b for a, b in zip(row, weights)))
    J = abs_ceiling(unit)
    entries = [[int(d), str(S.expand(c).coeff(R, 0)),
                str(S.expand(c).coeff(R, 1))]
               for (d,), c in sorted(poly.terms()) if c != 0]
    base = dict(state=index, prime_polynomial=entries, unit_ceiling=str(J),
                scope='raw_rough_prefix_shared_cutoff_ceil_sqrt_2X',
                all_integer_blocks=True, whole_signed_bound_proved=False)
    meter.charge(10+len(entries)*8)
    if not entries:
        return dict(base, status='zero_prime_polynomial', lead_degree=None,
                    sign=0, coefficient_floor='0', remainder_ceiling='0',
                    q_threshold='1/2', coefficient_ceiling='0', r=None,
                    energy_upper_exponent='-1', energy_lower_exponent=None,
                    upper_constant=str(J**2), upper_log_power=0,
                    refutes_separate_subpower_payment=False)
    degree = entries[0][0]
    leading = poly.nth(degree)
    low, high = affine_interval(leading)
    sign = 1 if low > 0 else -1 if high < 0 else 0
    A = min(abs(low), abs(high)) if sign else S.Integer(0)
    C = sum(abs_ceiling(poly.nth(d)) for d, _, _ in entries[1:])
    D = abs_ceiling(leading)+C
    q0 = min(S.Rational(1, 2), A/(2*C)) if C and sign else S.Rational(1, 2)
    exponent = S.Rational(degree, 6)
    if exponent < 1:
        upper_power = 1-2*exponent
        upper_constant = (J+2*D/(1-exponent))**2
        upper_log = 0
    elif exponent == 1:
        upper_power, upper_log = -1, 2
        upper_constant = (J+2*D)**2
    else:
        upper_power, upper_log = -1, 0
        upper_constant = (J+D*(1+1/(exponent-1)))**2
    lower_power = 1-2*exponent if sign and exponent < 1 else None
    return dict(base,
        status='two_sided_power_bound' if lower_power is not None else
            ('unresolved_leading_coefficient' if not sign else 'upper_bound_only'),
        lead_degree=degree, sign=sign, coefficient_floor=str(A),
        remainder_ceiling=str(C), q_threshold=str(q0), coefficient_ceiling=str(D),
        r=str(exponent), energy_upper_exponent=str(upper_power),
        energy_lower_exponent=None if lower_power is None else str(lower_power),
        upper_constant=str(upper_constant), upper_log_power=upper_log,
        refutes_separate_subpower_payment=bool(lower_power is not None and lower_power > 0))


def discover(source, spec=None):
    """Induce a rational row module under prime-power coefficient sections."""
    meter = Budget(spec)
    local, weights = compile_source(source)
    n = len(local)
    jets = [coefficients(f, max(meter.spec['valuations'])) for f in local]
    rows = [S.ones(1, n)]
    programs = [dict(op='source')]
    trace = []
    parent = 0
    stop = None
    while parent < len(rows):
        for valuation in meter.spec['valuations']:
            values = [S.Poly(S.expand(rows[parent][j]*jets[j][valuation]), Q)
                      for j in range(n)]
            degrees = sorted({d for p in values for (d,), c in p.terms()
                              if c and d <= meter.spec['max_degree']})
            for degree in degrees:
                meter.charge(n**3+10)
                candidate = S.Matrix([[p.nth(degree) for p in values]])
                first = next((v for v in candidate if v), None)
                if first is None:
                    continue
                scale = 1/first
                candidate *= scale
                independent = S.Matrix.vstack(*rows, candidate).rank() > len(rows)
                if independent:
                    if len(rows) >= meter.spec['max_states']:
                        stop = 'state_cap'
                        break
                    rows.append(candidate)
                    programs.append(dict(op='jet', parent=parent, valuation=valuation,
                                         degree=degree, scale=str(scale)))
                trace.append(dict(parent=parent, valuation=valuation, degree=degree,
                                  new_state=len(rows)-1 if independent else None))
            if stop:
                break
        if stop:
            break
        parent += 1
    B = S.Matrix.vstack(*rows)
    pivots = B.rref()[1]
    minor = B[:, list(pivots)]
    product = B*S.diag(*local)
    transfer = (product[:, list(pivots)]*minor.inv()).applyfunc(S.cancel)
    closed = all(S.cancel(x) == 0 for x in transfer*B-product)
    meter.charge(n*n*len(rows)*25)
    states = [dict(row=list(map(str, row)), program=program)
              for row, program in zip(rows, programs)]
    result = dict(status='universal_law_proposed' if closed else 'unclosed_prime_module',
                  states=states, trace=trace, limits=meter.spec, stop=stop,
                  operations=meter.operations, whole_signed_bound_proved=False,
                  RH_proved=False)
    if closed:
        unit = [dict(constant=str(S.expand(v).coeff(R, 0)),
                     R=str(S.expand(v).coeff(R, 1))) for v in B*S.Matrix(weights)]
        bounds = [frontier_bound(i, row, local, weights, meter)
                  for i, row in enumerate(rows)]
        certificate = dict(source=source, states=states, basis=encode_matrix(B),
            transfer=[[encode_function(v) for v in row] for row in transfer.tolist()],
            unit=unit, target_row=['1']+['0']*(len(rows)-1),
            domain=dict(prime=True, cofactor_coprime=True, all_valuations=True),
            frontier_bounds=bounds)
        result['certificate'] = certificate
        result['operations'] = meter.operations
    return result


def search_joined_forms(frontier):
    """Try actual joined-storage candidates against the discovered obstruction.

    No numerical matrix fit is used. A Schur complement prices the raw rough
    state inside every positive definite candidate. A surviving singular form
    must instead be a multiple of the original target energy. Neither case is
    allowed to masquerade as a paid auxiliary endpoint.
    """
    if (frontier['energy_lower_exponent'] is None or
            rat(frontier['energy_lower_exponent']) <= 0):
        return dict(status='no_positive_rough_obstruction', rows=[],
                    whole_signed_bound_proved=False)
    diagonal = ['1/2', '1', '2', '3', '4']
    cross = ['-4', '-3', '-2', '-1', '-1/2', '0', '1/2', '1', '2', '3', '4']
    rows = []
    for a0 in diagonal:
        for c0 in diagonal:
            for b0 in cross:
                a, b, c = map(rat, (a0, b0, c0))
                row = dict(diagonal_left=a0, cross=b0, diagonal_right=c0,
                           schur_complement=None, endpoint_multiple=None)
                if a < 1 or c < 1 or (a-1)*(c-1) < (b-1)**2:
                    row['classification'] = 'target_not_dominated'
                else:
                    schur = a-b*b/c
                    row['schur_complement'] = str(schur)
                    if schur > 0:
                        row['classification'] = 'refuted_by_rough_lower_bound'
                    else:
                        if not (schur == 0 and a == b == c and a >= 1):
                            raise ArithmeticError('singular target-domination invariant')
                        row['classification'] = 'endpoint_restatement'
                        row['endpoint_multiple'] = str(a)
                rows.append(row)
    return dict(status='instantaneous_joined_storage_grammar_exhausted',
        dictionary=dict(diagonal=diagonal, cross=cross), rows=rows,
        scope='constant quadratic form in the two same-cutoff raw prefixes A,B',
        source_lower_state=frontier['state'],
        source_lower_exponent=frontier['energy_lower_exponent'],
        counts={label: sum(row['classification'] == label for row in rows)
                for label in ('target_not_dominated', 'refuted_by_rough_lower_bound',
                              'endpoint_restatement')},
        proof_rule='Q-J PSD; Schur(Q) A^2 <= (A,B)Q(A,B)^t; singular survivor=kJ',
        broader_multiscale_grammar_refuted=False, operations=30*len(rows),
        whole_signed_bound_proved=False, RH_proved=False)


def feedback(search, verification, joined=None):
    """Make a failed auxiliary estimate an input to the next construction search."""
    if not verification['verified']:
        raise ValueError('verified source laws and frontier certificates required')
    root = search['certificate']['frontier_bounds'][0]
    forced = root['refutes_separate_subpower_payment']
    result = dict(schema='prime-cofactor-bound-feedback-v1',
        source='original_complete_core_f',
        authoritative_parent='candidate10_moment_region_obligation.json',
        direct_source_route=True, current_Z033_isolated=False,
        target=dict(expression='X^-2 sum_(X<=n<2X) F(n)^2',
                    F='sum_(1<=k<=n) f(k)',
                    required='for every epsilon>0, <=C_epsilon X^epsilon, all integers X>=1',
                    constants='C_epsilon independent of X and all auxiliary cutoffs'),
        decomposition=dict(cutoff='y_X=ceil(sqrt(2X))',
            rough='A_X(n)=f(1)+sum_(y_X<p<=n, p prime) f(p)',
            complement='B_X(n)=sum_(k<=n, k>1, least_prime_factor(k)<=y_X) f(k)',
            identity='F(n)=A_X(n)+B_X(n)',
            energy='E_F=E_A+E_B+2 C_AB',
            covariance='C_AB=X^-2 sum_(X<=n<2X) A_X(n) B_X(n)',
            unit_allocation='A only', all_powers_and_crosses=True),
        obstruction=dict(rule='prime_polynomial_binomial_count',
            proof_state=0, proved=forced,
            lower_exponent=root['energy_lower_exponent'], lower_log_power=-2,
            refuted_rule='pay every raw rough state by a uniform subpower energy bound',
            scope='this auxiliary only; no lower bound on full F'),
        next_construction=dict(kind='coupled_prime_cutoff_prefix_storage',
            state_programs=search['states'],
            recurrence='H(x;y_prev)=H(x;p)+sum_(e>=1)T_e(p)H(x/p^e;p)',
            exact_domain='p next prime; every valuation, both increasing cutoff and decreasing x',
            must_retain=['prime and composite cross term', 'moving prefix boundaries',
                         'unit', 'parameter and metric conversion', 'complete valuation tail'],
            admissible_outputs=['new auxiliary plus independently priced endpoint',
                                'joint signed covariance inequality with a proof',
                                'recurrence with a decreasing proved potential'],
            insufficient_outputs=['source energy as its own potential',
                                  'subtract prime profile and leave its complement unpriced',
                                  'finite fitted exponent', 'separate false rough-state payment']),
        dependency_graph=[dict(id='full_prefix_energy', requires=['joined_storage']),
                          dict(id='joined_storage', status='OPEN',
                               disallowed_cycle=['full_prefix_energy'])],
        whole_signed_bound_proved=False, RH_proved=False)
    if joined is not None:
        result['joined_form_search'] = dict(status=joined['status'],
            counts=joined.get('counts', {}),
            implication='need additional scale/cutoff states or a new arithmetic inequality',
            full_multiscale_search_refuted=False)
    return result
