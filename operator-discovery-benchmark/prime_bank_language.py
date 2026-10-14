"""Exact branch-bound and support language for a complete prime-bank target.

The arithmetic inequalities are reviewed analytic lemmas, explicitly identified
below. This module verifies their rational exponent consequences and finite
algebra; it is not a formal proof assistant for the analytic premises.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import lcm

REVIEW = 'PRIME_BANK_COVARIANCE_REVIEW_001.txt'
SCOPE = dict(source='actual_mu_candidate10', domain='all dyadic integers X>=1',
             quantifiers='for every epsilon>0, exists C_epsilon independent of X')
BRANCHES = (('L0', '0', '18'), ('Lu', '1/3', '9'), ('Lv', '2/3', '9'))
SOURCE_OPERATOR = dict(type='product_of_normalized_shift_increments', shifts=['1/3','2/3'],
    formula='((zeta(s+1/3)/zeta(s)-1)/(1/3))*((zeta(s+2/3)/zeta(s)-1)/(2/3))')
SOURCE_DEFINITIONS = dict(a='p-d', a_b='mu * (n^(-b)), Dirichlet convolution', beta='9/2',
    p='((a_(1/3)-delta)/(1/3))*((a_(2/3)-delta)/(2/3))',
    z_0='2*p(k)+beta*(a_(1/3)(k)+a_(2/3)(k))',
    z_u='p(k)+beta*a_(2/3)(k)', z_v='p(k)+beta*a_(1/3)(k)',
    K='sum_{2<=n<=x, largest_prime_factor(n)<=Y} a(n)',
    L_b='sum_{2<=k<=M} z_b(k)*Pi_b(x,k)', Pi_b='sum_{Y<q<=x/k, q prime} q^(-b)')


def charge(meter, n=1):
    if meter is not None: meter.charge(n)


def rational(text):
    if type(text) is not str or len(text) > 64:
        raise ValueError('canonical rational text')
    value = Q(text)
    if str(value) != text: raise ValueError('canonical rational text')
    return value


def bank_bound(b_text, theta_text, coefficient_text, meter=None):
    """Derive growth for ANY b in [0,1), theta in [1/2,1).

    Premise: |z(k)|<=C d_2(k), k>=2. Complete banks exclude k=1.
    For b>0 the reviewed Chebyshev/divisor argument removes the log loss.
    For b=0, Pi_0<=x/k and sum_(k<=M)d_2(k)/k
    <=(sum_(r<=M)1/r)^2<=(1+log x)^2 prove the unweighted rule directly.
    """
    b, theta, C = map(rational, (b_text, theta_text, coefficient_text))
    if not (0 <= b < 1 and Q(1, 2) <= theta < 1 and C > 0):
        raise ValueError('supported prime-bank inequality domain')
    charge(meter, 20)
    alpha = 1 - b * theta; power = 2 * alpha - 1
    log_degree = 2 if b == 0 else 0
    if b:
        constant = dict(rational_factor=str(C * (1-theta) / (b*(1-b)*theta)),
                        factors=['C_psi', '(1+1/log(2))'])
        proof = 'Chebyshev_weighted_prime_sum_and_divisor_prefix'
    else:
        constant = dict(rational_factor=str(C), factors=[])
        proof = 'integer_majorant_and_two_harmonic_sums'
    regime = ('finite_critical_integral' if power < 0 else
              'bounded_block_energy' if power == 0 and log_degree == 0 else
              'polylog_block_energy' if power == 0 else 'positive_power_remaining')
    return dict(schema='prime-bank-exponent-certificate-v1', b=b_text, theta=theta_text,
                coefficient=coefficient_text, pointwise_power=str(alpha),
                pointwise_log_degree=log_degree, energy_power=str(power),
                energy_log_degree=2*log_degree, constant=constant,
                pointwise_template='A*x^alpha*(1+log(x))^log_degree',
                block_constant='A^2*2^(2*alpha)*(1+log(2))^(2*log_degree)',
                critical_integral_factor=str(1/(-power)) if power < 0 and not log_degree else None,
                regime=regime, cofinal_padding=power <= 0,
                premises=['complete bank, k>=2, strict q>x^theta',
                          '|z(k)|<=C*d_2(k) for all k>=2',
                          'psi(t)<=C_psi*t for all t>=1'] if b else
                         ['complete bank, k>=2, strict q>x^theta', '|z(k)|<=C*d_2(k) for all k>=2'],
                analytic_rule=proof, analytic_provenance=REVIEW,
                verification_scope='exact consequences of reviewed analytic premises',
                complete_target_proved=False, RH_proved=False)


def verify_bound(certificate, meter=None):
    if type(certificate) is not dict: raise ValueError('bound certificate object')
    expected = bank_bound(certificate.get('b'), certificate.get('theta'),
                          certificate.get('coefficient'), meter)
    if expected != certificate: raise ValueError('altered exponent/constant/scope certificate')
    return True


def smooth_prefix_bound(eta_text, theta_text, coefficient_text, meter=None):
    """Derive a paid low-index sector from a generic complete divisor envelope."""
    eta,theta,C=map(rational,(eta_text,theta_text,coefficient_text))
    if not (0<eta<=theta<1 and theta>=Q(1,2) and C>0):
        raise ValueError('low coefficient prefix must lie inside the smooth sector')
    power=2*eta-1;charge(meter,20)
    factor=None
    if power<0:
        gap=-power;factor=str(1/gap+2*eta/gap**2+2*eta**2/gap**3)
    return dict(eta=eta_text,theta=theta_text,coefficient=coefficient_text,
                expression='sum_{2<=h<=x^eta} a(h)',
                pointwise_bound='C*x^eta*(1+eta*log(x))',energy_power=str(power),
                energy_log_degree=2,cofinal_padding=power<=0,critical_integral_factor=factor,
                support_reason='Pplus(h)<=h<=x^eta<=x^theta',
                premises=['|a(h)|<=C*d_2(h) for every h>=2'],
                analytic_provenance=REVIEW,complete_target_proved=False)


def weighted_moment_bank_bound(b_text, theta_text, moment_power_text, meter=None):
    """Transfer a proved NO-LOG absolute cofactor moment to a complete bank.

    The supplied premise is sum_(2<=k<=M)|f(k)|k^(b-1)<=B*M^gamma.
    The result remains conditional until a reviewed source derivation supplies
    that premise. In particular this does not assume a signed RH-strength sum.
    """
    b,theta,gamma=map(rational,(b_text,theta_text,moment_power_text))
    if not (0<b<1 and Q(1,2)<=theta<1 and gamma>=0):
        raise ValueError('positive weighted bank and nonnegative moment power')
    alpha=1-b+(1-theta)*gamma;power=2*alpha-1;charge(meter,24)
    return dict(b=b_text,theta=theta_text,moment_power=moment_power_text,
                premise='sum_(2<=k<=M)|f(k)|*k^(b-1)<=B*M^gamma for all M>=1',
                pointwise_power=str(alpha),pointwise_log_degree=-1,energy_power=str(power),
                constant=dict(rational_factor=str(1/(theta*(1-b))),factors=['B','C_psi']),
                nonempty_domain='x>2^(1/(1-theta)); bank zero otherwise',
                cofinal_padding=power<=0,finite_critical_integral=power<=0,
                endpoint_critical_integral='A^2*(1-theta)/log(2)' if power==0 else None,
                analytic_provenance=REVIEW,conditional_on_cofactor_moment=True,
                complete_target_proved=False)


def difference_cofactor_moment(u_text,v_text,b_text,beta_text,meter=None):
    """Positive g=n^-u-n^-v supplies the moment without a cancellation premise."""
    u,v,b,beta=map(rational,(u_text,v_text,b_text,beta_text))
    if not (0<u<v and 0<b<1 and beta>0):raise ValueError('positive ordered shifts')
    charge(meter,20)
    return dict(u=u_text,v=v_text,b=b_text,beta=beta_text,
                source='Delta=-beta*(mu*g), g(n)=n^(-u)-n^(-v)>=0, g(1)=0',
                moment_power=b_text,
                B=dict(rational_factor=str(beta/b),factors=['G']),
                G='zeta(1+u)-zeta(1+v)=sum_(d>=1)g(d)/d>0',
                proof='|mu|<=1; sum_(r<=M/d)r^(b-1)<=(M/d)^b/b; positive g, absolute convergent G',
                finite_harmonic_bound='abs(sum_(2<=k<=M)Delta(k)/k)<=2*beta*G',
                analytic_provenance=REVIEW,full_signed_source_bound_assumed=False)


def normalize_polynomial(rows, meter=None):
    """Formal cofactor-valued polynomial: rows=(rational exponent, atom, coeff)."""
    out = {}
    for exponent, atom, coefficient in rows:
        e = rational(exponent); c = rational(coefficient)
        if e < 0 or e.denominator > 12 or type(atom) is not str or not atom:
            raise ValueError('bounded nonnegative rational power and atom')
        key = (e, atom); out[key] = out.get(key, Q(0)) + c; charge(meter, 2)
    return [[str(e), atom, str(c)] for (e, atom), c in sorted(out.items()) if c]


def factor_unit_difference(rows, meter=None):
    """Find all common factors (1-t), after generic rational-power lifting.

    This searches algebraically for a factor, without a selected numerical
    coefficient or an assumption that factorization improves a signed bound.
    """
    normalized = normalize_polynomial(rows, meter)
    if not normalized: raise ValueError('nonzero source polynomial required')
    denominator = lcm(*(Q(r[0]).denominator for r in normalized))
    data = {}
    for e, atom, c in normalized: data.setdefault(atom, {})[int(Q(e)*denominator)] = Q(c)
    degree = max(max(p) for p in data.values())
    if degree > 128: raise ValueError('bounded polynomial degree')
    multiplicity = 0
    while degree > 0 and all(sum(p.values(), Q(0)) == 0 for p in data.values()):
        next_data = {}
        for atom, p in data.items():
            running = Q(0); quotient = {}
            for j in range(degree):
                running += p.get(j, Q(0)); charge(meter, 2)
                if running: quotient[j] = running
            next_data[atom] = quotient
        data = next_data; degree -= 1; multiplicity += 1
    quotient = normalize_polynomial([[str(Q(e, denominator)), atom, str(c)]
                                    for atom, p in data.items() for e, c in p.items()], meter)
    rebuilt = quotient
    for _ in range(multiplicity):
        rebuilt = normalize_polynomial(rebuilt + [[str(Q(e)+Q(1, denominator)), atom, str(-Q(c))]
                                                   for e, atom, c in rebuilt], meter)
    if rebuilt != normalized: raise ArithmeticError('exact polynomial recomposition')
    return dict(source=normalized, step=str(Q(1, denominator)), multiplicity=multiplicity,
                quotient=quotient, factor='1-q^(-step)', identity_verified=True,
                uniform_improvement_proved=False)


def cutoff_change(retained, meter=None):
    """Exact change as Y1 increases to Y2, preserving ALL entering terms."""
    rows = {'K': (-1, 1, 1), '-L0': (1, 0, 0), 'Lu': (0, -1, 0),
            'Lv': (0, 0, -1), '-main': (0, 0, 0)}
    if len(set(retained)) != len(retained) or any(s not in rows for s in retained):
        raise ValueError('distinct complete state atoms')
    charge(meter, 3 * len(retained))
    return [str(sum(rows[s][i] for s in retained)) for i in range(3)]


def catalogue(obligation, theta_menu, meter=None):
    if (obligation.get('id') != 'candidate10_complete_prime_bank_covariance' or
        obligation.get('schema') != 'candidate10-prime-bank-obligation-v1' or
        obligation.get('scope') != SCOPE or obligation.get('status') != 'open' or
        obligation.get('operator') != SOURCE_OPERATOR or
        obligation.get('exact_reduction', {}).get('identity') != 'R=R_new+L_v'):
        raise ValueError('complete, scope-bound unresolved source obligation')
    if any(obligation.get('definitions',{}).get(k)!=v for k,v in SOURCE_DEFINITIONS.items()):
        raise ValueError('source coefficients and complete partition must match the arithmetic backend')
    if len(set(theta_menu)) != len(theta_menu): raise ValueError('distinct cutoff menu')
    programs = []
    for theta in theta_menu:
        bounds = {name: bank_bound(b, theta, C, meter) for name, b, C in BRANCHES}
        eliminations = []
        for size in range(1, len(BRANCHES)+1):
            for subset in combinations(bounds, size):
                charge(meter, size)
                paid = all(bounds[name]['cofinal_padding'] for name in subset)
                eliminations.append(dict(branches=list(subset),
                    energy_power=max((bounds[name]['energy_power'] for name in subset), key=Q),
                    cofinal_padding=paid, proof='complete triangle inequality using every listed branch',
                    target_discharged=False))
        paid = [name for name, _, _ in BRANCHES if bounds[name]['cofinal_padding']]
        retained = [s for s in ('K','-L0','Lu','Lv','-main') if s.lstrip('-') not in paid]
        programs.append(dict(theta=theta, source_obligation_id=obligation['id'], scope=dict(SCOPE),
                             bounds=bounds, elimination_search=eliminations,
                             smooth_prefix_search=[smooth_prefix_bound(eta,theta,'9',meter)
                                for eta in ('1/6','1/3','1/2','2/3') if Q(eta)<=Q(theta)],
                             difference_channel_bounds=[dict(
                                cofactor_derivation=difference_cofactor_moment('1/3','2/3',b,'9/2',meter),
                                bank_transfer=weighted_moment_bank_bound(b,theta,b,meter))
                                for b in ('1/3','2/3')],
                             paid_branches=paid, remaining_atoms=retained,
                             cutoff_transport_coefficients=cutoff_change(retained, meter),
                             complete_uniform_bound_proved=False, RH_proved=False))
    return dict(schema='complete-prime-bank-language-v1', source_obligation=obligation,
                source_factorization=factor_unit_difference([
                    ['0','zu','-1'], ['0','zv','-1'], ['1/3','zu','1'], ['2/3','zv','1']], meter),
                source_relation='z0=zu+zv; exact substitution in p,a_u,a_v',
                complete_cutoff_transport=cutoff_change(['K','-L0','Lu','Lv','-main'],meter),
                programs=programs, target_equivalence_class=obligation['id'],
                finite_evidence_cannot_discharge_uniform_premises=True)


def select_regimes(language, meter=None):
    """Choose critical and first strict improvement from symbolic bounds only."""
    out = []
    for strict in (False, True):
        choices = []
        for program in language['programs']:
            charge(meter)
            paid = program['paid_branches']
            if not paid: continue
            power = max(Q(program['bounds'][name]['energy_power']) for name in paid)
            if ((power < 0) if strict else (power == 0)): choices.append(program['theta'])
        if choices: out.append(min(choices, key=Q))
    if len(out) != 2: raise ValueError('menu must contain critical and strictly decaying paid regimes')
    return out


def entry_time(prime, theta_text, meter=None):
    """First integer n with prime<=n^theta, including exact equality."""
    theta = rational(theta_text)
    if type(prime) is not int or prime < 2 or not Q(1,2) <= theta < 1:
        raise ValueError('positive prime-sized integer and valid theta')
    target = prime ** theta.denominator; lo, hi = 1, prime * prime
    charge(meter, theta.denominator+1)
    while lo < hi:
        mid = (lo+hi)//2; charge(meter, theta.numerator+3)
        if mid ** theta.numerator >= target: hi = mid
        else: lo = mid+1
    return lo


def overlap_kernel(X, h, largest_h, q, k, theta_text, meter=None):
    """Count smooth/bank support intersection; inputs require Pplus(h)=largest_h.

    This is a finite integer kernel, not a bound on its signed coefficient sum.
    The empty same-prime diagonal follows from the two opposed entry times.
    """
    if any(type(n) is not int or n < 1 for n in (X,h,largest_h,q,k)) or k < 2:
        raise ValueError('integer support data, k>=2')
    begin = max(X,h,entry_time(largest_h,theta_text,meter),q*k)
    end = min(2*X,entry_time(q,theta_text,meter))
    charge(meter, 6)
    return max(0,end-begin)
