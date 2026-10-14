"""Independent exact cutoff-work certificate audit.

The compiler's reduced polynomial ring is not used here.  Three ordinary
polynomial specializations and interpolation determine every increment and
Hermitian energy sector.  No numerical source archive or producer is imported.
"""
from fractions import Fraction as Q
from math import comb, factorial

from check_core_split_bound_search import _require, _same, _rational
from check_core_bound_goal_search import _source
from check_core_moment_bound_search import _audit_graph


_REAL = {'c', 'a', 'v', 'x'}
_COMPLEX = {'A', 'E', 'D', 'z', 'b'}
_SYMBOLS = _REAL | _COMPLEX | {s+'bar' for s in _COMPLEX}
_SCALARS = ['-2', '-1', '-1/2', '1/2', '1', '2']


def _integer(value, lower, upper):
    _require(type(value) is int and lower <= value <= upper, 'bounded exact integer')
    return value


def _decode(rows, meter, allow_x=True):
    _require(type(rows) is list and len(rows) <= 200000, 'bounded canonical sparse polynomial')
    out = {}; previous = None
    for row in rows:
        _require(type(row) is dict and set(row) == {'monomial', 'coefficient'}, 'complete polynomial term')
        names = row['monomial']
        _require(type(names) is list and len(names) <= 256 and
                 all(type(s) is str and s in _SYMBOLS for s in names) and names == sorted(names),
                 'sorted declared polynomial symbols')
        key = tuple(names)
        _require(previous is None or previous < key, 'strictly ordered unique polynomial monomials')
        _require((allow_x or 'x' not in key) and key.count('x') <= 2, 'canonical ternary or sector polynomial')
        coefficient = _rational(row['coefficient'], meter)
        _require(coefficient != 0, 'zero terms must be omitted')
        out[key] = coefficient; previous = key; meter.charge(10+len(key))
    meter.live(20*len(out))
    return out


def _encode(polynomial):
    return [dict(monomial=list(k), coefficient=str(v)) for k, v in sorted(polynomial.items()) if v]


def _add(*polynomials):
    out = {}
    for polynomial in polynomials:
        for k, v in polynomial.items():
            out[k] = out.get(k, Q(0))+v
    return {k: v for k, v in out.items() if v}


def _scale(polynomial, scalar):
    return {k: v*scalar for k, v in polynomial.items() if v*scalar}


def _atom(name):
    return {(name,): Q(1)}


def _product(left, right, meter):
    out = {}
    for k, a in left.items():
        for l, b in right.items():
            key = tuple(sorted(k+l)); out[key] = out.get(key, Q(0))+a*b
            meter.charge(20+len(key))
    _require(len(out) <= 200000, 'bounded independent polynomial expansion')
    meter.live(20*len(out))
    return {k: v for k, v in out.items() if v}


def _power(polynomial, exponent, meter):
    _integer(exponent, 0, 64)
    out = {(): Q(1)}; base = polynomial
    while exponent:
        if exponent & 1: out = _product(out, base, meter)
        exponent //= 2
        if exponent: base = _product(base, base, meter)
    return out


def _conjugate(polynomial):
    def star(s):
        if s in _REAL: return s
        if s in _COMPLEX: return s+'bar'
        _require(s.endswith('bar') and s[:-3] in _COMPLEX, 'declared complex conjugate')
        return s[:-3]
    return {tuple(sorted(star(s) for s in k)): v for k, v in polynomial.items()}


def _interpolate(zero, positive, negative):
    return [zero, _scale(_add(positive, _scale(negative, -1)), Q(1, 2)),
            _add(_scale(_add(positive, negative), Q(1, 2)), _scale(zero, -1))]


def transition(p, m, subtract_head, meter):
    """Construct through ordinary specialization, not x^3=x reduction."""
    _integer(p, 0, 16); _integer(m, 2, 32)
    _require(type(subtract_head) is bool, 'exact head representation switch')
    A, E, c, D, z, a, b, v = map(_atom, ['A', 'E', 'c', 'D', 'z', 'a', 'b', 'v'])
    old = _product(_power(A, p, meter), _power(E, m, meter), meter)
    if subtract_head: old = _add(old, _scale(_product(_power(c, m, meter), D, meter), -1))
    old_energy = _product(old, _conjugate(old), meter)
    changes = {}; energies = {}
    for sign in (0, 1, -1):
        new_A = _add(A, _scale(b, sign))
        new_E = _add(E, _scale(_product(z, _add(a, _scale(b, -1)), meter), sign))
        child = _product(_power(new_A, p, meter), _power(new_E, m, meter), meter)
        if subtract_head:
            child = _add(child, _scale(_product(_power(_add(c, _scale(a, sign)), m, meter),
                                                    _add(D, _product(v, b, meter)), meter), -1))
        changes[sign] = _add(child, _scale(old, -1))
        energies[sign] = _add(_product(child, _conjugate(child), meter), _scale(old_energy, -1))
    increments = _interpolate(changes[0], changes[1], changes[-1])
    works = _interpolate(energies[0], energies[1], energies[-1])
    child = dict(old)
    for i, polynomial in enumerate(increments):
        child = _add(child, {tuple(sorted(k+('x',)*i)): value for k, value in polynomial.items()})
    return dict(parent=_encode(old), child=_encode(child), increment_sectors=[_encode(x) for x in increments],
        work_sectors=[_encode(x) for x in works], mu_powers=[0, 1, 2],
        weight='abs(zeta(s+1-theta)/s)^2', q_domain='every integer q>=2; U=q-1',
        substitutions=dict(A='A+x*b', E='E+x*z*(a-b)', c='c+x*a', D='D+v*b'),
        symbols=dict(x='mu(q)', a='1/q', b='q^(-s)', z='zeta(s)',
            D='complete finite head polynomial through q-1', v='exact head atom coefficient at q'),
        pole_removal_preserved='E=1+z*(c-A), with coupled c and A changes',
        all_conjugates_crosses_and_zero_mu_branch_retained=True,
        residue_update='evaluate the COMPLETE polynomial increment at s=theta; retain its opposite J_theta/theta drift',
        ordinary_moment_convergence_inferred=False)


def verify_transition(p, m, subtract_head, result, meter):
    for key in ('parent', 'child'): _decode(result[key], meter)
    for key in ('increment_sectors', 'work_sectors'):
        _require(type(result[key]) is list and len(result[key]) == 3, 'all zero, odd, even sectors')
        for rows in result[key]: _decode(rows, meter, False)
    expected = transition(p, m, subtract_head, meter)
    _require(_same(result, expected), 'three-point interpolation gives complete increment and Hermitian energy')
    return dict(verified=True)


def absorption(power, log_degree, goal):
    _integer(log_degree, 0, 128)
    gap = goal-power
    if gap < 0 or (gap == 0 and log_degree):
        return dict(proved=False, multiplier=None, gap=str(gap))
    # y^k <= k! gap^-k exp(gap*y), (1+y)^k <= 2^k(1+y^k).
    cost = Q(1) if log_degree == 0 else 2**log_degree*(1+Q(factorial(log_degree))/gap**log_degree)
    return dict(proved=True, multiplier=str(cost), gap=str(gap))


def head_bound(p, m, theta, sigma, alpha, goal):
    _integer(p, 0, 16); _integer(m, 2, 32)
    _require(0 < sigma < theta < 1 and 0 < alpha < 1 and goal > 0, 'finite head Mellin and cutoff premises')
    order = abs(m-p); log_degree = 2*max(0, order-1)
    # Split the complete centered kernel at x=1 before Plancherel; both
    # terms are mandatory. Apply weighted finite-shift Minkowski afterwards.
    norm = (1/sigma+1/(theta-sigma))/(2*theta**2)
    up = Q(0) if order == 0 else 2-2*sigma
    constant = norm*4**m if order == 0 else norm*4**m/(1-sigma)**2
    return dict(atom='One' if m >= p else 'mu', convolution_power=order, c_power=m,
        cutoff='all n<=U, including unit', centered_prefix_constant=str(2**m/theta),
        centered_prefix_U_power='0' if order == 0 else '1', centered_prefix_log_degree=max(0, order-1),
        kernel_global_norm_constant=str(norm), global_squared_norm_constant=str(constant),
        global_U_power=str(up), global_log_degree=log_degree, target_absorption=absorption(up, log_degree, goal),
        physical_energy_X_power=str(Q(-1) if order == 0 else 2*alpha-1),
        fixed_log_degree_paid_by_negative_X_power=(order == 0 or 2*alpha-1 < 0),
        complete_finite_residue='c^m*sum_(n<=U)head_atom(n)*n^(-theta)',
        centered_head='K*head-(M_head/theta)*J_theta', opposite_drift_retained=True,
        full_unit_and_x_below_one_retained=True)


def head_trials(p, m, meter):
    """Compare horizon convolution normal forms derived from the rules.

    Put One=z and mu=z^-1. The supplied inverse rule and E=c*One
    on n<=U give the source normal form c^m*z^(m-p). Enumeration
    discovers its atom; the inverse rule itself is supplied, not discovered.
    """
    _integer(p, 0, 16); _integer(m, 2, 32)
    trials = []; matches = []
    for c_order in range(p+m+1):
        for order in range(p+m+1):
            for family in (['One'] if order == 0 else ['One', 'mu']):
                for scalar in _SCALARS:
                    laurent_order = order if family == 'One' else -order
                    matched = c_order == m and laurent_order == m-p and Q(scalar) == 1
                    trials.append(dict(c_power=c_order, atom=family, convolution_power=order,
                                       multiplier=scalar, matches_source_head=matched))
                    if matched: matches.append(len(trials)-1)
                    meter.charge(25)
    return dict(trials=trials, matched_indices=matches,
        normal_form=[dict(c_power=m, One_power=m-p, coefficient='1')],
        zero_power_atom_deduplicated=True, identity_scope='coefficients n<=U only; no global equality',
        matching_rule='expand supplied source AST in mu*One=delta quotient, then compare candidate normal forms')


def _selected_plan(target, alpha, meter):
    """Fast replay of the inherited chosen theorem, not an old grid search."""
    p = _integer(target['p'], 0, 16); m = _integer(target['m'], 2, 32)
    theta = _rational(target['theta'], meter)
    _require(theta == Q(2, 3), 'actual source K has shift 1/3')
    lines = target['lines']; _require(type(lines) is list, 'retained inherited contour candidates')
    feasible = [i for i, line in enumerate(lines) if line['selected_plan'] is not None]
    def rank(i):
        line = lines[i]; plan = line['plans'][line['selected_plan']]
        return (-_rational(plan['required_low_U_power'], meter), _rational(plan['tau'], meter), i)
    selected = min(feasible, key=rank) if feasible else None
    _require(_same(selected, target['selected_line']), 'inherited selected contour remains attached to retained candidates')
    if selected is None:
        _require(target['low_obligation'] is None, 'no detached low-Gram obligation')
        return None
    line = lines[selected]; sigma = _rational(line['sigma'], meter)
    _require(0 < sigma < min(Q(1, 2), theta), 'strict belowhalf contour')
    _integer(line['selected_plan'], 0, len(line['plans'])-1)
    plan = line['plans'][line['selected_plan']]
    kappa = _rational(plan['kappa'], meter); epsilon = _rational(plan['epsilon'], meter)
    fraction = _rational(plan['epsilon_fraction'], meter); tau = _rational(plan['tau'], meter)
    _require(0 < kappa < Q(1, 4) and 0 < fraction < 1 and tau > 0, 'strict twisted length and common height')
    branches = []
    for j in range(m+1):
        height = theta-sigma-1
        if j: height += j*(1-2*sigma)
        if j >= 2: height += (j-2)*sigma
        r = p+j
        branches.append(dict(j=j, r=r, support_U_power=r,
            coefficient_envelope=dict(multiplier=str(3**j), divisor_order=r, constant_polynomial=r == 0),
            height_power=str(height), weight_U_power=str(r*(1-2*sigma))))
        meter.charge(100)
    _require(_same(line['branches'], branches), 'all j0/j1/higher reflection and weight branches')
    saving = min(-Q(b['height_power']) for b in branches)
    _require(saving > 0 and epsilon == fraction*saving, 'strict fixed epsilon consumes only a fraction of saving')
    requirements = [(kappa, Q(b['r'])) for b in branches]
    requirements += [(-Q(b['height_power'])-epsilon, Q(b['weight_U_power'])) for b in branches]
    _require(all(a > 0 for a, _ in requirements), 'strict Mellin tail on every branch')
    _require(tau == max(b/a for a, b in requirements), 'minimal common tau satisfies every length and exponent requirement')
    replay = []
    for b in branches:
        tail = Q(b['height_power'])+epsilon
        replay.append(dict(j=b['j'], length_slack=str(tau*kappa-b['r']), tail_height_power=str(tail),
                           tail_U_power=str(Q(b['weight_U_power'])+tau*tail)))
    high = max(Q(b['tail_U_power']) for b in replay)
    generic_low = 2*(p+m)*(1-sigma); integer_error = 2*(p+m)*(1-theta)
    expected = dict(kappa=str(kappa), epsilon_fraction=str(fraction), epsilon=str(epsilon), tau=str(tau), branches=replay,
        within_tau_cap=True, high_U_power=str(high), high_energy_X_power=str(2*sigma-1),
        required_low_U_power=str((1-2*sigma)/alpha), generic_low_U_power=str(generic_low),
        generic_low_energy_X_power=str(2*sigma-1+alpha*generic_low), integer_error_U_power=str(integer_error),
        integer_error_X_power=str(-1+alpha*integer_error), high_auxiliary_proved=True,
        generic_complete_component_proved=(2*sigma-1+alpha*generic_low <= 0 and -1+alpha*integer_error <= 0),
        low_obligation_status='proved_by_generic_fallback' if 2*sigma-1+alpha*generic_low <= 0 else 'open_actual_Mobius_bound')
    _require(_same(plan, expected), 'selected high theorem, low cost and integer correction remain independently consistent')
    low = dict(kind='complete_zeta_weighted_low_Mellin_Gram',
        parameters=dict(p=p, m=m, theta=str(theta), sigma=str(sigma), alpha=str(alpha)),
        source_weights=dict(A='mu(n)*1_(n<=U)', c='sum_(n<=U)mu(n)/n', T='c*delta-A', E='delta+One*T', B_j='A^p*T^j'),
        height=dict(prefactor='2', U_power=str(tau), interval='abs(t)<H'), measure='dt/(2*pi)',
        kernel='abs(zeta(s+1-theta)/s)^2*zeta(s)^j*conj(zeta(s)^k)', finite_polynomial_product='B_j(s)*conj(B_k(s))',
        matrix_entries=[dict(j=j, k=k, contraction=str(comb(m, j)*comb(m, k))) for j in range(m+1) for k in range(m+1)],
        integer_pairs='all ordered d,e, with actual signed B_j(d)*B_k(e)', unweighted_Gaussian_substitution_allowed=False,
        diagonal_only_allowed=False, required_upper=dict(constant='C_low', U_power=expected['required_low_U_power'], log_degree=0,
            quantifier='every integer U>=1, one fixed finite C_low independent of U,X,N'), status=expected['low_obligation_status'],
        generic_fallback_U_power=str(generic_low), complete_cross_terms_retained=True)
    _require(_same(target['low_obligation'], low), 'complete inherited low head, all signed crosses and uniform scope')
    return theta, sigma, plan


def _parent(parent, meter):
    _require(type(parent) is dict and parent.get('schema') == 'core-weighted-height-feedback-v1' and
        parent.get('status') == 'open' and parent.get('whole_signed_bound_proved') is False and parent.get('RH_proved') is False,
        'complete open inherited weighted-height publication')
    join = _source(parent, meter); reduction = parent['complete_source_reduction']
    _require(_same(reduction['inherited_complete_signed_join'], join) and
        _same(reduction['bindings'], parent['generated_bound_obligations']), 'independent inverse, signed source and binding replay')
    _require(reduction['transport_error_retained'] == '-e' and reduction['whole_join_cross_terms_retained'] is True and
        reduction['common_horizon'] == 'N=4X-1 for BOTH blocks; same coefficients and cutoffs',
        'transport, complete signed cross terms and common horizon retained')
    bindings = parent['generated_bound_obligations']
    _require(type(bindings) is list and len(bindings) == 144 and
        len({b['parent_obligation_id'] for b in bindings}) == 144, 'all 144 unique inherited original recoveries')
    for binding in bindings:
        _require(binding.get('whole_signed_bound_proved') is False and binding.get('RH_proved') is False, 'original recovery stays open')
        node = binding; seen = set()
        while 'transport_program' not in node:
            _require(id(node) not in seen and type(node.get('inherited_binding')) is dict, 'acyclic retained transport ancestry')
            seen.add(id(node)); node = node['inherited_binding']; meter.charge(30)
        _require(type(node['transport_program']) is dict and bool(node['transport_program']), 'full original transport program')
    terms = [t for t in join['collected_terms'] if t['powers'][2] == 1 and t['powers'][3] >= 2 and
        all(t['powers'][i] == 0 for i in (1, 4, 5, 6, 7))]
    old = parent['auxiliary_bound_targets']; targets = parent['weighted_height_targets']
    _require(type(old) is list and type(targets) is list and len(old) == len(targets) == len(terms), 'every inherited pure-E target retained')
    alpha = _rational(parent['selected_source_representation']['alpha'], meter)
    eligible = []
    for prior, target, term in zip(old, targets, terms):
        p, m = term['powers'][0], term['powers'][3]; ident = 'centered_A'+str(p)+'_E'+str(m)
        _require(target['p'] == p and target['m'] == m and target['target_id'] == ident and
            _same(target['source_term'], term) and _same(prior['source_term'], term) and
            prior['p'] == p and prior['m'] == m and prior['target_id'] == ident and prior['theta'] == '2/3' and
            type(prior['component_bound_proved']) is bool and target['inherited_component_bound_proved'] is prior['component_bound_proved'],
            'actual target source coefficient, kernel and inherited payment membership')
        head = dict(domain='every integer 1<=n<=U', expression='(A^p*E^m)(n)', scalar='c^m',
            coefficient=dict(atom='One' if m >= p else 'mu', convolution_power=abs(m-p)), zero_power='delta',
            derivation='mu*One=delta on n<=U and E(n)=c', supplies_full_Gram_bound=False)
        _require(_same(target['source_head_identity'], head), 'supplied finite-horizon head identity has its exact scope')
        centering = dict(kind='analytic_residue', M='A(theta)^p*E(theta)^m',
            centered_coefficient='K*A^p*E^m-(M/theta)*J_theta', retained_opposite_drift='source_coefficient*(M/theta)*J_theta',
            ordinary_moment_established_by_inherited_prefix_rule=Q(m-1, m) < Q(2, 3), ordinary_prefix_power=str(Q(m-1, m)),
            ordinary_convergence_required_for_this_route=False, unit_J_theta_1='1',
            continuous_small_x_tail='-(M/theta)*x^theta on 0<x<1', pole_at_1_removed_in_complete_E=True)
        _require(_same(target['centering'], centering) and target['new_source_payment'] is False,
            'analytic residue, small-x tail, unit and opposite drift retained without ordinary convergence inference')
        selected = _selected_plan(target, alpha, meter)
        if selected is not None and target['low_obligation']['status'] == 'open_actual_Mobius_bound':
            eligible.append((target, selected))
    paid = [t for t in old if t['component_bound_proved']]
    expected_paid = [dict(target_id=t['target_id'], source_term=t['source_term'],
        centered_component='source_coefficient*(K*A^p*E^m - M/theta*J_theta)',
        retained_opposite_drift='source_coefficient*M/theta*J_theta', ordinary_moment_proved=True) for t in paid]
    _require(_same(reduction['new_paid_components'], expected_paid), 'inherited payment flags and their complete compensation agree')
    _audit_graph(parent['proof_dependencies'], meter)
    nodes = {n['id']: n for n in parent['proof_dependencies']}
    _require('actual_signed_core' in nodes and nodes['actual_signed_core']['status'] == 'open' and
        'complete_signed_complement' in nodes and nodes['complete_signed_complement']['status'] == 'open',
        'explicit full signed complement and core remain open')
    return alpha, eligible


def _envelope(pair):
    return dict(U_power=str(pair[0]), log_degree=str(pair[1]))


def _sum_envelope(pair):
    power, logs = pair
    _require(logs >= 0, 'nonnegative envelope logarithm')
    # The harmonic endpoint is a logarithm, even for a power-only input.
    if power == -1: return Q(0), logs+1
    if power < -1: return Q(0), Q(0)
    return power+1, logs


def _meets(pair, goal):
    return pair[0] < goal or (pair[0] == goal and pair[1] == 0)


def finite_shift_control(terms, degree, theta, sigma, meter):
    _integer(degree, 0, 64)
    _require(0 < sigma < theta < 1, 'complete centered finite-shift kernel contour')
    polynomial = _decode(terms, meter, False)
    if any(any(s not in {'a', 'b', 'c', 'v'} for s in key) for key in polynomial):
        return dict(available=False, reason='not a certified finite-shift polynomial')
    contributions = []
    for key, coefficient in polynomial.items():
        if degree == 0 and 'v' in key: continue
        # Each b supplies a full kernel dilation q^-sigma. Each real a is
        # q^-1; the complete divisor bound pays v, not a guessed sign.
        power = -key.count('a')-sigma*key.count('b')+max(0, degree-1)*key.count('v')
        contributions.append(dict(root_U_power=str(power), coefficient_upper=str(abs(coefficient)*2**key.count('c'))))
        meter.charge(40+10*len(key))
    if not contributions:
        return dict(available=True, identically_zero=True, terms=[], squared_norm_constant='0',
            squared_norm_envelope=_envelope((Q(0), Q(0))), root_U_power='0', target_assumed_in_proof=False)
    norm = (1/sigma+1/(theta-sigma))/(2*theta**2)
    constant = sum(Q(row['coefficient_upper']) for row in contributions)
    power = max(Q(row['root_U_power']) for row in contributions)
    return dict(available=True, identically_zero=False, terms=contributions,
        squared_norm_constant=str(norm*constant**2), squared_norm_envelope=_envelope((2*power, Q(0))),
        root_U_power=str(power), target_assumed_in_proof=False,
        rule='finite shifted complete centered power kernels and Minkowski', norm_domain='entire real height line, hence every old window',
        v_bound='v=0 for degree 0, otherwise abs(v)<=q^(degree-1)',
        work_control='W0_integral<=2*sqrt(D)*q^a*sqrt(L_old)+D*q^(2*a)',
        absolute_work_control=True, retained_zero_mu_branch=True)


def _bound_search(program, certificate, theta, sigma, goal, generic_power, meter):
    _require(goal > 0 and generic_power >= 0, 'positive goal and supplied generic norm')
    transition_rows = program['transition']
    zero = finite_shift_control(transition_rows['increment_sectors'][0], certificate['convolution_power'], theta, sigma, meter)
    if certificate['atom'] == 'mu' and transition_rows['increment_sectors'][0]:
        zero = dict(available=False, reason='inverse-divisor v depends on mu(q); repartition before using the zero-sector rule')
    generic = (generic_power, Q(0))
    if program['subtract_exact_head']:
        generic = max(generic, (Q(certificate['global_U_power']), Q(certificate['global_log_degree'])))
    costs = []; accumulated = [(Q(0), Q(0))]
    for part in program['moving_height_shell']['parts']:
        per_step = (_rational(part['U_power'], meter), Q(_integer(part['log_degree'], 0, 128)))
        total = _sum_envelope(per_step); accumulated.append(total)
        costs.append(dict(name=part['name'], per_step=_envelope(per_step), summed=_envelope(total)))
    shell = max(accumulated)
    active = [i for i, polynomial in enumerate(transition_rows['work_sectors']) if polynomial]
    routes = [dict(id=0, method='inherited_norm_envelope', status='proved' if _meets(generic, goal) else 'insufficient_exponent',
        known_envelope=_envelope(generic), required_U_power=str(goal), open_leaves=[],
        relation_to_original_goal='original goal', target_assumed_in_proof=False)]
    cases = [('complete_work', active, None)]
    if zero['available'] and not zero['identically_zero']:
        cases.append(('pay_zero_sector_by_energy_feedback', [s for s in active if s != 0], Q(zero['root_U_power'])))
    for method, sectors, root in cases:
        feedback = (Q(0), Q(0)); nonnegative = shell
        if root is not None:
            summed_root = _sum_envelope((root, Q(0)))
            # Solving the quadratic inequality in sqrt(M) multiplies the
            # summed feedback power and its logarithmic degree by two.
            feedback = (2*summed_root[0], 2*summed_root[1])
            nonnegative = max(nonnegative, _sum_envelope((2*root, Q(0))))
        for mode in ('prefix', 'dyadic_max_partial', 'consecutive'):
            required = goal-1 if mode == 'consecutive' else goal
            arithmetic = _sum_envelope((required, Q(0))) if mode == 'consecutive' else (required, Q(0))
            recovered = max((Q(0), Q(0)), feedback, nonnegative, arithmetic)
            feasible = _meets(recovered, goal)
            known = generic
            if root is not None:
                cross = (generic[0]/2+root, generic[1]/2); square = (2*root, Q(0))
                if mode != 'consecutive': cross, square = _sum_envelope(cross), _sum_envelope(square)
                known = max(known, cross, square)
            supplied = _meets(known, required)
            ident = 'program_'+str(program['id'])+'_route_'+str(len(routes))+'_signed_work'
            expr, domain, upper = {
                'prefix': ('sum_(q=2..V) R_q', 'every integer V>=1; empty prefix is zero', 'C*V^power'),
                'dyadic_max_partial': ('sum_(q=U+1..V) R_q', 'every U=2^k, k>=0, and EVERY integer U<=V<=2*U', 'C*U^power'),
                'consecutive': ('R_q', 'every integer q>=2', 'C*q^power')}[mode]
            relation = ('optional stronger sufficient requirement; not equivalent' if mode == 'consecutive' else
                        'equivalent goal up to paid costs' if feasible else 'unpaid recovery in this rule set')
            forcing = dict(id=ident, status='proved_by_inherited_envelope' if supplied else 'open', expression=expr,
                R_q=dict(integral='dt/(2*pi) over abs(t)<H(q-1)', weight=transition_rows['weight'], sectors=sectors,
                    sector_polynomials=[transition_rows['work_sectors'][i] for i in sectors], term='sum_(i in sectors) mu(q)^i*W_i'),
                upper=upper, power=str(required), quantifier=domain, uniform_constant='one finite C independent of q,U,V,X,N',
                known_envelope=_envelope(known), actual_Mobius_required=True, arbitrary_sign_identity_suffices=False,
                sector_signs_assumed=False, moving_shells_included_separately=True, target_assumed_in_proof=False)
            recurrence = dict(rule='finite_maximum_and_sublinear_Young', energy_root='1/2',
                feedback_envelope=_envelope(feedback), resulting_envelope=_envelope(recovered),
                inequality='M<=D+A*M^r implies M<=2*D+(2*A)^(1/(1-r))',
                D='initial energy + summed nonnegative costs + upper bound for EVERY signed prefix',
                target_assumed_in_proof=False, all_integer_cutoffs=True)
            status = 'unpaid_auxiliary_cost' if not feasible else 'proved' if supplied else 'conditional_open_signed_work'
            routes.append(dict(id=len(routes), method=method, aggregation=mode, status=status,
                required_U_power=str(goal), recurrence=recurrence, shell_costs=costs,
                nonnegative_cost=_envelope(nonnegative), open_leaves=[] if supplied else [ident], forcing=forcing,
                dyadic_to_prefix_constant=str(1+2/goal) if mode == 'dyadic_max_partial' else None,
                endpoint_samples_suffice=False, all_integer_cutoffs=True, relation_to_original_goal=relation,
                target_assumed_in_proof=False)); meter.charge(500)
    eligible = [r for r in routes if r['status'] in ('proved', 'conditional_open_signed_work')]
    chosen = min(eligible, key=lambda row: (row['status'] != 'proved',
        len(row.get('forcing', {}).get('R_q', {}).get('sectors', [])), row.get('aggregation') == 'consecutive', row['id']))['id'] if eligible else None
    next_targets = [routes[chosen]['forcing']] if chosen is not None and routes[chosen]['status'] != 'proved' else []
    return dict(schema='cutoff-bound-composition-v1', goal_U_power=str(goal), supplied_generic_envelope=_envelope(generic),
        zero_sector_control=zero, routes=routes, selected_route=chosen, next_bound_targets=next_targets,
        goal_proved=any(r['status'] == 'proved' for r in routes), model_calls=0, numerical_observations=0,
        selection='proved goal first, fewer unbounded sectors, cumulative before stronger consecutive condition, enumeration order',
        new_arithmetic_estimate_proved=False,
        proof_rule_limit='finite-shift kernels, Cauchy, summation, sublinear maximum, inherited norm envelope',
        automatic_feedback='unresolved selected forcing becomes the next bound target, with its exact signed polynomial')


def verify_bound_search(program, certificate, theta, sigma, goal, generic_power, result, meter):
    expected = _bound_search(program, certificate, theta, sigma, goal, generic_power, meter)
    _require(_same(result, expected), 'complete automatic rule compositions, kernel costs, quantifiers and conditional status')
    return dict(verified=True, goal_proved=expected['goal_proved'], selected_route=expected['selected_route'])


def _target(target, selected, alpha, meter):
    theta, sigma, plan = selected; p, m = target['p'], target['m']
    goal = _rational(plan['required_low_U_power'], meter)
    head = head_bound(p, m, theta, sigma, alpha, goal); trials = head_trials(p, m, meter)
    states = [False, True] if trials['matched_indices'] and head['target_absorption']['proved'] else [False]
    programs = []
    for subtract in states:
        parts = [dict(name='raw_child_high_tail', U_power=plan['high_U_power'], log_degree=0,
            payment=absorption(Q(plan['high_U_power']), 0, goal-1))]
        if subtract:
            parts.append(dict(name='finite_head_full_norm', U_power=head['global_U_power'], log_degree=head['global_log_degree'],
                payment=absorption(Q(head['global_U_power']), head['global_log_degree'], goal-1)))
        paid_shell = all(part['payment']['proved'] for part in parts)
        program = dict(id=len(programs), subtract_exact_head=subtract, support_vanishes_through_U=subtract,
            transition=transition(p, m, subtract, meter),
            centering=dict(kind='analytic_residue', full_unit=True,
                source_identity='K*P_raw-(M_raw/theta)*J_theta = centered_head + centered_tail' if subtract else 'unchanged centered source component',
                all_opposite_drifts_retained=True, source_scalar=target['source_term']['coefficient']),
            low_bound_recovery=dict(kind='two_sided_squared_triangle_with_paid_head' if subtract else 'identity',
                factor='2' if subtract else '1', paid_head_constant=str(2*Q(head['global_squared_norm_constant'])*Q(head['target_absorption']['multiplier'])) if subtract else '0',
                preserved_U_power=str(goal), original_target_strength_preserved=True),
            moving_height_shell=dict(old_height_U_power=plan['tau'], old_height_prefactor='2', child_to_parent_cutoff_ratio_at_most='2',
                kappa=plan['kappa'], extended_kappa=str((Q(plan['kappa'])+Q(1, 4))/2), parts=parts,
                fixed_finite_uniform_constant=True, numerical_constant=None, proved=paid_shell),
            initial_low_norm=dict(U=1, upper='0' if subtract else head['kernel_global_norm_constant'], proved=True),
            missing_work=dict(status='open', expression='integral_(abs(t)<H(q-1)) weight*(W0+mu(q)*W1+mu(q)^2*W2)*dt/(2*pi)',
                q_power=str(goal-1), quantifier='every integer q>=2, one finite C_work independent of q,U,X,N',
                relation_to_endpoint_goal='optional stronger sufficient requirement; not equivalent', head_correction_preserves_this_work_goal=False,
                no_sector_sign_assumed=True, entire_old_height_domain_required=True),
            telescoping=dict(status='conditional_on_signed_work'+('' if paid_shell else '_and_shell'),
                resulting_U_power=str(goal), summation_constant=str(1+1/goal), all_integer_cutoffs=True, dyadic_samples_sufficient=False),
            component_bound_proved=False, new_source_payment=False)
        program['bound_search'] = _bound_search(program, head, theta, sigma, goal, Q(plan['generic_low_U_power']), meter)
        programs.append(program)
    chosen = min(range(len(programs)), key=lambda i: (not programs[i]['support_vanishes_through_U'], i))
    return dict(target_id=target['target_id'], p=p, m=m, theta=str(theta), sigma=str(sigma), source_term=target['source_term'],
        original_low_obligation=target['low_obligation'], head_search=trials, head_bound=head, programs=programs, selected_program=chosen,
        selection='proved support cancellation and paid recovery, then enumeration order; no arithmetic scores')


def _rules():
    return dict(transition_review='CORE_CUTOFF_TRANSITION_RULE_REVIEW_022.txt', scope_review='CORE_CUTOFF_TRANSITION_SCOPE_REVIEW_023.txt',
        ternary_identity='mu(q)^3=mu(q)', arithmetic_head='mu*One=delta for n<=U',
        head_kernel='complete centered power kernel, including x<1 and d>x',
        shell_rule='fixed-factor length extension with kappa_prime=(kappa+1/4)/2 and finite initial range',
        uniform_signed_work_proved=False, formal_proof_assistant_verified=False,
        automatic_control_review='CORE_CUTOFF_AUTOMATIC_CONTROL_REVIEW_024.txt')


def _diagnostic_spec():
    return dict(maximum_cutoff=2048, heights=['0', '1/2', '1', '2', '4', '8', '16'], positive_height_weight='2', zero_height_weight='1',
        continuous_Gram_estimate=False, used_for_selection=False, fitted_constants=0, fresh_arithmetic_holdout=False, executed=False,
        reason='user prioritizes automatic bound search; numerical work deferred before observations')


def verify_search(parent, result, meter):
    alpha, eligible = _parent(parent, meter)
    keys = {'schema', 'supplied_rules', 'targets', 'diagnostic_spec', 'inherited_complete_source_reduction', 'inherited_bindings',
            'inherited_proof_dependencies', 'statistics', 'source_payment_changed', 'model_calls_in_search', 'fitted_constants',
            'whole_signed_bound_proved', 'RH_proved'}
    _require(type(result) is dict and set(result) == keys and result['schema'] == 'core-cutoff-work-search-v1', 'complete cutoff-work artifact')
    _require(_same(result['supplied_rules'], _rules()), 'explicit supplied analytic and arithmetic rules, not discovered identities')
    _require(_same(result['diagnostic_spec'], _diagnostic_spec()), 'deferred diagnostic is never a proof or a selection score')
    _require(type(result['targets']) is list and len(result['targets']) == len(eligible), 'every actual open low-Gram leaf compiled')
    for (old, selected), new in zip(eligible, result['targets']):
        for program in new['programs']:
            tr = program['transition']
            for name in ('parent', 'child'): _decode(tr[name], meter)
            for name in ('increment_sectors', 'work_sectors'):
                _require(type(tr[name]) is list and len(tr[name]) == 3, 'all transition sectors retained')
                for polynomial in tr[name]: _decode(polynomial, meter, False)
        _require(_same(new, _target(old, selected, alpha, meter)),
            'full head language, exact transition, global kernel costs, shell, nonlinear search and unresolved work')
    for key, inherited in [('inherited_complete_source_reduction', 'complete_source_reduction'),
                           ('inherited_bindings', 'generated_bound_obligations'), ('inherited_proof_dependencies', 'proof_dependencies')]:
        _require(_same(result[key], parent[inherited]), 'unchanged signed source, all compensation, original recovery and proof dependencies')
    targets = result['targets']
    stats = dict(targets=len(targets), head_trials=sum(len(t['head_search']['trials']) for t in targets),
        exact_head_matches=sum(len(t['head_search']['matched_indices']) for t in targets),
        transition_programs=sum(len(t['programs']) for t in targets),
        paid_head_auxiliaries=sum(t['head_bound']['target_absorption']['proved'] for t in targets),
        bound_routes=sum(len(p['bound_search']['routes']) for t in targets for p in t['programs']),
        automatically_paid_zero_sectors=sum(p['bound_search']['zero_sector_control']['available'] and
            not p['bound_search']['zero_sector_control']['identically_zero'] for t in targets for p in t['programs']),
        closed_low_goals=sum(p['bound_search']['goal_proved'] for t in targets for p in t['programs']), new_component_bounds_proved=0)
    _require(_same(result['statistics'], stats), 'generated auxiliary counts never count as new source payments')
    _require(all(type(result[k]) is int and result[k] == 0 for k in ('model_calls_in_search', 'fitted_constants')) and
        all(result[k] is False for k in ('source_payment_changed', 'whole_signed_bound_proved', 'RH_proved')),
        'no fitted bound, changed payment or false core closure')
    return dict(verified=True, **stats, whole_signed_bound_proved=False, RH_proved=False)


def verify_feedback(parent, result, next_input, input_file, artifact, meter):
    _require(type(input_file) is str and bool(input_file) and type(artifact) is str and bool(artifact), 'explicit immutable publication references')
    tasks = [dict(target_id='actual_signed_core', priority=0, status='open', search_kind='joint_signed_core_control',
        preserve='complete inherited signed residual, source cross terms, drifts, unit and -e')]
    for target in result['targets']:
        program = target['programs'][target['selected_program']]
        tasks.append(dict(target_id=target['target_id'], priority=1, status='open',
            search_kind='bound_actual_cutoff_work_or_physical_localization', exact_work=program['missing_work'],
            transition=program['transition'], shell=program['moving_height_shell'], paid_head=target['head_bound'],
            automatic_bound_search=program['bound_search'], next_bound_targets=program['bound_search']['next_bound_targets'],
            global_target_strength_unchanged=True))
    expected = dict(schema='core-cutoff-work-feedback-v1', status='open', parent_obligation_file=input_file, complete_search_artifact=artifact,
        selected_source_representation=parent['selected_source_representation'], generated_bound_obligations=parent['generated_bound_obligations'],
        complete_source_reduction=parent['complete_source_reduction'], retained_original_proof_frontier=parent['retained_original_proof_frontier'],
        auxiliary_bound_targets=parent['auxiliary_bound_targets'], weighted_height_targets=parent['weighted_height_targets'],
        cutoff_work_targets=result['targets'], inherited_next_search_tasks=parent['next_search_tasks'], next_search_tasks=tasks,
        inherited_proof_dependencies=parent['proof_dependencies'], new_component_bounds_proved=0, whole_signed_bound_proved=False, RH_proved=False)
    _require(_same(next_input, expected), 'all old tasks, targets, source, drifts and original recovery preserved with exact open next leaves')
    meter.charge(500+100*len(tasks))
    return dict(verified=True, status='open', new_component_bounds_proved=0)
