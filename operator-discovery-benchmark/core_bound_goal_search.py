"""Search auxiliary identities and backwards estimates for an open bound.

The supplied language contains finite convolution algebra, moment annihilation,
hyperbola errors and complete kernel remainders.  It supplies no remainder
estimate to the search.  Conditional estimates never enter the theorem set.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb, gcd, lcm
from functools import reduce

import bound_split_search as SPLIT


DEFAULT_SPEC = dict(linear_coefficient_radius=2, maximum_residual_degree=32,
                    diagnostic_denominator_max=12, energy_power='0')
SYMBOLS = ['A', 'B', 'K', 'E', 'S', 'C', 'O', 'R_u']


def trim(a):
    a = list(map(Q, a))
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a or [Q(0)]


def add(a, b):
    return trim([(a[i] if i < len(a) else 0)+(b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])


def scale(a, c):
    return trim([Q(c)*v for v in a])


def mul(a, b):
    c = [Q(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return trim(c)


def value(a, x):
    return sum((c*x**i for i, c in enumerate(a)), Q(0))


def divide(a, b):
    a, b = trim(a), trim(b)
    if b == [0]:
        raise ValueError('nonzero polynomial denominator')
    quotient = [Q(0)]*max(1, len(a)-len(b)+1)
    while a != [0] and len(a) >= len(b):
        degree, c = len(a)-len(b), a[-1]/b[-1]
        quotient[degree] += c
        a = add(a, [Q(0)]*degree+scale(b, -c))
    if a != [0]:
        raise ValueError('exact polynomial division required')
    return trim(quotient)


def nonnegative(a, lo, hi):
    a = trim(a)
    if len(a) > 3:
        raise ValueError('licensed sign checker is at most quadratic')
    points = [lo, hi]
    if len(a) == 3 and a[2] > 0:
        stationary = -a[1]/(2*a[2])
        if lo < stationary < hi:
            points.append(stationary)
    return all(value(a, x) >= 0 for x in points)


def strings(a):
    return list(map(str, trim(a)))


def error_family(theta, rule):
    theta = Q(theta)
    if not 0 < theta < 1:
        raise ValueError('0<theta<1')
    if rule == 'ordinary':
        lines = [([0], [1]), ([theta], [-theta, 1])]
    elif rule == 'euler_remainder':
        lines = [([theta-1], [2-theta]), ([theta], [-theta, 1]), ([0, 1], [0])]
    else:
        raise ValueError('supplied analytic error rule')
    return [(trim(a), trim(b)) for a, b in lines]


def synthesize_family(theta, rule, meter):
    """Find a symbolic minimax certificate valid throughout 0<=rho<theta."""
    theta = Q(theta)
    lines = error_family(theta, rule)
    found = []
    for i, j in combinations(range(len(lines)), 2):
        meter.charge(300)
        for rising, falling in ((i, j), (j, i)):
            ai, bi = lines[rising]
            aj, bj = lines[falling]
            den = add(bi, scale(bj, -1))
            tn = add(aj, scale(ai, -1))
            rn = add(mul(ai, den), mul(bi, tn))
            gaps = [add(rn, scale(add(mul(a, den), mul(b, tn)), -1)) for a, b in lines]
            if (not all(value(den, x) > 0 for x in (Q(0), theta)) or
                    not all(nonnegative(p, Q(0), theta) for p in
                            [bi, scale(bj, -1), tn, add(den, scale(tn, -1))]+gaps)):
                continue
            # C exponent is (1-r)/(1-rho); cancellation must be exact.
            an = divide(add(den, scale(rn, -1)), [1, -1])
            found.append(dict(active_pair=[rising, falling], denominator=strings(den),
                parameter_numerator=strings(tn), power_numerator=strings(rn),
                C_power_numerator=strings(an), gap_polynomials=list(map(strings, gaps)),
                dual_weight_numerators=[strings(scale(bj, -1)), strings(bi)]))
    if not found:
        raise ValueError('no certified symbolic minimax family in the supplied error language')
    result = found[0]
    result.update(rule=rule, theta=str(theta), rho_domain=dict(lower='0', upper=str(theta), upper_excluded=True),
        lines=[dict(intercept=strings(a), slope=strings(b)) for a, b in lines],
        moment='complete ordinarily convergent conditional moment; rho<theta',
        scale='T0=C^(1/(1-rho)); R=n/T0; D=ceil(T0*R^t) when n>=T0',
        all_small_prefixes_included=True,
        retained_euler_compensation=(dict(coefficient='c_theta', expression='h',
            bound='|c_theta|<=1/theta', separately_bounded=True) if rule == 'euler_remainder' else None))
    return result


def primitive_integer(values):
    values = list(map(Q, values))
    den = lcm(*(q.denominator for q in values))
    nums = [int(q*den) for q in values]
    divisor = reduce(gcd, (abs(n) for n in nums), 0) or 1
    return [n//divisor for n in nums]


def admission(family, alpha, p, energy_power):
    """Clear a positive denominator; derive the required (b,rho) half-plane."""
    den = list(map(Q, family['denominator']))
    rn = list(map(Q, family['power_numerator']))
    an = list(map(Q, family['C_power_numerator']))
    if len(an) != 1:
        raise ValueError('this backward compiler requires constant C numerator')
    s, alpha = (Q(energy_power)+1)/2, Q(alpha)
    b_coefficient = alpha*an[0]
    residual = add(add(rn, scale([p, -p], b_coefficient)), scale(den, -s))
    if len(residual) > 2:
        raise ValueError('affine backward region')
    coefficients = primitive_integer([b_coefficient, residual[1] if len(residual) > 1 else 0, -residual[0]])
    return dict(b_coefficient=str(coefficients[0]), rho_coefficient=str(coefficients[1]),
        rhs=str(coefficients[2]), relation='<', b_lower='0', rho_domain=family['rho_domain'],
        target_energy_power=energy_power, critical_prefix_power=str(s),
        bound_schema='exists fixed C,k: |P_(E^m)(t)|<=C U^b t^rho (1+log(2Ut))^k; all U,t>=1',
        finite_factor_U_cost=f'{p}*(1-rho)',
        equality_scope='fixed polylogarithmic energy only; no constant payment at equality')


def substituted_region(region, j):
    a, b, c = (Q(region[k]) for k in ('b_coefficient', 'rho_coefficient', 'rhs'))
    slope, rhs = b-a*j, c-a*j
    upper = Q(region['rho_domain']['upper'])
    endpoints = [Q(0), upper]
    # Strict inequality on the half-open domain; an open upper endpoint
    # cannot be the sole successful point for an affine strict inequality.
    feasible = any(slope*x < rhs for x in endpoints)
    return dict(j=j, substitution=dict(b_constant=str(j), b_rho_coefficient=str(-j)),
        kappa_coefficient=str(slope), rhs=str(rhs), relation='<',
        kappa_domain=region['rho_domain'], has_strictly_feasible_exponent=feasible,
        threshold=str(rhs/slope) if slope else None,
        status='conditional; the complete remainder estimate has not been proved')


def family_point(family, rho, meter):
    rho = Q(rho)
    theta = Q(family['theta'])
    if not 0 <= rho < theta:
        raise ValueError('ordinary moment convergence needs rho<theta')
    lines = error_family(theta, family['rule'])
    problem = dict(lower='0', upper='1', terms=[dict(intercept=str(value(a, rho)), slope=str(value(b, rho))) for a, b in lines])
    certificate = SPLIT.solve(problem, meter)
    denominator = value(list(map(Q, family['denominator'])), rho)
    if (Q(certificate['power']) != value(list(map(Q, family['power_numerator'])), rho)/denominator or
            Q(certificate['parameter']) != value(list(map(Q, family['parameter_numerator'])), rho)/denominator):
        raise ArithmeticError('symbolic family and generic rational minimax disagree')
    return dict(rho=str(rho), split=certificate,
        C_power=str((1-Q(certificate['power']))/(1-rho)))


def linear_factor_search(basis, moments, tail, radius, meter):
    """Bounded coefficient search; neither a named factor nor its vector is supplied."""
    if not 1 <= len(basis) <= 5 or len(moments) != len(basis) or len(tail) != len(basis):
        raise ValueError('finite linear basis and exact coefficient/moment maps')
    rows = []
    atoms = sorted({a for moment in moments for a in moment})
    for vector in product(range(-radius, radius+1), repeat=len(basis)):
        meter.charge(5*len(basis))
        if reduce(gcd, (abs(x) for x in vector), 0) != 1:
            continue
        moment = {a: sum(Q(c)*Q(m.get(a, '0')) for c, m in zip(vector, moments)) for a in atoms}
        rows.append(dict(coefficients=list(vector), harmonic_moment={a: str(c) for a, c in moment.items() if c},
            zero_moment=all(not c for c in moment.values()), exact_tail_match=list(vector) == tail))
    matches = [i for i, r in enumerate(rows) if r['zero_moment'] and r['exact_tail_match']]
    return dict(basis=basis, harmonic_moment_map=moments, required_convolution_tail=tail,
        coefficient_radius=radius, candidates=rows, selected=matches[0] if matches else None,
        selection='first exact tail match with identically zero harmonic moment')


def extract_tail(expression, outer, basis):
    """Factor a shared convolution symbol out of a supplied affine expression."""
    anchor, tail = Q(0), [Q(0)]*len(basis)
    for term in expression:
        factors, coefficient = list(term['factors']), Q(term['coefficient'])
        if not factors:
            anchor += coefficient
            continue
        if factors.count(outer) != 1:
            raise ValueError('one shared outer factor in every nonconstant term')
        factors.remove(outer)
        if len(factors) > 1 or (factors and factors[0] not in basis):
            raise ValueError('affine finite tail in the declared basis')
        tail[basis.index(factors[0] if factors else 'delta')] += coefficient
    if any(q.denominator != 1 for q in tail):
        raise ValueError('this finite factor grammar searches integer coefficients')
    return str(anchor), [int(q) for q in tail]


def complete_source(parent, meter):
    source = parent['selected_source_representation']
    polynomial = {}
    origins = []
    for case in source['cases']:
        mode = case['mode']
        if mode['positive_shift'] not in (None, '1/3'):
            raise ValueError('actual common kernel theta=2/3 source')
        for term in case['program']['terms']:
            a, b, c = term['a'], term['b'], Q(term['coefficient'])
            keys = []
            for m in range(a+1):
                powers = (mode['p'], mode['q'], int(mode['positive_shift'] is not None), m, b, a-m, a-m,
                          int(mode['coefficient'] == '-R_u'))
                scalar = {'beta': Q(9, 2), '-beta': Q(-9, 2), '-R_u': Q(-1)}[mode['coefficient']]
                coefficient = scalar*c*comb(a, m)*(-1)**(a-m)
                polynomial[powers] = polynomial.get(powers, Q(0))+coefficient
                keys.append(dict(powers=list(powers), coefficient=str(coefficient)))
                meter.charge(30)
            origins.append(dict(mode=mode['name'], a=a, b=b, terms=keys))
    return dict(symbols=SYMBOLS, substitution='R=E-C*O; C=c*delta; c=sum_(d<=U)mu(d)/d',
        collected_terms=[dict(powers=list(k), coefficient=str(v)) for k, v in sorted(polynomial.items()) if v],
        source_expansions=origins, transport_error=dict(coefficient='-1', definition='e=f-g'),
        all_compensations_retained=True,
        common_horizon='N=4X-1; every source prefix n<=N; U=floor(N^alpha), V=floor(N^gamma)',
        scope='exact alternative source representation; nonzero formal terms need not be arithmetically independent')


def moment_cancellation(j, meter):
    # The supplied jet-product rule propagates vanishing order, rather than
    # assuming the desired main-term polynomial coefficients or its estimate.
    trace, order = [], 0
    for _ in range(j):
        trace.append(dict(left_order=order, right_order=1, product_order=order+1))
        order += 1
    expansion = []
    for degree in range(j):
        terms = [dict(log_n_power=degree-k, moment_degree=k,
                      coefficient=str((-1)**k*comb(degree, k))) for k in range(degree+1)]
        expansion.append(dict(main_log_degree=degree, terms=terms, identically_zero=True))
        meter.charge(20*(degree+1))
    return dict(j=j, finite_factor='T^j', moment_point='1', T_zero_moment=True,
        valuation_trace=trace, zero_moment_degrees=list(range(j)), main_term_expansions=expansion,
        polynomial='arbitrary fixed polynomial in log(x) of degree at most j-1',
        full_support_sum=True, include_d_greater_than_n=True,
        remainder_definition='Delta_j(x)=D_j(x)-x*P_(j-1)(log(x)); EVERY real x>0',
        D_definition='D_j(x)=sum_(n<=x) (One^j)(n); zero for 0<x<1',
        bounded_polynomial=['1'] if j == 1 else None,
        identity_proved=True, remainder_bound_proved=(j == 1))


def residual_bound(m):
    if m == 1:
        return dict(rho='0', U_power='1', constant='2', combined_log_degree=0)
    return dict(rho=str(Q(m-1, m)), U_power='1', constant=str(2*(2*m+1)*3**(m-1)),
                combined_log_degree=2*m-3)


def target_for_term(term, alpha, spec, families, meter):
    p, _, _, m, *_ = term['powers']
    known = residual_bound(m)
    theta, rho = Q(2, 3), Q(known['rho'])
    routes = []
    for family in families:
        region = admission(family, alpha, p, spec['energy_power'])
        if rho >= theta:
            current = dict(status='unlicensed', reason='rho>=theta: complete ordinary moment not established by this bound')
        else:
            point = family_point(family, rho, meter)
            e = Q(point['split']['power'])+Q(alpha)*Q(point['C_power'])*(1+p*(1-rho))
            current = dict(status='proved exponent with fixed polylogarithmic losses', **point,
                prefix_N_power=str(e), energy_N_power=str(2*e-1),
                strictly_meets_target=2*e-1 < Q(spec['energy_power']))
        j_regions = [substituted_region(region, j) for j in range(2, m+1)]
        head_point = family_point(family, '0', meter)
        heads = []
        for j in (0, 1):
            e = Q(head_point['split']['power'])+Q(alpha)*Q(head_point['C_power'])*(j+p)
            heads.append(dict(j=j, b=str(j), **head_point,
                prefix_N_power=str(e), energy_N_power=str(2*e-1),
                strictly_meets_target=2*e-1 < Q(spec['energy_power'])))
        routes.append(dict(rule=family['rule'], family_reference=family['rule'],
            current_generic_bound=current, missing_prefix_bound_region=region,
            proved_head_branches=heads,
            remainder_branch_regions=j_regions,
            all_remainder_branches_feasible=all(r['has_strictly_feasible_exponent'] for r in j_regions),
            conditional_auxiliary_route_has_feasible_exponents=(all(h['strictly_meets_target'] for h in heads)
                and all(r['has_strictly_feasible_exponent'] for r in j_regions))))
    identity = [dict(j=j, coefficient=str(comb(m, j)), kernel='One^j', finite_factor='T^j') for j in range(m+1)]
    branches = []
    for j in range(m+1):
        branches.append(dict(j=j, coefficient=str(comb(m, j)),
            prefix_rule=('delta' if j == 0 else 'complete_floor_remainder' if j == 1 else 'complete_kernel_remainder'),
            status='proved' if j < 2 else 'open',
            rho='0' if j < 2 else 'kappa_j',
            U_power='0' if j == 0 else '1' if j == 1 else f'{j}*(1-kappa_j)',
            constant='1' if j == 0 else '3' if j == 1 else f'C_j*(2+1/(1-kappa_j))^{j}',
            mass_bound=dict(constant=str(3**j), U_log_degree=j, t_log_degree=max(0, j-1), t_power='1'),
            uniform_quantifiers='fixed finite constants and log degrees; EVERY U,t>=1',
            complete_remainder_for_all_positive_arguments=True))
    return dict(id=f'centered_A{p}_E{m}', source_term=term, p=p, m=m,
        target='P_(K*A^p*E^m - m_theta(A^p*E^m)*J_theta/theta)',
        theta='2/3', original_moment_drift_retained=True,
        moment_drift_status='conditional on ordinary convergence; never discarded',
        generic_prefix_rule=known, routes=routes,
        auxiliary_identity=dict(anchor='delta', base='E=delta+One*T', terms=identity,
            all_j_including_zero_retained=True, identity_proved=True),
        remainder_branches=branches,
        status='open', component_bound_proved=False, complete_source_bound_proved=False)


def proof_graph(targets):
    nodes = [dict(id='finite_moment_factor', status='proved', depends_on=[]),
             dict(id='generic_multiple_prefix_rule', status='proved', depends_on=[])]
    for target in targets:
        ident = target['id']
        for branch in target['remainder_branches']:
            j = branch['j']
            nodes.append(dict(id=f'{ident}_remainder_{j}', status=branch['status'],
                depends_on=['finite_moment_factor'],
                expression=f'complete D_{j} remainder bound' if j > 1 else branch['prefix_rule']))
        nodes.append(dict(id=ident, status='open', depends_on=[f'{ident}_remainder_{j}' for j in range(target['m']+1)],
            dependency_semantics='necessary proof obligations in this branch; exponent/cost gates must also pass'))
    nodes.append(dict(id='complete_signed_complement', status='open', depends_on=[],
        expression='every remaining source term, every centering drift and the exact transport error; retain their signed correlations'))
    nodes.append(dict(id='actual_signed_core', status='open', depends_on=[t['id'] for t in targets]+['complete_signed_complement'],
        other_obligations='all untouched terms, compensating drifts, joint correlations and exact transport error remain'))
    nodes.append(dict(id='original_RH_recovery', status='conditional', depends_on=['actual_signed_core']))
    return nodes


def next_tasks(targets):
    tasks = [dict(target_id='actual_signed_core', search_kind='joint_signed_core_control',
        status='open', priority=0, preserve='complete signed join, inherited recovery and all compensation/error terms')]
    for target in targets:
        feasible = [r['rule'] for r in target['routes'] if r['conditional_auxiliary_route_has_feasible_exponents']]
        tasks.append(dict(target_id=target['id'], status='open', priority=1,
            search_kind='search_complete_remainder_bounds' if feasible else 'search_joint_weighted_remainder_control',
            conditionally_admissible_routes=feasible,
            reason=('some separate remainder exponents satisfy the derived cost gates; their proofs remain open' if feasible else
                    'no separate remainder-bound portfolio in this declared family pays all branches at the current cutoff'),
            preserve='the entire signed auxiliary identity, finite T^j weights, unit, all quotients and full centering moment',
            prohibits='do not infer arithmetic impossibility or close an estimate from its requested exponent'))
    return tasks


def search(parent, spec, meter):
    if (set(spec) != set(DEFAULT_SPEC) or type(spec['linear_coefficient_radius']) is not int or
            not 1 <= spec['linear_coefficient_radius'] <= 4 or
            type(spec['maximum_residual_degree']) is not int or not 2 <= spec['maximum_residual_degree'] <= 64 or
            type(spec['diagnostic_denominator_max']) is not int or not 2 <= spec['diagnostic_denominator_max'] <= 24):
        raise ValueError('bounded declared argument grammar')
    SPLIT.rational(spec['energy_power'])
    if parent['whole_signed_bound_proved'] is not False or parent['RH_proved'] is not False:
        raise ValueError('open actual source required')
    row = parent['selected_source_representation']
    join = complete_source(parent, meter)
    max_degree = max(t['powers'][3] for t in join['collected_terms'])
    if max_degree > spec['maximum_residual_degree']:
        raise ValueError('complete source exceeds declared degree budget; never truncate')
    expression = [dict(coefficient='1', factors=[]), dict(coefficient='-1', factors=['O', 'A']),
                  dict(coefficient='1', factors=['O', 'C'])]
    basis = ['A', 'C', 'delta']
    anchor, tail = extract_tail(expression, 'O', basis)
    if anchor != '1':
        raise ValueError('the actual centered residual has unit anchor')
    factor = linear_factor_search(basis, [{'c': '1'}, {'c': '1'}, {'one': '1'}],
                                 tail, spec['linear_coefficient_radius'], meter)
    factor.update(supplied_residual_expression=expression, extracted_anchor=anchor, outer_factor='O')
    if factor['selected'] is None:
        raise ValueError('no zero-moment factor found for the supplied source')
    families = [synthesize_family('2/3', name, meter) for name in ('ordinary', 'euler_remainder')]
    eligible = [t for t in join['collected_terms'] if t['powers'][2] == 1 and t['powers'][3] >= 2
                and all(t['powers'][i] == 0 for i in (1, 4, 5, 6, 7))]
    targets = [target_for_term(t, row['alpha'], spec, families, meter) for t in eligible]
    rationals = sorted({Q(n, d) for d in range(1, spec['diagnostic_denominator_max']+1)
                        for n in range(d+1) if Q(n, d) < Q(2, 3)})
    diagnostics = [dict(rule=f['rule'], points=[family_point(f, rho, meter) for rho in rationals]) for f in families]
    paid = sum(any(r['current_generic_bound'].get('strictly_meets_target', False) for r in t['routes']) for t in targets)
    # This pilot compiles open obligations.  If a changed grammar actually pays
    # one, its complete constants and recovery must be published by a new stage.
    if paid:
        raise ValueError('new payable component requires a complete payment/recovery implementation')
    tasks = next_tasks(targets)
    return dict(schema='core-bound-goal-search-v1', spec=spec,
        inherited_selected_source=row, inherited_bound_obligations=parent['generated_bound_obligations'],
        inherited_proof_frontier=parent['proof_frontier'], complete_signed_join=join,
        factor_search=factor, symbolic_bound_families=families, diagnostic_minimax=diagnostics,
        moment_cancellation_certificates=[moment_cancellation(j, meter) for j in range(1, max_degree+1)],
        generated_bound_targets=targets, proof_dependencies=proof_graph(targets), next_search_tasks=tasks,
        statistics=dict(original_source_terms=row['component_count'], collected_signed_terms=len(join['collected_terms']),
            linear_candidates=len(factor['candidates']), zero_moment_candidates=sum(r['zero_moment'] for r in factor['candidates']),
            source_matched_factors=1, generated_bound_targets=len(targets),
            kernel_remainder_branches=sum(t['m']-1 for t in targets),
            targets_redirected_to_joint_control=sum(t['search_kind'] == 'search_joint_weighted_remainder_control' for t in tasks),
            symbolic_bound_families=len(families), independent_rational_split_probes=len(rationals)*len(families),
            inherited_bindings=len(parent['generated_bound_obligations']), new_component_bounds_proved=0),
        actual_source_observations=0, model_calls_in_search=0,
        detector_has_general_analytic_prover=False, whole_signed_bound_proved=False, RH_proved=False)


def feedback(result, input_file, artifact):
    return dict(schema='core-bound-goal-feedback-v1', status='open', parent_obligation_file=input_file,
        complete_search_artifact=artifact, selected_source_representation=result['inherited_selected_source'],
        generated_bound_obligations=result['inherited_bound_obligations'],
        auxiliary_bound_targets=result['generated_bound_targets'], proof_dependencies=result['proof_dependencies'],
        next_search_tasks=result['next_search_tasks'],
        retained_original_proof_frontier=result['inherited_proof_frontier'],
        next_priority='search the open arithmetic remainder estimates AND the complete signed join; keep full recovery costs',
        all_remainder_estimates_are_conditional=True, new_component_bounds_proved=0,
        scope='checked auxiliary identities and backwards requirements; no new full signed control',
        whole_signed_bound_proved=False, RH_proved=False)
