"""Search source applications and proof routes for a requested energy bound.

The mathematical rules are supplied.  Splits, proof routes, cutoff tests,
complete source decompositions and remaining obligations are generated.
No arithmetic observations, fitted constants or model calls select them.
"""
from fractions import Fraction as Q
from itertools import product
from math import ceil

import bound_split_search as SPLIT
import core_truncated_inverse as INVERSE


DEFAULT_SPEC = dict(root_denominator_min=2, root_denominator_max=24,
                    maximum_inverse_factors=64,
                    target=dict(energy_power='0', log_degree=0))


def ancestors(parent):
    seen = set()
    while isinstance(parent, dict):
        if id(parent) in seen:
            raise ValueError('acyclic inherited obligation')
        seen.add(id(parent))
        yield parent
        parent = parent.get('parent_obligation')


def inherited(parent):
    chain = list(ancestors(parent))
    sources = next(p for p in chain if p.get('schema') == 'source-specific-short-inverse-search-input-v1')
    programs = next(p for p in chain if p.get('schema') == 'detector-bound-program-search-input-v1')
    modes = [c['mode'] for c in sources['source_geometries'][0]['cases']]
    if any([c['mode'] for c in row['cases']] != modes for row in sources['source_geometries']):
        raise ValueError('same complete arithmetic source for every inherited geometry')
    if parent.get('whole_signed_bound_proved') is not False or parent.get('RH_proved') is not False:
        raise ValueError('open signed source required')
    return modes, programs['generated_bound_program_obligations']


def validate_spec(spec):
    if set(spec) != set(DEFAULT_SPEC) or set(spec['target']) != {'energy_power', 'log_degree'}:
        raise ValueError('declared root grammar and target')
    lo, hi = spec['root_denominator_min'], spec['root_denominator_max']
    if (type(lo) is not int or type(hi) is not int or not 2 <= lo <= hi <= 64
            or type(spec['maximum_inverse_factors']) is not int
            or not 4 <= spec['maximum_inverse_factors'] <= 128):
        raise ValueError('bounded fractional root and convolution grammar')
    SPLIT.rational(spec['target']['energy_power'])
    if type(spec['target']['log_degree']) is not int or not 0 <= spec['target']['log_degree'] <= 32:
        raise ValueError('nonnegative bounded target log degree')


def target_payment(energy, target):
    difference = Q(energy['power'])-Q(target['energy_power'])
    logarithms = max(0, energy['log_degree']-target['log_degree'])
    if difference > 0 or (difference == 0 and logarithms):
        return None
    factor = Q(1) if not logarithms else 2**logarithms*(1+(Q(logarithms)/(-difference))**logarithms)
    return str(Q(energy['constant'])*factor)


def weighted_mass(exponent):
    """Universal sum_(d<=V)d^-s bound, retaining the s=1 logarithm."""
    s = Q(exponent)
    if s > 1:
        return dict(constant=str(1+1/(s-1)), cutoff_power='0', log_degree=0)
    if s == 1:
        return dict(constant='1', cutoff_power='0', log_degree=1)
    if s <= 0:
        raise ValueError('this supplied weighted mass rule requires s>0')
    return dict(constant=str(1/(1-s)), cutoff_power=str(1-s), log_degree=0)


def proof_routes(mode, term, alpha, gamma, split, target, meter):
    theta = 1-Q(mode['positive_shift'])
    r = Q(split['power'])
    if split['problem'] != SPLIT.power_kernel_problem(str(theta)) or not 0 < r <= theta < 1:
        raise ValueError('bound the licensed error envelope, including the small-n branch')
    a, b, p, q = Q(alpha), Q(gamma), mode['p'], mode['q']
    T = 6/(theta*(1-theta))
    # Generic centering of the entire h: no multiplication rule for J is used.
    c0, l0 = 2*3**q, 3*Q(5, 2)**q
    direct = dict(rule='center_complete_bounded_prefix_factor',
        prefix_constant=str(T*l0*c0), U_power=str((p+1)*(1-r)),
        V_power=str(Q(q, 3)*(1-r)), log_degree=p+1,
        premises=dict(prefix_constant=str(c0), prefix_U_power=str(p+1),
            prefix_V_power=str(Q(q, 3)), density_constant=str(l0), density_log_degree=p+1),
        full_conditional_moment=True, small_n_case_included=True)
    # Center E first, propagate through finite factors, then PAY the full
    # h0*J - m_theta(h0)*J commutator, including factors beyond the prefix.
    wb = weighted_mass(Q(2, 3)+r)
    commutator = dict(rule='finite_weighted_propagation_with_complete_commutator',
        prefix_constant=str(42/(theta*(1-theta))*(1/(1-r))**p*Q(wb['constant'])**q),
        U_power=str((p+1)*(1-r)), V_power=str(q*Q(wb['cutoff_power'])),
        log_degree=1+q*wb['log_degree'],
        premises=dict(B_weight_exponent=str(Q(2, 3)+r), B_weight_bound=wb,
            E_moment_constant=str(2/(1-theta)+4), E_moment_U_power=str(1-theta),
            commutator_prefix='n^r * sum_all_d |h0(d)|/d^r',
            commutator_all_d_including_d_gt_n=True),
        full_conditional_moment=True, small_n_case_included=True)
    scalar = {'beta': Q(9, 2), '-beta': Q(9, 2), '-R_u': Q(5)}[mode['coefficient']]
    routes = []
    for route in (direct, commutator):
        u, v = Q(route['U_power']), Q(route['V_power'])
        prefix_power = r+u*a+v*b
        energy = dict(constant=str(4*(scalar*Q(term['coefficient'])*Q(route['prefix_constant']))**2),
                      power=str(2*prefix_power-1), log_degree=2*route['log_degree'])
        route.update(local_n_power=str(r), prefix_N_power=str(prefix_power), energy=energy,
            target_constant=target_payment(energy, target),
            cutoff_condition=dict(alpha_upper=str((Q(target['energy_power'])+1-2*r-2*v*b)/(2*u)),
                strict=energy['log_degree'] > target['log_degree'], gamma=str(b),
                scope='sufficient within this proof route; failure is not an arithmetic counterexample'))
        routes.append(route)
        meter.charge(300)
    return routes


def application(mode, term, alpha, gamma, split, target, ident, meter):
    if mode['positive_shift'] is None or term['a'] != 1 or term['b'] != 0:
        raise ValueError('bounded-prefix match requires one R and no additional residual factor')
    theta = 1-Q(mode['positive_shift'])
    factors = ['A']*mode['p']+['B']*mode['q']+['E']
    coeff = Q(term['coefficient'])
    routes = proof_routes(mode, term, alpha, gamma, split, target, meter)
    chosen = min(range(len(routes)), key=lambda i: (Q(routes[i]['energy']['power']),
        routes[i]['energy']['log_degree'], Q(routes[i]['energy']['constant']), i))
    return dict(id=ident, source_key=dict(mode=mode['name'], a=term['a'], b=term['b']),
        source_scalar=mode['coefficient'], source_coefficient=str(coeff), theta=str(theta),
        h_factors=factors,
        moment=dict(kind='complete_conditional_moment', theta=str(theta), factors=factors,
            factorization='finite moments of A,B times the full infinite conditional moment of E',
            truncated_at_horizon=False),
        pieces=[dict(kind='centered_power_convolution', coefficient=str(coeff), factors=factors),
                dict(kind='moment_drift', coefficient=str(coeff/theta), kernel='J_theta'),
                dict(kind='centering_compensation', coefficient=str(-coeff),
                     factors=['A']*mode['p']+['B']*mode['q']+['C', 'K', 'O'])],
        routes=routes, selected_route=chosen,
        component_target_proved=routes[chosen]['target_constant'] is not None,
        compensating_terms_bounded=False,
        scope='one centered component; the complete signed residual stays open')


def geometry(modes, alpha, gamma, spec, splits, ident, meter):
    cases, applications, untouched = [], [], []
    for mode in modes:
        polynomial = INVERSE.synthesize(alpha, gamma, mode['p'], mode['q'], meter)
        cases.append(dict(mode=mode, program=polynomial))
        for term in polynomial['terms']:
            if mode['positive_shift'] is not None and term['a'] == 1 and term['b'] == 0:
                theta = str(1-Q(mode['positive_shift']))
                applications.append(application(mode, term, alpha, gamma, splits[theta],
                                    spec['target'], len(applications), meter))
            else:
                untouched.append(dict(mode=mode['name'], a=term['a'], b=term['b']))
    depth = max(c['mode']['p']+c['mode']['q']+t['a']+t['b']+int(c['mode']['positive_shift'] is not None)
                for c in cases for t in c['program']['terms'])
    if depth > spec['maximum_inverse_factors']:
        raise ValueError('complete source exceeds declared degree budget; never truncate it')
    paid = [a['id'] for a in applications if a['component_target_proved']]
    terms = sum(len(c['program']['terms']) for c in cases)
    return dict(id=ident, alpha=alpha, gamma=gamma, cases=cases,
        component_count=terms, maximum_convolution_factors=depth,
        applications=applications,
        exact_join=dict(untouched_source_terms=untouched, replaced_source_terms=[a['source_key'] for a in applications],
            paid_centered_components=paid,
            residual_centered_components=[a['id'] for a in applications if a['id'] not in paid],
            all_moment_drifts=[a['id'] for a in applications],
            all_centering_compensations=[a['id'] for a in applications],
            transport_error_coefficient='-1', transport_error_definition='e=f-g',
            identity='g=P+R; P=sum(paid centered components); R=all other complete signed pieces-e'),
        full_signed_bound_proved=False, RH_proved=False)


def rank(row):
    paid = [a for a in row['applications'] if a['component_target_proved']]
    worst = max((Q(a['routes'][a['selected_route']]['energy']['power']) for a in paid), default=Q(1000))
    return (-len(paid), worst, row['component_count'], row['maximum_convolution_factors'],
            Q(row['alpha']), Q(row['gamma']))


def channel_cost(construction):
    # Abel summation retains ALL prefixes and varying logarithmic weights.
    return sum((Q(2)**ceil(Q(c['eta']))*(abs(Q(c['polynomial'][0]))+
        2*sum(abs(Q(a)) for a in c['polynomial'][1:])))**2 for c in construction['channels'])


def reductions(row, obligations, target, meter):
    if target != dict(energy_power='0', log_degree=0):
        # Generic component search supports other goals.  This bridge currently
        # pays a constant; other goal recoveries must be explicitly implemented.
        return []
    paid = [a for a in row['applications'] if a['component_target_proved']]
    source_cost = len(paid)*sum((Q(a['routes'][a['selected_route']]['target_constant']) for a in paid), Q(0))
    result = []
    for parent in obligations:
        target_degree = Q(parent['reduction']['target_log_power'])
        recovery_degree = Q(parent['construction']['recovery_log_power'])
        residual_degree = target_degree-recovery_degree
        expected_degree = Q(parent['reduction']['required_coarse_forcing_log_power'])+int(Q(parent['reduction']['rho']) == 1)
        if residual_degree != expected_degree or residual_degree < 0:
            raise ValueError('constant-paid bridge needs nonnegative inherited target log degree')
        cc = channel_cost(parent['construction'])
        result.append(dict(parent_obligation_id=parent['id'], geometry_id=row['id'],
            transport_program=parent['transport_program'], channel_abel_constant=str(cc),
            combined_paid_energy_constant=str(cc*source_cost),
            sufficient_goal=dict(expression='complete signed projected residual energy S_R(X)',
                upper='C*(1+log2X)^p', p=str(residual_degree),
                quantifier='one fixed finite C; EVERY dyadic X>=1', status='open'),
            original_target_log_degree=str(target_degree), inherited_recovery_log_power=str(recovery_degree),
            inherited_recovery_constant=parent['construction']['recovery_constant'],
            original_recovery=parent['conditional_conclusion']['original_recovery'],
            recovery='S_g<=2*S_R+2*C_paid; S_R<=2*S_g+2*C_paid',
            common_horizon='N=4X-1 for BOTH blocks',
            all_units_primes_prime_powers_and_cross_terms_retained=True,
            exact_transport_error_retained=True,
            whole_signed_bound_proved=False, RH_proved=False))
        meter.charge(200+100*len(parent['construction']['channels']))
    return result


def search(parent, spec, meter):
    validate_spec(spec)
    modes, obligations = inherited(parent)
    thetas = sorted({str(1-Q(m['positive_shift'])) for m in modes if m['positive_shift'] is not None}, key=Q)
    splits = {t: SPLIT.solve(SPLIT.power_kernel_problem(t), meter) for t in thetas}
    roots = [str(Q(1, d)) for d in range(spec['root_denominator_min'], spec['root_denominator_max']+1)]
    rows = [geometry(modes, a, b, spec, splits, i, meter) for i, (a, b) in enumerate(product(roots, repeat=2))]
    chosen = min(rows, key=rank)
    bindings = reductions(chosen, obligations, spec['target'], meter)
    applications = [a for row in rows for a in row['applications']]
    paid = [a for a in applications if a['component_target_proved']]
    return dict(schema='core-split-bound-search-v1', spec=spec, split_certificates=splits,
        geometries=rows, selected_geometry=chosen['id'], selected_bindings=bindings,
        statistics=dict(geometries=len(rows), source_terms=sum(r['component_count'] for r in rows),
            applications=len(applications), proof_routes=sum(len(a['routes']) for a in applications),
            component_target_certificates=len(paid),
            geometries_with_component_control=sum(bool(r['exact_join']['paid_centered_components']) for r in rows),
            selected_component_controls=len(chosen['exact_join']['paid_centered_components']),
            inherited_route_bindings=len(bindings)),
        supplied=['arithmetic atom facts', 'centering identity', 'hyperbola and Abel error inequalities',
                  'complete finite-factor commutator bound', 'root grammar and ranking policy'],
        generated=['error-balancing split', 'full source inverse polynomials', 'matching subexpressions',
                   'competing proof routes', 'cutoff feasibility inequalities', 'paid partition',
                   'complete compensating terms and remaining signed obligations'],
        source_observations=0, model_calls_in_search=0, general_analytic_prover=False,
        whole_signed_bound_proved=False, RH_proved=False)


def feedback(result, input_file, result_file):
    chosen = result['geometries'][result['selected_geometry']]
    return dict(schema='core-split-bound-feedback-v1', status='open',
        parent_obligation_file=input_file, complete_search_artifact=result_file,
        selected_geometry=chosen['id'], selected_source_representation=chosen,
        generated_bound_obligations=result['selected_bindings'],
        proof_frontier=[
            dict(id='actual_signed_core', expression=chosen['exact_join'], status='open',
                depends_on=[], priority='independent signed control of the complete join'),
            dict(id='source_recovery', status='proved conditional reduction', depends_on=['actual_signed_core']),
            dict(id='previous_frame_moment_conditions', status='open', parent_file=input_file,
                priority='retained; conditioning alone does not bound the common core')],
        unsupported_next_targets=[
            dict(expression='multiple residual factors R,S in the untouched complete source terms',
                missing='a signed-prefix, correlation or recurrence rule beyond the current bounded-prefix factor language'),
            dict(expression='joint moment drifts, centering compensations, and untouched source minus e',
                missing='a uniform signed estimate retaining their interaction')],
        actual_new_component_controls=len(chosen['exact_join']['paid_centered_components']),
        complete_compensations_and_original_target_retained=True,
        scope='new partial all-scale component controls; full signed core and RH remain open',
        whole_signed_bound_proved=False, RH_proved=False)
