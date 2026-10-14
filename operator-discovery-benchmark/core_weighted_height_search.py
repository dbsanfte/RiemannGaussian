"""Search a reviewed bound language while retaining its open arithmetic leaves.

Rational proof choices and harmonic-null directions are generated here. No
arithmetic observations or analyst-selected winning contour enter selection.
The analytic rules are a declared trust base, not a general theorem prover.
"""
from fractions import Fraction as Q
from math import ceil, comb


DEFAULT_SPEC = dict(sigma_denominator_max=24, kappa_denominator_max=12,
    epsilon_fractions=['1/2', '1/4', '1/8'], maximum_tau='128',
    dilation_max=6, amplitude_max=6)
RULES = dict(
    twisted_fourth=dict(status='unconditional_import', critical_real_part='1/2',
        zeta_power='4', polynomial_power='2', height_power='1+epsilon',
        coefficient_class='abs(alpha_n)<=C_nu*n^nu for every nu>0, uniformly in U and phases',
        length_premise='R<=(Y/2)^kappa; fixed 0<kappa<1/4',
        source='https://arxiv.org/html/1609.02539v1',
        original_source='https://doi.org/10.1006/jnth.1995.1086'),
    transfer=dict(review='CORE_WEIGHTED_MOMENT_RULE_REVIEW_020.txt',
        method='positive strip Poisson kernels for pole-removed zeta squared; phase-uniform boundary moments',
        polynomial_squared_normalization='R^(1-2sigma)',
        below_length_threshold_licensed=False),
    recovery=dict(review='CORE_WEIGHTED_MOMENT_RULE_REVIEW_020.txt',
        method='analytic-residue Gaussian Perron, global Mellin norm, integer-cell averaging, full-history Hardy/Abel',
        ordinary_moment_not_inferred_from_residue=True,
        all_source_cross_terms_and_compensations_retained=True),
    generic_sharpness=dict(review='CORE_WEIGHTED_MOMENT_SHARPNESS_REVIEW_021.txt',
        method='exact harmonic-null dilation and fixed small-height lower bound',
        scope='generic bounded finite weights, not actual Mobius or the complete signed source'),
    formal_proof_assistant_verified=False)


def rational(value):
    if not isinstance(value, str) or str(Q(value)) != value:
        raise ValueError('canonical rational strings required')
    return Q(value)


def grid(bound, maximum):
    return sorted({Q(n, d) for d in range(2, maximum+1)
                   for n in range(1, d) if Q(n, d) < bound})


def validate_spec(spec):
    if set(spec) != set(DEFAULT_SPEC):
        raise ValueError('complete declared weighted-height grammar required')
    for key, lower, upper in [('sigma_denominator_max', 3, 32),
            ('kappa_denominator_max', 5, 24), ('dilation_max', 2, 12),
            ('amplitude_max', 1, 16)]:
        if type(spec[key]) is not int or not lower <= spec[key] <= upper:
            raise ValueError('bounded integer grammar parameter '+key)
    if not 0 < rational(spec['maximum_tau']) <= 1024:
        raise ValueError('bounded rational common height exponent')
    fs = spec['epsilon_fractions']
    if (not isinstance(fs, list) or not 1 <= len(fs) <= 8 or len(set(fs)) != len(fs)
            or any(not 0 < rational(f) < 1 for f in fs)):
        raise ValueError('distinct strict rational saving fractions')


def branches(p, m, theta, sigma, meter):
    if (type(p) is not int or not 0 <= p <= 16 or type(m) is not int
            or not 2 <= m <= 64 or not 0 < theta < 1
            or not 0 < sigma < min(Q(1, 2), theta)):
        raise ValueError('finite integer convolution powers and licensed non-pole contour')
    u = 1-theta
    result = []
    for j in range(m+1):
        r = p+j
        d = -sigma-u if j == 0 else 1-u-3*sigma if j == 1 else j-u-(j+3)*sigma
        result.append(dict(j=j, r=r, support_U_power=r,
            coefficient_envelope=dict(multiplier=str(3**j), divisor_order=r,
                constant_polynomial=(r == 0)),
            height_power=str(d), weight_U_power=str(r*(1-2*sigma))))
        meter.charge(50)
    return result


def line_search(p, m, theta, alpha, sigma, spec, meter):
    if not 0 < alpha < 1:
        raise ValueError('strict short-cutoff exponent required')
    bs = branches(p, m, theta, sigma, meter)
    savings = [-Q(b['height_power']) for b in bs]
    plans, failures = [], []
    if min(savings) <= 0:
        failures.append('at_least_one_complete_branch_has_no_strict_height_saving')
    else:
        for kappa in grid(Q(1, 4), spec['kappa_denominator_max']):
            for fraction in spec['epsilon_fractions']:
                epsilon = Q(fraction)*min(savings)
                tau = max([Q(b['r'])/kappa for b in bs] +
                    [Q(b['weight_U_power'])/(-Q(b['height_power'])-epsilon) for b in bs])
                pb = [dict(j=b['j'], length_slack=str(tau*kappa-b['r']),
                    tail_height_power=str(Q(b['height_power'])+epsilon),
                    tail_U_power=str(Q(b['weight_U_power'])+tau*(Q(b['height_power'])+epsilon))) for b in bs]
                high = max(Q(b['tail_U_power']) for b in pb)
                low = 2*(p+m)*(1-sigma)
                error = 2*(p+m)*(1-theta)
                within_cap = tau <= Q(spec['maximum_tau'])
                plans.append(dict(kappa=str(kappa), epsilon_fraction=fraction,
                    epsilon=str(epsilon), tau=str(tau), branches=pb, within_tau_cap=within_cap,
                    high_U_power=str(high), high_energy_X_power=str(2*sigma-1),
                    required_low_U_power=str((1-2*sigma)/alpha),
                    generic_low_U_power=str(low), generic_low_energy_X_power=str(2*sigma-1+alpha*low),
                    integer_error_U_power=str(error), integer_error_X_power=str(-1+alpha*error),
                    high_auxiliary_proved=within_cap,
                    generic_complete_component_proved=within_cap and 2*sigma-1+alpha*low <= 0 and -1+alpha*error <= 0,
                    low_obligation_status='proved_by_generic_fallback' if 2*sigma-1+alpha*low <= 0 else 'open_actual_Mobius_bound'))
                meter.charge(80+40*len(bs))
        if not any(c['within_tau_cap'] for c in plans):
            failures.append('every_valid_common_height_exceeds_declared_tau_cap')
    eligible = [i for i, c in enumerate(plans) if c['high_auxiliary_proved']]
    selected = min(eligible, key=lambda i: (Q(plans[i]['tau']),
        -Q(plans[i]['epsilon']), -Q(plans[i]['kappa']), i)) if eligible else None
    return dict(sigma=str(sigma), branches=bs, plans=plans, selected_plan=selected,
        failed_premises=failures)


def harmonic_null_search(spec, meter):
    accepted = []
    tried = 0
    for d in range(2, spec['dilation_max']+1):
        directions = set()
        for a in range(-spec['amplitude_max'], spec['amplitude_max']+1):
            for b in range(-spec['amplitude_max'], spec['amplitude_max']+1):
                tried += 1
                meter.charge(15)
                if a == b == 0 or Q(a)+Q(b, d) != 0:
                    continue
                scale = max(abs(a), abs(b)) * (1 if a > 0 else -1)
                directions.add((Q(a, scale), Q(b, scale)))
        for x, y in sorted(directions):
            accepted.append(dict(dilation=d, x=str(x), y=str(y), harmonic_tail='0', c='1',
                unit='1', seed_interval='Q<n<=2Q', image_interval='n -> dilation*n',
                horizon='U=2*dilation*Q', quantifier='every integer Q>=2',
                tail_factor=dict(constant=str(x), dilation_coefficient=str(y), dilation=d),
                uniform_magnitude_gap='abs(y)*dilation^(-sigma)-abs(x)>0 for 0<sigma<1',
                lower_U_power='2*(p+m)*(1-sigma)',
                proof='paired harmonic identity, rotated seed sum, zeta nonzero on real (0,1), fixed-window continuity',
                status='proved_generic_class_obstruction',
                applies_to_actual_Mobius=False, applies_to_prescribed_X_block=False,
                applies_to_arbitrary_projected_channel=False, applies_to_full_signed_core=False))
    return dict(integer_pairs_examined=tried, witnesses=accepted,
        scope='generic bounded finite weights with harmonic cancellation',
        ordinary_moment_convergence_not_assumed=True)


def low_gram(p, m, theta, sigma, alpha, plan):
    return dict(kind='complete_zeta_weighted_low_Mellin_Gram',
        parameters=dict(p=p, m=m, theta=str(theta), sigma=str(sigma), alpha=str(alpha)),
        source_weights=dict(A='mu(n)*1_(n<=U)', c='sum_(n<=U)mu(n)/n',
            T='c*delta-A', E='delta+One*T', B_j='A^p*T^j'),
        height=dict(prefactor='2', U_power=plan['tau'], interval='abs(t)<H'),
        measure='dt/(2*pi)',
        kernel='abs(zeta(s+1-theta)/s)^2*zeta(s)^j*conj(zeta(s)^k)',
        finite_polynomial_product='B_j(s)*conj(B_k(s))',
        matrix_entries=[dict(j=j, k=k, contraction=str(comb(m, j)*comb(m, k)))
                        for j in range(m+1) for k in range(m+1)],
        integer_pairs='all ordered d,e, with actual signed B_j(d)*B_k(e)',
        unweighted_Gaussian_substitution_allowed=False, diagonal_only_allowed=False,
        required_upper=dict(constant='C_low', U_power=plan['required_low_U_power'], log_degree=0,
            quantifier='every integer U>=1, one fixed finite C_low independent of U,X,N'),
        status=plan['low_obligation_status'],
        generic_fallback_U_power=plan['generic_low_U_power'],
        complete_cross_terms_retained=True)


def channel_multipliers(channels, sigma, theta):
    hardy = error = Q(0)
    for channel in channels:
        eta = rational(channel['eta'])
        if eta < 0:
            raise ValueError('nonnegative logarithmic channel exponent required')
        cs = [rational(c) for c in channel['polynomial']]
        mass = sum(map(abs, cs))
        derivative = sum(j*abs(c) for j, c in enumerate(cs))
        hardy += (Q(2)**ceil(eta)*(mass+2*(1+1/sigma)*derivative))**2
        error += (Q(2)**ceil(eta)*(mass+2*(1+1/(1-theta))*derivative))**2
    return hardy, error


def recovery_bindings(parent, context, target, line, plan, meter):
    programs = {p['id']: p for p in context['channel_programs']}
    if (len(programs) != len(context['channel_programs']) or
            set(programs) != {b['parent_obligation_id'] for b in parent['generated_bound_obligations']}):
        raise ValueError('every original full-history channel binding required')
    scalar = Q(target['source_term']['coefficient'])**2
    alpha, sigma, theta = Q(parent['selected_source_representation']['alpha']), Q(line['sigma']), Q(target['theta'])
    b, error_up = Q(plan['required_low_U_power']), Q(plan['integer_error_U_power'])
    output = []
    for old in parent['generated_bound_obligations']:
        program = programs[old['parent_obligation_id']]
        # New input has nested old recovery bindings; original transport is
        # retained there and the full-source independent checker replays it.
        h, e = channel_multipliers(program['construction']['channels'], sigma, theta)
        output.append(dict(parent_obligation_id=old['parent_obligation_id'],
            source_coefficient_squared=str(scalar), channel_Hardy_constant=str(h),
            channel_error_constant=str(e), low_constant_multiplier=str(scalar*64*h*Q(4)**ceil(alpha*b)),
            high_constant_multiplier=str(scalar*64*h),
            error_constant_multiplier=str(scalar*4*e*Q(4)**ceil(alpha*error_up)),
            low_energy_X_power='0', high_energy_X_power=plan['high_energy_X_power'],
            error_energy_X_power=plan['integer_error_X_power'],
            constant_symbols=['C_low', 'C_high', 'C_residue_squared'], numerical_value=None,
            status='conditional_on_complete_low_Gram_bound',
            complete_history=True, parent_and_child_common_horizon='N=4X-1'))
        meter.charge(100+50*len(program['construction']['channels']))
    return output


def target_search(parent, context, target, spec, meter):
    p, m, theta = target['p'], target['m'], rational(target['theta'])
    alpha = rational(parent['selected_source_representation']['alpha'])
    lines = [line_search(p, m, theta, alpha, sigma, spec, meter)
             for sigma in grid(min(Q(1, 2), theta), spec['sigma_denominator_max'])]
    eligible = [i for i, c in enumerate(lines) if c['selected_plan'] is not None]
    def key(i):
        line = lines[i]
        plan = line['plans'][line['selected_plan']]
        return (-Q(plan['required_low_U_power']), Q(plan['tau']), i)
    selected = min(eligible, key=key) if eligible else None
    output = dict(target_id=target['target_id'], p=p, m=m, theta=str(theta),
        source_term=target['source_term'], inherited_component_bound_proved=target['component_bound_proved'],
        lines=lines, selected_line=selected, high_auxiliary_proved=selected is not None,
        new_source_payment=False, low_obligation=None, conditional_recovery_bindings=[],
        centering=dict(kind='analytic_residue', M='A(theta)^p*E(theta)^m',
            centered_coefficient='K*A^p*E^m-(M/theta)*J_theta',
            retained_opposite_drift='source_coefficient*(M/theta)*J_theta',
            ordinary_moment_established_by_inherited_prefix_rule=1-Q(1, m) < theta,
            ordinary_prefix_power=str(1-Q(1, m)), ordinary_convergence_required_for_this_route=False,
            unit_J_theta_1='1', continuous_small_x_tail='-(M/theta)*x^theta on 0<x<1',
            pole_at_1_removed_in_complete_E=True),
        source_head_identity=dict(domain='every integer 1<=n<=U',
            expression='(A^p*E^m)(n)', scalar='c^m',
            coefficient=dict(atom='One' if m >= p else 'mu', convolution_power=abs(m-p)),
            zero_power='delta', derivation='mu*One=delta on n<=U and E(n)=c',
            supplies_full_Gram_bound=False))
    if selected is not None:
        line = lines[selected]
        plan = line['plans'][line['selected_plan']]
        output['low_obligation'] = low_gram(p, m, theta, Q(line['sigma']), alpha, plan)
        output['conditional_recovery_bindings'] = recovery_bindings(parent, context, target, line, plan, meter)
    return output


def dependencies(targets, witnesses):
    graph = [dict(id='reviewed_weighted_rules', status='reviewed_and_imported', depends_on=[]),
        dict(id='inherited_verified_frontier', status='reviewed_and_imported', depends_on=[]),
        dict(id='generic_weight_class_obstruction', status='proved' if witnesses['witnesses'] else 'open',
            depends_on=['reviewed_weighted_rules'])]
    for t in targets:
        ident = t['target_id']
        if t['selected_line'] is None:
            graph.append(dict(id='route_'+ident, status='open', depends_on=[]))
            continue
        line = t['lines'][t['selected_line']]
        plan = line['plans'][line['selected_plan']]
        graph.extend([
            dict(id='high_'+ident, status='proved', depends_on=['reviewed_weighted_rules']),
            dict(id='low_'+ident, status='proved' if t['low_obligation']['status'] == 'proved_by_generic_fallback' else 'open',
                depends_on=['reviewed_weighted_rules']),
            dict(id='integer_'+ident, status='proved' if Q(plan['integer_error_X_power']) <= 0 else 'open',
                depends_on=['reviewed_weighted_rules']),
            dict(id='route_'+ident, status='proved' if plan['generic_complete_component_proved'] else 'conditional',
                depends_on=['high_'+ident, 'low_'+ident, 'integer_'+ident])])
    graph.extend([dict(id='complete_signed_complement', status='open', depends_on=['inherited_verified_frontier']),
        dict(id='actual_signed_core', status='open',
            depends_on=['route_'+t['target_id'] for t in targets]+['complete_signed_complement']),
        dict(id='original_RH_recovery', status='conditional', depends_on=['actual_signed_core'])])
    return graph


def next_tasks(targets):
    tasks = [dict(target_id='actual_signed_core', priority=0, status='open',
        search_kind='joint_signed_core_control',
        preserve='complete inherited residual Z, every source cross, drift, unit, -e and recovery',
        componentwise_routes_are_optional=True)]
    for t in targets:
        if t['inherited_component_bound_proved']:
            continue
        tasks.append(dict(target_id=t['target_id'], priority=1, status='open',
            search_kind='bound_actual_signed_low_Gram' if t['low_obligation'] else 'discover_joint_weighted_provider',
            exact_missing_estimate=t['low_obligation'], source_head_constraint=t['source_head_identity'],
            available_constructions=['signed pairing', 'finite inverse head subtraction with full restoration',
                'joint Hermitian Gram domination', 'scale recurrence', 'correlation reduction'],
            generic_sharpness_is_not_an_actual_Mobius_disproof=True,
            increasing_tau_requires_rebounding_the_expanded_low_head=True))
    return tasks


def search(parent, context, spec, meter):
    validate_spec(spec)
    if (parent.get('schema') != 'core-moment-bound-feedback-v1' or parent.get('status') != 'open'
            or parent.get('whole_signed_bound_proved') is not False or parent.get('RH_proved') is not False):
        raise ValueError('complete open inherited moment feedback required')
    terms = context['complete_signed_join']['collected_terms']
    ids = [t['target_id'] for t in parent['auxiliary_bound_targets']]
    if len(set(ids)) != len(ids) or not ids or any(t['source_term'] not in terms for t in parent['auxiliary_bound_targets']):
        raise ValueError('distinct actual complete-source targets required')
    targets = [target_search(parent, context, t, spec, meter) for t in parent['auxiliary_bound_targets']]
    witnesses = harmonic_null_search(spec, meter)
    statistics = dict(targets=len(targets), candidate_lines=sum(len(t['lines']) for t in targets),
        height_plans=sum(len(c['plans']) for t in targets for c in t['lines']),
        high_auxiliary_bounds_proved=sum(t['high_auxiliary_proved'] for t in targets),
        open_low_Gram_obligations=sum(t['low_obligation'] is not None and t['low_obligation']['status'] == 'open_actual_Mobius_bound' for t in targets),
        generic_witnesses=len(witnesses['witnesses']), new_component_bounds_proved=0,
        inherited_component_bounds_proved=sum(t['inherited_component_bound_proved'] for t in targets),
        inherited_bindings=len(parent['generated_bound_obligations']))
    meter.live(100*statistics['candidate_lines']+200*statistics['height_plans']+100*statistics['inherited_bindings'])
    return dict(schema='core-weighted-height-search-v1', spec=spec, supplied_rules=RULES,
        targets=targets, generic_weight_test=witnesses,
        inherited_complete_source_reduction=parent['complete_source_reduction'],
        inherited_bindings=parent['generated_bound_obligations'],
        inherited_proof_dependencies=parent['proof_dependencies'],
        proof_dependencies=dependencies(targets, witnesses), next_search_tasks=next_tasks(targets), statistics=statistics,
        actual_source_observations=0, fitted_constants=0, model_calls_in_search=0,
        detector_has_general_analytic_prover=False, whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, result, input_file, artifact):
    return dict(schema='core-weighted-height-feedback-v1', status='open', parent_obligation_file=input_file,
        complete_search_artifact=artifact, selected_source_representation=parent['selected_source_representation'],
        generated_bound_obligations=parent['generated_bound_obligations'],
        auxiliary_bound_targets=parent['auxiliary_bound_targets'], weighted_height_targets=result['targets'],
        generic_weight_test=result['generic_weight_test'], proof_dependencies=result['proof_dependencies'],
        inherited_proof_dependencies=parent['proof_dependencies'], next_search_tasks=result['next_search_tasks'],
        complete_source_reduction=parent['complete_source_reduction'],
        retained_original_proof_frontier=parent['retained_original_proof_frontier'],
        new_component_bounds_proved=0,
        next_priority='bound the complete signed residual; search the actual signed low Gram or a new joint construction, preserving the high/low dependency',
        whole_signed_bound_proved=False, RH_proved=False)
