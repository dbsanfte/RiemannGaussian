"""Executable search for proofs of complete centered arithmetic energy bounds.

Analysts supply general analytic rules, not a selected contour or allocation.
The search composes reflection, moment interpolation, Holder and convexity,
then checks all convergence, cutoff, centering and source-recovery premises.
Unspecified uniform theorem constants are symbolic; they are never fitted.
"""
from fractions import Fraction as Q
from itertools import product
from math import ceil


DEFAULT_SPEC = dict(sigma_denominator_max=24, moment_orders=['2', '4'],
                    target_energy_power='0')
RULES = dict(
    imported_fourth_moment=dict(status='unconditional_import', order='4',
        real_part='1/2', dyadic_power='1', logarithmic_power=4,
        source='https://arxiv.org/html/1609.02539v1',
        original_source='https://doi.org/10.1112/plms/s2-27.1.273',
        constant='fixed finite B4; no numerical value asserted'),
    moment_transfer=dict(orders=['2', '4'], real_part_domain='[1/2,1)',
        power='1+epsilon', derivation='Gaussian pole-removed L2 three-lines; lower moments by Holder'),
    reflection=dict(power_per_factor='1/2-real_part',
        source='https://dlmf.nist.gov/25.4.E2'),
    convexity=dict(real_part_domain='(0,1)', power_per_factor='(1-real_part)/2+epsilon'),
    analytic_bridge=dict(review='JOINT_REMAINDER_MOMENT_REVIEW_018.txt',
        contour='Gaussian Perron, cross only theta, then Mellin Plancherel',
        integer_correction='complete J_theta and weighted integer cells, including n=1',
        channel_transfer='global weighted Hardy/Abel; orthogonal cell projection',
        formal_proof_assistant_verified=False))


def rational(text):
    if not isinstance(text, str) or str(Q(text)) != text:
        raise ValueError('canonical rational strings required')
    return Q(text)


def holder_vertices(upper):
    """All vertices of 0<=lambda_i<=upper_i, sum lambda_i<=1."""
    if not 1 <= len(upper) <= 4 or any(not 0 <= u <= 1 for u in upper):
        raise ValueError('bounded Holder simplex')
    vertices = {v for v in product(*[(Q(0), u) for u in upper]) if sum(v) <= 1}
    for free in range(len(upper)):
        others = [i for i in range(len(upper)) if i != free]
        for corner in product(*[(Q(0), upper[i]) for i in others]):
            v = [Q(0)]*len(upper)
            for i, c in zip(others, corner):
                v[i] = c
            v[free] = 1-sum(corner)
            if 0 <= v[free] <= upper[free]:
                vertices.add(tuple(v))
    return sorted(vertices)


def product_moment_search(factors, orders, meter):
    """Bound integral_T^2T product |zeta(a_i+it)|^b_i, with rational b_i.

    Minimize its height exponent over reflections, licensed moment orders,
    and the entire Holder allocation polytope (its exact vertices suffice).
    This primitive also accepts fractional absolute-moment powers.
    """
    if not 1 <= len(factors) <= 4 or orders not in ([], ['2'], ['4'], ['2', '4']):
        raise ValueError('declared unconditional moment library')
    parsed = [(rational(f['real_part']), rational(f['power'])) for f in factors]
    if any(not 0 < a < 1 or not 0 < b <= 128 for a, b in parsed):
        raise ValueError('positive bounded powers on non-pole strip lines')
    best, examined = None, 0
    for reflected in product((False, True), repeat=len(parsed)):
        lines = [1-a if r else a for (a, _), r in zip(parsed, reflected)]
        choices = [[Q(0)]+list(map(Q, orders)) if a >= Q(1, 2) else [Q(0)] for a in lines]
        for qs in product(*choices):
            upper = [min(Q(1), b/q) if q else Q(0) for (_, b), q in zip(parsed, qs)]
            for weights in holder_vertices(upper):
                examined += 1
                meter.charge(30*len(parsed))
                rows = []
                exponent, slack_cost = Q(1), Q(0)
                for (a, b), line, r, q, lam in zip(parsed, lines, reflected, qs, weights):
                    remainder = b-lam*q
                    fe = b*(Q(1, 2)-a) if r else Q(0)
                    pointwise = remainder*(1-line)/2
                    exponent += fe+pointwise
                    slack_cost += remainder+lam
                    rows.append(dict(original_real_part=str(a), power=str(b), reflected=r,
                        effective_real_part=str(line), moment_order=str(q), holder_weight=str(lam),
                        convexity_power=str(remainder), reflection_height_power=str(fe),
                        convexity_height_power=str(pointwise)))
                candidate = dict(factors=rows, holder_unused=str(1-sum(weights)),
                    integral_height_power=str(exponent), epsilon_coefficient=str(slack_cost))
                # First tie in a deterministic enumeration; no arithmetic data fitted.
                if best is None or (exponent, slack_cost) < (Q(best['integral_height_power']), Q(best['epsilon_coefficient'])):
                    best = candidate
    return dict(best=best, allocations_examined=examined,
        completeness='every reflection/order and every Holder box-simplex vertex')


def sigma_grid(theta, maximum):
    return sorted({Q(n, d) for d in range(2, maximum+1) for n in range(1, d)
                   if Q(n, d) < min(Q(1, 2), theta)})


def moment_convergence(p, m, theta):
    rho = 1-Q(1, m)
    return dict(rule='complete E^m hyperbola prefix then finite A^p convolution and Abel tail',
        residual_prefix_power=str(rho), theta=str(theta), finite_factor_degree=p,
        ordinarily_convergent=rho < theta,
        analytic_residue_is_not_ordinary_convergence=True,
        full_infinite_tail_retained=True)


def candidate(p, m, theta, alpha, sigma, orders, goal, meter):
    if (type(p) is not int or not 0 <= p <= 16 or type(m) is not int or not 2 <= m <= 64
            or not 0 < alpha < 1 or not 0 < sigma < min(Q(1, 2), theta) or not theta < 1):
        raise ValueError('licensed belowhalf contour, kernel and finite arithmetic powers')
    u = 1-theta
    branches = [product_moment_search([dict(real_part=str(sigma+u), power='2')], orders, meter),
        product_moment_search([dict(real_part=str(sigma), power=str(2*m)),
                              dict(real_part=str(sigma+u), power='2')], orders, meter)]
    heights = [Q(b['best']['integral_height_power'])-2 for b in branches]
    slack = max(Q(b['best']['epsilon_coefficient']) for b in branches)
    strict = max(heights) < 0
    epsilon = min(Q(1), -max(heights)/(2*(1+slack))) if strict else None
    finite_power = 2*(p+m)*(1-sigma)
    energy = 2*sigma-1+alpha*finite_power
    ordinary = moment_convergence(p, m, theta)
    failures = []
    if not strict:
        failures.append('dyadic_Mellin_tail_not_summable_by_this_plan')
    if not ordinary['ordinarily_convergent']:
        failures.append('ordinary_centering_moment_unproved')
    if energy > goal:
        failures.append('cutoff_cost_exceeds_target_energy_power')
    return dict(sigma=str(sigma), moment_branches=branches,
        mellin_height_powers=list(map(str, heights)),
        epsilon=str(epsilon) if epsilon is not None else None,
        strict_tail_summation=strict,
        full_finite_factor_U_power=str(finite_power), residue_squared_U_power=str(2*(p+m)*(1-theta)),
        complete_centering=ordinary, recovered_energy_X_power=str(energy),
        energy_log_degree=0, target_met=not failures, failed_premises=failures,
        constants_uniform_in=['U', 'X', 'N'], constants_may_depend_on=['p', 'm', 'theta', 'sigma', 'epsilon'],
        pole_removal='T(1)=c-A(1)=0 before estimating E(s)=1+zeta(s)T(s)',
        analytic_residue='A(theta)^p E(theta)^m/theta',
        centered_coefficient='K*A^p*E^m - A(theta)^p E(theta)^m*J_theta/theta',
        full_unit_and_small_x_tail_retained=True)


def channel_constant(channels, sigma):
    total = Q(0)
    for ch in channels:
        eta = rational(ch['eta'])
        if eta < 0:
            raise ValueError('Hardy channel rule requires nonnegative eta')
        coeff = [rational(c) for c in ch['polynomial']]
        p0 = sum(map(abs, coeff))
        p1 = sum(j*abs(c) for j, c in enumerate(coeff))
        total += (Q(2)**ceil(eta)*(p0+2*(1+1/sigma)*p1))**2
    return str(total)


def targets_search(parent, spec, meter):
    alpha = rational(parent['selected_source_representation']['alpha'])
    results = []
    for target in parent['auxiliary_bound_targets']:
        p, m, theta = target['p'], target['m'], rational(target['theta'])
        if type(p) is not int or not 0 <= p <= 16 or type(m) is not int or not 2 <= m <= 64 or not 0 < theta < 1:
            raise ValueError('licensed arithmetic source powers and kernel')
        grid = sigma_grid(theta, spec['sigma_denominator_max'])
        candidates = [candidate(p, m, theta, alpha, s, spec['moment_orders'],
            Q(spec['target_energy_power']), meter) for s in grid]
        passing = [i for i, c in enumerate(candidates) if c['target_met']]
        selected = min(passing, key=lambda i: (Q(candidates[i]['recovered_energy_X_power']),
            -min(-Q(x) for x in candidates[i]['mellin_height_powers']), i)) if passing else None
        results.append(dict(target_id=target['id'], p=p, m=m, theta=str(theta),
            source_term=target['source_term'], candidate_lines=candidates, selected=selected,
            component_bound_proved=selected is not None,
            proof_constant=(dict(name='C_norm_'+target['id'], kind='fixed_finite_theorem_constant',
                statement='sum_(n>=1)|complete centered prefix(n)|^2*n^(-2sigma-1)<=C_norm*U^b',
                numerical_value=None, uniform_in=['U', 'X', 'N']) if selected is not None else None),
            all_source_compensations_retained=True))
    return results


def source_reduction(parent, context, targets, meter):
    paid = [t for t in targets if t['component_bound_proved']]
    programs = {p['id']: p for p in context['channel_programs']}
    if set(programs) != {b['parent_obligation_id'] for b in parent['generated_bound_obligations']}:
        raise ValueError('all inherited complete channel programs required')
    terms = context['complete_signed_join']['collected_terms']
    if any(t['source_term'] not in terms for t in paid):
        raise ValueError('new paid pieces must occur in the actual complete signed source')
    alpha = Q(parent['selected_source_representation']['alpha'])
    bindings = []
    for old in parent['generated_bound_obligations']:
        program = programs[old['parent_obligation_id']]
        if program['transport_program'] != old['transport_program']:
            raise ValueError('unchanged original transport program')
        costs = []
        for t in paid:
            c = t['candidate_lines'][t['selected']]
            if Q(c['recovered_energy_X_power']) > 0:
                raise ValueError('constant recovery bridge requires nonpositive energy power')
            sigma, up = Q(c['sigma']), Q(c['full_finite_factor_U_power'])
            cc = Q(channel_constant(program['construction']['channels'], sigma))
            # Local norm restriction and N<=4X. Covers parent AND child with
            # the same U. Ceil only enlarges a fixed positive constant.
            cutoff_cost = Q(2)**ceil(2*sigma+1+2*alpha*up)
            multiplier = len(paid)*Q(t['source_term']['coefficient'])**2*cc*cutoff_cost
            costs.append(dict(target_id=t['target_id'], constant=t['proof_constant']['name'],
                rational_multiplier=str(multiplier), channel_Hardy_constant=str(cc),
                local_and_cutoff_constant=str(cutoff_cost), energy_X_power=c['recovered_energy_X_power']))
            meter.charge(100+100*len(program['construction']['channels']))
        bindings.append(dict(parent_obligation_id=old['parent_obligation_id'], inherited_binding=old,
            new_paid_constant=dict(kind='positive_linear_combination_of_uniform_theorem_constants', terms=costs),
            sufficient_goal=dict(expression='S_Z(X), complete signed residual after old and new paid pieces',
                upper=old['sufficient_goal']['upper'], p=old['sufficient_goal']['p'],
                quantifier=old['sufficient_goal']['quantifier'], status='open'),
            recovery=('S_g<=4*S_Z+4*C_new+2*C_old; S_Z<=4*S_g+4*C_old+2*C_new' if paid else old['recovery']),
            all_history_and_units_retained=True, whole_signed_bound_proved=False, RH_proved=False))
    return dict(inherited_complete_signed_join=context['complete_signed_join'],
        inherited_original_frontier=parent['retained_original_proof_frontier'],
        new_paid_components=[dict(target_id=t['target_id'], source_term=t['source_term'],
            centered_component='source_coefficient*(K*A^p*E^m - M/theta*J_theta)',
            retained_opposite_drift='source_coefficient*M/theta*J_theta',
            ordinary_moment_proved=True) for t in paid],
        exact_identity='g=P_old+P_new+Z; Z=R_old-P_new; R_old is the inherited complete signed residual',
        whole_join_cross_terms_retained=True, transport_error_retained='-e',
        common_horizon='N=4X-1 for BOTH blocks; same coefficients and cutoffs', bindings=bindings)


def next_tasks(targets):
    tasks = [dict(target_id='actual_signed_core', priority=0, status='open',
        search_kind='joint_signed_core_control',
        preserve='complete new residual Z, every drift, signed cross term, transport error and inherited recovery')]
    for t in targets:
        if t['component_bound_proved']:
            continue
        energy_lines = [c for c in t['candidate_lines'] if Q(c['recovered_energy_X_power']) <= 0]
        # A concrete missing moment inequality is a new target, not a theorem.
        c = min(energy_lines, key=lambda c: max(map(Q, c['mellin_height_powers']))) if energy_lines else None
        tasks.append(dict(target_id=t['target_id'], priority=1, status='open',
            search_kind='search_joint_moment_or_short_factor_gain',
            missing_estimate=(dict(sigma=c['sigma'],
                expression='integral_T^2T |zeta(s+1-theta)|^2*(1+|zeta(s)|^(2m)) dt',
                required_height_power='strictly less than 2',
                current_height_power=str(2+max(map(Q, c['mellin_height_powers']))),
                quantifiers='one fixed positive saving; every T>=2; constants independent of U,X,N',
                ordinary_centering_moment_also_required=not c['complete_centering']['ordinarily_convergent']) if c else None),
            alternative='retain the actual finite A,T weights inside the moment; prove a smaller U cost or a joint signed recurrence',
            finite_language_failure_is_not_arithmetic_disproof=True))
    return tasks


def search(parent, context, spec, meter):
    if (set(spec) != set(DEFAULT_SPEC) or type(spec['sigma_denominator_max']) is not int
            or not 3 <= spec['sigma_denominator_max'] <= 32
            or spec['moment_orders'] not in ([], ['2'], ['4'], ['2', '4'])
            or rational(spec['target_energy_power']) != 0):
        raise ValueError('bounded declared proof grammar and constant-energy recovery')
    if parent.get('whole_signed_bound_proved') is not False or parent.get('RH_proved') is not False:
        raise ValueError('unclosed actual signed core required')
    targets = targets_search(parent, spec, meter)
    reduction = source_reduction(parent, context, targets, meter)
    nodes = [dict(id='analytic_rule_library', status='reviewed_and_imported', depends_on=[])]
    for t in targets:
        nodes.append(dict(id='moment_'+t['target_id'], status='proved' if t['component_bound_proved'] else 'open',
            depends_on=['analytic_rule_library'] if t['component_bound_proved'] else []))
    nodes += [dict(id='complete_signed_complement', status='open', depends_on=[]),
        dict(id='actual_signed_core', status='open', depends_on=['moment_'+t['target_id'] for t in targets]+['complete_signed_complement']),
        dict(id='original_RH_recovery', status='conditional', depends_on=['actual_signed_core'])]
    return dict(schema='core-moment-bound-search-v1', spec=spec, supplied_rules=RULES,
        targets=targets, source_reduction=reduction, proof_dependencies=nodes,
        next_search_tasks=next_tasks(targets),
        statistics=dict(targets=len(targets), candidate_lines=sum(len(t['candidate_lines']) for t in targets),
            moment_allocations_examined=sum(b['allocations_examined'] for t in targets
                for c in t['candidate_lines'] for b in c['moment_branches']),
            new_component_bounds_proved=sum(t['component_bound_proved'] for t in targets),
            inherited_bindings=len(reduction['bindings'])),
        actual_source_observations=0, fitted_constants=0, model_calls_in_search=0,
        detector_has_general_analytic_prover=False, whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, result, input_file, artifact):
    return dict(schema='core-moment-bound-feedback-v1', status='open', parent_obligation_file=input_file,
        complete_search_artifact=artifact, selected_source_representation=parent['selected_source_representation'],
        generated_bound_obligations=result['source_reduction']['bindings'],
        auxiliary_bound_targets=result['targets'], proof_dependencies=result['proof_dependencies'],
        next_search_tasks=result['next_search_tasks'], complete_source_reduction=result['source_reduction'],
        retained_original_proof_frontier=parent['retained_original_proof_frontier'],
        new_component_bounds_proved=result['statistics']['new_component_bounds_proved'],
        next_priority='discover a bound for the complete signed residual Z; feed explicit unpaid moment obligations back into search',
        whole_signed_bound_proved=False, RH_proved=False)
