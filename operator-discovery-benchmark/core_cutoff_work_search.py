"""Exact arithmetic head discovery and ternary Mobius cutoff-work compilation."""
from fractions import Fraction as Q
from math import factorial
import core_cutoff_bound_planner as BOUNDS

REAL = {'c', 'a', 'v', 'x'}
COMPLEX = {'A', 'E', 'D', 'z', 'b'}
MULTIPLIERS = ['-2', '-1', '-1/2', '1/2', '1', '2']
DIAGNOSTIC_SPEC = dict(maximum_cutoff=2048, heights=['0', '1/2', '1', '2', '4', '8', '16'],
    positive_height_weight='2', zero_height_weight='1', continuous_Gram_estimate=False,
    used_for_selection=False, fitted_constants=0, fresh_arithmetic_holdout=False)
DIAGNOSTIC_SPEC.update(executed=False, reason='user prioritizes automatic bound search; numerical work deferred before observations')
RULES = dict(transition_review='CORE_CUTOFF_TRANSITION_RULE_REVIEW_022.txt',
    scope_review='CORE_CUTOFF_TRANSITION_SCOPE_REVIEW_023.txt',
    ternary_identity='mu(q)^3=mu(q)', arithmetic_head='mu*One=delta for n<=U',
    head_kernel='complete centered power kernel, including x<1 and d>x',
    shell_rule='fixed-factor length extension with kappa_prime=(kappa+1/4)/2 and finite initial range',
    uniform_signed_work_proved=False, formal_proof_assistant_verified=False)
RULES['automatic_control_review'] = 'CORE_CUTOFF_AUTOMATIC_CONTROL_REVIEW_024.txt'


def plus(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, Q(0))+v
        if not out[k]:
            del out[k]
    return out


def scale(a, c):
    return {k: v*Q(c) for k, v in a.items() if v*Q(c)}


def atom(name):
    return {(name,): Q(1)}


def multiply(a, b, meter, ternary=False):
    out = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = ka+kb
            if ternary:
                count = key.count('x')
                key = tuple(t for t in key if t != 'x')+('x',)*(0 if count == 0 else 1+(count-1)%2)
            key = tuple(sorted(key))
            out[key] = out.get(key, Q(0))+va*vb
            meter.charge(20+len(key))
    return {k: v for k, v in out.items() if v}


def power(a, n, meter, ternary=False):
    if type(n) is not int or not 0 <= n <= 64:
        raise ValueError('bounded nonnegative polynomial power')
    value = {(): Q(1)}
    for _ in range(n):
        value = multiply(value, a, meter, ternary)
    return value


def conjugate(a):
    def star(name):
        if name in REAL:
            return name
        if name in COMPLEX:
            return name+'bar'
        if name.endswith('bar') and name[:-3] in COMPLEX:
            return name[:-3]
        raise ValueError('declared real/complex symbol')
    return {tuple(sorted(star(n) for n in key)): value for key, value in a.items()}


def encode(a):
    return [dict(monomial=list(k), coefficient=str(v)) for k, v in sorted(a.items())]


def sectors(a):
    out = [{}, {}, {}]
    for key, value in a.items():
        count = key.count('x')
        if count > 2:
            raise ArithmeticError('unreduced Mobius power')
        out[count][tuple(t for t in key if t != 'x')] = value
    return [encode(p) for p in out]


def compile_transition(p, m, head, meter):
    if type(p) is not int or not 0 <= p <= 16 or type(m) is not int or not 2 <= m <= 32:
        raise ValueError('bounded actual polynomial source powers')
    A, E, c, D, z, a, b, v, x = map(atom, ['A', 'E', 'c', 'D', 'z', 'a', 'b', 'v', 'x'])
    times = lambda l, r: multiply(l, r, meter, True)
    xp = lambda l, n: power(l, n, meter, True)
    P = times(xp(A, p), xp(E, m))
    newA = plus(A, times(x, b))
    newE = plus(E, times(times(x, z), plus(a, scale(b, -1))))
    newc = plus(c, times(x, a))
    newD = plus(D, times(v, b))
    child = times(xp(newA, p), xp(newE, m))
    if head:
        P = plus(P, scale(times(xp(c, m), D), -1))
        child = plus(child, scale(times(xp(newc, m), newD), -1))
    delta = plus(child, scale(P, -1))
    # Form all three cross products before collecting ternary sectors.
    work = plus(plus(times(conjugate(P), delta), times(P, conjugate(delta))),
                times(delta, conjugate(delta)))
    return dict(parent=encode(P), child=encode(child), increment_sectors=sectors(delta),
        work_sectors=sectors(work), mu_powers=[0, 1, 2],
        weight='abs(zeta(s+1-theta)/s)^2', q_domain='every integer q>=2; U=q-1',
        substitutions=dict(A='A+x*b', E='E+x*z*(a-b)', c='c+x*a', D='D+v*b'),
        symbols=dict(x='mu(q)', a='1/q', b='q^(-s)', z='zeta(s)',
            D='complete finite head polynomial through q-1', v='exact head atom coefficient at q'),
        pole_removal_preserved='E=1+z*(c-A), with coupled c and A changes',
        all_conjugates_crosses_and_zero_mu_branch_retained=True,
        residue_update='evaluate the COMPLETE polynomial increment at s=theta; retain its opposite J_theta/theta drift',
        ordinary_moment_convergence_inferred=False)


def absorb(power_value, logs, goal):
    gap = goal-power_value
    if gap < 0 or (gap == 0 and logs):
        return dict(proved=False, multiplier=None, gap=str(gap))
    cost = Q(1) if not logs else Q(2)**logs*(1+Q(factorial(logs))/gap**logs)
    return dict(proved=True, multiplier=str(cost), gap=str(gap))


def head_certificate(p, m, theta, sigma, alpha, goal):
    if not (0 < sigma < theta < 1 and alpha > 0 and goal > 0):
        raise ValueError('positive cutoff and goal, with 0<sigma<theta<1')
    degree = abs(m-p)
    delta = degree == 0
    logs = 2*max(0, degree-1)
    B = (1/(theta-sigma)+1/sigma)/(2*theta**2)
    exponent = Q(0) if delta else 2*(1-sigma)
    constant = B*Q(4)**m*(1 if delta else 1/(1-sigma)**2)
    absorption = absorb(exponent, logs, goal)
    return dict(atom='One' if m >= p else 'mu', convolution_power=degree, c_power=m,
        cutoff='all n<=U, including unit', centered_prefix_constant=str(Q(2)**m/theta),
        centered_prefix_U_power='0' if delta else '1', centered_prefix_log_degree=max(0, degree-1),
        kernel_global_norm_constant=str(B), global_squared_norm_constant=str(constant),
        global_U_power=str(exponent), global_log_degree=logs, target_absorption=absorption,
        physical_energy_X_power=str(-1 if delta else 2*alpha-1),
        fixed_log_degree_paid_by_negative_X_power=(delta or 2*alpha-1 < 0),
        complete_finite_residue='c^m*sum_(n<=U)head_atom(n)*n^(-theta)',
        centered_head='K*head-(M_head/theta)*J_theta',
        opposite_drift_retained=True, full_unit_and_x_below_one_retained=True)


def restricted_normal_form(p, m, meter):
    """Compute in the restricted convolution quotient, never insert the answer.

    Keys are (scalar c degree, convolution One degree). Negative One degree
    is mu. This quotient is valid for coefficients n<=U ONLY.
    """
    def product(left, right):
        out = {}
        for (a, b), x in left.items():
            for (c, d), y in right.items():
                key = (a+c, b+d)
                out[key] = out.get(key, Q(0))+x*y
                meter.charge(20)
        return {k: v for k, v in out.items() if v}
    unit, one, mu, scalar = {(0, 0): Q(1)}, {(0, 1): Q(1)}, {(0, -1): Q(1)}, {(1, 0): Q(1)}
    E = plus(unit, product(one, plus(scalar, scale(mu, -1))))
    result = unit
    for atom_value, degree in [(mu, p), (E, m)]:
        for _ in range(degree):
            result = product(result, atom_value)
    return result


def head_search(p, m, meter):
    expected = restricted_normal_form(p, m, meter)
    trials, matches = [], []
    for a in range(p+m+1):
        for degree in range(p+m+1):
            for name in (['One'] if degree == 0 else ['One', 'mu']):
                for scalar in MULTIPLIERS:
                    record = dict(c_power=a, atom=name, convolution_power=degree, multiplier=scalar)
                    candidate = {(a, degree if name == 'One' else -degree): Q(scalar)}
                    record['matches_source_head'] = candidate == expected
                    trials.append(record)
                    if record['matches_source_head']:
                        matches.append(len(trials)-1)
                    meter.charge(25)
    return dict(trials=trials, matched_indices=matches,
        normal_form=[dict(c_power=k[0], One_power=k[1], coefficient=str(v)) for k, v in sorted(expected.items())],
        zero_power_atom_deduplicated=True, identity_scope='coefficients n<=U only; no global equality',
        matching_rule='expand supplied source AST in mu*One=delta quotient, then compare candidate normal forms')


def compile_target(target, alpha, meter):
    p, m, theta = target['p'], target['m'], Q(target['theta'])
    line = target['lines'][target['selected_line']]
    plan = line['plans'][line['selected_plan']]
    sigma, goal = Q(line['sigma']), Q(plan['required_low_U_power'])
    if not (0 < Q(plan['kappa']) < Q(1, 4) and Q(plan['tau']) > 0):
        raise ValueError('valid inherited short-polynomial shell plan required')
    found = head_search(p, m, meter)
    cert = head_certificate(p, m, theta, sigma, alpha, goal)
    programs = []
    for head in [False]+([True] if found['matched_indices'] and cert['target_absorption']['proved'] else []):
        shell_parts = [dict(name='raw_child_high_tail', U_power=plan['high_U_power'], log_degree=0,
            payment=absorb(Q(plan['high_U_power']), 0, goal-1))]
        if head:
            shell_parts.append(dict(name='finite_head_full_norm', U_power=cert['global_U_power'],
                log_degree=cert['global_log_degree'], payment=absorb(Q(cert['global_U_power']), cert['global_log_degree'], goal-1)))
        shell_paid = all(t['payment']['proved'] for t in shell_parts)
        programs.append(dict(id=len(programs), subtract_exact_head=head,
            support_vanishes_through_U=head, transition=compile_transition(p, m, head, meter),
            centering=dict(kind='analytic_residue', full_unit=True,
                source_identity='K*P_raw-(M_raw/theta)*J_theta = centered_head + centered_tail' if head else 'unchanged centered source component',
                all_opposite_drifts_retained=True, source_scalar=target['source_term']['coefficient']),
            low_bound_recovery=dict(kind='two_sided_squared_triangle_with_paid_head' if head else 'identity',
                factor='2' if head else '1', paid_head_constant=(str(2*Q(cert['global_squared_norm_constant'])*Q(cert['target_absorption']['multiplier'])) if head else '0'),
                preserved_U_power=str(goal), original_target_strength_preserved=True),
            moving_height_shell=dict(old_height_U_power=plan['tau'], old_height_prefactor='2',
                child_to_parent_cutoff_ratio_at_most='2', kappa=plan['kappa'],
                extended_kappa=str((Q(plan['kappa'])+Q(1, 4))/2), parts=shell_parts,
                fixed_finite_uniform_constant=True, numerical_constant=None, proved=shell_paid),
            initial_low_norm=dict(U=1, upper='0' if head else str(cert['kernel_global_norm_constant']), proved=True),
            missing_work=dict(status='open', expression='integral_(abs(t)<H(q-1)) weight*(W0+mu(q)*W1+mu(q)^2*W2)*dt/(2*pi)',
                q_power=str(goal-1), quantifier='every integer q>=2, one finite C_work independent of q,U,X,N',
                relation_to_endpoint_goal='optional stronger sufficient requirement; not equivalent',
                head_correction_preserves_this_work_goal=False,
                no_sector_sign_assumed=True, entire_old_height_domain_required=True),
            telescoping=dict(status='conditional_on_signed_work'+('' if shell_paid else '_and_shell'),
                resulting_U_power=str(goal), summation_constant=str(1+1/goal),
                all_integer_cutoffs=True, dyadic_samples_sufficient=False),
            component_bound_proved=False, new_source_payment=False))
        programs[-1]['bound_search'] = BOUNDS.search_bounds(programs[-1], cert, theta, sigma,
            goal, Q(plan['generic_low_U_power']), meter)
    chosen = min(range(len(programs)), key=lambda i: (not programs[i]['support_vanishes_through_U'], i))
    return dict(target_id=target['target_id'], p=p, m=m, theta=str(theta), sigma=str(sigma),
        source_term=target['source_term'], original_low_obligation=target['low_obligation'],
        head_search=found, head_bound=cert, programs=programs, selected_program=chosen,
        selection='proved support cancellation and paid recovery, then enumeration order; no arithmetic scores')


def search(parent, meter):
    if (parent.get('schema') != 'core-weighted-height-feedback-v1' or parent.get('whole_signed_bound_proved') is not False
            or parent.get('RH_proved') is not False):
        raise ValueError('complete preceding open weighted-height feedback required')
    alpha = Q(parent['selected_source_representation']['alpha'])
    eligible = [t for t in parent['weighted_height_targets'] if t['low_obligation'] is not None
                and t['low_obligation']['status'] == 'open_actual_Mobius_bound']
    targets = [compile_target(t, alpha, meter) for t in eligible]
    return dict(schema='core-cutoff-work-search-v1', supplied_rules=RULES, targets=targets,
        diagnostic_spec=DIAGNOSTIC_SPEC, inherited_complete_source_reduction=parent['complete_source_reduction'],
        inherited_bindings=parent['generated_bound_obligations'], inherited_proof_dependencies=parent['proof_dependencies'],
        statistics=dict(targets=len(targets), head_trials=sum(len(t['head_search']['trials']) for t in targets),
            exact_head_matches=sum(len(t['head_search']['matched_indices']) for t in targets),
            transition_programs=sum(len(t['programs']) for t in targets),
            paid_head_auxiliaries=sum(t['head_bound']['target_absorption']['proved'] for t in targets),
            bound_routes=sum(len(p['bound_search']['routes']) for t in targets for p in t['programs']),
            automatically_paid_zero_sectors=sum(p['bound_search']['zero_sector_control']['available']
                and not p['bound_search']['zero_sector_control']['identically_zero'] for t in targets for p in t['programs']),
            closed_low_goals=sum(p['bound_search']['goal_proved'] for t in targets for p in t['programs']),
            new_component_bounds_proved=0),
        source_payment_changed=False, model_calls_in_search=0, fitted_constants=0,
        whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, result, input_file, artifact):
    tasks = [dict(target_id='actual_signed_core', priority=0, status='open',
        search_kind='joint_signed_core_control', preserve='complete inherited signed residual, source cross terms, drifts, unit and -e')]
    for t in result['targets']:
        selected = t['programs'][t['selected_program']]
        tasks.append(dict(target_id=t['target_id'], priority=1, status='open',
            search_kind='bound_actual_cutoff_work_or_physical_localization',
            exact_work=selected['missing_work'], transition=selected['transition'],
            shell=selected['moving_height_shell'], paid_head=t['head_bound'],
            automatic_bound_search=selected['bound_search'],
            next_bound_targets=selected['bound_search']['next_bound_targets'],
            global_target_strength_unchanged=True))
    return dict(schema='core-cutoff-work-feedback-v1', status='open', parent_obligation_file=input_file,
        complete_search_artifact=artifact, selected_source_representation=parent['selected_source_representation'],
        generated_bound_obligations=parent['generated_bound_obligations'],
        complete_source_reduction=parent['complete_source_reduction'],
        retained_original_proof_frontier=parent['retained_original_proof_frontier'],
        auxiliary_bound_targets=parent['auxiliary_bound_targets'], weighted_height_targets=parent['weighted_height_targets'],
        cutoff_work_targets=result['targets'], inherited_next_search_tasks=parent['next_search_tasks'],
        next_search_tasks=tasks, inherited_proof_dependencies=parent['proof_dependencies'],
        new_component_bounds_proved=0, whole_signed_bound_proved=False, RH_proved=False)
