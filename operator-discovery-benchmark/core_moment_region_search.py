"""Search exact compositions of moment regions and analytic residue transfers.

The supplied theorems are trust-base inputs. Contours, reflection, Holder
weights, epsilon margins and source payments are machine-selected. The code
never identifies an analytic residue with an unproved ordinary moment.
"""
import copy
from fractions import Fraction as Q
from itertools import product
from math import ceil

LIBRARY = [
    dict(id='moment2', order='2', lower='1/2', strict=False),
    dict(id='moment4', order='4', lower='1/2', strict=False),
    dict(id='moment6', order='6', lower='7/12', strict=True),
    dict(id='moment8', order='8', lower='5/8', strict=True),
    dict(id='moment10', order='10', lower='41/60', strict=True),
    dict(id='moment12', order='12', lower='5/7', strict=True)]
for _row in LIBRARY:
    _row.update(height_power='1', epsilon_coefficient='1',
        upper='1', upper_strict=True, status='unconditional_external_theorem',
        source=('https://arxiv.org/html/1609.02539v1' if Q(_row['order']) <= 4
                else 'https://arxiv.org/pdf/math/0311403'),
        reference=('fourth moment and Holder; off-line transfer in018'
                   if Q(_row['order']) <= 4 else 'equations(1.3)-(1.5), strict domains'))
DEFAULT_SPEC = dict(sigma_denominator_max=24,
                    library_ids=[r['id'] for r in LIBRARY], target_energy_power='0')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def rational(s):
    require(type(s) is str and len(s) <= 64, 'bounded canonical rational string')
    q = Q(s)
    require(str(q) == s, 'canonical rational string')
    return q


def providers(ids):
    require(type(ids) is list and len(ids) == len(set(ids)), 'unique moment provider identifiers')
    lookup = {r['id']: r for r in LIBRARY}
    require(all(i in lookup for i in ids), 'only unconditional supplied providers')
    require(ids == [r['id'] for r in LIBRARY if r['id'] in ids], 'canonical library order')
    return [lookup[i] for i in ids]


def available(row, line):
    return line < 1 and (line > Q(row['lower']) if row['strict'] else line >= Q(row['lower']))


def vertices(upper):
    result = {v for v in product(*[(Q(0), x) for x in upper]) if sum(v) <= 1}
    for free in range(len(upper)):
        other = [i for i in range(len(upper)) if i != free]
        for corner in product(*[(Q(0), upper[i]) for i in other]):
            v = [Q(0)]*len(upper)
            for i, x in zip(other, corner):
                v[i] = x
            v[free] = 1-sum(corner)
            if 0 <= v[free] <= upper[free]:
                result.add(tuple(v))
    return sorted(result)


def product_bound(factors, library_ids, meter):
    """Complete box-simplex allocation search; fractional absolute powers allowed."""
    require(type(factors) is list and 1 <= len(factors) <= 4, 'one through four zeta factors')
    require(all(type(f) is dict and set(f) == {'real_part', 'power'} for f in factors), 'factor schema')
    parsed = [(rational(f['real_part']), rational(f['power'])) for f in factors]
    require(all(0 < a < 1 and 0 < b <= 128 for a, b in parsed), 'non-pole strip and positive bounded powers')
    library = providers(library_ids)
    best, examined = None, 0
    for reflection in product((False, True), repeat=len(parsed)):
        lines = [1-a if r else a for (a, _), r in zip(parsed, reflection)]
        choices = [[None]+[row for row in library if available(row, a)] for a in lines]
        for rows in product(*choices):
            orders = [Q(row['order']) if row else Q(0) for row in rows]
            upper = [min(Q(1), b/q) if q else Q(0) for (_, b), q in zip(parsed, orders)]
            for weights in vertices(upper):
                examined += 1
                meter.charge(30*len(parsed))
                details, height, slack = [], Q(1), Q(0)
                for (a, b), line, refl, row, q, lam in zip(parsed, lines, reflection, rows, orders, weights):
                    rem = b-q*lam
                    fe = b*(Q(1, 2)-a) if refl else Q(0)
                    pointwise = rem*(1-line)/2
                    height += fe+pointwise
                    slack += rem+lam
                    details.append(dict(original_real_part=str(a), power=str(b), reflected=refl,
                        effective_real_part=str(line), provider_id=row['id'] if row else None,
                        moment_order=str(q), holder_weight=str(lam), convexity_power=str(rem),
                        reflection_height_power=str(fe), convexity_height_power=str(pointwise)))
                trial = dict(factors=details, holder_unused=str(1-sum(weights)),
                             integral_height_power=str(height), epsilon_coefficient=str(slack))
                if best is None or (height, slack) < (Q(best['integral_height_power']), Q(best['epsilon_coefficient'])):
                    best = trial
    return dict(best=best, allocations_examined=examined,
                completeness='all supplied moment regions, reflections and Holder box-simplex vertices')


def contour_grid(theta, maximum):
    require(type(maximum) is int and 2 <= maximum <= 48, 'contour denominator bound2..48')
    return sorted({Q(n, d) for d in range(2, maximum+1) for n in range(1, d)
                   if Q(n, d) < min(Q(1, 2), theta)})


def candidate(p, m, theta, rho, sigma, library_ids, meter):
    theta, rho, sigma = map(Q, (theta, rho, sigma))
    require(type(p) is int and 0 <= p <= 16 and type(m) is int and 2 <= m <= 64,
            'finite polynomial powers')
    require(0 < rho < 1 and 0 < sigma < min(Q(1, 2), theta) and theta < 1,
            'belowhalf contour below kernel pole and growing cutoff')
    factors = [[dict(real_part=str(sigma+1-theta), power='2')],
               [dict(real_part=str(sigma), power=str(2*m)),
                dict(real_part=str(sigma+1-theta), power='2')]]
    branches = [product_bound(f, library_ids, meter) for f in factors]
    tails = [Q(b['best']['integral_height_power'])-2 for b in branches]
    slack = max(Q(b['best']['epsilon_coefficient']) for b in branches)
    epsilon = min(Q(1), -max(tails)/(2*(1+slack))) if max(tails) < 0 else None
    costs = [d+epsilon*Q(b['best']['epsilon_coefficient']) for d, b in zip(tails, branches)] if epsilon else None
    up = 2*(p+m)*(1-sigma)
    energy = 2*sigma-1+rho*up
    failures = []
    if epsilon is None:
        failures.append('global_Mellin_height_tail_not_summable')
    if energy > 0:
        failures.append('finite_factor_cost_exceeds_subpower_target')
    return dict(sigma=str(sigma), moment_branches=branches, mellin_height_powers=list(map(str, tails)),
        epsilon=str(epsilon) if epsilon else None,
        paid_height_powers=list(map(str, costs)) if costs else None,
        full_finite_factor_U_power=str(up), residue_squared_U_power=str(2*(p+m)*(1-theta)),
        recovered_energy_N_power=str(energy), target_met=not failures, failed_premises=failures,
        centering=dict(kind='analytic_residue', ordinary_coefficient_moment_required=False,
            ordinary_coefficient_moment_claimed=False, exact_moment='A(theta)^p*E(theta)^m',
            coefficient='K*A^p*E^m-(A(theta)^p*E(theta)^m/theta)*J_theta',
            unit_included=True, whole_x_below_one_tail_included=True,
            pole_at_one_removed_by='c=A(1) in E(s)=1+zeta(s)*(c-A(s))'),
        norm_statement='sum_(n>=1)|complete centered prefix(n)|^2*n^(-2sigma-1)<=C_norm*U^b',
        integer_cell_correction=dict(integral_multiplier='8', residue_multiplier='32',
            residue_denominator=str(2+2*sigma-2*theta)),
        constants_uniform_in=['U', 'N', 'X'],
        constants_may_depend_on=['p', 'm', 'theta', 'sigma', 'epsilon'],
        generic_bounded_weights_same_U_power=True)


def target_search(t, rho, spec, meter):
    p, m, theta = t['p'], t['m'], Q(t['theta'])
    trials = [candidate(p, m, theta, rho, sigma, spec['library_ids'], meter)
              for sigma in contour_grid(theta, spec['sigma_denominator_max'])]
    eligible = [i for i, c in enumerate(trials) if c['target_met']]
    selected = min(eligible, key=lambda i: (Q(trials[i]['recovered_energy_N_power']),
        max(Q(h) for h in trials[i]['paid_height_powers']), i)) if eligible else None
    return dict(target_id=t['target_id'], p=p, m=m, theta=t['theta'], source_term=copy.deepcopy(t['source_term']),
        inherited_component_paid=t['component_bound_proved'], trials=trials, selected=selected,
        analytic_centered_bound_proved=selected is not None,
        new_source_payment=selected is not None and not t['component_bound_proved'],
        optimistic_moment_diagnostic=ideal_moment_envelope(p, m, rho),
        constant='C_region_'+t['target_id'] if selected is not None else None)


def ideal_moment_envelope(p, m, rho):
    """Lower bound on this proof envelope, NOT an arithmetic lower bound."""
    r = Q(rho)*(p+m)
    threshold = Q(m-1, 2*m)
    floor = (-1+r*(m+1))/m if r < Q(1, 2) else min(2*r-1, r)
    return dict(assumption='hypothetically grant all moments O(T^(1+epsilon)) on every fixed line >=1/2',
        reflected_tail_requires_sigma_above=str(threshold),
        optimistic_energy_infimum=str(floor),
        cutoff_alone_obstructs=r >= Q(1, 2),
        stronger_moment_library_alone_insufficient=floor >= 0,
        scope='only the full finite absolute-mass envelope in this belowhalf contour grammar',
        arithmetic_impossibility_claimed=False,
        next_mechanism='signed finite-factor or joint-correlation control; preserve source cross terms')


def channel_constant(channels, sigma):
    total = Q(0)
    for ch in channels:
        eta = rational(ch['eta'])
        require(eta >= 0, 'nonnegative channel logarithmic normalization')
        coeff = [rational(c) for c in ch['polynomial']]
        require(coeff, 'nonempty channel polynomial')
        a = sum(map(abs, coeff))
        b = sum(j*abs(c) for j, c in enumerate(coeff))
        total += (Q(2)**ceil(eta)*(a+2*(1+1/sigma)*b))**2
    return total


def original_transport(binding):
    while 'transport_program' not in binding:
        binding = binding['inherited_binding']
    return binding['transport_program']


def reduction(parent, context, targets, meter):
    paid = [t for t in targets if t['new_source_payment']]
    programs = {p['id']: p for p in context['channel_programs']}
    require(len(programs) == len(context['channel_programs']), 'unique channel programs')
    require(set(programs) == {b['parent_obligation_id'] for b in parent['generated_bound_obligations']},
            'every original channel binding')
    rho = Q(parent['selected_source_representation']['alpha'])
    bindings = []
    for index, old in enumerate(parent['generated_bound_obligations']):
        require(old['recovery'] == 'S_g<=4*S_Z+4*C_new+2*C_old; S_Z<=4*S_g+4*C_old+2*C_new',
                'licensed inherited source-recovery coefficients')
        program = programs[old['parent_obligation_id']]
        require(original_transport(old) == program['transport_program'], 'unaltered transport')
        costs = []
        for t in paid:
            c = t['trials'][t['selected']]
            sigma, up = Q(c['sigma']), Q(c['full_finite_factor_U_power'])
            cc = channel_constant(program['construction']['channels'], sigma)
            local = Q(2)**ceil(2*sigma+1+2*rho*up)
            costs.append(dict(target_id=t['target_id'], constant=t['constant'],
                channel_squared_constant=str(cc), local_cutoff_constant=str(local),
                rational_multiplier=str(len(paid)*Q(t['source_term']['coefficient'])**2*cc*local),
                energy_X_power=c['recovered_energy_N_power']))
            meter.charge(100+100*len(program['construction']['channels']))
        bindings.append(dict(parent_obligation_id=old['parent_obligation_id'], inherited_binding_index=index,
            paid_constant_terms=costs, residual_goal=dict(old['sufficient_goal'],
                expression='S_Z033(X), complete signed residual after all listed payments', status='open'),
            forward='S_g<=8*S_Z033+8*C_033+4*C_prev+2*C_old',
            reverse='S_Z033<=8*S_g+8*C_old+4*C_prev+2*C_033',
            whole_signed_bound_proved=False, RH_proved=False))
    return dict(exact_identity='g=P_old+P_033+Z033; Z033=Z_previous-P_033',
        paid_components=[dict(target_id=t['target_id'], source_term=t['source_term'],
            centered_component='source_coefficient*(K*A^p*E^m-M_analytic*J_theta/theta)',
            retained_opposite_drift='source_coefficient*M_analytic*J_theta/theta',
            ordinary_coefficient_moment_claimed=False) for t in paid],
        bindings=bindings, complete_source_retained=True, all_cross_terms_retained=True,
        transport_error_retained='-e', common_horizon='N=4X-1 for BOTH blocks; same U',
        new_residual_expression='Z_previous minus only the listed analytic-centered paid components',
        whole_signed_bound_proved=False, RH_proved=False)


def cube_composition(parent, targets):
    old = parent['cutoff_work_targets'][0]
    require((old['p'], old['m'], old['theta']) == (2, 3, '2/3'), 'current finite cube source adapter')
    t = next(t for t in targets if t['target_id'] == old['target_id'])
    rho = Q(parent['selected_source_representation']['alpha'])
    require(rho == Q(1, 24), 'current inherited finite-cube cutoff')
    saved = parent['complete_convolution_search']['centered_transfer']
    chosen = saved['trials'][saved['selected']] if saved['selected'] is not None else None
    head = old['head_bound']
    require((head['atom'], head['convolution_power'], head['c_power'], head['centered_prefix_U_power'],
             head['centered_prefix_constant']) == ('One', 1, 3, '1', '12'), 'complete certified head')
    require(old['source_term'] == t['source_term'], 'same original centered cube component')
    component, finite = [], []
    if t['selected'] is not None:
        c = t['trials'][t['selected']]
        component = [dict(constant=t['constant'], multiplier='2', N_power=c['recovered_energy_N_power'], log_degree=0),
                     dict(constant='1', multiplier='288', N_power=str(2*rho-1), log_degree=0)]
        if chosen is not None:
            finite = [dict(r, multiplier=str(2*Q(r['multiplier']))) for r in component]
            finite += [dict(constant='1', multiplier=str(2*Q(r['constant'])), N_power=r['N_power'],
                            log_degree=r['log_degree']) for r in chosen['normalized_error_energy']]
    return dict(target_id=t['target_id'], full_source='F=A^2*E^3-c^3*One_[1,U]',
        finite_source='F_R=A^2*(E restricted<=floor(N^beta))^3-c^3*One_[1,U]',
        analytic_full_moment='A(theta)^2*E(theta)^3-c^3*D(theta)',
        same_head_and_full_moment_defect_retained=True, selected_transfer=copy.deepcopy(chosen),
        full_component_energy_terms=component, finite_cube_energy_terms=finite,
        complete_component_bound_proved=bool(component), finite_cube_bound_proved=bool(finite),
        original_fixed_sigma_low_Gram_proved=False, full_core_bound_proved=False,
        energy='N^-2*sum_(1<=n<=N)|complete centered prefix(n)|^2',
        domain='integer U,N>=1, U<=N^(1/24); same N and r over whole prefix',
        ordinary_cubic_coefficient_moment_claimed=False)


def search(parent, context, spec, meter):
    require(parent['schema'] == 'core-complete-convolution-feedback-v1', 'accepted stage032 input')
    require(set(spec) == set(DEFAULT_SPEC) and spec['target_energy_power'] == '0', 'subpower search specification')
    providers(spec['library_ids'])
    join = parent['complete_source_reduction']['inherited_complete_signed_join']
    require(context['complete_signed_join'] == join, 'original full source context')
    ts = parent['auxiliary_bound_targets']
    require(len({t['target_id'] for t in ts}) == len(ts), 'unique component targets')
    for t in ts:
        require(t['theta'] == '2/3', 'actual source K(n)=n^(-1/3)')
        require(t['source_term'] in join['collected_terms'], 'component belongs to original signed source')
        require(t['source_term']['powers'] == [t['p'], 0, 1, t['m'], 0, 0, 0, 0], 'full A^p K E^m source AST')
    rho = Q(parent['selected_source_representation']['alpha'])
    targets = [target_search(t, rho, spec, meter) for t in ts]
    all_trials = [c for t in targets for c in t['trials']]
    cube = cube_composition(parent, targets)
    graph = [dict(id='supplied_moments', dependencies=[], proved=True),
             dict(id='analytic_residue_bridge', dependencies=[], proved=True),
             dict(id='inherited_head_and_transfer', dependencies=[], proved=True)]
    graph += [dict(id='norm:'+t['target_id'], dependencies=['supplied_moments', 'analytic_residue_bridge'],
                   proved=t['analytic_centered_bound_proved']) for t in targets]
    graph += [dict(id='source_reduction', dependencies=['norm:'+t['target_id'] for t in targets
                                                     if t['new_source_payment']], proved=True),
              dict(id='finite_cube', dependencies=['norm:'+cube['target_id'], 'inherited_head_and_transfer'],
                   proved=cube['finite_cube_bound_proved']),
              dict(id='remaining_joint_residual', dependencies=[], proved=False),
              dict(id='full_signed_core', dependencies=['source_reduction', 'remaining_joint_residual'], proved=False)]
    # One structural proof, valid for ALL |a_n|<=1; no synthetic arithmetic samples.
    ablation = dict(weights='arbitrary complex |a_n|<=1, c=sum_(n<=U)a_n/n',
        finite_A_bound='U^(1-sigma)/(1-sigma)',
        finite_c_minus_A_bound='2*U^(1-sigma)/(1-sigma)',
        identical_moment_trials=True, identical_U_powers=True,
        additional_logU_loss=0, arithmetic_power_advantage=False,
        generic_centers_are_their_own_analytic_residues=True,
        generic_finite_cube_composition_claimed=False)
    return dict(schema='core-moment-region-search-v1', spec=copy.deepcopy(spec), library=copy.deepcopy(LIBRARY),
        supplied_rules=['CORE_MOMENT_REGION_REVIEW_033.txt', 'CORE_MOMENT_REGION_CHECK_033.txt'],
        rho=str(rho), targets=targets, source_reduction=reduction(parent, context, targets, meter),
        cube_composition=cube, ablation=ablation, proof_dependencies=graph,
        statistics=dict(targets=len(targets), contour_trials=len(all_trials),
            moment_allocations=sum(b['allocations_examined'] for c in all_trials for b in c['moment_branches']),
            paid_analytic_components=sum(t['analytic_centered_bound_proved'] for t in targets),
            new_source_payments=sum(t['new_source_payment'] for t in targets),
            original_bindings=len(parent['generated_bound_obligations']),
            actual_source_observations=0, runtime_model_calls=0, fitted_constants=0),
        formal_proof_assistant_verified=False, whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, result, artifact):
    out = copy.deepcopy(parent)
    out.update(schema='core-moment-region-feedback-v1', status='moment_regions_verified_core_open',
        parent_obligation_file='candidate10_complete_convolution_obligation.json',
        moment_region_artifact=artifact, moment_region_search=copy.deepcopy(result),
        new_component_bounds_proved=result['statistics']['new_source_payments'])
    out['inherited_moment_region_tasks'] = copy.deepcopy(parent['next_search_tasks'])
    tasks = [dict(parent['next_search_tasks'][0], residual_reference='moment_region_search.source_reduction',
        next_action='search joint control of the complete residual Z033, including all opposite analytic drifts')]
    tasks += [dict(priority=1, search_kind='unpaid_analytic_centered_component', target_id=t['target_id'],
        p=t['p'], m=t['m'], theta=t['theta'], status='open',
        moment_library_alone_insufficient=t['optimistic_moment_diagnostic']['stronger_moment_library_alone_insufficient'],
        requirement='signed finite-factor/correlation control with complete source recovery'
            if t['optimistic_moment_diagnostic']['stronger_moment_library_alone_insufficient']
            else 'new moment or signed finite-factor/correlation control with complete source recovery')
        for t in result['targets'] if not t['analytic_centered_bound_proved']]
    tasks += [dict(priority=1, search_kind='joint_opposite_analytic_drift_control', status='open',
        paid_components=[t['target_id'] for t in result['targets'] if t['new_source_payment']],
        requirement='retain and bound drift jointly with the remaining original source, not separately erase it')]
    tasks += [dict(priority=2, search_kind='original_fixed_sigma_Mellin_target', status='open',
        target_id=parent['cutoff_work_targets'][0]['target_id'],
        requirement='alternate physical component proof does not pay the old fixed-line U^(12/5) Gram claim')]
    out['next_search_tasks'] = tasks
    return out
