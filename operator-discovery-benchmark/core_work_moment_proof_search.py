"""Try uniform proofs of generated work moments, using a supplied rule library.

The source remains the complete signed polynomial. Absolute estimates are
explicit proof attempts, not replacements for that source or arithmetic
assumptions. No finite observations or fitted exponents enter this search.
"""
import copy
from fractions import Fraction as Q
from math import comb

import core_cutoff_work_search as ALG
import core_cutoff_prefix_projections as PREFIX
import core_moment_bound_search as MOMENT

DEFAULT_SPEC = dict(event_weights=['-1', '-1/2', '0', '1/6', '1/3', '1/2', '2/3', '1', '3/2', '2'],
                    moment_orders=['2', '4'], epsilon='1/1000')
REPRESENTATIONS = ['collected_sectors', 'signed_virtual_branches',
                   'substituted_virtual_branches', 'polarized_increment', 'two_child_energies']
require = PREFIX.require


def decode(rows):
    return {tuple(t['monomial']): Q(t['coefficient']) for t in rows}


def substitute(poly, replacements, meter):
    result = {}
    for key, coefficient in poly.items():
        term = {(): coefficient}
        for symbol in key:
            term = ALG.multiply(term, replacements.get(symbol, ALG.atom(symbol)), meter)
        result = ALG.plus(result, term)
    return result


def add_envelopes(*values):
    out = {}
    for value in values:
        for key, coefficient in value.items():
            out[key] = out.get(key, Q(0))+coefficient
    return {key: c for key, c in out.items() if c}


def multiply_envelopes(left, right, meter):
    out = {}
    for (r, k), a in left.items():
        for (s, j), b in right.items():
            key = (r+s, k+j)
            out[key] = out.get(key, Q(0))+a*b
            meter.charge(30)
    return out


def envelope_rows(value):
    return [dict(q_power=str(r), zeta_power=k, constant=str(c)) for (r, k), c in sorted(value.items())]


def parse_envelope(rows):
    return {(Q(t['q_power']), t['zeta_power']): Q(t['constant']) for t in rows}


def polynomial_envelope(poly, sigma, meter):
    """Absolute coefficient envelope; E uses its coupled c-A definition."""
    sigma = Q(sigma)
    require(0 < sigma < 1, 'finite coefficient majorants on the open strip')
    output = {}
    for symbols, coefficient in poly.items():
        counts = {s: symbols.count(s) for s in set(symbols)}
        require(set(counts) <= {'A', 'Abar', 'D', 'Dbar', 'E', 'Ebar', 'c', 'a', 'b', 'bbar', 'z', 'zbar', 'v'},
                'every real and conjugate source symbol has a licensed envelope')
        ad = sum(counts.get(s, 0) for s in ('A', 'Abar', 'D', 'Dbar'))
        e = counts.get('E', 0)+counts.get('Ebar', 0)
        phase = counts.get('b', 0)+counts.get('bbar', 0)
        z = counts.get('z', 0)+counts.get('zbar', 0)
        base_power = ad*(1-sigma)-counts.get('a', 0)-phase*sigma
        constant = abs(coefficient)*2**counts.get('c', 0)/(1-sigma)**ad
        for i in range(e+1):
            key = (base_power+i*(1-sigma), z+i)
            term = constant*comb(e, i)*(2+1/(1-sigma))**i
            output[key] = output.get(key, Q(0))+term
            meter.charge(50+len(symbols))
    return output


def maximum_branch_envelope(branches):
    keys = set().union(*(p.keys() for p in branches))
    return {key: max(p.get(key, Q(0)) for p in branches) for key in keys}


def source_envelopes(transition, sigma, meter):
    """Enumerate exact source presentations before applying inequalities."""
    child = decode(transition['child'])
    children = {e: substitute(child, {'x': {(): Q(e)}, 'v': {(): Q(1)}}, meter)
                for e in (0, 1, -1)}
    square = lambda p: ALG.multiply(p, ALG.conjugate(p), meter)
    zero_square = square(children[0])
    joined = {e: ALG.plus(square(children[e]), ALG.scale(zero_square, -1)) for e in (1, -1)}
    sectors = [decode(p) for p in transition['work_sectors']]
    for e in (1, -1):
        expected = substitute(ALG.plus(ALG.scale(sectors[1], e), sectors[2]), {'v': {(): Q(1)}}, meter)
        require(joined[e] == expected, 'exact actual-minus-zero work, with every signed cross retained')
    E = ALG.plus({(): Q(1)}, ALG.plus({('c', 'z'): Q(1)}, {('A', 'z'): Q(-1)}))
    replacements = {'E': E, 'Ebar': ALG.conjugate(E)}
    candidates = {}
    candidates['collected_sectors'] = add_envelopes(*(polynomial_envelope(p, sigma, meter) for p in sectors[1:]))
    candidates['signed_virtual_branches'] = maximum_branch_envelope(
        [polynomial_envelope(joined[e], sigma, meter) for e in (1, -1)])
    candidates['substituted_virtual_branches'] = maximum_branch_envelope(
        [polynomial_envelope(substitute(joined[e], replacements, meter), sigma, meter) for e in (1, -1)])
    zero = polynomial_envelope(children[0], sigma, meter)
    polarized, separate = [], []
    for e in (1, -1):
        increment = ALG.plus(children[e], ALG.scale(children[0], -1))
        delta = polynomial_envelope(increment, sigma, meter)
        cross = multiply_envelopes(zero, delta, meter)
        polarized.append(add_envelopes({key: 2*c for key, c in cross.items()}, multiply_envelopes(delta, delta, meter)))
        branch = polynomial_envelope(children[e], sigma, meter)
        separate.append(add_envelopes(multiply_envelopes(branch, branch, meter), multiply_envelopes(zero, zero, meter)))
    candidates['polarized_increment'] = maximum_branch_envelope(polarized)
    candidates['two_child_energies'] = maximum_branch_envelope(separate)
    return dict(branches={str(e): ALG.encode(joined[e]) for e in (1, -1)},
        representations=[dict(id=name, envelope=envelope_rows(candidates[name]),
            squared_envelope=envelope_rows(multiply_envelopes(candidates[name], candidates[name], meter)))
            for name in REPRESENTATIONS],
        meaning='abs(j_q) <= sum constant*q^q_power*abs(zeta(s))^zeta_power',
        source_signs_retained=True, mu_zero_joined_work_is_zero=True,
        zero_mu_history_and_head_retained=True, cached_samples_used=False)


def summed_power(power):
    power = Q(power)
    return dict(B_power=str(max(Q(0), power+1)), log_degree='1' if power == -1 else '0')


def envelope(power, logs=0):
    return dict(B_power=str(Q(power)), log_degree=str(Q(logs)))


def cost(bound):
    return Q(bound['B_power']), Q(bound['log_degree'])


def max_envelope(values):
    return max(values, key=cost) if values else envelope(0)


def height_bound(moment, tau, epsilon):
    """Compact head plus geometric dyadic summation, with explicit slack."""
    h = Q(moment['best']['integral_height_power'])-2
    c = Q(moment['best']['epsilon_coefficient'])
    tau, epsilon = Q(tau), Q(epsilon)
    require(tau > 0 and epsilon > 0 and c >= 0, 'positive height and epsilon, nonnegative moment slack')
    if h < 0:
        epsilon = min(epsilon, -h/(2*(1+c)))
    exponent = h+c*epsilon
    return dict(dyadic_power_before_epsilon=str(h), epsilon=str(epsilon), epsilon_coefficient=str(c),
        dyadic_power=str(exponent), compact_head_retained=True, measure='dt/(2*pi)', denominator='abs(s)^2',
        common_height='2*(2*B)^tau', tau=str(tau),
        bound=envelope(tau*max(Q(0), exponent), 1 if exponent == 0 else 0),
        full_height_bound_available=exponent < 0,
        constant='fixed finite; depends on contour and chosen epsilon, never B,V,X,N')


def moment_library(representations, sigma, u, tau, spec, meter):
    powers = sorted({r['zeta_power'] for p in representations for key in ('envelope', 'squared_envelope') for r in p[key]} |
                    {2*r['zeta_power'] for p in representations for r in p['envelope']})
    library = []
    for k in powers:
        factors = ([dict(real_part=str(Q(sigma)), power=str(k))] if k else [])+[
            dict(real_part=str(Q(sigma)+Q(u)), power='2')]
        result = MOMENT.product_moment_search(factors, spec['moment_orders'], meter)
        library.append(dict(zeta_power=k, factors=factors, moment=result,
            height=height_bound(result, tau, spec['epsilon'])))
    return library


def direct_bound(rows, heights, meter):
    terms, floors = [], []
    for row in rows:
        q = summed_power(row['q_power']); h = heights[row['zeta_power']]['bound']
        terms.append(dict(q_power=row['q_power'], zeta_power=row['zeta_power'], constant=row['constant'],
            bound=envelope(Q(q['B_power'])+Q(h['B_power']), Q(q['log_degree'])+Q(h['log_degree']))))
        floors.append(q)
        meter.charge(60)
    bound = max_envelope([t['bound'] for t in terms])
    return dict(method='sum_event_L1', term_count=len(terms),
                bottleneck_terms=[t for t in terms if cost(t['bound']) == cost(bound)], bound=bound,
                coefficient_cost_floor=max_envelope(floors), coefficient_floor_is_not_a_bound_on_actual_work=True,
                theorem='M_common(B) <= sum_(q=2..2B) integral kappa*abs(j_q) dt/(2*pi)',
                uniform_in=['B', 'V', 'projection', 'X', 'N'])


def label_weight(program, gamma):
    gamma = Q(gamma)
    require(gamma >= 0, 'nonnegative label exponent')
    fixed = program['projection'] == 'smooth' and program['prime_program']['kind'] == 'fixed'
    return dict(q_power='0' if fixed else str(gamma),
        multiplier=('max(1,p^gamma), p='+str(program['prime_program']['fixed_prime'])) if fixed else '1',
        rule='label in {1,p}' if fixed else '1 <= label <= q',
        constant_may_depend_on_fixed_prime=fixed, constant_may_depend_on_gamma=True)


def gram_attempt(rep, weight, heights, method, alpha, meter):
    g = Q(weight['q_power']); terms, floors = [], []
    if method == 'weighted_event_Cauchy':
        a = Q(alpha); mass = summed_power(-a)
        for row in rep['squared_envelope']:
            q = summed_power(Q(row['q_power'])+g+a); h = heights[row['zeta_power']]['bound']
            terms.append(dict(q_power=row['q_power'], zeta_power=row['zeta_power'], constant=row['constant'],
                bound=envelope(Q(mass['B_power'])+Q(q['B_power'])+Q(h['B_power']),
                               Q(mass['log_degree'])+Q(q['log_degree'])+Q(h['log_degree']))))
            floors.append(envelope(Q(mass['B_power'])+Q(q['B_power']), Q(mass['log_degree'])+Q(q['log_degree'])))
            meter.charge(70)
        rule = 'Q_gamma <= sup_label(sum_in_label q^(-alpha))*sum_q label(q)^gamma*q^alpha*integral kappa*abs(j_q)^2'
    elif method == 'weighted_label_Minkowski':
        require(alpha is None, 'Minkowski has no event mass parameter')
        mass = None
        for row in rep['envelope']:
            q = summed_power(Q(row['q_power'])+g/2); h = heights[2*row['zeta_power']]['bound']
            terms.append(dict(q_power=row['q_power'], zeta_power=2*row['zeta_power'], constant=row['constant'],
                bound=envelope(2*Q(q['B_power'])+Q(h['B_power']), 2*Q(q['log_degree'])+Q(h['log_degree']))))
            floors.append(envelope(2*Q(q['B_power']), 2*Q(q['log_degree'])))
            meter.charge(70)
        rule = 'sqrt(Q_gamma) <= sum_q label(q)^(gamma/2)*norm_L2(kappa)(j_q); retain complete vector norm'
    else:
        raise ValueError('licensed norm-composition method')
    bound = max_envelope([t['bound'] for t in terms])
    return dict(representation=rep['id'], method=method, event_weight=alpha, label_weight=weight,
        event_mass=mass, term_count=len(terms),
        bottleneck_terms=[t for t in terms if cost(t['bound']) == cost(bound)], bound=bound, rule=rule,
        coefficient_cost_floor=max_envelope(floors), coefficient_floor_is_not_a_bound_on_actual_work=True,
        every_signed_cross_in_source=True, proved_uniform_bound=True,
        constant='fixed finite; no numerical value fitted', target_assumed_in_proof=False)


def meets(bound, required):
    return cost(bound) <= (Q(required['B_power']), Q(required['log_degree']))


def source_binding(parent, meter):
    require(parent['schema'] == 'core-cutoff-prefix-projection-feedback-v1', 'published complete-prefix target')
    binding = PREFIX.source_binding(dict(parent, schema='core-cutoff-prime-orbit-feedback-v1'), meter)
    require(binding == parent['prefix_projection_search']['binding'], 'complete unchanged signed work')
    PREFIX.require(parent['prefix_projection_search']['catalogue'] == PREFIX.program_catalogue(), 'all generated projections')
    return binding


def search(parent, spec, meter):
    require(spec == DEFAULT_SPEC, 'declared bounded proof grammar')
    binding = source_binding(parent, meter)
    target = parent['cutoff_work_targets'][0]
    program = target['programs'][target['selected_program']]
    require((target['p'], target['m'], target['sigma'], target['theta']) == (2, 3, '9/20', '2/3'),
            'current supported complete head-corrected source')
    source = source_envelopes(program['transition'], target['sigma'], meter)
    inherited = parent['prefix_projection_search']['proof_search']
    require(inherited == PREFIX.proof_search(dict(parent, schema='core-cutoff-prime-orbit-feedback-v1'), binding, meter),
            'complete inherited projection and moment targets reproducible from the source')
    tau = inherited['common_window']['H']['U_power']
    library = moment_library(source['representations'], target['sigma'], 1-Q(target['theta']), tau, spec, meter)
    heights = {v['zeta_power']: v['height'] for v in library}
    direct = [dict(representation=r['id'], **direct_bound(r['envelope'], heights, meter)) for r in source['representations']]
    selected_direct = min(range(len(direct)), key=lambda i: (*cost(direct[i]['bound']), direct[i]['term_count'], i))
    attempts, tasks = [], []
    # Proofs depend on label-weight geometry and gamma, not on finite scores.
    cache = {}
    for p in parent['prefix_projection_search']['catalogue']:
        route = inherited['programs'][p['id']]
        for g in route['gram_auxiliaries']:
            weight = label_weight(p, g['gamma'])
            key = tuple(sorted(weight.items()))
            if key not in cache:
                choices = []
                for rep in source['representations']:
                    for a in spec['event_weights']:
                        choices.append(gram_attempt(rep, weight, heights, 'weighted_event_Cauchy', a, meter))
                    choices.append(gram_attempt(rep, weight, heights, 'weighted_label_Minkowski', None, meter))
                selected = min(range(len(choices)), key=lambda i: (*cost(choices[i]['bound']), choices[i]['term_count'], i))
                cache[key] = len(attempts)
                attempts.append(dict(id=len(attempts), label_weight=weight, candidates=choices, selected=selected))
            aid = cache[key]; best = attempts[aid]['candidates'][attempts[aid]['selected']]
            floor = min((c['coefficient_cost_floor'] for c in attempts[aid]['candidates']), key=cost)
            closed = meets(best['bound'], g['sufficient_bound'])
            tasks.append(dict(program_id=p['id'], gamma=g['gamma'], attempt_id=aid,
                required=copy.deepcopy(g['sufficient_bound']), established=copy.deepcopy(best['bound']),
                best_coefficient_cost_floor=floor,
                excluded_by_coefficient_cost_floor=not meets(floor, g['sufficient_bound']),
                requested_bound_proved=closed, gap_B_power=str(Q(best['bound']['B_power'])-Q(g['sufficient_bound']['B_power'])),
                uniform_domain='all dyadic B>=1 and every integer B<V<=2B',
                status='requested_bound_proved' if closed else 'weaker_uniform_bound_proved_target_open'))
    return dict(schema='core-work-moment-proof-search-v1', spec=copy.deepcopy(spec), binding=binding,
        source=source, moment_library=library, direct_attempts=direct, selected_direct=selected_direct,
        Gram_attempt_classes=attempts, targets=tasks,
        trust=dict(review='CORE_WORK_MOMENT_PROOF_RULE_REVIEW_028.txt',
            inherited_moment_rules=MOMENT.RULES, formal_proof_assistant_verified=False),
        statistics=dict(source_presentations=len(source['representations']), moment_products=len(library),
            distinct_Gram_proof_searches=len(attempts), Gram_argument_candidates=sum(len(a['candidates']) for a in attempts),
            requested_Gram_bounds=len(tasks), requested_Gram_bounds_proved=sum(t['requested_bound_proved'] for t in tasks),
            targets_excluded_even_without_height_cost=sum(t['excluded_by_coefficient_cost_floor'] for t in tasks),
            direct_grouped_bound_proved=True, direct_grouped_goal_proved=meets(direct[selected_direct]['bound'],
                dict(B_power=binding['inherited_bound']['power'], log_degree=0))),
        scope='uniform bounds conditional only on declared unconditional analytic trust base; no finite-source observations',
        whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, result, artifact):
    out = copy.deepcopy(parent)
    out.update(schema='core-work-moment-proof-feedback-v1', status='automatic_work_moment_proof_attempts_complete',
        parent_obligation_file='candidate10_cutoff_prefix_projection_obligation.json', complete_search_artifact=artifact)
    out['work_moment_proof_search'] = copy.deepcopy(result)
    out['inherited_work_moment_tasks'] = copy.deepcopy(parent['next_search_tasks'])
    out['next_search_tasks'] = [copy.deepcopy(parent['next_search_tasks'][0])]
    for winner in parent['prefix_projection_search']['selection']['selected']:
        ident = winner['program_id']
        attempted = [t for t in result['targets'] if t['program_id'] == ident]
        out['next_search_tasks'].append(dict(priority=1, target_id=result['binding']['target_id'],
            search_kind='search_signed_work_arguments_after_uniform_moment_attempts', status='open',
            program=parent['prefix_projection_search']['catalogue'][ident],
            precise_Gram_attempts=attempted,
            best_direct_grouped_bound=result['direct_attempts'][result['selected_direct']]['bound'],
            signed_source_ref='work_moment_proof_search.binding.inherited_bound.R_q',
            allowed_next_mechanisms=['exact_signed_group_identity', 'controlled_cross_correlation', 'uniform_scale_recurrence'],
            failure_scope='only the enumerated absolute-polynomial and unconditional moment proof language',
            arithmetic_bound_refuted=False, complete_source_preserved=True,
            original_goal_and_all_alternatives_retained=True))
    out['next_search_tasks'].extend(copy.deepcopy(parent['next_search_tasks'][1:]))
    return out
