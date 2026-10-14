"""Complete-prefix factor projections and generated weighted Gram obligations.

The finite search reuses preserved work samples. Universal factor identities,
mask recovery, and Cauchy compose conditional proof routes; no finite score is
a continuous moment theorem. No arithmetic source is generated here.
"""
import copy
from fractions import Fraction as Q
from flint import arb

import core_cutoff_prime_orbits as PREVIOUS

HEIGHTS = PREVIOUS.HEIGHTS
DISCOVERY = [64, 128, 256, 512]
EVALUATION = [1024]
GAMMAS = ['0', '1/6', '1/3', '1/2', '2/3', '1', '3/2']
LANES = [a+':'+b for a in ('fixed', 'prefix', 'window') for b in ('rough', 'smooth')]
require, ball = PREVIOUS.require, PREVIOUS.ball


def program_catalogue():
    programs = []
    for base in PREVIOUS.program_catalogue():
        for projection in ('rough', 'smooth'):
            programs.append(dict(id=len(programs), parent_program_id=base['id'], projection=projection,
                                 lane=base['lane']+':'+projection, prime_program=base))
    return programs


def prime_table(N, meter):
    flags = [True]*(N+1)
    flags[:2] = [False, False]
    for p in range(2, N+1):
        if flags[p]:
            for n in range(p*p, N+1, p):
                flags[n] = False
                meter.charge(1)
    meter.charge(3*(N+1))
    return flags


def group_case(program, B, samples, meter):
    require(program in program_catalogue(), 'complete sealed factor projection')
    require(type(B) is int and 1 <= B <= 1024 and B & (B-1) == 0 and
            samples['start'] == 2 and samples['end'] >= 2*B and samples['heights'] == HEIGHTS,
            'complete initial prefix and declared partial endpoint block')
    primes = PREVIOUS.selected_primes(program['prime_program'], B, meter)
    is_prime = prime_table(2*B, meter)
    rows = samples['records'][:2*B-1]
    require([r['q'] for r in rows] == list(range(2, 2*B+1)), 'every initial and current event')
    groups, members = {}, {}
    total_cost, peak, baseline, odd_total, even_total = [arb(0) for _ in range(5)]
    initial, zeros, curve = arb(0), 0, []
    for row in rows:
        q, x = row['q'], row['mu']
        require(x == samples['mu'][q] and type(x) is int and x in (-1, 0, 1), 'actual source event')
        if x == 0:
            zeros += 1
        else:
            a, b = 1, q
            for p in primes:
                if b % p == 0:
                    a *= p; b //= p
                    require(b % p != 0, 'squarefree event only')
                meter.charge(4)
            require(a*b == q and samples['mu'][a]*samples['mu'][b] == x,
                    'complete actual coprime multiplicative factorization')
            label = b if program['projection'] == 'rough' else a
            group = groups.setdefault(label, [arb(0) for _ in HEIGHTS])
            members.setdefault(label, []).append(q)
            require(len(row['values']) == len(HEIGHTS), 'every height')
            for h, value in enumerate(row['values']):
                odd, even = x*arb(value['w1']), arb(value['w2'])
                joined = odd+even
                old = group[h]
                group[h] += joined
                total_cost += abs(group[h])-abs(old)
                baseline += abs(joined)
                odd_total += odd; even_total += even
                meter.charge(100)
        if q == B:
            initial = total_cost
        if q > B:
            curve.append(ball(total_cost))
            peak = peak.max(total_cost)
    singleton = sum((sum((abs(x) for x in groups[r]), arb(0))
                     for r, ns in members.items() if len(ns) == 1), arb(0))
    bits = None if baseline.contains(0) else 0
    if bits is not None:
        for k in range(1, 21):
            if 2**k*peak <= baseline:
                bits = k
    meter.live(100*B*len(HEIGHTS))
    return dict(program_id=program['id'], B=B, prefix_start=2, primes=primes,
        group_sizes=[[r, len(members[r])] for r in sorted(members)], zero_events=zeros,
        partial_curve=curve, initial_grouped_absolute=ball(initial), grouped_peak_absolute=ball(peak),
        grouped_endpoint_absolute=ball(total_cost), ungrouped_absolute=ball(baseline),
        odd_total=ball(odd_total), even_total=ball(even_total), joined_total=ball(odd_total+even_total),
        singleton_absolute=ball(singleton),
        cross_scale_groups=sum(min(ns) <= B < max(ns) for ns in members.values()),
        groups_with_opposite_mu=sum({samples['mu'][q] for q in ns} == {-1, 1} for ns in members.values()),
        prime_composite_groups=sum(any(is_prime[q] for q in ns) and any(not is_prime[q] for q in ns)
                                   for ns in members.values()),
        nontrivial_partition=len(members) > 1 and max(map(len, members.values()), default=0) > 1,
        cancellation_bits=bits)


def select(programs, cases, meter):
    require(programs == program_catalogue(), 'entire projection grammar')
    keyed = {(c['program_id'], c['B']): c for c in cases}
    require(len(keyed) == len(cases), 'unique generated case')
    scores, rejected = {}, []
    for p in programs:
        rows = [keyed.get((p['id'], B)) for B in DISCOVERY]
        reason = ('missing_discovery_case' if any(c is None for c in rows) else
                  'zero_baseline' if any(arb(c['ungrouped_absolute']).contains(0) for c in rows) else
                  'degenerate_partition' if any(not c['nontrivial_partition'] for c in rows) else None)
        if reason:
            rejected.append(dict(program_id=p['id'], reason=reason))
            continue
        score = arb(0)
        for c in rows:
            score = score.max(arb(c['grouped_peak_absolute'])/arb(c['ungrouped_absolute']))
            meter.charge(100)
        scores[p['id']] = score
    selected, undominated = [], {}
    for lane in LANES:
        ids = [p['id'] for p in programs if p['lane'] == lane and p['id'] in scores]
        frontier = [i for i in ids if not any(scores[j] < scores[i] for j in ids)]
        undominated[lane] = frontier
        if frontier:
            selected.append(dict(lane=lane, program_id=min(frontier)))
        meter.charge(100*(1+len(ids)**2))
    return dict(discovery_bases=DISCOVERY, selected=selected, rejected=rejected,
                undominated_by_lane=undominated)


def source_binding(parent, meter):
    require(parent['schema'] == 'core-cutoff-prime-orbit-feedback-v1', 'exact preceding projection obstruction')
    view = dict(parent, schema='core-cutoff-work-feedback-v1')
    binding = PREVIOUS.bind_target(view, meter)
    require(binding == parent['prime_orbit_search']['binding'], 'unchanged complete signed work binding')
    return binding


def summed_power(power):
    p = Q(power)
    return dict(B_power=str(max(Q(0), p+1)), log_degree=1 if p == -1 else 0)


def mass_rule(program, gamma):
    """Uniform source-independent label mass; never count just observed labels."""
    require(program in program_catalogue(), 'typed prime projection')
    g = Q(gamma)
    require(g >= 0, 'nonnegative weighting exponent')
    if program['projection'] == 'smooth' and program['prime_program']['kind'] == 'fixed':
        return dict(method='labels_subset_1_and_fixed_prime', B_power='0', log_degree=0, constant='2')
    if g < 1:
        return dict(method='all_integer_labels_through_2B', B_power=str(1-g), log_degree=0,
                    constant=str(2/(1-g)))
    if g == 1:
        return dict(method='all_integer_labels_through_2B', B_power='0', log_degree=1, constant='1')
    return dict(method='all_integer_labels_through_2B', B_power='0', log_degree=0,
                constant=str(g/(g-1)))


def proof_search(parent, binding, meter):
    require(source_binding(parent, meter) == binding, 'complete source-bound proof input')
    target = parent['cutoff_work_targets'][0]
    chosen = target['programs'][target['selected_program']]
    beta = Q(binding['inherited_bound']['power'])
    shell = chosen['moving_height_shell']
    parts = {p['name']: p['U_power'] for p in shell['parts']}
    require(shell['proved'] and parts == dict(raw_child_high_tail='-1/16', finite_head_full_norm='11/10')
        and chosen['subtract_exact_head'] and beta == Q(12, 5), 'licensed virtual-branch and full-head provider')
    powers = {name: summed_power(power) for name, power in parts.items()}
    recovery_power = max(Q(v['B_power']) for v in powers.values())
    recovery = dict(rule='complete_prefix_common_window_by_each_event_own_tail',
        review='CORE_CUTOFF_PREFIX_PROJECTION_REVIEW_027.txt',
        original_masks='abs(t)<H(q-1)', common_mask='abs(t)<H(2B)',
        H=dict(prefactor='2', U_power='45/2'), event_domain='2<=q<=V<=2B',
        identity='kappa*j_q=(abs(F_actual_child)^2-abs(F_zero_child)^2)/abs(s)^2',
        virtual_branches=[-1, 0, 1], virtual_coefficient_bound='1', virtual_c_bound='5/2',
        length_ratio='q/(q-1)<=2 for each event; no comparison of tiny q with B',
        per_event_powers=parts, summed_powers=powers, cost_B_power=str(recovery_power),
        gap_to_goal=str(beta-recovery_power), paid=recovery_power < beta,
        constant_uniform_in=['B', 'V', 'prime_set', 'number_of_groups', 'X', 'N'],
        numeric_constant=None, unit_event='q=1 is zero event with full initial energy retained',
        whole_signed_bound_proved=False)
    routes = []
    for program in program_catalogue():
        grams = []
        for gamma in GAMMAS:
            mass = mass_rule(program, gamma)
            grams.append(dict(gamma=gamma, eta='label^(-gamma)', mass=mass,
                kernel_mass_constant='100/13',
                expression='Q_eta(B,V)=integral_(abs(t)<H(2B)) kappa*sum_label label^gamma*abs(Gamma_label(V,t))^2 dt/(2*pi)',
                Gamma='sum_(2<=q<=V,selected_label(q)=label) (mu(q)*W1(q,s)+mu(q)^2*W2(q,s))',
                W_sectors_are_unweighted=True, kappa='abs(zeta(s+1/3)/s)^2', measure='dt/(2*pi)',
                cached_weighted_samples_are_not_a_Gram_estimate=True,
                ordered_pairs='all same-label ordered q,q_prime with every odd/even and previous-state cross',
                sufficient_bound=dict(B_power=str(2*beta-Q(mass['B_power'])),
                    log_degree=-mass['log_degree'], logarithm='1+log(2B)'),
                implication='M_common^2 <= (100/13)*(uniform label-mass bound)*Q_eta',
                higher_moment_provider_available=False, status='open_actual_arithmetic_Gram',
                uniform_in=['B', 'V', 'X', 'N'], target_assumed_in_proof=False))
            meter.charge(200)
        routes.append(dict(program_id=program['id'], projection=program['projection'],
            factorization='q=a*b, a supported on P(B), gcd(b,product(P(B)))=1; actual mu(q)=mu(a)*mu(b)',
            selected_label='b' if program['projection'] == 'rough' else 'a',
            insertion_preserved='fresh prime in P(B)' if program['projection'] == 'rough' else 'fresh prime outside P(B)',
            target=dict(expression='sup_(B<V<=2B) integral_R sum_label abs(sum_(2<=q<=V,label(q)=label) rho_q(t)) dt/(2*pi)',
                required_B_power=str(beta), all_integer_V=True, every_dyadic_B=True, complete_prefix=True,
                old_masks_retained=True, relation='stronger sufficient control; abs(S(V))<=M(B)<=C*V^beta',
                prior_block_summation_needed=False, status='open'),
            grammar_scope='factor projections and all signed interactions within each resulting group',
            gram_auxiliaries=grams, closed_uniform_bound=False))
    return dict(schema='cutoff-prefix-projection-proofs-v1', common_window=recovery, programs=routes,
        monotonicity=dict(rough='enlarging P coarsens groups and cannot increase the L1 grouped cost',
                          smooth='enlarging P refines groups and cannot decrease the L1 grouped cost',
                          mathematical_reason='triangle inequality; no arithmetic gain follows'),
        one_bucket_scope='a repackaging of the full joined target; not an independent arithmetic estimate',
        higher_moments_not_inherited_from_fourth_moment=True,
        statistics=dict(projections=len(routes), conditional_Gram_routes=sum(len(r['gram_auxiliaries']) for r in routes),
                        uniform_mask_recoveries=1, new_uniform_signed_arithmetic_estimates=0),
        whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, binding, proof, selection, cases, artifact):
    out = copy.deepcopy(parent)
    out.update(schema='core-cutoff-prefix-projection-feedback-v1', status='projection_controls_and_Gram_routes_open',
        parent_obligation_file='candidate10_cutoff_prime_orbit_obligation.json', complete_search_artifact=artifact)
    out['prefix_projection_search'] = dict(binding=binding, proof_search=proof,
        catalogue=program_catalogue(), selection=selection, finite_cases=cases,
        data_scope='new projections of previously observed finite work; no fresh or unseen arithmetic claim',
        numeric_Gram_estimates_used=False, whole_signed_bound_proved=False)
    out['inherited_prefix_projection_tasks'] = copy.deepcopy(parent['next_search_tasks'])
    out['next_search_tasks'] = [copy.deepcopy(parent['next_search_tasks'][0])]
    for winner in selection['selected']:
        pid = winner['program_id']
        out['next_search_tasks'].append(dict(priority=1, target_id=binding['target_id'],
            search_kind='prove_complete_prefix_projection_or_generated_weighted_Gram', status='open',
            program=program_catalogue()[pid], proof_route=proof['programs'][pid],
            common_window_recovery=proof['common_window'],
            signed_work_ref='prefix_projection_search.binding.inherited_bound.R_q',
            complete_source_preserved=True, finite_score_proves_uniform_bound=False))
    out['next_search_tasks'].extend(copy.deepcopy(parent['next_search_tasks'][1:]))
    return out
