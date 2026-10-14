"""Independent complete-prefix factor-projection audits.

Only cached finite signed samples are consumed.  No zeta evaluations,
arithmetic archive reads, fitted constants, or producer are imported.
"""
from copy import deepcopy
from fractions import Fraction as Q

from flint import arb, ctx
from check_core_split_bound_search import _require, _same, _rational
from check_core_cutoff_prime_orbits import program_catalogue as _prime_catalogue
from check_core_cutoff_prime_orbits import _program_primes, _parse_ball, _ball, _prime, HEIGHTS


def program_catalogue():
    result = []
    for prime_program in _prime_catalogue():
        for projection in ('rough', 'smooth'):
            result.append(dict(id=len(result), parent_program_id=prime_program['id'], projection=projection,
                lane=prime_program['lane']+':'+projection, prime_program=prime_program))
    return result


def _labels(q, primes, mu, meter):
    _require(type(q) is int and q >= 2 and mu[q] in (-1, 1), 'squarefree nonunit event label')
    selected = 1
    for p in primes:
        if q % p == 0: selected *= p
        meter.charge(5)
    rough = q//selected
    _require(selected*rough == q and all(rough % p != 0 for p in primes) and mu[selected]*mu[rough] == mu[q],
        'complete actual coprime smooth/rough factor partition')
    return dict(rough=rough, smooth=selected)


def _group_columns(program, B, samples, meter):
    """Form each complete group's column first, then all prefix variations."""
    catalogue = program_catalogue()
    _require(ctx.prec == 256 and type(program) is dict and type(program.get('id')) is int and
        0 <= program['id'] < len(catalogue) and _same(program, catalogue[program['id']]), 'independent sealed projection grammar')
    _require(type(B) is int and 1 <= B <= 1024 and B & (B-1) == 0, 'exact dyadic complete-prefix block')
    _require(samples.get('schema') == 'cutoff-work-samples-v1' and samples['start'] == 2 and samples['end'] >= 2*B and
        samples['heights'] == HEIGHTS, 'complete inherited samples q2 through the endpoint')
    mu = samples['mu']
    _require(type(mu) is list and len(mu) == samples['end']+1 and mu[:2] == [0, 1] and
        all(type(x) is int and x in (-1, 0, 1) for x in mu), 'complete previously certified Mobius cache and arithmetic unit')
    rows = {row['q']: row for row in samples['records']}
    _require(len(rows) == len(samples['records']) and all(q in rows for q in range(2, 2*B+1)), 'all unique complete-prefix events')
    primes = _program_primes(program['prime_program'], B, meter)
    groups = {}; signed = {}; zero_count = 0
    odd = arb(0); even = arb(0); baseline = arb(0)
    for q in range(2, 2*B+1):
        row = rows[q]
        _require(type(row['mu']) is int and row['mu'] == mu[q] and type(row['values']) is list and len(row['values']) == len(HEIGHTS),
            'all heights of the actual cache-signed event')
        signed[q] = []
        for value in row['values']:
            o = mu[q]*_parse_ball(value['w1'], meter)
            e = mu[q]**2*_parse_ball(value['w2'], meter)
            r = o+e if mu[q] else arb(0)
            signed[q].append(r); odd += o; even += e; baseline += abs(r); meter.charge(50)
        if mu[q] == 0:
            zero_count += 1; continue
        labels = _labels(q, primes, mu, meter)
        group = labels[program['projection']]
        groups.setdefault(group, []).append(q)
    changes = [arb(0) for _ in range(2*B-1)]; singleton = arb(0)
    for label, events in sorted(groups.items()):
        for h in range(len(HEIGHTS)):
            running = arb(0); previous = arb(0)
            for q in events:
                running += signed[q][h]; current = abs(running)
                changes[q-2] += current-previous; previous = current; meter.charge(40)
            if len(events) == 1: singleton += previous
    cost = arb(0); full_curve = []
    for change in changes:
        cost += change; full_curve.append(cost); meter.charge(25)
    curve = full_curve[B-1:]
    _require(len(curve) == B, 'every and only declared V=B+1 through 2B')
    peak = arb(0)
    for value in curve: peak = peak.max(value); meter.charge(20)
    meter.live(20*len(groups)+30*len(signed)*len(HEIGHTS)+20*B)
    return dict(primes=primes, groups=groups, zero_events=zero_count, curve=curve, peak=peak,
        initial=arb(0) if B == 1 else full_curve[B-2],
        endpoint=curve[-1], baseline=baseline, odd=odd, even=even, singleton=singleton)


def group_case(program, B, samples, meter):
    columns = _group_columns(program, B, samples, meter)
    groups = columns['groups']; mu = samples['mu']
    prime_events = {q: _prime(q, meter) for events in groups.values() for q in events}
    bits = None if columns['baseline'].contains(0) else 0
    if bits is not None:
        for exponent in range(1, 21):
            if 2**exponent*columns['peak'] <= columns['baseline']: bits = exponent
    return dict(program_id=program['id'], B=B, primes=columns['primes'],
        group_sizes=[[label, len(events)] for label, events in sorted(groups.items())], zero_events=columns['zero_events'],
        prefix_start=2, cross_scale_groups=sum(min(events) <= B < max(events) for events in groups.values()),
        groups_with_opposite_mu=sum({mu[q] for q in events} == {-1, 1} for events in groups.values()),
        prime_composite_groups=sum(any(prime_events[q] for q in events) and any(not prime_events[q] for q in events) for events in groups.values()),
        initial_grouped_absolute=_ball(columns['initial']), partial_curve=[_ball(v) for v in columns['curve']],
        grouped_peak_absolute=_ball(columns['peak']), grouped_endpoint_absolute=_ball(columns['endpoint']),
        ungrouped_absolute=_ball(columns['baseline']), joined_total=_ball(columns['odd']+columns['even']),
        odd_total=_ball(columns['odd']), even_total=_ball(columns['even']), singleton_absolute=_ball(columns['singleton']),
        nontrivial_partition=len(groups) > 1 and max((len(events) for events in groups.values()), default=0) > 1,
        cancellation_bits=bits)


def select(programs, cases, meter):
    _require(_same(programs, program_catalogue()) and type(cases) is list, 'complete immutable 36-program projection grammar')
    bases = [64, 128, 256, 512]; lookup = {}
    for case in cases:
        key = (case['program_id'], case['B'])
        _require(key not in lookup, 'unique projection program/block case')
        lookup[key] = case
    ratios = {}; rejected = []
    for program in programs:
        rows = [lookup.get((program['id'], B)) for B in bases]
        if any(row is None for row in rows): reason = 'missing_discovery_case'
        elif any(_parse_ball(row['ungrouped_absolute'], meter).contains(0) for row in rows): reason = 'zero_baseline'
        elif any(row['nontrivial_partition'] is False for row in rows): reason = 'degenerate_partition'
        else:
            _require(all(row['nontrivial_partition'] is True for row in rows), 'typed nondegenerate complete partitions')
            worst = arb(0)
            for row in rows:
                ratio = _parse_ball(row['grouped_peak_absolute'], meter)/_parse_ball(row['ungrouped_absolute'], meter)
                _require(ratio.is_finite(), 'finite worst observed prefix ratio')
                worst = worst.max(ratio); meter.charge(60)
            ratios[program['id']] = worst; continue
        rejected.append(dict(program_id=program['id'], reason=reason))
    selected = []; undominated = {}
    for lane in ('fixed:rough', 'fixed:smooth', 'prefix:rough', 'prefix:smooth', 'window:rough', 'window:smooth'):
        eligible = [p['id'] for p in programs if p['lane'] == lane and p['id'] in ratios]
        survivors = [ident for ident in eligible if not any(ratios[other] < ratios[ident] for other in eligible)]
        undominated[lane] = survivors
        if survivors: selected.append(dict(lane=lane, program_id=min(survivors)))
    return dict(discovery_bases=bases, selected=selected, rejected=rejected, undominated_by_lane=undominated)


def source_binding(parent, meter):
    from check_core_cutoff_prime_orbits import bind_target
    _require(type(parent) is dict and parent.get('schema') == 'core-cutoff-prime-orbit-feedback-v1' and
        parent.get('whole_signed_bound_proved') is False and parent.get('RH_proved') is False, 'complete open inherited prime-orbit input')
    binding = bind_target(dict(parent, schema='core-cutoff-work-feedback-v1'), meter)
    _require(_same(binding, parent['prime_orbit_search']['binding']), 'exact inherited full signed-work source binding')
    return binding


def mass_rule(program, gamma):
    _require(type(program) is dict and type(program.get('id')) is int and 0 <= program['id'] < 36 and
        _same(program, program_catalogue()[program['id']]), 'typed complete factor projection')
    gamma = Q(gamma); _require(gamma >= 0, 'nonnegative label decay exponent')
    if program['projection'] == 'smooth' and program['prime_program']['kind'] == 'fixed':
        # The only possible labels are 1,p. This finite bound is not licensed
        # for prime windows that grow with B, regardless of observed counts.
        return dict(method='labels_subset_1_and_fixed_prime', B_power='0', log_degree=0, constant='2')
    if gamma == 1:
        return dict(method='all_integer_labels_through_2B', B_power='0', log_degree=1, constant='1')
    if gamma > 1:
        return dict(method='all_integer_labels_through_2B', B_power='0', log_degree=0, constant=str(1+1/(gamma-1)))
    # Sum n^-gamma <= (2B)^(1-gamma)/(1-gamma); round 2^(1-gamma)<=2.
    return dict(method='all_integer_labels_through_2B', B_power=str(1-gamma), log_degree=0, constant=str(2/(1-gamma)))


def _sum_power(power):
    power = Q(power)
    if power < -1: return dict(B_power='0', log_degree=0)
    if power == -1: return dict(B_power='0', log_degree=1)
    return dict(B_power=str(power+1), log_degree=0)


def _proof(parent, binding, meter):
    _require(_same(binding, source_binding(parent, meter)), 'independent complete arithmetic and source-bound proof input')
    target = parent['cutoff_work_targets'][0]; selected = target['programs'][target['selected_program']]
    beta = _rational(binding['inherited_bound']['power'], meter)
    shell = selected['moving_height_shell']; parts = {p['name']: p['U_power'] for p in shell['parts']}
    _require(shell['proved'] is True and selected['subtract_exact_head'] is True and beta == Q(12, 5) and
        parts == {'raw_child_high_tail': '-1/16', 'finite_head_full_norm': '11/10'},
        'licensed local virtual branches and complete finite-head tail premises')
    sums = {name: _sum_power(power) for name, power in parts.items()}
    exponent = max(Q(row['B_power']) for row in sums.values())
    common = dict(rule='complete_prefix_common_window_by_each_event_own_tail', review='CORE_CUTOFF_PREFIX_PROJECTION_REVIEW_027.txt',
        original_masks='abs(t)<H(q-1)', common_mask='abs(t)<H(2B)', H=dict(prefactor='2', U_power='45/2'),
        event_domain='2<=q<=V<=2B', identity='kappa*j_q=(abs(F_actual_child)^2-abs(F_zero_child)^2)/abs(s)^2',
        virtual_branches=[-1, 0, 1], virtual_coefficient_bound='1', virtual_c_bound='5/2',
        length_ratio='q/(q-1)<=2 for each event; no comparison of tiny q with B', per_event_powers=parts,
        summed_powers=sums, cost_B_power=str(exponent), gap_to_goal=str(beta-exponent), paid=exponent < beta,
        constant_uniform_in=['B', 'V', 'prime_set', 'number_of_groups', 'X', 'N'], numeric_constant=None,
        unit_event='q=1 is zero event with full initial energy retained', whole_signed_bound_proved=False)
    theta, sigma = Q(target['theta']), Q(target['sigma'])
    kernel = (1/sigma+1/(theta-sigma))/(2*theta**2)
    rows = []
    for program in program_catalogue():
        grams = []
        for gamma in ('0', '1/6', '1/3', '1/2', '2/3', '1', '3/2'):
            mass = mass_rule(program, gamma)
            grams.append(dict(gamma=gamma, eta='label^(-gamma)', mass=mass, kernel_mass_constant=str(kernel),
                expression='Q_eta(B,V)=integral_(abs(t)<H(2B)) kappa*sum_label label^gamma*abs(Gamma_label(V,t))^2 dt/(2*pi)',
                Gamma='sum_(2<=q<=V,selected_label(q)=label) (mu(q)*W1(q,s)+mu(q)^2*W2(q,s))',
                W_sectors_are_unweighted=True, kappa='abs(zeta(s+1/3)/s)^2', measure='dt/(2*pi)',
                cached_weighted_samples_are_not_a_Gram_estimate=True,
                ordered_pairs='all same-label ordered q,q_prime with every odd/even and previous-state cross',
                sufficient_bound=dict(B_power=str(2*beta-Q(mass['B_power'])), log_degree=-mass['log_degree'], logarithm='1+log(2B)'),
                implication='M_common^2 <= (100/13)*(uniform label-mass bound)*Q_eta',
                higher_moment_provider_available=False, status='open_actual_arithmetic_Gram', uniform_in=['B', 'V', 'X', 'N'],
                target_assumed_in_proof=False)); meter.charge(200)
        rows.append(dict(program_id=program['id'], projection=program['projection'],
            factorization='q=a*b, a supported on P(B), gcd(b,product(P(B)))=1; actual mu(q)=mu(a)*mu(b)',
            selected_label='b' if program['projection'] == 'rough' else 'a',
            insertion_preserved='fresh prime in P(B)' if program['projection'] == 'rough' else 'fresh prime outside P(B)',
            target=dict(expression='sup_(B<V<=2B) integral_R sum_label abs(sum_(2<=q<=V,label(q)=label) rho_q(t)) dt/(2*pi)',
                required_B_power=str(beta), all_integer_V=True, every_dyadic_B=True, complete_prefix=True, old_masks_retained=True,
                relation='stronger sufficient control; abs(S(V))<=M(B)<=C*V^beta', prior_block_summation_needed=False, status='open'),
            grammar_scope='factor projections and all signed interactions within each resulting group', gram_auxiliaries=grams,
            closed_uniform_bound=False))
    return dict(schema='cutoff-prefix-projection-proofs-v1', common_window=common, programs=rows,
        monotonicity=dict(rough='enlarging P coarsens groups and cannot increase the L1 grouped cost',
            smooth='enlarging P refines groups and cannot decrease the L1 grouped cost', mathematical_reason='triangle inequality; no arithmetic gain follows'),
        one_bucket_scope='a repackaging of the full joined target; not an independent arithmetic estimate',
        higher_moments_not_inherited_from_fourth_moment=True,
        statistics=dict(projections=len(rows), conditional_Gram_routes=sum(len(p['gram_auxiliaries']) for p in rows),
            uniform_mask_recoveries=1, new_uniform_signed_arithmetic_estimates=0), whole_signed_bound_proved=False, RH_proved=False)


def verify_proof_search(parent, binding, proof, meter):
    _require(_same(proof, _proof(parent, binding, meter)), 'complete conditional Gram grammar, common-window payment and all signed cross terms')
    return dict(verified=True, conditional_Gram_routes=252, new_uniform_signed_arithmetic_estimates=0, RH_proved=False)


def verify_cases(producer_cases, checker_cases, meter):
    scalar = {'initial_grouped_absolute', 'grouped_peak_absolute', 'grouped_endpoint_absolute', 'ungrouped_absolute',
              'joined_total', 'odd_total', 'even_total', 'singleton_absolute'}
    metadata = {'program_id', 'B', 'prefix_start', 'primes', 'group_sizes', 'zero_events', 'cross_scale_groups',
                'groups_with_opposite_mu', 'prime_composite_groups', 'nontrivial_partition', 'cancellation_bits'}
    _require(type(producer_cases) is list and type(checker_cases) is list and len(producer_cases) == len(checker_cases), 'complete compared projection cases')
    seen = set()
    for producer, checker in zip(producer_cases, checker_cases):
        _require(type(producer) is dict and type(checker) is dict and set(producer) == set(checker) == scalar | metadata | {'partial_curve'},
            'complete projection score and exact coverage schema')
        _require(all(_same(producer[k], checker[k]) for k in metadata), 'complete initial-prefix factors, source signs, singleton and zero counts agree')
        key = (checker['program_id'], checker['B']); _require(key not in seen, 'unique projection/block case'); seen.add(key)
        _require(type(producer['partial_curve']) is list and type(checker['partial_curve']) is list and
            len(producer['partial_curve']) == len(checker['partial_curve']) == checker['B'], 'all declared partial prefixes')
        for k in scalar:
            _require(_parse_ball(producer[k], meter).overlaps(_parse_ball(checker[k], meter)), 'independent full-prefix scalar costs agree')
        for a, b in zip(producer['partial_curve'], checker['partial_curve']):
            _require(_parse_ball(a, meter).overlaps(_parse_ball(b, meter)), 'independent complete-prefix group columns agree')
    return dict(verified=True, cases=len(checker_cases), all_partial_prefixes=True, uniform_bound_proved=False, RH_proved=False)


def verify_feedback(parent, binding, proof, selection, cases, output, artifact, meter):
    _require(type(artifact) is str and bool(artifact), 'immutable projection search artifact')
    verify_proof_search(parent, binding, proof, meter)
    _require(_same(selection, select(program_catalogue(), cases, meter)), 'empirical interval dominance uses only declared discovery/validation blocks')
    expected = deepcopy(parent)
    expected.update(schema='core-cutoff-prefix-projection-feedback-v1', status='projection_controls_and_Gram_routes_open',
        parent_obligation_file='candidate10_cutoff_prime_orbit_obligation.json', complete_search_artifact=artifact)
    expected['prefix_projection_search'] = dict(binding=binding, proof_search=proof, catalogue=program_catalogue(),
        selection=selection, finite_cases=cases, data_scope='new projections of previously observed finite work; no fresh or unseen arithmetic claim',
        numeric_Gram_estimates_used=False, whole_signed_bound_proved=False)
    _require(type(parent['next_search_tasks']) is list and bool(parent['next_search_tasks']) and
        parent['next_search_tasks'][0]['target_id'] == 'actual_signed_core' and parent['next_search_tasks'][0]['priority'] == 0,
        'full inherited signed core remains priority zero')
    expected['inherited_prefix_projection_tasks'] = deepcopy(parent['next_search_tasks'])
    tasks = [deepcopy(parent['next_search_tasks'][0])]
    for winner in selection['selected']:
        ident = winner['program_id']
        tasks.append(dict(priority=1, target_id=binding['target_id'], search_kind='prove_complete_prefix_projection_or_generated_weighted_Gram',
            status='open', program=program_catalogue()[ident], proof_route=proof['programs'][ident], common_window_recovery=proof['common_window'],
            signed_work_ref='prefix_projection_search.binding.inherited_bound.R_q', complete_source_preserved=True, finite_score_proves_uniform_bound=False))
    tasks.extend(deepcopy(parent['next_search_tasks'][1:]))
    expected['next_search_tasks'] = tasks
    _require(_same(output, expected), 'all original source, unit, drifts, recoveries and tasks preserved; all generated Gram controls remain open')
    meter.charge(500+100*len(tasks))
    return dict(verified=True, uniform_bound_proved=False, RH_proved=False)
