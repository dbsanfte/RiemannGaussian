"""Generated prime/cofactor controls for the open signed cutoff work.

This search measures a finite discrete functional. It is neither quadrature
nor a certificate for the continuous Mellin integral. The exact partition
identity is universal; its useful uniform bound remains an obligation.
"""
import copy
from fractions import Fraction as Q

from flint import arb, acb, ctx

HEIGHTS = ['0', '1/2', '1', '2', '4', '8', '16']
EXPONENTS = ['0', '1/6', '1/3', '1/2', '2/3', '1']
DISCOVERY = [64, 128, 256, 512]
EVALUATION = [1024]
SIGMA, THETA, TAU = Q(9, 20), Q(2, 3), Q(45, 2)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def ball(value):
    require(value.is_finite(), 'finite real interval')
    return value.str(85)


def real(value):
    value = Q(value)
    return arb(value.numerator)/value.denominator


def norm(z):
    return z.real**2+z.imag**2


def complex_write(z):
    return dict(real=ball(z.real), imag=ball(z.imag))


def complex_read(z):
    value = acb(arb(z['real']), arb(z['imag']))
    require(value.is_finite(), 'finite continuation')
    return value


def validate_mu(mu, meter):
    require(type(mu) is list and 2 <= len(mu) <= 2049 and mu[:2] == [0, 1]
        and all(type(x) is int and x in (-1, 0, 1) for x in mu), 'complete exact Mobius prefix')
    inverse = [0]*len(mu)
    for d in range(1, len(mu)):
        for n in range(d, len(mu), d):
            inverse[n] += mu[d]
            meter.charge(2)
    require(inverse[1] == 1 and not any(inverse[2:]), 'all inverse divisor equations including unit')
    meter.live(3*len(mu))


def inside(t, U):
    return (Q(t)/2)**TAU.denominator < Q(U)**TAU.numerator


def work_sectors(A, E, c, D, z, a, b):
    """Three-valued polynomial increments, followed by all energy crosses."""
    old = A**2*E**3-c**3*D
    children = {x: (A+x*b)**2*(E+x*z*(a-b))**3-(c+x*a)**3*(D+b)
                for x in (-1, 0, 1)}
    J0 = children[0]-old
    J1 = (children[1]-children[-1])/2
    J2 = (children[1]+children[-1])/2-children[0]
    base = old+J0
    zero = 2*(old.conjugate()*J0).real+norm(J0)
    odd = 2*(base.conjugate()*J1+J1.conjugate()*J2).real
    even = 2*(base.conjugate()*J2).real+norm(J1)+norm(J2)
    return zero, odd, even, children


def measure(mu, start, end, previous_state, meter):
    require(ctx.prec == 192, 'producer uses 192-bit intervals')
    require(type(start) is int and type(end) is int and 2 <= start <= end <= 2048
        and len(mu) == end+1, 'complete declared numerical phase')
    validate_mu(mu, meter)
    kernels = []
    for t in HEIGHTS:
        s = acb(real(SIGMA), real(t))
        z = s.zeta()
        weight = (1 if t == '0' else 2)*norm((s+real(1-THETA)).zeta()/s)
        require(z.is_finite() and weight.is_finite(), 'finite zeta samples')
        kernels.append((s, z, weight))
        meter.charge(12000)
    if previous_state is None:
        require(start == 2, 'start from the complete unit')
        A, D = [acb(1) for _ in HEIGHTS], [acb(1) for _ in HEIGHTS]
        c = arb(1)
        initial = [arb(0) for _ in HEIGHTS]
    else:
        require(previous_state['schema'] == 'producer-cutoff-continuation-v1'
            and previous_state['q'] == start-1 and previous_state['mu_prefix'] == mu[:start],
            'own previous phase and complete arithmetic prefix')
        A = [complex_read(z) for z in previous_state['A']]
        D = [complex_read(z) for z in previous_state['D']]
        c = arb(previous_state['c'])
        initial = [arb(x) for x in previous_state['last_energy']]
        require(len(A) == len(D) == len(initial) == len(HEIGHTS), 'all continued heights')
    records = []
    for q in range(start, end+1):
        x, a = mu[q], arb(1)/q
        old_masks = [inside(t, q-1) for t in HEIGHTS]
        new_masks = [inside(t, q) for t in HEIGHTS]
        values, energies = [], []
        for h, (s, z, weight) in enumerate(kernels):
            b = (-s*arb(q).log()).exp()
            E = 1+z*(c-A[h])
            w0, w1, w2, children = work_sectors(A[h], E, c, D[h], z, a, b)
            energy = weight*norm(children[x]) if new_masks[h] else arb(0)
            shell = energy if new_masks[h] and not old_masks[h] else arb(0)
            zero, odd, even = [v*weight if old_masks[h] else arb(0) for v in (w0, w1, w2)]
            old_energy = weight*norm(A[h]**2*E**3-c**3*D[h]) if old_masks[h] else arb(0)
            require((energy-old_energy-zero-x*odd-x*x*even-shell).contains(0),
                    'complete sampled energy difference')
            values.append(dict(w1=ball(odd), w2=ball(even), zero=ball(zero),
                               shell=ball(shell), energy=ball(energy)))
            energies.append(energy)
            A[h] += x*b
            D[h] += b
            meter.charge(6000)
        c += x*a
        records.append(dict(q=q, mu=x, mask_old=old_masks, mask_new=new_masks, values=values))
        meter.live(100*len(records)*len(HEIGHTS)+20*len(mu))
    state = dict(schema='producer-cutoff-continuation-v1', q=end, mu_prefix=mu[:end+1],
        A=[complex_write(z) for z in A], D=[complex_write(z) for z in D], c=ball(c),
        last_energy=[ball(v) for v in energies])
    return dict(schema='cutoff-work-samples-v1', start=start, end=end, precision=192,
        heights=HEIGHTS, mu=mu[:end+1], initial_energy=[ball(v) for v in initial], records=records, state=state)


def program_catalogue():
    programs = [dict(id=i, lane='fixed', kind='fixed', fixed_prime=p) for i, p in enumerate((2, 3, 5))]
    for i, lo in enumerate(EXPONENTS):
        for hi in EXPONENTS[i+1:]:
            programs.append(dict(id=len(programs), lane='prefix' if lo == '0' else 'window',
                                 kind='window', lower=lo, upper=hi))
    return programs


def floor_power(B, exponent):
    e = Q(exponent)
    require(type(B) is int and B >= 1 and 0 <= e <= 1, 'exact bounded fractional prime scale')
    target, left, right = B**e.numerator, 0, B+1
    while left+1 < right:
        middle = (left+right)//2
        if middle**e.denominator <= target:
            left = middle
        else:
            right = middle
    return left


def selected_primes(program, B, meter):
    require(program in program_catalogue(), 'a sealed grammar program')
    if program['kind'] == 'fixed':
        return [program['fixed_prime']]
    lower = 0 if program['lower'] == '0' else floor_power(B, program['lower'])
    upper = floor_power(B, program['upper'])
    composite = [False]*(upper+1)
    primes = []
    for p in range(2, upper+1):
        if composite[p]:
            continue
        if p > lower:
            primes.append(p)
        for n in range(p*p, upper+1, p):
            composite[n] = True
            meter.charge(1)
    meter.charge(3*(upper+1))
    return primes


def group_case(program, B, samples, meter):
    require(type(B) is int and 2 <= B <= 1024 and samples['start'] <= B+1
        and samples['end'] >= 2*B and samples['heights'] == HEIGHTS, 'complete block and all sampled heights')
    primes = selected_primes(program, B, meter)
    rows = samples['records'][B+1-samples['start']:2*B+1-samples['start']]
    require([r['q'] for r in rows] == list(range(B+1, 2*B+1)), 'every integer and every partial cutoff')
    groups, sizes = {}, {}
    cost, peak, baseline = arb(0), arb(0), arb(0)
    odd_total, even_total = arb(0), arb(0)
    zero_events, curve = 0, []
    for row in rows:
        q, x = row['q'], row['mu']
        require(x == samples['mu'][q] and x in (-1, 0, 1), 'exact source event')
        if x == 0:
            zero_events += 1
            curve.append(ball(cost))
            continue
        r = q
        for p in primes:
            if r % p == 0:
                r //= p
                require(r % p != 0, 'squarefree orbit rule only on nonzero Mobius events')
            meter.charge(3)
        require(samples['mu'][r] != 0, 'complete squarefree cofactor')
        sizes[r] = sizes.get(r, 0)+1
        group = groups.setdefault(r, [arb(0) for _ in HEIGHTS])
        for h, value in enumerate(row['values']):
            odd, even = x*arb(value['w1']), arb(value['w2'])
            joined = odd+even
            old = group[h]
            group[h] = old+joined
            cost += abs(group[h])-abs(old)
            baseline += abs(joined)
            odd_total += odd
            even_total += even
            meter.charge(100)
        peak = peak.max(cost)
        curve.append(ball(cost))
    singleton = sum((sum((abs(v) for v in groups[r]), arb(0))
                     for r in sizes if sizes[r] == 1), arb(0))
    bits = None if baseline.contains(0) else 0
    if bits is not None:
        for k in range(1, 21):
            if (2**k)*peak <= baseline:
                bits = k
    meter.live(50*B*len(HEIGHTS)+20*len(samples['mu']))
    return dict(program_id=program['id'], B=B, primes=primes,
        group_sizes=[[r, sizes[r]] for r in sorted(sizes)], zero_events=zero_events,
        partial_curve=curve, grouped_peak_absolute=ball(peak), grouped_endpoint_absolute=ball(cost),
        ungrouped_absolute=ball(baseline), joined_total=ball(odd_total+even_total),
        odd_total=ball(odd_total), even_total=ball(even_total), singleton_absolute=ball(singleton),
        nontrivial_partition=len(sizes) > 1 and max(sizes.values(), default=0) > 1,
        cancellation_bits=bits)


def select(programs, cases):
    require(programs == program_catalogue(), 'entire sealed grammar for selection')
    keyed = {(c['program_id'], c['B']): c for c in cases}
    require(len(keyed) == len(cases), 'no duplicate search case')
    eligible, rejected = [], []
    for program in programs:
        trial = [keyed.get((program['id'], B)) for B in DISCOVERY]
        reason = ('missing_discovery_case' if any(c is None for c in trial) else
                  'zero_baseline' if any(c['cancellation_bits'] is None for c in trial) else
                  'degenerate_partition' if any(not c['nontrivial_partition'] for c in trial) else None)
        if reason:
            rejected.append(dict(program_id=program['id'], reason=reason))
        else:
            eligible.append(dict(lane=program['lane'], program_id=program['id'],
                minimum_cancellation_bits=min(c['cancellation_bits'] for c in trial)))
    chosen = []
    for lane in ('fixed', 'prefix', 'window'):
        choices = [p for p in eligible if p['lane'] == lane]
        if choices:
            chosen.append(min(choices, key=lambda p: (-p['minimum_cancellation_bits'], p['program_id'])))
    return dict(discovery_bases=DISCOVERY, selected=chosen, rejected=rejected)


def bind_target(parent, meter):
    """Reject a different source instead of silently measuring this one."""
    import core_cutoff_work_search as predecessor
    require(parent['schema'] == 'core-cutoff-work-feedback-v1'
        and not parent['whole_signed_bound_proved'] and not parent['RH_proved'], 'open preceding obligation')
    targets = parent['cutoff_work_targets']
    require(len(targets) == 1, 'single current supported numerical target')
    t = targets[0]
    require((t['target_id'], t['p'], t['m'], t['sigma'], t['theta']) ==
        ('centered_A2_E3', 2, 3, '9/20', '2/3'), 'supported full polynomial and contour')
    program = t['programs'][t['selected_program']]
    require(program['subtract_exact_head'] is True and program['centering']['all_opposite_drifts_retained']
        and program['transition'] == predecessor.compile_transition(2, 3, True, meter),
        'exact inherited complete work polynomial and head')
    required = t['original_low_obligation']['required_upper']
    require(required['U_power'] == '12/5' and t['original_low_obligation']['height'] ==
        dict(U_power='45/2', interval='abs(t)<H', prefactor='2'), 'current continuous all-scale bound')
    goals = program['bound_search']['next_bound_targets']
    require(len(goals) == 1 and goals[0]['power'] == '12/5' and goals[0]['status'] == 'open',
        'one inherited unresolved joined signed work target')
    return dict(target_id=t['target_id'], inherited_bound=copy.deepcopy(goals[0]),
        measure_scope='finite discrete samples only; not quadrature', heights=HEIGHTS,
        source_scalar=t['source_term']['coefficient'], original_continuous_measure='dt/(2*pi)',
        sampled_measure='weight 1 at zero, 2 at each positive declared height; no quadrature widths',
        complete_source_unchanged=True, whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, binding, selection, cases, artifact):
    out = copy.deepcopy(parent)
    out.update(schema='core-cutoff-prime-orbit-feedback-v1',
        parent_obligation_file='candidate10_cutoff_work_obligation.json', complete_search_artifact=artifact,
        status='finite_prime_orbit_search_verified_uniform_bound_open')
    out['prime_orbit_search'] = dict(binding=binding, selected_programs=selection['selected'],
        programme_catalogue=program_catalogue(), finite_results=cases,
        source_history='all Mobius inputs previously observed; new finite cutoff-work observables',
        new_uniform_signed_arithmetic_estimates=0, continuous_integral_control=False)
    out['inherited_prime_orbit_search_tasks'] = copy.deepcopy(parent['next_search_tasks'])
    out['next_search_tasks'] = [copy.deepcopy(parent['next_search_tasks'][0])]
    for winner in selection['selected']:
        program = program_catalogue()[winner['program_id']]
        out['next_search_tasks'].append(dict(priority=1, target_id=binding['target_id'],
            search_kind='bound_complete_truncated_prime_orbit_work', status='open', program=program,
            expression='sup_(B<V<=2B) integral_R sum_r abs(sum_(B<q<=V, P-free cofactor(q)=r) rho_q(t)) dt/(2*pi)',
            rho_q='1_(abs(t)<H(q-1))*abs(zeta(s+1-theta)/s)^2*(mu(q)*W1(q,s)+mu(q)^2*W2(q,s))',
            R_q=binding['inherited_bound']['R_q'], required_upper='C*B^(12/5)',
            quantifier='every dyadic integer B>=1 and every integer V in (B,2B]; C independent of B,V,X,N',
            relation='stronger sufficient control of joined signed work; not an independent proved estimate',
            retained=['all squarefree faces and exits', 'zero Mobius events have R_q=0',
                'q=1 is initial state', 'odd and even sector interaction', 'actual prefix state at every q',
                'complete old height integral at every q', 'paid W0 and moving shell separately',
                'original full source, recovery, drifts and scalar'],
            possible_lemmas=['signed prime/cofactor state variation', 'complete truncated even/odd cube interaction',
                'boundary and singleton control uniform in changing prime set'],
            finite_samples_establish_bound=False, circular_target_substitution_allowed=False,
            whole_signed_bound_proved=False, RH_proved=False))
    # Keep the ungrouped target available even if every generated orbit fails.
    out['next_search_tasks'].extend(copy.deepcopy(parent['next_search_tasks'][1:]))
    return out
