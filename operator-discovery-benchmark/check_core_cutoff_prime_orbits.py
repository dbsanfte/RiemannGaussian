"""Independent finite sampled-energy and prime-orbit audits.

Actual arithmetic is supplied by the frozen runner, not read on import.
Counterfactual energy differences replace the producer's increment formula.
These diagnostics never certify a continuous norm or an all-scale bound.
"""
from fractions import Fraction as Q
from math import isqrt
from copy import deepcopy

from flint import arb, acb, ctx
from check_core_split_bound_search import _require, _same, _rational

HEIGHTS = ['0', '1/2', '1', '2', '4', '8', '16']
SIGMA = Q(9, 20)
THETA = Q(2, 3)
TAU = Q(45, 2)


def _ball(value):
    _require(type(value) is arb and value.is_finite(), 'finite serialized real sample')
    return value.str(90)


def _complex_record(value):
    _require(type(value) is acb and value.is_finite(), 'finite checker continuation value')
    return dict(real=_ball(value.real), imag=_ball(value.imag))


def _complex_read(value):
    _require(type(value) is dict and set(value) == {'real', 'imag'}, 'private complex continuation schema')
    result = acb(arb(value['real']), arb(value['imag']))
    _require(result.is_finite(), 'finite parsed checker continuation')
    return result


def validate_mu(mu, meter):
    """Trial factorization is independent of divisor-inverse validation."""
    _require(type(mu) is list and 2 <= len(mu) <= 2049 and mu[0] == 0 and mu[1] == 1 and
        all(type(x) is int and x in (-1, 0, 1) for x in mu), 'complete exact bounded Mobius prefix with unit')
    for n in range(2, len(mu)):
        remainder = n; sign = 1; square = False
        divisor = 2
        while divisor*divisor <= remainder:
            if remainder % divisor == 0:
                remainder //= divisor; sign = -sign
                if remainder % divisor == 0:
                    square = True; break
            divisor += 1; meter.charge(5)
        if remainder > 1: sign = -sign
        expected = 0 if square else sign
        _require(mu[n] == expected, 'independently factorized Mobius value at every integer')
        meter.charge(20)
    meter.live(10*len(mu))
    return dict(verified=True, maximum_cutoff=len(mu)-1, full_unit=True)


def _prime(n, meter):
    if n < 2: return False
    for d in range(2, isqrt(n)+1):
        meter.charge(3)
        if n % d == 0: return False
    return True


def _root_comparison(n, B, exponent):
    """Exact n<=B^exponent; no floating cutoff approximation."""
    return n**exponent.denominator <= B**exponent.numerator


def _norm_square(value):
    _require(type(value) is acb and value.is_finite(), 'finite complex sampled state')
    return value.real**2+value.imag**2


def _real(value):
    if type(value) is Q: return arb(value.numerator)/value.denominator
    return arb(value)


def _inside_window(t, U, tau):
    if U == 0: return False
    # t<2*U^tau, including strict boundary masks, exactly over rationals.
    return (t/Q(2))**tau.denominator < Q(U)**tau.numerator


def _counterfactual_samples(mu, theta, sigma, tau, heights, start, end, previous_state, meter):
    """All source prefixes via Abel sums, all energy sectors via three norms.

    The caller binds these parameters to the verified current source program.
    This helper supports the fixed p=2,m=3,One-head numerical construction.
    """
    _require(ctx.prec == 256, 'independent checker precision 256')
    _require(0 < sigma < theta < 1 and tau > 0 and type(heights) is list and
        heights == sorted(set(heights)) and all(type(t) is Q and t >= 0 for t in heights), 'exact sampled contour and height grid')
    validate_mu(mu, meter)
    kernels = []
    for t in heights:
        s = acb(_real(sigma), _real(t)); z = s.zeta()
        shifted = (s+_real(1-theta)).zeta()/s
        weight = (1 if t == 0 else 2)*_norm_square(shifted)
        _require(z.is_finite() and weight.is_finite(), 'finite declared zeta-weighted samples')
        kernels.append((s, z, weight)); meter.charge(12000)
    if previous_state is None:
        _require(start == 2, 'initial checker phase begins at q=2 with the complete unit')
        abel = [acb(0) for _ in heights]; A = [acb(1) for _ in heights]
        D = [acb(1) for _ in heights]; old_weight = [acb(1) for _ in heights]
        c = Q(1); mertens = 1; initial_energy = [arb(0) for _ in heights]
    else:
        _require(type(previous_state) is dict and set(previous_state) == {'schema', 'q', 'mu_prefix', 'c', 'M', 'abel', 'A', 'D', 'old_weight', 'last_energy'} and
            previous_state['schema'] == 'checker-cutoff-continuation-v1' and previous_state['q'] == start-1 and
            _same(previous_state['mu_prefix'], mu[:start]), 'own complete checker continuation at the preceding cutoff')
        text = previous_state['c']
        _require(type(text) is str and 0 < len(text) <= 2500, 'bounded exact harmonic checkpoint')
        try: c = Q(text)
        except (ValueError, ZeroDivisionError) as error: raise ValueError('exact harmonic checkpoint') from error
        _require(str(c) == text and max(abs(c.numerator).bit_length(), c.denominator.bit_length()) <= 4096,
            'canonical exact harmonic checkpoint')
        meter.charge(len(text)+1); mertens = previous_state['M']
        _require(type(mertens) is int and mertens == sum(mu[:start]) and
            c == sum((Q(mu[q], q) for q in range(1, start)), Q(0)), 'exact harmonic and Mertens checkpoint binding')
        lists = {}
        for name in ('abel', 'A', 'D', 'old_weight'):
            _require(type(previous_state[name]) is list and len(previous_state[name]) == len(heights), 'all private height continuations')
            lists[name] = [_complex_read(v) for v in previous_state[name]]
        abel, A, D, old_weight = (lists[n] for n in ('abel', 'A', 'D', 'old_weight'))
        initial_energy = [arb(v) for v in previous_state['last_energy']]
        _require(len(initial_energy) == len(heights) and all(v.is_finite() for v in initial_energy), 'complete previous sampled energy')
    rows = []
    for q in range(start, end+1):
        new_c = c+Q(mu[q], q); new_mertens = mertens+mu[q]
        R = []; sectors = [[], [], []]; shells = []; old_masks = []; child_masks = []
        old_energies = []; child_energies = []
        for h, (t, kernel) in enumerate(zip(heights, kernels)):
            s, z, positive_weight = kernel
            b = (-s*arb(q).log()).exp()
            E = 1+z*(_real(c)-A[h]); P = A[h]**2*E**3-_real(c)**3*D[h]
            old_energy = positive_weight*_norm_square(P)
            child_D = D[h]+b
            child_norms = {}
            for sign in (0, 1, -1):
                child_A = A[h]+sign*b
                counter_c = _real(c+Q(sign, q))
                child_E = 1+z*(counter_c-child_A)
                child_P = child_A**2*child_E**3-counter_c**3*child_D
                child_norms[sign] = positive_weight*_norm_square(child_P)
                meter.charge(1000)
            actual = child_norms[mu[q]]
            old_mask = _inside_window(t, q-1, tau); child_mask = _inside_window(t, q, tau)
            W0 = child_norms[0]-old_energy
            W1 = (child_norms[1]-child_norms[-1])/2
            W2 = (child_norms[1]+child_norms[-1])/2-child_norms[0]
            # The unit is a base state, not a q>=2 recurrence event.
            masked = [W0, W1, W2] if old_mask else [arb(0), arb(0), arb(0)]
            r = mu[q]*masked[1]+mu[q]**2*masked[2] if mu[q] else arb(0)
            shell = actual if child_mask and not old_mask else arb(0)
            old_sample = old_energy if old_mask else arb(0)
            new_sample = actual if child_mask else arb(0)
            _require((new_sample-old_sample-masked[0]-r-shell).contains(0), 'exact sampled energy change includes zero-sector and child shell')
            R.append(r); shells.append(shell)
            for i in range(3): sectors[i].append(masked[i])
            old_masks.append(old_mask); child_masks.append(child_mask)
            old_energies.append(old_sample); child_energies.append(new_sample)
            # Independent complete Abel reconstruction of A at the actual q.
            abel[h] += mertens*(old_weight[h]-b)
            next_A = abel[h]+new_mertens*b
            _require(next_A.overlaps(A[h]+mu[q]*b), 'full Mertens Abel prefix and unit agree with exact update')
            A[h] = next_A; D[h] = child_D; old_weight[h] = b
            meter.charge(1000)
        rows.append(dict(q=q, mu=mu[q], R=R, W=sectors, child_shell=shells, old_masks=old_masks,
            child_masks=child_masks, old_energy=old_energies, child_energy=child_energies))
        c = new_c; mertens = new_mertens; meter.live(100*len(rows)*len(heights)+20*len(mu))
    state = dict(schema='checker-cutoff-continuation-v1', q=end, mu_prefix=mu[:end+1], c=str(c), M=mertens,
        abel=[_complex_record(v) for v in abel], A=[_complex_record(v) for v in A], D=[_complex_record(v) for v in D],
        old_weight=[_complex_record(v) for v in old_weight], last_energy=[_ball(v) for v in rows[-1]['child_energy']])
    return rows, state, initial_energy


def measure(mu, start, end, previous_state, meter):
    _require(type(start) is int and type(end) is int and 2 <= start <= end <= 2048 and len(mu) == end+1,
        'declared complete sampled cutoff range')
    rows, state, initial = _counterfactual_samples(mu, THETA, SIGMA, TAU,
        [Q(t) for t in HEIGHTS], start, end, previous_state, meter)
    records = []
    for row in rows:
        values = [dict(w1=_ball(row['W'][1][h]), w2=_ball(row['W'][2][h]), zero=_ball(row['W'][0][h]),
            shell=_ball(row['child_shell'][h]), energy=_ball(row['child_energy'][h])) for h in range(len(HEIGHTS))]
        records.append(dict(q=row['q'], mu=row['mu'], mask_old=row['old_masks'], mask_new=row['child_masks'], values=values))
    return dict(schema='cutoff-work-samples-v1', start=start, end=end, precision=256, heights=HEIGHTS,
        mu=mu[:end+1], initial_energy=[_ball(v) for v in initial], records=records, state=state)


def program_catalogue():
    rows = [dict(id=i, lane='fixed', kind='fixed', fixed_prime=p) for i, p in enumerate((2, 3, 5))]
    exponents = ['0', '1/6', '1/3', '1/2', '2/3', '1']
    for lo in range(len(exponents)-1):
        for hi in range(lo+1, len(exponents)):
            rows.append(dict(id=len(rows), lane='prefix' if lo == 0 else 'window', kind='window',
                             lower=exponents[lo], upper=exponents[hi]))
    return rows


def _program_primes(program, B, meter):
    catalogue = program_catalogue()
    _require(type(program) is dict and type(program.get('id')) is int and 0 <= program['id'] < len(catalogue) and
        _same(program, catalogue[program['id']]), 'complete frozen 18-program prime grammar')
    if program['kind'] == 'fixed': return [program['fixed_prime']]
    lower, upper = Q(program['lower']), Q(program['upper'])
    return [p for p in range(2, B+1) if _prime(p, meter) and _root_comparison(p, B, upper) and
            (lower == 0 or not _root_comparison(p, B, lower))]


def _parse_ball(text, meter):
    _require(type(text) is str and 0 < len(text) <= 4096, 'bounded serialized sampled real interval')
    value = arb(text)
    _require(value.is_finite() and value.rad() <= arb(2)**-96*(1+abs(value.mid())), 'finite tight sampled interval')
    meter.charge(25+len(text)//10)
    return value


def group_case(program, B, samples, meter):
    _require(ctx.prec == 256 and type(B) is int and 1 <= B <= 1024 and B & (B-1) == 0,
        'independent precision and exact dyadic orbit block')
    _require(samples.get('schema') == 'cutoff-work-samples-v1' and samples['heights'] == HEIGHTS and
        samples['start'] <= B+1 and samples['end'] >= 2*B, 'complete sampled block coverage')
    mu = samples['mu']; validate_mu(mu, meter)
    lookup = {row['q']: row for row in samples['records']}
    _require(len(lookup) == len(samples['records']) and all(q in lookup for q in range(B+1, 2*B+1)), 'every unique event in the orbit block')
    primes = _program_primes(program, B, meter); groups = {}; parsed = {}; zeros = 0
    total = arb(0); odd = arb(0); even = arb(0); absolute = arb(0)
    for q in range(B+1, 2*B+1):
        row = lookup[q]
        _require(row['mu'] == mu[q] and type(row['values']) is list and len(row['values']) == len(HEIGHTS), 'source-signed complete sampled event')
        signed = []
        for value in row['values']:
            w1, w2 = _parse_ball(value['w1'], meter), _parse_ball(value['w2'], meter)
            o, e = mu[q]*w1, mu[q]**2*w2
            r = o+e if mu[q] else arb(0)
            signed.append(r); total += r; odd += o; even += e; absolute += abs(r)
            meter.charge(50)
        parsed[q] = signed
        if mu[q] == 0:
            zeros += 1; continue
        core = q
        for p in primes:
            if core % p == 0: core //= p
            meter.charge(5)
        groups.setdefault(core, []).append(q)
    # Audit independently by columns of each orbit. Each column's absolute
    # value is piecewise constant between events, so record its changes and
    # only then form every partial-prefix cost. No event pairing is omitted.
    changes = [arb(0) for _ in range(B)]
    singleton = arb(0)
    for core, events in sorted(groups.items()):
        for h in range(len(HEIGHTS)):
            running = arb(0); previous_absolute = arb(0)
            for q in events:
                running += parsed[q][h]
                current_absolute = abs(running)
                changes[q-B-1] += current_absolute-previous_absolute
                previous_absolute = current_absolute; meter.charge(40)
            if len(events) == 1: singleton += previous_absolute
    curve = []; cost = arb(0); peak = arb(0)
    for change in changes:
        cost += change; curve.append(cost); peak = peak.max(cost); meter.charge(30)
    bits = None if absolute.contains(0) else 0
    if bits is not None:
        for b in range(1, 21):
            if 2**b*peak <= absolute: bits = b
    _require((total-odd-even).contains(0), 'exact complete joined odd and even signed work')
    meter.live(20*len(groups)+30*len(parsed)*len(HEIGHTS)+10*B)
    return dict(program_id=program['id'], B=B, primes=primes, group_sizes=[[k, len(v)] for k, v in sorted(groups.items())],
        zero_events=zeros, partial_curve=[_ball(v) for v in curve], grouped_peak_absolute=_ball(peak),
        grouped_endpoint_absolute=_ball(curve[-1]), ungrouped_absolute=_ball(absolute), joined_total=_ball(total),
        odd_total=_ball(odd), even_total=_ball(even), singleton_absolute=_ball(singleton),
        nontrivial_partition=len(groups) > 1 and max((len(v) for v in groups.values()), default=0) > 1,
        cancellation_bits=bits)


def select(programs, cases):
    _require(_same(programs, program_catalogue()) and type(cases) is list, 'complete immutable program grammar and discovery cases')
    bases = [64, 128, 256, 512]; lookup = {}
    for case in cases:
        key = (case['program_id'], case['B'])
        _require(key not in lookup, 'unique program/block discovery case')
        lookup[key] = case
    eligible = []; rejected = []
    for program in programs:
        rows = [lookup.get((program['id'], B)) for B in bases]
        if any(row is None for row in rows): reason = 'missing_discovery_case'
        elif any(row['cancellation_bits'] is None for row in rows): reason = 'zero_baseline'
        elif any(row['nontrivial_partition'] is False for row in rows): reason = 'degenerate_partition'
        else:
            _require(all(type(row['cancellation_bits']) is int and 0 <= row['cancellation_bits'] <= 20 and
                row['nontrivial_partition'] is True for row in rows), 'typed finite empirical cancellation rank')
            eligible.append((program, min(row['cancellation_bits'] for row in rows))); continue
        rejected.append(dict(program_id=program['id'], reason=reason))
    chosen = []
    for lane in ('fixed', 'prefix', 'window'):
        options = [(program, bits) for program, bits in eligible if program['lane'] == lane]
        if options:
            program, bits = min(options, key=lambda item: (-item[1], item[0]['id']))
            chosen.append(dict(lane=lane, program_id=program['id'], minimum_cancellation_bits=bits))
    return dict(discovery_bases=bases, selected=chosen, rejected=rejected)


def verify_samples(producer, checker, meter):
    _require(ctx.prec == 256, 'independent interval comparison precision')
    keys = {'schema', 'start', 'end', 'precision', 'heights', 'mu', 'initial_energy', 'records', 'state'}
    for sample, precision in ((producer, 192), (checker, 256)):
        _require(type(sample) is dict and set(sample) == keys and sample['schema'] == 'cutoff-work-samples-v1' and
            sample['precision'] == precision and sample['heights'] == HEIGHTS, 'typed finite sampled-energy role and schema')
        start, end = sample['start'], sample['end']
        _require(type(start) is int and type(end) is int and 2 <= start <= end <= 2048 and len(sample['mu']) == end+1,
            'complete source/sample range')
        validate_mu(sample['mu'], meter)
        _require(type(sample['initial_energy']) is list and len(sample['initial_energy']) == len(HEIGHTS), 'complete initial sampled energy')
        previous = [_parse_ball(v, meter) for v in sample['initial_energy']]
        _require(type(sample['records']) is list and len(sample['records']) == end-start+1, 'complete sequential sampled events')
        for q, row in zip(range(start, end+1), sample['records']):
            _require(type(row) is dict and set(row) == {'q', 'mu', 'mask_old', 'mask_new', 'values'} and
                type(row['q']) is int and row['q'] == q and type(row['mu']) is int and row['mu'] == sample['mu'][q], 'exact sequential source event')
            for field, U in (('mask_old', q-1), ('mask_new', q)):
                expected = [_inside_window(Q(t), U, TAU) for t in HEIGHTS]
                _require(_same(row[field], expected), 'complete strict old-window and child-shell masks')
            _require(type(row['values']) is list and len(row['values']) == len(HEIGHTS), 'all seven declared heights')
            for h, value in enumerate(row['values']):
                _require(type(value) is dict and set(value) == {'w1', 'w2', 'zero', 'shell', 'energy'}, 'all signed sectors, zero sector and shell')
                parsed = {k: _parse_ball(v, meter) for k, v in value.items()}
                if not row['mask_old'][h]:
                    _require(all(parsed[k] == 0 for k in ('w1', 'w2', 'zero')), 'no work outside the complete old window')
                if row['mask_old'][h] == row['mask_new'][h]: _require(parsed['shell'] == 0, 'shell only in the new added window')
                if not row['mask_new'][h]: _require(parsed['energy'] == 0, 'energy only on the current sampled head')
                difference = parsed['energy']-previous[h]-parsed['zero']-row['mu']*parsed['w1']-row['mu']**2*parsed['w2']-parsed['shell']
                _require(difference.contains(0), 'all sampled energy changes, unit base, zero sector and child shell retained')
                previous[h] = parsed['energy']
    _require(all(_same(producer[k], checker[k]) for k in ('schema', 'start', 'end', 'heights', 'mu')), 'identical declared cutoff/height/source coverage')
    for a, b in zip(producer['initial_energy'], checker['initial_energy']):
        _require(_parse_ball(a, meter).overlaps(_parse_ball(b, meter)), 'independent initial energy intervals agree')
    for a, b in zip(producer['records'], checker['records']):
        _require(all(_same(a[k], b[k]) for k in ('q', 'mu', 'mask_old', 'mask_new')), 'same exact signed events and masks')
        for x, y in zip(a['values'], b['values']):
            for key in ('w1', 'w2', 'zero', 'shell', 'energy'):
                _require(_parse_ball(x[key], meter).overlaps(_parse_ball(y[key], meter)), 'independent counterfactual and cross-form intervals agree')
    return dict(verified=True, sampled_events=len(checker['records']), continuous_Gram_proved=False, RH_proved=False)


def verify_cases(producer_cases, checker_cases, meter):
    _require(type(producer_cases) is list and type(checker_cases) is list and len(producer_cases) == len(checker_cases), 'complete compared orbit cases')
    scalars = {'grouped_peak_absolute', 'grouped_endpoint_absolute', 'ungrouped_absolute', 'joined_total', 'odd_total', 'even_total', 'singleton_absolute'}
    metadata = {'program_id', 'B', 'primes', 'group_sizes', 'zero_events', 'nontrivial_partition', 'cancellation_bits'}
    seen = set()
    for producer, checker in zip(producer_cases, checker_cases):
        _require(type(producer) is dict and type(checker) is dict and set(producer) == set(checker) == scalars | metadata | {'partial_curve'}, 'complete orbit score and coverage schema')
        _require(all(_same(producer[k], checker[k]) for k in metadata), 'exact prime membership, groups, zero events and empirical ranks agree')
        key = (checker['program_id'], checker['B']); _require(key not in seen, 'unique compared orbit block'); seen.add(key)
        _require(type(producer['partial_curve']) is list and type(checker['partial_curve']) is list and
            len(producer['partial_curve']) == len(checker['partial_curve']) == checker['B'], 'every integer partial prefix retained')
        for k in scalars:
            _require(_parse_ball(producer[k], meter).overlaps(_parse_ball(checker[k], meter)), 'independent signed and absolute orbit summaries agree')
        for x, y in zip(producer['partial_curve'], checker['partial_curve']):
            _require(_parse_ball(x, meter).overlaps(_parse_ball(y, meter)), 'independent complete partial-prefix variation agrees')
    return dict(verified=True, cases=len(checker_cases), all_partial_prefixes=True, uniform_bound_proved=False, RH_proved=False)


def bind_target(parent, meter):
    """Fast independent ancestry/source and generated-work replay."""
    import check_core_cutoff_work_search as PREVIOUS
    _require(type(parent) is dict and parent.get('schema') == 'core-cutoff-work-feedback-v1' and
        parent.get('whole_signed_bound_proved') is False and parent.get('RH_proved') is False,
        'complete open current cutoff-work obligation')
    prior = dict(parent)
    prior.update(schema='core-weighted-height-feedback-v1', status='open', proof_dependencies=parent['inherited_proof_dependencies'])
    alpha, eligible = PREVIOUS._parent(prior, meter)
    _require(len(eligible) == 1, 'one currently supported numerical low-Gram source target')
    expected = [PREVIOUS._target(target, selected, alpha, meter) for target, selected in eligible]
    _require(_same(parent['cutoff_work_targets'], expected), 'exact inherited head, full signed transition, all costs and generated work')
    target = expected[0]
    _require((target['target_id'], target['p'], target['m'], target['theta'], target['sigma']) ==
        ('centered_A2_E3', 2, 3, '2/3', '9/20'), 'supported actual complete polynomial and contour')
    program = target['programs'][target['selected_program']]
    _require(program['subtract_exact_head'] is True and target['original_low_obligation']['required_upper']['U_power'] == '12/5' and
        target['original_low_obligation']['height'] == dict(prefactor='2', U_power='45/2', interval='abs(t)<H'),
        'unchanged actual all-integer continuous low-Gram goal')
    goals = program['bound_search']['next_bound_targets']
    _require(len(goals) == 1 and goals[0]['status'] == 'open' and goals[0]['power'] == '12/5' and
        goals[0]['R_q']['sectors'] == [1, 2], 'one actual unresolved joined odd/even signed work leaf')
    return dict(target_id=target['target_id'], inherited_bound=deepcopy(goals[0]),
        measure_scope='finite discrete samples only; not quadrature', heights=HEIGHTS,
        source_scalar=target['source_term']['coefficient'], original_continuous_measure='dt/(2*pi)',
        sampled_measure='weight 1 at zero, 2 at each positive declared height; no quadrature widths',
        complete_source_unchanged=True, whole_signed_bound_proved=False, RH_proved=False)


def verify_feedback(parent, binding, selection, cases, output, artifact, meter):
    _require(type(artifact) is str and bool(artifact), 'immutable empirical search artifact reference')
    _require(_same(binding, bind_target(parent, meter)), 'independent complete source and signed-work binding')
    _require(_same(selection, select(program_catalogue(), cases)), 'only the four declared discovery/validation blocks select programs')
    expected = deepcopy(parent)
    expected.update(schema='core-cutoff-prime-orbit-feedback-v1', parent_obligation_file='candidate10_cutoff_work_obligation.json',
        complete_search_artifact=artifact, status='finite_prime_orbit_search_verified_uniform_bound_open')
    expected['prime_orbit_search'] = dict(binding=binding, selected_programs=selection['selected'],
        programme_catalogue=program_catalogue(), finite_results=cases,
        source_history='all Mobius inputs previously observed; new finite cutoff-work observables',
        new_uniform_signed_arithmetic_estimates=0, continuous_integral_control=False)
    expected['inherited_prime_orbit_search_tasks'] = deepcopy(parent['next_search_tasks'])
    _require(type(parent['next_search_tasks']) is list and bool(parent['next_search_tasks']) and
        parent['next_search_tasks'][0]['target_id'] == 'actual_signed_core' and parent['next_search_tasks'][0]['priority'] == 0,
        'original complete signed core remains first')
    tasks = [deepcopy(parent['next_search_tasks'][0])]
    catalogue = program_catalogue()
    for winner in selection['selected']:
        program = catalogue[winner['program_id']]
        tasks.append(dict(priority=1, target_id=binding['target_id'], search_kind='bound_complete_truncated_prime_orbit_work', status='open',
            program=program, expression='sup_(B<V<=2B) integral_R sum_r abs(sum_(B<q<=V, P-free cofactor(q)=r) rho_q(t)) dt/(2*pi)',
            rho_q='1_(abs(t)<H(q-1))*abs(zeta(s+1-theta)/s)^2*(mu(q)*W1(q,s)+mu(q)^2*W2(q,s))',
            R_q=binding['inherited_bound']['R_q'], required_upper='C*B^(12/5)',
            quantifier='every dyadic integer B>=1 and every integer V in (B,2B]; C independent of B,V,X,N',
            relation='stronger sufficient control of joined signed work; not an independent proved estimate',
            retained=['all squarefree faces and exits', 'zero Mobius events have R_q=0', 'q=1 is initial state',
                'odd and even sector interaction', 'actual prefix state at every q', 'complete old height integral at every q',
                'paid W0 and moving shell separately', 'original full source, recovery, drifts and scalar'],
            possible_lemmas=['signed prime/cofactor state variation', 'complete truncated even/odd cube interaction',
                'boundary and singleton control uniform in changing prime set'], finite_samples_establish_bound=False,
            circular_target_substitution_allowed=False, whole_signed_bound_proved=False, RH_proved=False))
    tasks.extend(deepcopy(parent['next_search_tasks'][1:]))
    expected['next_search_tasks'] = tasks
    _require(_same(output, expected), 'complete inherited source and tasks retained; empirical orbit controls stay uniform open obligations')
    meter.charge(500+100*len(tasks))
    return dict(verified=True, uniform_bound_proved=False, continuous_integral_control=False, RH_proved=False)
