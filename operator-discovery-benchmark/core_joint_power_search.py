"""Synthesize joint power drifts and controls from complete finite factors.

The primitive integral remainder theorem is supplied. Which source pieces
to center, their exact moment polynomial, and the resulting bound are
generated without source observations or nominated coefficients.
"""
from fractions import Fraction as Q
from math import ceil

THETAS = ('1/6', '1/3', '1/2', '2/3', '5/6', '1')


def ref_key(reference):
    s = reference['source_key']
    return s['mode'], s['a'], s['b'], reference['depth'], reference['piece']


def resolve(prefix_result, references):
    terms = {(t['key']['mode'], t['key']['a'], t['key']['b']): t for t in prefix_result['terms']}
    seen, result = set(), []
    for reference in references:
        key = ref_key(reference)
        if key in seen or key[:3] not in terms:
            raise ValueError('unique complete inherited piece reference')
        seen.add(key)
        term = terms[key[:3]]
        if key[3] != term['selected_depth']:
            raise ValueError('reference to selected centering only')
        pieces = term['alternatives'][key[3]]['pieces']
        if type(key[4]) is not int or not 0 <= key[4] < len(pieces):
            raise ValueError('complete inherited piece index')
        result.append((reference, term, pieces[key[4]]))
    return result


def eligible_pieces(row, prefix_result, references):
    modes = {c['mode']['name']: c['mode'] for c in row['cases']}
    eligible = []
    for index, (reference, term, piece) in enumerate(resolve(prefix_result, references)):
        factors = list(piece['expression'])
        if factors.count('K') != 1:
            continue
        factors.remove('K')
        if any(f not in ('A', 'B', 'C') for f in factors):
            continue
        shift = modes[term['key']['mode']]['positive_shift']
        if shift is None or not 0 <= Q(shift) < 1:
            raise ValueError('power kernel needs its actual source shift')
        eligible.append(dict(id=index, reference=reference, source_scalar=term['source_scalar'],
            coefficient=piece['coefficient'], factors=factors, kernel_shift=shift, old_energy=piece['energy']))
    if len(eligible) > 12:
        raise ValueError('bounded exhaustive subset search')
    return eligible


def profiles(shifts):
    result = []
    for shift in sorted(set(shifts), key=Q):
        power = 1-Q(shift)
        for theta in THETAS:
            valid = Q(theta) == power
            result.append(dict(kernel_shift=shift, theta=theta,
                status='supported' if valid else 'unmatched_power_profile',
                leading_power=str(power), leading_coefficient=str(1/power),
                solved_multiplier=str(1/power) if valid else None,
                universal_remainder_constant=str(1/power) if valid else None))
    return result


def scalar_polynomial(piece):
    """Exact signed finite moment, before dividing by theta."""
    c = Q(piece['coefficient'])
    scalar = piece['source_scalar']
    if scalar in ('beta', '-beta'):
        c *= Q(9, 2)*(1 if scalar == 'beta' else -1)
        ru = 0
    elif scalar == '-R_u':
        c = -c
        ru = 1
    else:
        raise ValueError('complete actual source scalar')
    powers = tuple(piece['factors'].count(name) for name in ('A', 'B', 'C'))+(ru,)
    return powers, c


def energy(constant, power, log_degree=0):
    """Complete prefix -> shared-horizon block energy, including log payment."""
    c, e, k = 4*Q(constant)**2, 2*Q(power)-1, 2*log_degree
    if e > 0 or (e == 0 and k):
        paid = None
    elif k == 0:
        paid = c
    else:
        paid = c*2**k*(1+(Q(k)/(-e))**k)
    return dict(constant=str(c), power=str(e), log_degree=k,
                uniform_constant=None if paid is None else str(paid))


def finite_remainder(piece, theta, alpha, gamma):
    powers, coefficient = scalar_polynomial(piece)
    p, q, r, ru = powers
    constant = abs(coefficient)*3**q*2**r*5**ru/Q(theta)
    power = p*Q(alpha)+q*Q(gamma)/3
    return dict(eligible_id=piece['id'], theta=theta,
        definition='signed K*h minus its complete signed moment/theta times J_theta',
        prefix_bound=dict(constant=str(constant), power=str(power), log_degree=0),
        energy=energy(constant, power))


def moment_envelope(s, cutoff_power):
    s, r = Q(s), Q(cutoff_power)
    if s < 0 or not 0 < r < 1:
        raise ValueError('nonnegative moment weight and strict cutoff power')
    if s < 1:
        return 1/(1-s), r*(1-s), 0
    if s == 1:
        return Q(1), Q(0), 1
    return s/(s-1), Q(0), 0


def drift_bound(theta, polynomial, alpha, gamma):
    factors = [moment_envelope(theta, alpha), moment_envelope(Q(theta)+Q(2, 3), gamma),
               (Q(2), Q(0), 0), (Q(5), Q(0), 0)]
    costs = []
    for term in polynomial:
        c, e, k = abs(Q(term['coefficient'])), Q(0), 0
        for count, (constant, power, degree) in zip(term['powers'], factors):
            c *= constant**count
            e += power*count
            k += degree*count
        costs.append((c, e, k))
    if not costs:
        raise ValueError('zero drift must be removed by exact polynomial cancellation')
    # Separate maxima are essential: a lower N power may carry more logs.
    constant = sum(c for c, _, _ in costs)
    power = Q(theta)+max(e for _, e, _ in costs)
    degree = max(k for _, _, k in costs)
    return dict(constant=str(constant), power=str(power), log_degree=degree)


def subset(mask, eligible, profile_trials, alpha, gamma, meter):
    supported = {p['kernel_shift']: p for p in profile_trials if p['status'] == 'supported'}
    chosen = [p for i, p in enumerate(eligible) if mask & (1 << i)]
    unchanged = [p for i, p in enumerate(eligible) if not mask & (1 << i)]
    if any(p['kernel_shift'] not in supported for p in chosen):
        return dict(mask=mask, status='unsupported_power_profile')
    polynomials, remainders = {}, []
    for piece in chosen:
        theta = supported[piece['kernel_shift']]['theta']
        remainders.append(finite_remainder(piece, theta, alpha, gamma))
        powers, coefficient = scalar_polynomial(piece)
        polynomial = polynomials.setdefault(theta, {})
        polynomial[powers] = polynomial.get(powers, Q(0))+coefficient/Q(theta)
        meter.charge(100)
    drifts = []
    for theta, data in sorted(polynomials.items(), key=lambda x: Q(x[0])):
        polynomial = [dict(powers=list(powers), coefficient=str(c))
                      for powers, c in sorted(data.items()) if c]
        if polynomial:
            prefix = drift_bound(theta, polynomial, alpha, gamma)
            drifts.append(dict(theta=theta, polynomial=polynomial, prefix_bound=prefix,
                energy=energy(prefix['constant'], prefix['power'], prefix['log_degree'])))
        meter.charge(80*len(data))
    bounds = [p['old_energy'] for p in unchanged]+[r['energy'] for r in remainders]+[d['energy'] for d in drifts]
    unpaid = [b for b in bounds if b['uniform_constant'] is None]
    worst = max([(Q(0), 0)]+[(Q(b['power']), b['log_degree']) for b in unpaid])
    score = [str(worst[0]), worst[1], len(unpaid), len(chosen), mask]
    return dict(mask=mask, status='exact_decomposition_with_bound_certificates',
        centered_ids=[p['id'] for p in chosen], unchanged_ids=[p['id'] for p in unchanged],
        remainders=remainders, joint_drifts=drifts, score=score,
        comparison_scope='eligible finite-factor subsum only; other full-core pieces are unchanged',
        whole_signed_bound_proved=False)


def search(row, prefix_result, references, meter):
    eligible = eligible_pieces(row, prefix_result, references)
    profile_trials = profiles(p['kernel_shift'] for p in eligible)
    alternatives = [subset(mask, eligible, profile_trials, row['alpha'], row['gamma'], meter)
                    for mask in range(1 << len(eligible))]
    admissible = [r for r in alternatives if r['status'] == 'exact_decomposition_with_bound_certificates']
    selected = min(admissible, key=lambda r: (Q(r['score'][0]), *r['score'][1:]))
    return dict(schema='core-joint-power-search-v1', geometry_id=row['id'], alpha=row['alpha'], gamma=row['gamma'],
        moment_variable_order=['m_theta_A', 'm_theta_B', 'c_U', 'R_u'],
        operator_definition='J_theta(n)=n^theta-(n-1)^theta; complete finite moments multiply under Dirichlet convolution',
        remaining_refs=references, eligible=eligible, profile_trials=profile_trials,
        alternatives=alternatives, selected_mask=selected['mask'],
        statistics=dict(eligible_pieces=len(eligible), profile_trials=len(profile_trials),
            rejected_profiles=sum(p['status'] != 'supported' for p in profile_trials),
            subsets=len(alternatives), selected_centered=len(selected['centered_ids']),
            selected_joint_drifts=len(selected['joint_drifts']),
            selected_paid_remainders=sum(r['energy']['uniform_constant'] is not None for r in selected['remainders'])),
        whole_signed_bound_proved=False, RH_proved=False)


def reduction(parent, construction, result):
    if parent['remaining_signed_pieces'] != result['remaining_refs']:
        raise ValueError('exact complete current remaining vector')
    selected = result['alternatives'][result['selected_mask']]
    by_id = {p['id']: p for p in result['eligible']}
    centered_refs = {ref_key(by_id[i]['reference']) for i in selected['centered_ids']}
    original_remaining = [r for r in result['remaining_refs'] if ref_key(r) not in centered_refs]
    paid, open_remainders, open_drifts = [], [], []
    for remainder in selected['remainders']:
        c = remainder['energy']['uniform_constant']
        if c is None:
            open_remainders.append(remainder['eligible_id'])
        else:
            paid.append(dict(kind='remainder', eligible_id=remainder['eligible_id'], uniform_energy_constant=c))
    for drift in selected['joint_drifts']:
        c = drift['energy']['uniform_constant']
        if c is None:
            open_drifts.append(drift['theta'])
        else:
            paid.append(dict(kind='drift', theta=drift['theta'], uniform_energy_constant=c))
    channel = Q(0)
    for c in construction['channels']:
        p = list(map(Q, c['polynomial']))
        eta = Q(c['eta'])
        if eta < 0:
            raise ValueError('nonnegative channel weight')
        channel += (2**ceil(eta)*(abs(p[0])+2*sum(map(abs, p[1:]))))**2
    degree = parent['goal']['p']
    if Q(degree) < 0:
        raise ValueError('nonnegative inherited target degree')
    constant = len(paid)*channel*sum((Q(p['uniform_energy_constant']) for p in paid), Q(0))
    return dict(schema='core-joint-power-reduction-v1', parent_obligation_id=parent['parent_obligation_id'],
        geometry_id=result['geometry_id'], selected_mask=result['selected_mask'], newly_paid=paid,
        remaining_source_refs=original_remaining, remaining_centered_remainders=open_remainders,
        remaining_joint_drifts=open_drifts, channel_abel_constant=str(channel), combined_paid_constant=str(constant),
        exact_split='Z_old=P_new+Z_new; Z_new retains all untouched pieces, unpaid centered remainders, complete joint drifts, and -e where e=f-g',
        recovery='S_old<=2*S_new+2*C_new; S_new<=2*S_old+2*C_new',
        goal=dict(expression='S_new(X)<=C*(1+log2X)^p for every dyadicX>=1',
                  p=degree, status='open', same_finite_constant=True),
        full_finite_moments_retained=True, all_remaining_crosses_retained=True,
        transport_error_retained=True, original_fixed_recurrence_discharged=False,
        whole_signed_bound_proved=False, RH_proved=False)
