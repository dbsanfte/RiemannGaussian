"""Infer coercive energies and neighboring-parent controls for signed cores."""
from fractions import Fraction as Q
from itertools import combinations, product
from math import gcd, prod
import prime_insertion_search_055 as INTERVAL
import prime_insertion_core_search_056 as RULES

Meter = INTERVAL.Meter


def feature(primes, gamma, upper='1'):
    return {'primes': primes, 'gamma': gamma, 'lower_fraction': '0', 'upper_fraction': upper}


DEFAULT_FEATURES = [feature([2, 3], '5/18'), feature([2], '5/8'),
    feature([3], '5/8'), feature([5], '5/8'), feature([2, 5], '5/18'),
    feature([3, 5], '5/18'), feature([2, 3], '5/18', '1/3'),
    feature([2, 3], '5/18', '1/2'), feature([2, 3], '5/18', '2/3')]


def validate_features(features):
    if type(features) is not list or not 2 <= len(features) <= 32:
        raise ValueError('bounded exact middle-feature dictionary')
    keys = []
    for f in features:
        if type(f) is not dict or set(f) != {'primes', 'gamma', 'lower_fraction', 'upper_fraction'}:
            raise ValueError('exact middle-feature fields')
        RULES.primes(f['primes'])
        if not f['primes'] or RULES.rational(f['gamma'], Q(0), Q(64)) <= 0:
            raise ValueError('nonempty inserted source and positive cutoff exponent')
        lo, hi = [RULES.rational(f[k], Q(0), Q(1)) for k in ('lower_fraction', 'upper_fraction')]
        if lo >= hi: raise ValueError('nonempty fractional subinterval')
        keys.append((tuple(f['primes']), f['gamma'], f['lower_fraction'], f['upper_fraction']))
    if len(set(keys)) != len(keys): raise ValueError('distinct exact source features')


def parent_transports(max_denominator=3, meter=None):
    meter = meter or Meter()
    if type(max_denominator) is not int or not 1 <= max_denominator <= 32:
        raise ValueError('bounded rational transport grammar')
    triples = set()
    for d in range(1, max_denominator+1):
        for a in range(d+1):
            for b in range(d-a+1):
                triples.add((Q(a, d), Q(b, d), Q(d-a-b, d))); meter.charge()
    return [{'id': 'parent_transport_'+str(i).zfill(3), 'weights': list(map(str, w)),
        'center_only': w == (Q(0), Q(1), Q(0))} for i, w in enumerate(sorted(triples))]


def grammar(features=None, meter=None):
    meter = meter or Meter(); features = DEFAULT_FEATURES if features is None else features
    validate_features(features)
    forms = [{'id': 'middle_energy_0000', 'coefficients': [0]*len(features),
        'lambda': '0', 'support': [], 'baseline': True, 'signed_auxiliary': False}]
    for size in (1, 2):
        for indices in combinations(range(len(features)), size):
            if indices == (0,): continue
            for values in product(range(-2, 3), repeat=size):
                meter.charge(size+1)
                if any(v == 0 for v in values) or values[0] <= 0: continue
                common = 0
                for v in values: common = gcd(common, v)
                if common != 1: continue
                vector = [0]*len(features)
                for i, v in zip(indices, values): vector[i] = v
                for weight in ['1/4', '1', '4']:
                    forms.append({'id': 'middle_energy_'+str(len(forms)).zfill(4),
                        'coefficients': vector, 'lambda': weight, 'support': list(indices),
                        'baseline': False, 'signed_auxiliary': min(values) < 0})
    transports = parent_transports(3, meter)
    deltas = ['0', '1/7', '1/3', '1/2', '1']
    return {'schema': 'middle-parent-control-grammar-v1', 'features': features,
        'forms': forms, 'transports': transports, 'decay_exponents': deltas,
        'constants': ['0']+[str(Q(2)**k) for k in range(-24, 13)],
        'bound_candidate_count': len(forms)*len(transports)*len(deltas),
        'recurrence_minimum': 3, 'base_domain': [2, 3, 4, 5], 'parities': [0, 1],
        'operator_target': 'actual moving-middle feature0',
        'proof_provider_used': False, 'uniform_recurrence_proved': False}


def sample_numbers(scales):
    if any(type(n) is not int or n < 3 for n in scales): raise ValueError('parent centers N>=3')
    return sorted({x for n in scales for x in (n-1, n, n+1, 2*n, 2*n+1)})


def source_request(alpha, f, N):
    return {'alpha': alpha, **f, 'N': N}


def score_form(form, table, scales, transports, decays, constants, meter=None):
    meter = meter or Meter()
    energies = {n: INTERVAL.energy(form, table[n], n, meter) for n in sample_numbers(scales)}
    rows = []
    for transport in transports:
        weights = list(map(Q, transport['weights']))
        drifts = []
        for n in scales:
            parent = tuple(sum((w*energies[n+s][k] for w, s in zip(weights, (-1, 0, 1))), Q(0)) for k in (0, 1))
            for r in (0, 1):
                child = energies[2*n+r]
                drifts.append((n, r, (child[0]-parent[1], child[1]-parent[0])))
            meter.charge(128)
        for delta in decays:
            required = max([Q(0)]+[drift[1]/decays[delta][n][0] for n, r, drift in drifts])
            constant = next((c for c in constants if c >= required), None)
            rows.append({'id': form['id']+'_'+transport['id']+'_delta_'+delta.replace('/', '_'),
                'form': form, 'transport': transport, 'delta': delta,
                'C': None if constant is None else str(constant),
                'required_training_C_upper': str(required),
                'training_branches': 2*len(scales),
                'status': 'NO_DECLARED_CONSTANT' if constant is None else 'FINITE_TRAINING_PASS',
                'uniform_recurrence_proved': False, 'uniform_middle_bound_proved': False, 'RH_proved': False})
            meter.charge(64*len(drifts))
    return rows


def rank(row):
    form = row['form']; weights = list(map(Q, row['transport']['weights']))
    return (Q(row['C']), Q(row['required_training_C_upper']), len(form['support']),
        sum(abs(x) for x in form['coefficients']), sum(w.denominator for w in weights),
        Q(form['lambda']), row['id'])


def select(rows):
    eligible = [r for r in rows if r['status'] == 'FINITE_TRAINING_PASS']
    selected, used = [], set()
    for delta in sorted(set(r['delta'] for r in eligible), key=Q):
        group = sorted([r for r in eligible if r['delta'] == delta], key=rank)
        families = [('target_center_control', lambda r: r['form']['baseline'] and r['transport']['center_only']),
            ('target_neighbor_transport', lambda r: r['form']['baseline'] and not r['transport']['center_only']),
            ('signed_auxiliary_control', lambda r: r['form']['signed_auxiliary'])]
        for family, predicate in families:
            row = next((r for r in group if predicate(r)), None)
            if row is not None and row['id'] not in used:
                selected.append(dict(row, archive_family=family)); used.add(row['id'])
    return {'selected': selected, 'eligible_bounds': len(eligible),
        'selection': 'preserve every growth exponent; center control, inferred neighbor transport, signed auxiliary',
        'ranking_uses_unrounded_training_constant': True,
        'final_values_used': False, 'proof_provider_used': False, 'uniform_middle_bound_proved': False}


def recovery_request(alpha, features, row):
    return {'alpha': alpha, 'features': features,
        'coefficients': row['form']['coefficients'], 'lambda': row['form']['lambda'],
        'weights': row['transport']['weights'], 'delta': row['delta'], 'C': row['C']}


def recovery_certificate(request):
    features = request['features']; validate_features(features)
    alpha = RULES.rational(request['alpha'], Q(0), Q(1))
    if not 0 < alpha < 1: raise ValueError('fractional alpha')
    weights = [RULES.rational(w, Q(0), Q(1)) for w in request['weights']]
    if len(weights) != 3 or sum(weights) != 1: raise ValueError('convex neighboring-parent transport')
    vector = request['coefficients']
    if len(vector) != len(features) or any(type(x) is not int for x in vector):
        raise ValueError('complete integer coefficient vector')
    weight = RULES.rational(request['lambda'], Q(0))
    delta, C = [RULES.rational(request[key], Q(0)) for key in ('delta', 'C')]
    envelopes = [12*prod(f['primes'])/(len(f['primes'])-alpha) for f in features]
    base = 5*(envelopes[0]**2+weight*sum(abs(c)*b for c, b in zip(vector, envelopes))**2)
    terms = INTERVAL.drift_polynomial({'coefficients': vector, 'lambda': str(weight)})['terms']
    return {'schema': 'prime-insertion-middle-parent-recovery-v1', 'request': request,
        'matrix_terms': terms, 'source_envelopes': list(map(str, envelopes)), 'base_upper': str(base),
        'recurrence': {'minimum': 3, 'children': [0, 1], 'offsets': [-1, 0, 1],
            'formula': 'F(2N+r)<=sum_s w_s*F(N+s)+C/N^delta', 'status': 'OPEN'},
        'recovery': {'kind': 'bounded' if delta else 'logarithmic',
            'constant': str(base+2*C/delta if delta else base),
            'log_coefficient': '0' if delta else str(C), 'logarithm_base': 2,
            'argument_shift': 2, 'base_maximum': 5},
        'uniform_recurrence_proved': False, 'uniform_middle_bound_proved': False, 'RH_proved': False}


def proof_attempt(request, certificate):
    # A paid pointwise envelope cannot infer a favorable joined signed drift.
    base = Q(certificate['base_upper'])
    return {'paid_source_majorant': {'F_upper': str(base/5)+'*N', 'N_power': '1'},
        'requested_drift_power': str(-Q(request['delta'])),
        'status': 'POINTWISE_PROVIDER_INSUFFICIENT',
        'remaining_uniform_leaf': 'full child energy minus convex neighboring-parent energies, with each source at its own moving cutoff',
        'moving_boundary_terms_omitted': False,
        'uniform_recurrence_proved': False, 'uniform_middle_bound_proved': False, 'RH_proved': False}


def energy_correlations(form, weights):
    if len(weights) != 3 or any(Q(w) < 0 for w in weights) or sum(map(Q, weights)) != 1:
        raise ValueError('full convex-parent weights required')
    result = INTERVAL.drift_polynomial(form)
    result['formula'] = 'sum_(i<=j)Qij*[J_i(2N+r)*J_j(2N+r)/(2N+r)-sum_(s=-1,0,1)w_s*J_i(N+s)*J_j(N+s)/(N+s)]'
    result['weights'] = weights
    result['each_source_uses_its_own_moving_endpoints'] = True
    result['uniform_middle_bound_proved'] = False
    return result
