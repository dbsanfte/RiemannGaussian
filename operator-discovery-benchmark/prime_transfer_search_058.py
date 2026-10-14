"""Discover current operators, retain their weighted forcing and try bounds."""
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb, gcd, lcm, prod
import prime_transfer_algebra_058 as ALG

Meter = ALG.Meter


def canonical(vector, meter=None):
    meter = meter or Meter()
    entries = {i: Q(v) for i, v in vector.items() if Q(v)}
    if not entries: return ()
    denominator = 1
    for v in entries.values(): denominator = lcm(denominator, v.denominator)
    numerators = {i: v.numerator*(denominator//v.denominator) for i, v in entries.items()}
    common = 0
    for v in numerators.values(): common = gcd(common, abs(v))
    sign = 1 if numerators[min(numerators)] > 0 else -1
    meter.charge(4*len(entries)+denominator.bit_length())
    return tuple((i, sign*v//common) for i, v in sorted(numerators.items()))


def split(key, atoms):
    return tuple((i, c) for i, c in key if atoms[i]['divisor'] == 1), tuple((i, c) for i, c in key if atoms[i]['divisor'] > 1)


def rank(key, atoms):
    current, lower = split(key, atoms)
    signed = any(c > 0 for _, c in lower) and any(c < 0 for _, c in lower)
    return (not signed, len(lower), len(current), sum(abs(c) for _, c in key), key)


def promote(atoms, relations, meter=None, limit=512):
    meter = meter or Meter()
    if type(limit) is not int or not 1 <= limit <= 4096: raise ValueError('bounded proof-program archive')
    basis = []
    for row in relations:
        if len(row['coefficients']) != len(atoms): raise ValueError('full basis coordinates')
        key = canonical({i: Q(c) for i, c in enumerate(row['coefficients'])}, meter)
        if key: basis.append(key)
    proposals = {key: {'kind': 'basis', 'basis_indices': [i]} for i, key in enumerate(basis)}
    pair_attempts = 0
    for (i, left), (j, right) in combinations(enumerate(basis), 2):
        a, b = dict(left), dict(right)
        shared = [k for k in a.keys() & b.keys() if atoms[k]['divisor'] == 1]
        if not shared: continue
        # A generic elimination rule: remove the common current atom with
        # most inserted primes, then the smallest attenuation/column.
        anchor = min(shared, key=lambda k: (-len(atoms[k]['primes']), atoms[k]['attenuation'], k))
        key = canonical({k: b[anchor]*a.get(k, 0)-a[anchor]*b.get(k, 0) for k in a.keys() | b.keys()}, meter)
        pair_attempts += 1
        if key and key not in proposals:
            proposals[key] = {'kind': 'pair_current_elimination', 'basis_indices': [i, j], 'anchor_column': anchor}
        if len(proposals) > 100000: raise OverflowError('symbolic proposal capacity')
    representatives = {}
    for key, origin in proposals.items():
        current, lower = split(key, atoms)
        if not current or not lower: continue
        # Equivalent literal current coefficient vectors are a functional
        # cache key, not an artifact hash. Keep their simplest full proof.
        current_key = canonical(dict(current), meter)
        previous = representatives.get(current_key)
        if previous is None or rank(key, atoms) < rank(previous[0], atoms):
            representatives[current_key] = (key, origin)
    ordered = sorted(representatives.values(), key=lambda row: rank(row[0], atoms))
    rows = []
    for index, (key, origin) in enumerate(ordered[:limit]):
        current, lower = split(key, atoms)
        rows.append({'id': 'transfer_operator_'+str(index).zfill(4),
            'terms': [{'column': i, 'coefficient': str(c)} for i, c in key],
            'origin': origin, 'current_columns': [i for i, c in current],
            'lower_columns': [i for i, c in lower],
            'signed_lower_terms': any(c > 0 for _, c in lower) and any(c < 0 for _, c in lower),
            'uniform_signed_bound_proved': False})
    return {'rows': rows, 'basis_relations': len(basis), 'pair_attempts': pair_attempts,
        'distinct_proposals': len(proposals), 'distinct_current_operators': len(representatives),
        'proof_program_limit': limit, 'archive_truncated': len(ordered) > limit,
        'selection': 'signed lower transfers, fewer complete lower states, then expression complexity',
        'numeric_source_values_used': False}


def request(universe, atoms, row, current_only=False):
    terms = [term for term in row['terms'] if not current_only or atoms[term['column']]['divisor'] == 1]
    if not terms: raise ValueError('nonempty exact operator request')
    return {'universe': universe, 'atoms': [atoms[t['column']] for t in terms],
        'coefficients': [t['coefficient'] for t in terms]}


def order_certificate(req, meter=None):
    meter = meter or Meter()
    if any(a['divisor'] != 1 for a in req['atoms']): raise ValueError('integer current-source rule only')
    signature = ALG.signature(req['universe'], req['atoms'], meter)
    coefficients = list(map(Q, req['coefficients']))
    if len(coefficients) != len(req['atoms']): raise ValueError('complete coefficients')
    polynomials = {state: {} for state in product((0, 1), repeat=len(req['universe']))}
    for row in signature['rows']:
        c = sum((Q(e['value'])*coefficients[e['column']] for e in row['entries']), Q(0))
        if not c: continue
        ypoly = polynomials[tuple(row['valuations'])]
        powers = row['monomial']
        for e in product(*(range(k+1) for k in powers)):
            value = c*(-1)**sum(e)*prod(comb(k, j) for k, j in zip(powers, e))
            ypoly[e] = ypoly.get(e, Q(0))+value
            meter.charge(8+len(e))
    cases = []
    for presence, polynomial in sorted(polynomials.items()):
        terms = [{'powers': list(e), 'coefficient': str(c)} for e, c in sorted(polynomial.items()) if c]
        order = min((sum(t['powers']) for t in terms), default=None)
        envelope = sum((abs(Q(t['coefficient']))*prod(p**k for p, k in zip(req['universe'], t['powers'])) for t in terms), Q(0))
        cases.append({'presence': list(presence), 'terms': terms, 'order': order, 'envelope': str(envelope)})
    orders = [case['order'] for case in cases if case['order'] is not None]
    return {'schema': 'prime-transfer-source-order-v1', 'request': req, 'cases': cases,
        'order': min(orders) if orders else None,
        'envelope': str(max(Q(case['envelope']) for case in cases)), 'zero_source': not orders,
        'scope': {'N_minimum': 2, 'N_type': 'integer', 't_lower_exclusive': '0', 't_upper': '1'},
        'whole_bound_proved': False, 'RH_proved': False}


def parameter_grid(max_denominator=64):
    if type(max_denominator) is not int or not 1 <= max_denominator <= 128: raise ValueError('finite rational enumeration budget')
    return sorted({Q(a, b) for b in range(1, max_denominator+1) for a in range(1, 2*b+1)})


def endpoint_program(operator, order, alpha, gamma, tau='1/2'):
    a, g, t = Q(alpha), Q(gamma), Q(tau)
    k, B = order['order'], Q(order['envelope'])
    if order['zero_source'] or k is None or not 0 < a < 1 or k <= a or g <= 0 or not 0 < t < 1:
        raise ValueError('nonzero integrable source and valid endpoint parameters')
    L = sum(map(abs, map(Q, operator['coefficients'])), Q(0))
    req = {'operator': operator, 'alpha': str(a), 'gamma': str(g), 'tau': str(t)}
    return {'schema': 'prime-transfer-endpoints-v1', 'request': req, 'source_order': order,
        'microscopic': {'C': str(12*B/(k-a)), 'N_power': str(1-g*(k-a))},
        'tail': {'C': str(16*L/(t*t*(1-t))), 'N_power': str(1-t)},
        'middle_status': 'OPEN', 'uniform_full_source_bound_proved': False, 'RH_proved': False}


def select_endpoint_gamma(order, alpha, grid, meter=None):
    meter = meter or Meter(); k, a = order['order'], Q(alpha)
    if order['zero_source'] or k is None or k <= a: return None
    for gamma in grid:
        meter.charge(8)
        if 1-gamma*(k-a) <= Q(1, 2): return str(gamma)
    return None


def closure_attempt(universe, atoms, row, order):
    current, lower = split(tuple((t['column'], Q(t['coefficient'])) for t in row['terms']), atoms)
    free_case = next(c for c in order['cases'] if not any(c['presence']))
    # A triangle estimate cannot treat a changed source/weight as the same
    # state. In particular, signed lower coefficients are not contraction.
    current_keys = {(tuple(atoms[i]['primes']), atoms[i]['attenuation']) for i, c in current}
    lower_keys = {(tuple(atoms[i]['primes']), atoms[i]['attenuation']) for i, c in lower}
    self_state = len(current) == 1 and current_keys == lower_keys
    leaves = [{'atom': atoms[i], 'coefficient_on_rhs': str(-c),
        'domain': 'all real x=N/divisor>0 at the common parent integration cutoff',
        'status': 'OPEN_WEIGHTED_REAL_SOURCE_BOUND',
        'integer_middle_certificate_inherited': False} for i, c in lower]
    return {'status': 'OPEN_SOURCE_FORCING', 'free_sector_canceled': not free_case['terms'],
        'literal_self_state_recurrence': self_state,
        'all_lower_weights_and_units_retained': True,
        'unpaid_lower_states': leaves,
        'known_uniform_middle_inputs': 0,
        'pointwise_provider': {'operator_N_power': '1', 'required_N_power': '1/2',
            'condition': '0<alpha<min(1,source_order)', 'C': '12*source_envelope/(source_order-alpha)',
            'status': 'INSUFFICIENT_EXPONENT'},
        'homogeneous_lower_identity_is_not_target_domination': True,
        'uniform_signed_bound_proved': False, 'RH_proved': False}


def identify_exchange(universe, atoms, row, meter=None):
    meter = meter or Meter()
    current, lower = split(tuple((t['column'], Q(t['coefficient'])) for t in row['terms']), atoms)
    actual = canonical(dict(current), meter)
    positions = {(tuple(a['primes']), a['divisor'], a['attenuation']): i for i, a in enumerate(atoms)}
    for p, q in combinations(universe, 2):
        others = [r for r in universe if r not in (p, q)]
        for mask in range(1 << len(others)):
            R = [r for j, r in enumerate(others) if mask & (1 << j)]
            rp, rq = tuple(sorted(R+[p])), tuple(sorted(R+[q]))
            candidate = {(rp, 1, 1): 1, (rp, 1, q): -1, (rq, 1, 1): -1, (rq, 1, p): 1}
            if not all(k in positions for k in candidate): continue
            key = canonical({positions[k]: c for k, c in candidate.items()}, meter)
            if key == actual:
                index = min(positions[k] for k in candidate)
                template = {positions[k]: Q(c) for k, c in candidate.items()}
                return {'family': 'weighted_prime_exchange', 'R': R, 'p': p, 'q': q,
                    'scalar': str(dict(current)[index]/template[index]),
                    'interpretation_only_after_inference': True,
                    'RH_bridge': 'CONDITIONAL_SOURCE_ONLY_REVIEW_REQUIRED', 'uniform_bound_proved': False}
    return {'family': 'unclassified_transfer_operator', 'uniform_bound_proved': False}


def select_for_proof(rows, limit=16):
    # Keep the named, independently reviewable family and unclassified
    # alternatives. No measured value or fitted constant enters this gate.
    selected = []
    named = [r for r in rows if r['interpretation']['family'] == 'weighted_prime_exchange']
    others = [r for r in rows if r['interpretation']['family'] != 'weighted_prime_exchange']
    for r in named[:limit//2]: selected.append(r)
    seen = set()
    for r in others:
        if len(selected) >= limit: break
        key = (r['source_order']['order'], r['candidate']['signed_lower_terms'],
            tuple(sorted({tuple(leaf['atom']['primes']) for leaf in r['proof_attempt']['unpaid_lower_states']})))
        if key not in seen: selected.append(r); seen.add(key)
    return selected
