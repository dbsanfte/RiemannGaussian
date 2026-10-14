"""Structural generation and exact finite ranking of complete signed potentials.

No optimizer is used. Programs, rather than fitted coefficient vectors, mutate.
Finite constants and rankings do not establish the exported uniform obligation.
"""
from copy import deepcopy
from fractions import Fraction as Q
import json

FAMILIES = ('index_map', 'mask', 'signed_mix', 'nonlinear', 'divisor_sum', 'prime_bank')
LEVELS = (2, 3, 6, 12)
TRAIN = (1, 2, 4, 8, 16, 32, 64)
VALIDATION = (96, 128, 192, 256)
FINAL = (384, 512, 768, 1024)
FLAGS = dict(RH_proved=False, global_bound_proved=False, universal_estimate_proved=False)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def integer(n): return ['int', n]
def variable(name): return ['v', name]
def root(index, order): return ['root', deepcopy(index), 1, order]
def floor_div(left, right): return ['idiv', deepcopy(left), deepcopy(right)]
def prefix(index):
    return ['sum', 'i', integer(1), deepcopy(index), ['x', variable('i')]]
def add(left, right): return ['add', deepcopy(left), deepcopy(right)]
def scale(weight, state): return ['scale', str(Q(weight)), deepcopy(state)]
def product(left, right): return ['mul', deepcopy(left), deepcopy(right)]


def node_count(tree):
    return 1 + sum(node_count(t) for t in tree[1:] if isinstance(t, list))


def complexity(program):
    return sum(node_count(s['tree']) + 1 for s in program['states'])


def state_program(tree, weight='1'):
    return dict(states=[dict(weight=weight, tree=deepcopy(tree))])


def replace_t(tree, index):
    if tree == ['v', 't']:
        return deepcopy(index)
    return [replace_t(t, index) if isinstance(t, list) else t for t in tree]


def remap(tree, index):
    # A zero mapped endpoint gives zero state; no out-of-range source query.
    return ['guard', ['le', integer(1), deepcopy(index)], replace_t(tree, index)]


def generate_initial(meter):
    t, X = variable('t'), variable('X')
    base = prefix(t)
    pool = {family: [] for family in FAMILIES}
    def put(family, tree, production):
        meter.charge(node_count(tree) + 2)
        pool[family].append(dict(program=state_program(tree), production=production))
    for d in (2, 3, 6):
        small = prefix(floor_div(t, integer(d)))
        put('index_map', small, dict(kind='floor_index', divisor=d))
        for sign in (-2, -1, 1, 2):
            put('signed_mix', add(base, scale(sign, small)), dict(kind='signed_sum', divisor=d, coefficient=sign))
        for order in (2, 3, 6):
            moving = root(X, order)
            modulus = ['max', integer(2), moving]
            bound = root(t, order)
            put('index_map', prefix(bound), dict(kind='root_index', order=order))
            put('index_map', prefix(['max', integer(0), ['isub', t, moving]]),
                dict(kind='moving_shift', order=order))
            put('nonlinear', product(small, ['x', bound]),
                dict(kind='root_coefficient_product', divisor=d, order=order))
            put('nonlinear', product(small, prefix(bound)),
                dict(kind='two_prefix_product', divisor=d, order=order))
            i = variable('i')
            for residue in (0, 1):
                predicate = ['eq', ['imod', i, modulus], integer(residue)]
                put('mask', ['sum', 'i', integer(1), t, ['guard', predicate, ['x', i]]],
                    dict(kind='moving_residue', order=order, residue=residue))
            predicate = ['eq', ['gcd', i, modulus], integer(1)]
            put('mask', ['sum', 'i', integer(1), t, ['guard', predicate, ['x', i]]],
                dict(kind='moving_coprime', order=order))
    for order in (2, 3, 6):
        for coefficient in (-1, 1, 2):
            d = variable('d'); small = prefix(floor_div(t, d))
            body = product(['x', d], add(base, scale(coefficient, small)))
            put('divisor_sum', ['sum', 'd', integer(1), root(X, order), body],
                dict(kind='coupled_divisor_sum', order=order, coefficient=coefficient))
        p = variable('p'); small = prefix(floor_div(t, p))
        for coefficient in (0, -1, 1):
            body = small if coefficient == 0 else add(base, scale(coefficient, small))
            tree = ['sum', 'p', integer(2), root(X, order), ['guard', ['prime', p], body]]
            put('prime_bank', tree, dict(kind='coupled_moving_prime_bank', order=order, coefficient=coefficient))
    records = [dict(id=0, generation=0, family='baseline', program=dict(states=[]),
                    complexity=0, origin=dict(kind='unmodified_target_control'))]
    attempts = []
    seen = {canonical(records[0]['program'])}
    for family in FAMILIES:
        candidates = sorted(pool[family], key=lambda r: (complexity(r['program']), canonical(r['program'])))
        accepted = 0
        for item in candidates:
            key = canonical(item['program']); meter.charge(len(key) // 32 + 1)
            reason = 'duplicate_syntax' if key in seen else 'family_quota' if accepted == 8 else None
            attempts.append(dict(family=family, program=item['program'], production=item['production'],
                                 status='generated' if reason is None else 'rejected', reason=reason))
            if reason is not None:
                continue
            seen.add(key); accepted += 1
            records.append(dict(id=len(records), generation=0, family=family,
                                program=item['program'], complexity=complexity(item['program']),
                                origin=item['production']))
    return dict(records=records, attempts=attempts, response_values_used=False)


def generate_mutations(parents, initial, meter):
    t, X = variable('t'), variable('X')
    old = {canonical(r['program']) for r in initial}
    records, attempts = [], []
    if not parents:
        return dict(records=[], attempts=[], response_values_used=True)
    transforms = ('floor_remap', 'moving_shift', 'coprime_guard', 'root_mixture', 'source_product', 'parent_mixture')
    for transform_index, transform in enumerate(transforms):
        accepted = 0
        quota = 6 if transform_index < 2 else 5
        order = list(range(len(parents)))
        offset = transform_index % len(parents)
        order = order[offset:] + order[:offset]
        for position in order:
            parent = parents[position]
            tree = parent['program']['states'][0]['tree']
            if transform == 'floor_remap':
                candidate = remap(tree, floor_div(t, integer(2)))
            elif transform == 'moving_shift':
                candidate = remap(tree, ['max', integer(0), ['isub', t, root(X, 3)]])
            elif transform == 'coprime_guard':
                candidate = ['guard', ['eq', ['gcd', t, ['max', integer(2), root(X, 2)]], integer(1)], deepcopy(tree)]
            elif transform == 'root_mixture':
                candidate = add(tree, scale(-1, prefix(root(t, 6))))
            elif transform == 'source_product':
                candidate = product(tree, ['x', t])
            else:
                other = parents[(position + 1) % len(parents)]['program']['states'][0]['tree']
                candidate = add(tree, scale(-1, other))
            program = state_program(candidate); key = canonical(program)
            meter.charge(node_count(candidate) + len(key) // 32 + 1)
            reason = 'duplicate_syntax' if key in old else 'node_cap' if complexity(program) > 256 else 'mutation_family_quota' if accepted == quota else None
            origin = dict(kind=transform, parent=parent['id'])
            if transform == 'parent_mixture':
                origin['other_parent'] = parents[(position + 1) % len(parents)]['id']
            attempts.append(dict(program=program, origin=origin,
                                 status='generated' if reason is None else 'rejected', reason=reason))
            if reason is not None:
                continue
            old.add(key); accepted += 1
            records.append(dict(id=len(initial) + len(records), generation=1, family=parent['family'],
                                program=program, complexity=complexity(program), origin=origin))
    return dict(records=records, attempts=attempts, response_values_used=True)


def ceil_root(n, q, meter):
    if type(n) is not int or type(q) is not int or n < 1 or q < 1:
        raise ValueError('positive root arguments')
    lo, hi = 0, n
    while lo + 1 < hi:
        meter.charge(q + 2); mid = (lo + hi) // 2
        if meter.number(mid ** q) < n:
            lo = mid
        else:
            hi = mid
    return hi


def fit_constants(cases, meter):
    constants = {}
    for q in LEVELS:
        maximum = Q(0)
        for case in cases:
            meter.charge(3)
            maximum = max(maximum, meter.number(Q(case['innovation']) / ceil_root(case['X'], q, meter)))
        constants[str(q)] = str(maximum)
    return constants


def assess(cases, constants, meter):
    scores = []
    for case in cases:
        for q in LEVELS:
            meter.charge(4)
            bound = meter.number(Q(constants[str(q)]) * ceil_root(case['X'], q, meter))
            scores.append(dict(X=case['X'], q=q, bound=str(bound),
                               passed=Q(case['innovation']) <= bound,
                               in_dyadic_claim_domain=case['X'] & (case['X'] - 1) == 0))
    return scores


def anchored_cost(initial, constants, horizon, meter):
    costs = {}
    for q in LEVELS:
        total = Q(initial['W']); X = 1
        while X < horizon:
            meter.charge(3)
            total = meter.number(total + Q(constants[str(q)]) * ceil_root(X, q, meter)); X *= 2
        costs[str(q)] = str(total)
    return costs


def choose(records, evidence, meter, limit=8):
    """One representative per structural family, then a fixed multi-cost order."""
    by_id = {r['id']: r for r in records}
    valid = []
    for item in evidence:
        meter.charge(12)
        if item.get('status') != 'available' or item['id'] == 0:
            continue
        record = by_id[item['id']]
        costs = anchored_cost(item['initial'], item['constants'], max(VALIDATION), meter)
        failures = sum(not s['passed'] for s in item['validation_scores'])
        key = (failures, tuple(Q(costs[str(q)]) for q in reversed(LEVELS)),
               Q(item['initial']['W']), record['complexity'], record['id'])
        valid.append((key, record))
    valid.sort(key=lambda pair: pair[0])
    selected, seen = [], set()
    for family in FAMILIES:
        candidate = next((r for _, r in valid if r['family'] == family), None)
        if candidate is not None and len(selected) < limit:
            selected.append(candidate); seen.add(candidate['id'])
    for _, record in valid:
        if len(selected) == limit:
            break
        if record['id'] not in seen:
            selected.append(record); seen.add(record['id'])
    return selected


def obligation(record):
    return dict(id=record['id'], program=record['program'], target='actual_mobius_prefix_energy',
        complete_target='W(X)=X^-2 sum_{t=X}^{2X-1} M(t)^2 + V(X)',
        potential='V(X)=X^-2 sum_{t=X}^{2X-1} sum_j w_j U_j(X,t)^2',
        claim='exists integer q0>=1; every integer q>=q0 has finite Cq>=0 independent of dyadic X>=1 such that W(2X)-W(X)<=Cq*ceil(X^(1/q))',
        initial_cost='W(1) must be included; V>=0 by nonnegative rational square weights',
        unresolved=['uniform signed innovation estimate on actual arithmetic',
                    'independent universal source/compiler binding for the full program'],
        status='unproved_candidate', **FLAGS)
