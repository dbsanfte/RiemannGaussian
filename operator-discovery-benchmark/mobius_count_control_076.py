"""Discover variable-count operators under a paid correlation budget.

The remaining innovation bound is a conjecture outside finite tests.
"""
from fractions import Fraction as Q
from functools import lru_cache
from collections import OrderedDict

import numpy as np
from scipy.optimize import linprog

import mobius_prime_moment_075 as S
import mobius_prime_moment_feedback_075 as F


CERTIFIED_GAMMAS = ['1/2', '17/31', '7/11', '2/3', '1', '3/2']
OPEN_GAMMAS = ['1/3'] + CERTIFIED_GAMMAS
SOURCE_PARENT_LIMIT = 16_000_003  # inherited source horizon<=4,000,000
CACHE_ALLOWANCE = 512*1024**2


def numeric_bytes(value):
    if isinstance(value, Q):
        return 128+(value.numerator.bit_length()+value.denominator.bit_length()+7)//8
    if type(value) is int:
        return 64+(value.bit_length()+7)//8
    return 128+sum(numeric_bytes(x) for x in value)


class ByteCache:
    """Functional numeric cache bounded by prospective bytes, not entry count."""
    def __init__(self, limit=64*1024**2):
        self.limit, self.bytes = limit, 0
        self.values = OrderedDict()

    def get(self, key, compute):
        if key in self.values:
            value, size = self.values.pop(key)
            self.values[key] = (value, size)
            return value
        value = compute()
        size = numeric_bytes(key)+numeric_bytes(value)+256
        if size <= self.limit:
            while self.bytes+size > self.limit:
                _, (_, old_size) = self.values.popitem(last=False)
                self.bytes -= old_size
            self.values[key] = (value, size)
            self.bytes += size
        return value


_COUNT_CACHE, _FEATURE_CACHE = ByteCache(), ByteCache()


def count_bounds(count, gamma, precision):
    # Bypass075's entry-count LRU; arbitrary admitted exponents can produce
    # large endpoints, so076 owns a byte-bounded cache for this operation.
    return _COUNT_CACHE.get((count,gamma,precision),
                            lambda:F.count_power_bounds.__wrapped__(count,gamma,precision))


@lru_cache(maxsize=64)
def price_data(theta, multipliers, base_u):
    prices = tuple(S.price_bounds(dict(grid=80,theta=list(theta),multipliers=list(multipliers)),base_u))
    return prices, tuple(S.sqrt_upper(h) for h in prices)


def atom_key(atom):
    return atom['column'], S.B.rational(atom['gamma'])


def admit_atoms(atoms, spec):
    dimension = len(S.labels(spec))
    if type(atoms) is not list or len(atoms) > 256:
        raise ValueError('bounded atom list')
    keys = []
    for atom in atoms:
        if type(atom) is not dict or set(atom) != {'column', 'gamma'}:
            raise ValueError('exact atom schema')
        column, gamma = atom_key(atom)
        if type(column) is not int or not 0 <= column < dimension or gamma < 0:
            raise ValueError('valid source column and nonnegative rational power')
        keys.append((column, gamma))
    if keys != sorted(set(keys)):
        raise ValueError('unique ordered atoms')
    return keys


def grammar(spec, gammas, kind):
    S.parse_spec(spec)
    gs = sorted(set(map(S.B.rational, gammas)))
    if not gs or gs[0] < 0 or kind not in ('prime_only', 'joint', 'direct_only'):
        raise ValueError('count grammar inputs')
    split = len(spec['theta']) - 1
    atoms = []
    if kind != 'direct_only':
        atoms.extend(dict(column=i, gamma=str(g)) for i in range(split) for g in gs)
    if kind != 'prime_only':
        atoms.extend(dict(column=i, gamma='0') for i in range(split, len(S.labels(spec))))
    admit_atoms(atoms, spec)
    return atoms


def compact(atoms, coefficients):
    if len(atoms) != len(coefficients):
        raise ValueError('complete coefficients')
    active = [(atom, Q(a)) for atom, a in zip(atoms, coefficients) if a]
    return [p[0] for p in active], [p[1] for p in active]


def feature_enclosure(value, count, gamma, precision):
    if type(count) is not int or count < 0 or (not count and value):
        raise ValueError('actual counts and empty block sum')
    if not value:
        return Q(0), Q(0)
    def compute():
        lower, upper = count_bounds(max(1,count),gamma,precision)
        ends = Q(value)/lower, Q(value)/upper
        return min(ends),max(ends)
    return _FEATURE_CACHE.get((value,count,gamma,precision),compute)


def operator_enclosure(atoms, coefficients, row, precision=20):
    lo = hi = Q(0)
    for atom, a in zip(atoms, coefficients):
        if not a:
            continue
        column, gamma = atom_key(atom)
        lower, upper = feature_enclosure(row['components'][column], row['counts'][column], gamma, precision)
        left, right = a*lower, a*upper
        lo += min(left, right)
        hi += max(left, right)
    return lo, hi


def squared_interval(lo, hi):
    if lo > hi:
        raise ValueError('ordered interval')
    return (Q(0) if lo <= 0 <= hi else min(lo*lo, hi*hi), max(lo*lo, hi*hi))


def residual_enclosure(atoms, coefficients, row, q, precision=20):
    lower, upper = operator_enclosure(atoms, coefficients, row, precision)
    a, b = squared_interval(Q(row['z'])-upper, Q(row['z'])-lower)
    nlo, nhi = S.B.power_bounds(row['u'], q, precision)
    return a/nhi, b/nlo


def structural_weights(spec, atoms, coefficients, base_u):
    """Rational near-optimal weighted Cauchy price, without a fitted beta."""
    prices, roots = price_data(tuple(spec['theta']),tuple(spec['multipliers']),base_u)
    A = [Q(0)]*len(prices)
    for atom, a in zip(atoms, coefficients):
        A[atom['column']] += abs(a)
    exposure = S.dot(A, roots)
    beta = [v*exposure/h if v else Q(0) for v, h in zip(A, roots)]
    rho = S.dot(beta, prices)
    if rho > exposure*exposure:
        raise ArithmeticError('rational Cauchy price')
    return dict(beta=beta, prices=prices, roots=roots, exposure=exposure, rho=rho, column_mass=A)


def floating_features(data, atoms, meter):
    admit_atoms(atoms, data['spec'])
    meter.reserve(CACHE_ALLOWANCE+4096*max(1, len(atoms))*len(data['rows']))
    values = np.array([r['components'] for r in data['rows']], dtype=float)
    counts = np.maximum(1.0, np.array([r['counts'] for r in data['rows']], dtype=float))
    result = np.empty((len(data['rows']), len(atoms)), dtype=float)
    for j, atom in enumerate(atoms):
        column, gamma = atom_key(atom)
        result[:, j] = values[:, column] / counts[:, column]**float(gamma)
    meter.charge(len(data['rows'])*max(1, len(atoms))*10)
    return result


def fit_operator(data, atoms, q, radius, base_u, meter):
    """One LP jointly learns the operator and a finite residual bound."""
    q, radius = Q(q), Q(radius)
    if not 1 <= q < 2 or not 0 < radius < 1 or not atoms:
        raise ValueError('nonzero-budget minimax domain')
    matrix = floating_features(data, atoms, meter)
    m, d = matrix.shape
    meter.reserve(CACHE_ALLOWANCE+8192*m*d)
    normalizer = np.array([r['u'] for r in data['rows']], dtype=float)**(float(q)/2)
    A = matrix / normalizer[:, None]
    y = np.array([r['z'] for r in data['rows']], dtype=float) / normalizer
    _, roots = price_data(tuple(data['spec']['theta']),tuple(data['spec']['multipliers']),base_u)
    costs = [float(roots[atom['column']]) for atom in atoms]
    # a=a_plus-a_minus, with an explicit complete weighted l1 price.
    constraints = np.vstack([
        np.column_stack([A, -A, -np.ones(m)]),
        np.column_stack([-A, A, -np.ones(m)]),
        np.array([costs+costs+[0.0]])])
    rhs = np.concatenate([y, -y, [float(radius)]])
    result = linprog([0.0]*(2*d)+[1.0], A_ub=constraints, b_ub=rhs,
                     bounds=(0, None), method='highs', options={'time_limit': 120})
    meter.charge(int(constraints.size)*max(1, result.nit or 0))
    if not result.success:
        return dict(status='LP_PROPOSAL_UNAVAILABLE', message=result.message)
    coefficients = [Q(round(float(a-b)*8192), 8192) for a, b in zip(result.x[:d], result.x[d:2*d])]
    price = structural_weights(data['spec'], atoms, coefficients, base_u)
    factor = min(Q(1), radius/price['exposure']) if price['exposure'] else Q(1)
    coefficients = [factor*a for a in coefficients]
    new_atoms, coefficients = compact(atoms, coefficients)
    paid = structural_weights(data['spec'], new_atoms, coefficients, base_u)
    if paid['exposure'] > radius:
        raise ArithmeticError('exact coefficient rounding budget')
    return dict(status='PROPOSED', atoms=new_atoms, coefficients=list(map(str, coefficients)),
                radius=str(radius), exposure=str(paid['exposure']), rounding_rescale=str(factor),
                floating_residual_norm=float(result.fun), nonzero_atoms=len(new_atoms),
                proposed_from='minimax over generated count-power atoms')


def make_program(data, atoms, coefficients, q, mode, base_u=4096, precision=20, meter=None):
    meter = meter or S.Meter()
    admit_atoms(atoms, data['spec'])
    coefficients = list(map(Q, coefficients))
    atoms, coefficients = compact(atoms, coefficients)
    q = S.B.rational(q)
    if not 1 <= q < 2 or mode not in ('structural_cauchy', 'arithmetic_claim'):
        raise ValueError('proof mode and power target')
    if type(base_u) is not int or not 16 <= base_u <= SOURCE_PARENT_LIMIT or not data['rows'] or any(type(r['u']) is not int or not base_u < r['u'] <= SOURCE_PARENT_LIMIT for r in data['rows']):
        raise ValueError('nonempty discovery domain above base')
    meter.reserve(CACHE_ALLOWANCE+40*(base_u//4+1)+128*base_u+4096*len(data['rows'])*max(1,len(atoms)))
    split = len(data['spec']['theta']) - 1
    if mode == 'structural_cauchy' and any(a and atom['column'] < split and Q(atom['gamma']) < Q(1,2) for atom, a in zip(atoms, coefficients)):
        raise ValueError('unpaid count power in structural branch')
    paid = structural_weights(data['spec'], atoms, coefficients, base_u)
    r = S.sqrt_upper(paid['rho'])
    if not 0 <= r < 1:
        raise ValueError('contractive full moment price required')
    worst = max(residual_enclosure(atoms, coefficients, row, q, precision)[1] for row in data['rows'])
    # Upward dyadic rounding keeps certificate size bounded and leaves no
    # accidental dependence on a huge common denominator of root endpoints.
    C = S.ceiling_grid(worst, 1 << 40)
    # Inherited base helper owns its own meter; account a conservative
    # sieve/root-work allowance here as well as the simultaneous memory above.
    meter.charge(base_u*(30+q.numerator.bit_length()+q.denominator.bit_length()+precision))
    base = S.ceiling_grid(S.base_upper(base_u, q, precision), 1 << 40)
    B = max(base, C/(1-r)**2)
    meter.charge(30*len(data['rows'])*max(1, len(atoms)) + 10*base_u)
    return dict(schema='count-adaptive-control-program-v1', spec=data['spec'], atoms=atoms,
        operator=list(map(str, coefficients)), beta=list(map(str, paid['beta'])), correlation_mode=mode,
        q=str(q), base_u=base_u, price_bounds=list(map(str, paid['prices'])), rho_upper=str(paid['rho']),
        sqrt_rho_upper=str(r), innovation_C=str(C), base_upper=str(base), bound_B=str(B), precision=precision,
        training_scales=[row['u'] for row in data['rows']], uniform_innovation_proved=False,
        uniform_source_bound_proved=False, RH_proved=False)


def imported_operators(feedback, spec):
    """075 obstructions become operators, not names or an anticipated answer."""
    if feedback['source_spec'] != spec or feedback['schema'] != 'coherent-prime-control-feedback-v1':
        raise ValueError('matching exact feedback source')
    split = len(spec['theta'])-1
    outputs = []
    for index, template in enumerate(feedback['controls']):
        atoms = [dict(column=i, gamma=template['gamma'] if i<split else '0')
                 for i, a in enumerate(template['operator']) if Q(a)]
        coefficients = [Q(a) for a in template['operator'] if Q(a)]
        admit_atoms(atoms, spec)
        kind = 'joint' if any(a['column']>=split for a in atoms) else 'prime_only'
        mode = 'structural_cauchy' if all(a['column']>=split or Q(a['gamma'])>=Q(1,2) for a in atoms) else 'arithmetic_claim'
        outputs.append(dict(id='import_'+str(index).zfill(4), atoms=atoms, coefficients=list(map(str, coefficients)),
            kind=kind, mode=mode, origin_record=template['origin_record'], gamma=template['gamma']))
    return outputs


def select_imported(data, feedback, q, base_u, meter):
    """Float scores select formulas only; exact programs and checkers follow."""
    library = imported_operators(feedback, data['spec'])
    atoms = sorted({(a['column'], a['gamma']) for row in library for a in row['atoms']}, key=lambda p:(p[0], Q(p[1])))
    atom_specs = [dict(column=i, gamma=g) for i,g in atoms]
    features = floating_features(data, atom_specs, meter)
    positions = {p:i for i,p in enumerate(atoms)}
    target = np.array([row['z'] for row in data['rows']], dtype=float)
    normal = np.array([row['u'] for row in data['rows']], dtype=float)**float(Q(q))
    offers = []
    # Small column blocks avoid one giant rows-by-templates temporary.
    for item in library:
        coeff = list(map(Q, item['coefficients']))
        paid = structural_weights(data['spec'], item['atoms'], coeff, base_u)
        r = S.sqrt_upper(paid['rho'])
        if r >= 1:
            continue
        prediction = sum((float(a)*features[:,positions[(atom['column'],atom['gamma'])]] for atom,a in zip(item['atoms'],coeff)), np.zeros(len(target)))
        C = float(np.max((target-prediction)**2/normal))
        offers.append(dict(id=item['id'], kind=item['kind'], mode=item['mode'], innovation_score=C,
                           transfer_score=C/float((1-r)**2)))
    chosen = {}
    for kind in ('prime_only', 'joint'):
        for mode in ('structural_cauchy', 'arithmetic_claim'):
            group = [o for o in offers if o['kind']==kind and o['mode']==mode]
            for objective in ('innovation_score','transfer_score'):
                if group:
                    best = min(group, key=lambda x:(x[objective],x['transfer_score'],x['id']))
                    chosen.setdefault(best['id'],dict(best,selected_by=[]))['selected_by'].append(objective)
    lookup = {item['id']:item for item in library}
    meter.charge(20*len(library)*len(data['rows']))
    return dict(offers=offers, selected=[dict(lookup[key], selection=sel) for key,sel in chosen.items()],
                library_operators=len(library))


def diagnostics(program, baseline):
    C, C0 = Q(program['innovation_C']), Q(baseline['innovation_C'])
    r = Q(program['sqrt_rho_upper'])
    a = list(map(Q,program['operator']))
    paid = structural_weights(program['spec'],program['atoms'],a,program['base_u'])
    return dict(nonzero_atoms=len(a), active_gammas=sorted({x['gamma'] for x in program['atoms']},key=Q),
        repeated_source_columns=len({x['column'] for x in program['atoms']}) < len(a),
        exact_weighted_exposure=str(paid['exposure']), finite_residual_ratio=str(C/C0) if C0 else None,
        complete_transfer_ratio=str(C/((1-r)**2*C0)) if C0 else None,
        complete_bound_ratio=str(Q(program['bound_B'])/Q(baseline['bound_B'])) if Q(baseline['bound_B']) else None,
        transfer_ratio_assumes_required_correlation=True,
        base_dominated=Q(program['bound_B'])==Q(program['base_upper']),
        finite_residual_gain_is_not_a_uniform_proof=True)


def obligations(program, evaluation):
    leaves = []
    for lemma in ('innovation','correlation'):
        if lemma=='correlation' and evaluation.get('universal_correlation_proved'):
            continue
        failures = [w for w in evaluation.get('failures',[]) if w['lemma']==lemma]
        refuted = next((w for w in failures if w['status']=='REFUTED'),None)
        leaves.append(dict(lemma=lemma,
            status='FINITE_COUNTEREXAMPLE' if refuted else 'FINITE_ROUNDING_UNRESOLVED' if failures else 'UNIFORM_PROOF_REQUIRED',
            first_witness=refuted or (failures[0] if failures else None),
            all_integer_domain_above=program['base_u'], q=program['q'], atoms=program['atoms'],
            operator=program['operator'], beta=program['beta'], innovation_C=program['innovation_C'],
            must_not_assume_parent_source_bound=True,
            requested_construction='signed residual identity or a independently paid residual energy' if lemma=='innovation' else 'an all-scale arithmetic comparison including the count-power price'))
    return leaves
