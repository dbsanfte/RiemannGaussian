"""Search positive auxiliary energies and explicit all-integer drift lemmas.

The selector sees supplied numerical interval channels, not proof providers.
Every drift is a conjecture until an independent uniform argument closes it.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from math import gcd, isqrt
import time
from flint import arb, ctx


DEFAULT = {'features': [[], [2], [3], [5], [2, 3], [2, 5], [3, 5]],
    'coefficient_bound': 2, 'maximum_support': 2,
    'lambdas': ['1/4', '1', '4'], 'decay_exponents': ['0', '1/7', '1/3', '1/2', '1'],
    'constant_powers': list(range(-12, 9)), 'include_zero_constant': True}


class Meter:
    def __init__(self, cap=100_000_000_000, seconds=7200):
        self.cap, self.operations, self.deadline = cap, 0, time.monotonic()+seconds

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('auxiliary search work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('auxiliary search deadline')


def rational(text, *, minimum=Q(0), maximum=Q(4096)):
    if type(text) is not str or not 1 <= len(text) <= 1000:
        raise ValueError('bounded rational string')
    value = Q(text)
    if str(value) != text or not minimum <= value <= maximum:
        raise ValueError('canonical rational in declared range')
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > 2048:
        raise OverflowError('rational parameter bit cap')
    return value


def grammar(spec=None, meter=None):
    meter = meter or Meter()
    spec = DEFAULT if spec is None else spec
    if type(spec) is not dict or set(spec) != set(DEFAULT):
        raise ValueError('exact auxiliary grammar specification')
    features = spec['features']
    if type(features) is not list or not 2 <= len(features) <= 32 or features[0] != []:
        raise ValueError('target channel0 and bounded companion feature list')
    for feature in features:
        if (type(feature) is not list or len(feature) > 8
                or any(type(p) is not int or not 2 <= p <= 64 for p in feature)
                or feature != sorted(set(feature))):
            raise ValueError('canonical bounded insertion feature')
        if any(any(p % d == 0 for d in range(2, isqrt(p)+1)) for p in feature):
            raise ValueError('actual prime insertion generators required')
    if len({tuple(s) for s in features}) != len(features):
        raise ValueError('distinct feature channels')
    bound, support = spec['coefficient_bound'], spec['maximum_support']
    if type(bound) is not int or not 1 <= bound <= 4 or type(support) is not int or not 1 <= support <= 3:
        raise ValueError('finite integer coefficient/support grammar')
    lambdas = [rational(x) for x in spec['lambdas']]
    deltas = [rational(x) for x in spec['decay_exponents']]
    if (not lambdas or any(x <= 0 for x in lambdas) or len(set(lambdas)) != len(lambdas)
            or not deltas or len(set(deltas)) != len(deltas)):
        raise ValueError('distinct positive square weights and nonnegative decay exponents')
    powers = spec['constant_powers']
    if type(powers) is not list or not powers or any(type(k) is not int or not -64 <= k <= 64 for k in powers):
        raise ValueError('declared coarse constant powers')
    if powers != sorted(set(powers)) or type(spec['include_zero_constant']) is not bool:
        raise ValueError('canonical coarse constants')
    constants = ([Q(0)] if spec['include_zero_constant'] else [])+[Q(2)**k for k in powers]
    forms = [{'id': 'insertion_energy_0000', 'coefficients': [0]*len(features),
        'lambda': '0', 'support': [], 'baseline': True}]
    for size in range(1, min(support, len(features))+1):
        for indices in combinations(range(len(features)), size):
            # A scalar multiple of the target energy supplies no new auxiliary.
            if indices == (0,):
                continue
            for values in product(range(-bound, bound+1), repeat=size):
                meter.charge(size+1)
                if any(v == 0 for v in values) or values[0] <= 0:
                    continue
                common = 0
                for v in values: common = gcd(common, v)
                if common != 1:
                    continue
                vector = [0]*len(features)
                for i, v in zip(indices, values): vector[i] = v
                for weight in lambdas:
                    forms.append({'id': 'insertion_energy_'+str(len(forms)).zfill(4),
                        'coefficients': vector, 'lambda': str(weight), 'support': list(indices), 'baseline': False})
                    if len(forms) > 100000:
                        raise OverflowError('bounded auxiliary form enumeration')
    return {'schema': 'prime-insertion-auxiliary-grammar-v1', 'spec': spec,
        'forms': forms, 'form_count': len(forms), 'decay_exponents': [str(x) for x in deltas],
        'constants': [str(x) for x in constants], 'bound_candidate_count': len(forms)*len(deltas),
        'target': 't0(N)^2/N', 'majorant': '[t0(N)^2+lambda*(sum_i a_i*t_i(N))^2]/N',
        'recurrence': 'F(2N+r)<=F(N)+C/N^delta, everyintegerN>=2 andr0,1',
        'proof_provider_used': False, 'all_uniform_drifts_status': 'OPEN'}


def pair(data):
    if type(data) is not dict or set(data) != {'lower', 'upper'}:
        raise ValueError('exact rational interval fields')
    lo, hi = Q(data['lower']), Q(data['upper'])
    if str(lo) != data['lower'] or str(hi) != data['upper'] or lo > hi:
        raise ValueError('canonical ordered interval')
    return lo, hi


def interval(value): return {'lower': str(value[0]), 'upper': str(value[1])}


def square(value):
    lo, hi = value
    return (Q(0) if lo <= 0 <= hi else min(lo*lo, hi*hi), max(lo*lo, hi*hi))


def energy(form, values, N, meter=None):
    meter = meter or Meter()
    if type(N) is not int or N < 2 or len(values) != len(form['coefficients']):
        raise ValueError('bounded energy source at integerN>=2')
    target = square(values[0])
    lower = upper = Q(0)
    for c, (lo, hi) in zip(form['coefficients'], values):
        lower += c*(lo if c >= 0 else hi)
        upper += c*(hi if c >= 0 else lo)
    auxiliary = square((lower, upper))
    weight = Q(form['lambda'])
    if weight < 0:
        raise ValueError('positive-square majorant requires nonnegative weight')
    meter.charge(128+64*len(values))
    return ((target[0]+weight*auxiliary[0])/N, (target[1]+weight*auxiliary[1])/N)


def decay(N, delta, meter=None, precision=192):
    meter = meter or Meter()
    delta = rational(delta)
    if type(N) is not int or not 2 <= N <= 2_000_000 or precision not in (192, 256):
        raise ValueError('finite recurrence scale/precision')
    if delta == 0:
        meter.charge(1)
        return Q(1), Q(1)
    def endpoint(a):
        mantissa, power = a.man_exp(); mantissa, power = int(mantissa), int(power)
        return Q(mantissa << power) if power >= 0 else Q(mantissa, 1 << -power)
    with ctx.workprec(precision):
        value = (arb(N).log()*(-delta.numerator)/delta.denominator).exp()
        lower, upper = endpoint(value.lower()), endpoint(value.upper())
    if lower <= 0:
        raise ArithmeticError('strictly positive decay interval required')
    meter.charge(precision**2+64)
    return lower, upper


def assess(drift, forcing):
    return 'FINITE_PASS' if drift[1] <= forcing[0] else 'FINITE_REFUTATION' if drift[0] > forcing[1] else 'UNRESOLVED_INTERVAL'


def score_form(form, table, scales, weights, constants, meter=None):
    """Fit only coarseC from training upper intervals; no proof is consulted."""
    meter = meter or Meter()
    needed = sorted({x for n in scales for x in (n, 2*n, 2*n+1)})
    energies = {n: energy(form, table[n], n, meter) for n in needed}
    drifts = [(n, r, (energies[2*n+r][0]-energies[n][1], energies[2*n+r][1]-energies[n][0]))
        for n in scales for r in (0, 1)]
    rows = []
    for delta in weights:
        required = max([Q(0)]+[value[1]/weights[delta][n][0] for n, r, value in drifts])
        constant = next((c for c in constants if c >= required), None)
        meter.charge(64*len(drifts))
        rows.append({'id': form['id']+'_delta_'+delta.replace('/', '_'), 'form': form,
            'delta': delta, 'C': None if constant is None else str(constant),
            'required_training_C_upper': str(required), 'training_parent_scales': len(scales),
            'training_branches': len(drifts),
            'finite_status': 'NO_DECLARED_CONSTANT' if constant is None else 'FINITE_TRAINING_PASS',
            'uniform_drift_proved': False, 'uniform_target_bound_proved': False, 'RH_proved': False})
    return rows


def rank(row):
    return (-Q(row['delta']), Q(row['C']), len(row['form']['support']),
        sum(abs(c) for c in row['form']['coefficients']), Q(row['form']['lambda']), row['id'])


def select(candidates, limit=6):
    eligible = sorted((r for r in candidates if r['finite_status'] == 'FINITE_TRAINING_PASS'), key=rank)
    # Retain a comparable target-only control separately from the discoveries.
    baseline = next((r for r in eligible if r['form']['baseline']), None)
    selected, used = [], set()
    def add(row):
        if row['form']['id'] not in used and len(selected) < limit:
            selected.append(row); used.add(row['form']['id'])
    if baseline is not None: add(baseline)
    # Reserve one slot per involved companion feature, chosen by the same score.
    features = sorted({i for r in eligible for i in r['form']['support'] if i != 0})
    for feature in features:
        row = next((r for r in eligible if not r['form']['baseline'] and feature in r['form']['support'] and r['form']['id'] not in used), None)
        if row is not None: add(row)
    for row in eligible: add(row)
    return {'selected': selected, 'eligible_bound_candidates': len(eligible),
        'baseline_reserved': baseline is not None, 'final_scores_used': False,
        'proof_provider_used': False, 'all_uniform_drifts_status': 'OPEN'}


def drift_polynomial(form):
    """Exact correlation coefficients: no arithmetic leaf is paid by expansion."""
    vector, weight = form['coefficients'], Q(form['lambda'])
    terms = {}
    for i in range(len(vector)):
        for j in range(i, len(vector)):
            coefficient = weight*vector[i]*vector[j]*(1 if i == j else 2)
            if i == j == 0: coefficient += 1
            if coefficient: terms[(i, j)] = coefficient
    return {'terms': [{'i': i, 'j': j, 'coefficient': str(c)} for (i, j), c in terms.items()],
        'formula': 'sum_(i<=j)Qij*[t_i(2N+r)t_j(2N+r)/(2N+r)-t_i(N)t_j(N)/N]',
        'cross_terms_preserved': True, 'uniform_drift_proved': False}
