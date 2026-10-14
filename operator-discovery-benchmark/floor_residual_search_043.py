"""Discover fixed arithmetic coefficient families and residual refinements.

Selection sees only declared training supports. Exact dyadic root recipes define
the actual programs; neither per-support least squares nor fitted constants are
used. Numerical trends and conditional proof implications have distinct scopes.
"""
from fractions import Fraction as Q
import math
import time

import numpy as np

TRAIN_PARENTS = (8, 16, 24)
FINAL_PARENTS = (40, 64, 80)
MULTIPLIERS = (2, 3)
B_VALUES = ('-1', '-1/2', '0', '1/2', '1')
TAU_VALUES = ('1/64', '1/16', '1/4', '1/2')
LOG_ETAS = ('1/5', '1/3', '1/2', '2/3', '1')
LOG_COSTS = ('1/16', '1/4', '1', '4')
TRAIN_H = 32768
FINAL_H = 1048576
MAX_N = 4096
MAX_POWER_BITS = 400000
CHANNELS = ('mu', 'liouville', 'mu_convolution_mu', 'radical_sign',
            'one', 'mu_plus_half_liouville', 'mu_minus_half_liouville')


class Meter:
    def __init__(self, cap=2_000_000_000, seconds=1200):
        self.cap, self.operations = cap, 0
        self.deadline = time.monotonic() + seconds
        self.max_power_bits = 0

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('recipe work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('recipe time cap')

    def counts(self):
        return dict(operations=self.operations, max_power_bits=self.max_power_bits)


def rational(text):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational string')
    value = Q(text)
    if str(value) != text:
        raise ValueError('canonical rational string')
    return value


def root_floor(base, exponent, bits, meter=None):
    """Exactly floor(2**bits * base**exponent)/2**bits for 0<=base<=1.

    Arbitrary positive rational exponents are admitted by a cost/bit guard.
    No floating point root chooses the dyadic coefficient.
    """
    meter = meter or Meter()
    base, exponent = Q(base), rational(exponent)
    if not 0 <= base <= 1 or exponent <= 0 or type(bits) is not int or not 1 <= bits <= 128:
        raise ValueError('unit interval base, positive exponent, precision1..128')
    u, v = exponent.numerator, exponent.denominator
    predicted = bits*v + u*max(base.numerator.bit_length(), base.denominator.bit_length()) + 2
    if predicted > MAX_POWER_BITS:
        raise OverflowError('rational-root prospective power bit cap')
    meter.max_power_bits = max(meter.max_power_bits, predicted)
    meter.charge(max(1, predicted))
    if base in (0, 1):
        return base
    D = 1 << bits
    if exponent == 1:
        return Q(D*base.numerator//base.denominator, D)
    lhs_factor = pow(base.denominator, u)
    rhs = (1 << (bits*v))*pow(base.numerator, u)
    lo, hi = 0, D
    while lo+1 < hi:
        mid = (lo+hi)//2
        meter.charge(max(1, predicted//32))
        if pow(mid, v)*lhs_factor <= rhs:
            lo = mid
        else:
            hi = mid
    return Q(lo, D)


def arithmetic_channels(N, meter=None):
    """Actual integers/ordinary primes; sieve once, no stored source arrays."""
    meter = meter or Meter()
    if type(N) is not int or not 2 <= N <= MAX_N:
        raise ValueError('integer arithmetic support2..4096')
    least = [0]*(N+1)
    for p in range(2, N+1):
        if least[p] == 0:
            for n in range(p, N+1, p):
                if least[n] == 0:
                    least[n] = p
                meter.charge()
    mu, liouville, radical = [0]*(N+1), [0]*(N+1), [0]*(N+1)
    mu[1] = liouville[1] = radical[1] = 1
    for n in range(2, N+1):
        p = least[n]
        m = n//p
        mu[n] = 0 if m % p == 0 else -mu[m]
        liouville[n] = -liouville[m]
        radical[n] = radical[m] if m % p == 0 else -radical[m]
        meter.charge(6)
    convolution = [0]*(N+1)
    for d in range(1, N+1):
        for m in range(1, N//d+1):
            convolution[d*m] += mu[d]*mu[m]
            meter.charge(3)
    return dict(mu=mu, liouville=liouville, radical_sign=radical,
                mu_convolution_mu=convolution, one=[1]*(N+1),
                mu_plus_half_liouville=[Q(2*a+b, 2) for a, b in zip(mu, liouville)],
                mu_minus_half_liouville=[Q(2*a-b, 2) for a, b in zip(mu, liouville)])


def grammar():
    weights = [dict(taper=None, decay='0')]
    for alpha in ('1/5', '2/7', '1/2', '1', '2'):
        for gamma in ('1/3', '1', '5/4'):
            for decay in ('0', '1/7'):
                weights.append(dict(taper=dict(alpha=alpha, gamma=gamma), decay=decay))
    recipes = []
    for channel in CHANNELS:
        for weight in weights:
            for anchor in (False, True):
                recipes.append(dict(id='family_%04d' % (len(recipes)+1), channel=channel,
                                    **weight, anchor_cell_one=anchor))
    return dict(schema='floor-residual-family-grammar-v1', recipes=recipes,
                raw_family_count=len(recipes), refinement_count=len(recipes)*len(MULTIPLIERS)*len(B_VALUES),
                multipliers=list(MULTIPLIERS), b_values=list(B_VALUES), tau_values=list(TAU_VALUES),
                log_etas=list(LOG_ETAS), log_costs=list(LOG_COSTS),
                forcing_bound='norm(h_N)^2<=A/(1+floor(log2N))^eta',
                geometric_contraction_role='negative calibration; impossible uniformly for this basis by imported lower bound',
                coefficient_formula='c_n(N)=-a(n)*dyadic(n^(-beta))*dyadic((1-dyadic((n/N)^alpha))^gamma)',
                untapered_formula='c_n(N)=-a(n)',
                root_rounding='floor to2^(-4*ceil(log2(N))); inner and outer roots independently rounded',
                anchor_formula='optional add2*(1-sum c_n/n) to coefficient of f_2',
                channel_provenance='seven explicitly supplied arithmetic expressions; ordinary integer sieve',
                root_denominators_are_not_whitelisted=True, root_integer_bit_cap=MAX_POWER_BITS,
                per_N_coefficients_fitted=False, anticipated_winner=None)


def validate_recipe(recipe):
    if type(recipe) is not dict or set(recipe) != {'id', 'channel', 'taper', 'decay', 'anchor_cell_one'}:
        raise ValueError('exact family recipe schema')
    if type(recipe['id']) is not str or not 1 <= len(recipe['id']) <= 100 or recipe['channel'] not in CHANNELS:
        raise ValueError('family id and declared arithmetic channel')
    if type(recipe['anchor_cell_one']) is not bool or rational(recipe['decay']) < 0:
        raise ValueError('Boolean anchor and nonnegative decay')
    taper = recipe['taper']
    if taper is not None:
        if type(taper) is not dict or set(taper) != {'alpha', 'gamma'}:
            raise ValueError('exact taper schema')
        if rational(taper['alpha']) <= 0 or rational(taper['gamma']) <= 0:
            raise ValueError('positive taper exponents')


class Compiler:
    def __init__(self, maximum, meter=None):
        self.meter = meter or Meter()
        self.maximum = maximum
        self.channels = arithmetic_channels(maximum, self.meter)
        self.weights = {}

    def compile(self, recipe, N):
        validate_recipe(recipe)
        if type(N) is not int or not 2 <= N <= self.maximum:
            raise ValueError('support within compiler scope')
        taper = recipe['taper']
        key = (N, None if taper is None else (taper['alpha'], taper['gamma']), recipe['decay'])
        if key not in self.weights:
            bits = 4*(N-1).bit_length()
            weights = []
            for n in range(2, N+1):
                weight = Q(1)
                if taper is not None:
                    inner = root_floor(Q(n, N), taper['alpha'], bits, self.meter)
                    weight = root_floor(1-inner, taper['gamma'], bits, self.meter)
                if recipe['decay'] != '0':
                    weight *= root_floor(Q(1, n), recipe['decay'], bits, self.meter)
                weights.append(weight)
                self.meter.charge(8)
            self.weights[key] = weights
        coefficients = {n: -self.channels[recipe['channel']][n]*weight
                        for n, weight in zip(range(2, N+1), self.weights[key])}
        if recipe['anchor_cell_one']:
            coefficients[2] += 2*(1-sum((c/n for n, c in coefficients.items()), Q(0)))
        self.meter.charge(12*N)
        return program(recipe['id']+'_N'+str(N), coefficients)


def program(identifier, coefficients, steps=None):
    return dict(id=identifier, coefficients=[dict(n=n, value=str(Q(c))) for n, c in sorted(coefficients.items()) if c],
                steps=[dict(q=q, value=str(Q(c))) for q, c in sorted((steps or {}).items()) if c])


def lift_coefficients(parent, q):
    if parent.get('steps') != [] or type(q) is not int or q < 2:
        raise ValueError('pure floor target and integer dilation>=2')
    values = {}
    for row in parent['coefficients']:
        n, c = row['n'], rational(row['value'])
        values[q*n] = values.get(q*n, Q(0)) + c
        values[q] = values.get(q, Q(0)) - c/n
    return {n: c for n, c in values.items() if c}


def forcing_program(parent, child, q, b_text, identifier=None):
    if child.get('steps') != []:
        raise ValueError('pure child target')
    b = rational(b_text)
    coefficients = {row['n']: rational(row['value']) for row in child['coefficients']}
    for n, c in lift_coefficients(parent, q).items():
        coefficients[n] = coefficients.get(n, Q(0)) - b*c
    return program(identifier or child['id']+'_forcing_q'+str(q)+'_b'+b_text,
                   coefficients, {q: b})


def contraction_admissible(q, b_text, tau_text):
    if type(q) is not int or q < 2:
        raise ValueError('integer q>=2')
    b, tau = rational(b_text), rational(tau_text)
    if tau < 0:
        return False
    t = b*b/q
    gap = 1-t-tau
    return gap > 0 and gap*gap > 4*t*tau


def tail_bound(p, H):
    if any(row['q'] > H for row in p['steps']):
        raise ValueError('tail covers all steps')
    M = abs(1-sum((rational(row['value']) for row in p['steps']), Q(0)))
    M += sum((abs(rational(row['value']))*Q(row['n']-1, row['n']) for row in p['coefficients']), Q(0))
    return M*M/(H+1)


class TrainingNorms:
    def __init__(self, maximum, H, meter=None):
        self.maximum, self.H = maximum, H
        self.meter = meter or Meter()
        if maximum < 3 or not H >= maximum:
            raise ValueError('training support and complete step thresholds')
        cells = np.arange(1, H+1, dtype=np.int64)
        vectors = [np.ones(H)]
        vectors.extend((cells % n)/float(n) for n in range(2, maximum+1))
        vectors.extend((cells >= q).astype(float) for q in MULTIPLIERS)
        basis = np.asarray(vectors)
        weight = 1.0/(cells.astype(float)*(cells+1))
        self.gram = (basis*weight) @ basis.T
        self.meter.charge(2*H*len(vectors)**2)

    def norm(self, p):
        v = np.zeros(self.maximum+len(MULTIPLIERS))
        v[0] = 1.0
        for row in p['coefficients']:
            if not 2 <= row['n'] <= self.maximum:
                raise ValueError('only declared training support enters float evaluator')
            v[row['n']-1] = -float(rational(row['value']))
        for row in p['steps']:
            v[self.maximum+MULTIPLIERS.index(row['q'])] = -float(rational(row['value']))
        head = float(v @ self.gram @ v)
        tolerance = 1e-12*(1+float(np.abs(v) @ np.abs(self.gram) @ np.abs(v)))
        if not math.isfinite(head) or head < -tolerance:
            raise ArithmeticError('training numerical Gram failed')
        tail = float(tail_bound(p, self.H))
        upper = max(0., head)+tail+tolerance
        self.meter.charge(4*len(v)**2)
        return dict(head_estimate=head, analytic_tail_upper=tail,
                    ranking_lower_proxy=max(0., head-tolerance),
                    ranking_upper_proxy=upper, numerical_roundoff_guard=tolerance,
                    rigorous_norm_certificate=False)


def worst_power(values, supports):
    if len(values) != len(supports) or min(values) <= 0:
        raise ValueError('positive norm proxies at matching supports')
    return max(math.log(y/x)/math.log(b/a) for x, y, a, b in zip(values, values[1:], supports, supports[1:]))


def worst_log_power(values, supports):
    """Empirical slope only; continuous log scale avoids equal integer levels."""
    return max(math.log(y/x)/math.log((1+math.log(b))/(1+math.log(a)))
               for x, y, a, b in zip(values, values[1:], supports, supports[1:]))


def select(assessments, recipes, parents):
    if tuple(parents) != TRAIN_PARENTS:
        raise ValueError('only frozen training partition may select')
    expected = {(r['id'], q, b) for r in recipes for q in MULTIPLIERS for b in B_VALUES}
    actual = [(r['family'], r['q'], r['b']) for r in assessments]
    if len(actual) != len(set(actual)) or set(actual) != expected:
        raise ValueError('complete distinct recipe/refinement assessment matrix')
    for row in assessments:
        if [o['N'] for o in row['observations']] != list(parents):
            raise ValueError('selection received nontraining observations')
    def rank(row):
        return (row['finite_log_bound'] is None,
                row['worst_forcing_log_power'], row['worst_target_log_power'],
                row['observations'][-1]['forcing']['ranking_upper_proxy'], row['family'], row['q'], row['b'])
    selections = []
    for name, test in (('positive_refinement', lambda r: rational(r['b']) > 0),
                       ('negative_refinement', lambda r: rational(r['b']) < 0),
                       ('endpoint_restatement_control', lambda r: rational(r['b']) == 0)):
        chosen = min((r for r in assessments if test(r)), key=rank)
        selections.append(dict(stratum=name, family=chosen['family'], q=chosen['q'], b=chosen['b'],
                               finite_contraction_tau=chosen['finite_contraction_tau'],
                               finite_log_bound=chosen['finite_log_bound']))
    return selections


def search(frozen_grammar, meter=None):
    meter = meter or Meter()
    if frozen_grammar != grammar():
        raise ValueError('exact frozen grammar for043')
    recipes = frozen_grammar['recipes']
    maximum = max(TRAIN_PARENTS)*max(MULTIPLIERS)
    compiler = Compiler(maximum, meter)
    norms = TrainingNorms(maximum, TRAIN_H, meter)
    assessments = []
    for recipe in recipes:
        supports = sorted(set(TRAIN_PARENTS) | {q*N for q in MULTIPLIERS for N in TRAIN_PARENTS})
        targets = {N: compiler.compile(recipe, N) for N in supports}
        target_norms = {N: norms.norm(p) for N, p in targets.items()}
        for q in MULTIPLIERS:
            for b in B_VALUES:
                observations = []
                for N in TRAIN_PARENTS:
                    h = forcing_program(targets[N], targets[q*N], q, b)
                    hn = target_norms[q*N] if b == '0' else norms.norm(h)
                    observations.append(dict(N=N, parent=target_norms[N], child=target_norms[q*N], forcing=hn))
                taus = [tau for tau in TAU_VALUES if contraction_admissible(q, b, tau)
                        and all(o['forcing']['ranking_upper_proxy'] <= float(Q(tau))*o['parent']['ranking_lower_proxy']
                                for o in observations)]
                log_bounds = [dict(A=A, eta=eta) for eta in reversed(LOG_ETAS) for A in LOG_COSTS
                              if all(o['forcing']['ranking_upper_proxy'] <= float(Q(A))/o['N'].bit_length()**float(Q(eta))
                                     for o in observations)]
                assessments.append(dict(family=recipe['id'], q=q, b=b, observations=observations,
                    finite_contraction_tau=taus[0] if taus else None,
                    finite_log_bound=log_bounds[0] if log_bounds else None,
                    worst_forcing_log_power=worst_log_power([o['forcing']['ranking_upper_proxy'] for o in observations], TRAIN_PARENTS),
                    worst_target_log_power=worst_log_power([o['child']['ranking_upper_proxy'] for o in observations], TRAIN_PARENTS),
                    worst_forcing_power=worst_power([o['forcing']['ranking_upper_proxy'] for o in observations], TRAIN_PARENTS),
                    worst_target_power=worst_power([o['child']['ranking_upper_proxy'] for o in observations], TRAIN_PARENTS),
                    endpoint_restatement=b == '0', uniform_inequality_proved=False))
    selections = select(assessments, recipes, TRAIN_PARENTS)
    recipe_by_id = {r['id']: r for r in recipes}
    return dict(schema='floor-residual-search-v1', assessments=assessments, selections=selections,
                selected_recipes=[recipe_by_id[k] for k in sorted({s['family'] for s in selections})],
                training_parents=list(TRAIN_PARENTS), training_H=TRAIN_H,
                family_count=len(recipes), refinement_count=len(assessments),
                finite_contraction_matches=sum(r['finite_contraction_tau'] is not None for r in assessments),
                finite_log_bound_matches=sum(r['finite_log_bound'] is not None for r in assessments),
                b_zero_matches=sum(r['finite_contraction_tau'] is not None and r['b'] == '0' for r in assessments),
                final_observations_used_in_selection=False, fitted_coefficients=False,
                ranking='finite logarithmic bound first; worst observed forcing log power; worst target log power; final forcing proxy; stable id',
                geometric_contraction_uniformly_excluded_by_imported_lower_bound=True,
                signed_cross_terms_retained=True, global_N_convergence_proved=False, RH_proved=False,
                counts=meter.counts())
