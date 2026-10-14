"""Locally compatible arithmetic auxiliaries and signed bound discovery.

The expression language has a proved fixed-index limit, not a proved growing
support norm bound. Floating Gram scores select formulas only; exact rational
programs and independent whole-domain certificates determine final evidence.
"""
from copy import deepcopy
from fractions import Fraction as Q
import math
import time

from flint import arb, ctx
import numpy as np

# Frozen, tested arithmetic/root primitives, not the previous search or data.
from floor_residual_search_043 import arithmetic_channels, root_floor, rational, CHANNELS

TRAIN_PARENTS = (48, 96, 144)
FINAL_PARENTS = (257, 389, 521)
MULTIPLIERS = (2, 3)
B_VALUES = ('-1', '-1/2', '0', '1/2', '1')
LOG_ETAS = ('1/5', '1/3', '1/2', '2/3', '1')
LOG_COSTS = ('1/64', '1/16', '1/4', '1', '4')
TRAIN_H = 65536
FINAL_H = 1048576
MAX_N = 4096


class Meter:
    def __init__(self, cap=150_000_000_000, seconds=3600):
        self.cap, self.operations = cap, 0
        self.deadline = time.monotonic()+seconds
        self.max_power_bits = 0

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('044 prospective work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('044 time cap')

    def counts(self):
        return dict(operations=self.operations, max_power_bits=self.max_power_bits)


def ast_key(value):
    if type(value) is dict:
        return tuple((k, ast_key(v)) for k, v in sorted(value.items()))
    if type(value) is list:
        return tuple(map(ast_key, value))
    return value


def positive(value):
    result = rational(value)
    if result <= 0:
        raise ValueError('strictly positive rational exponent')
    return result


def weight_limit(weight, depth=0):
    """Structural proof that a typed, bounded weight tends to 1 at fixed n."""
    if type(weight) is not dict or depth > 6:
        raise ValueError('bounded typed weight AST')
    kind = weight.get('kind')
    if kind == 'unit' and set(weight) == {'kind'}:
        rule = 'constant_one'
        premises = []
    elif kind == 'taper' and set(weight) == {'kind', 'coordinate', 'alpha', 'gamma'}:
        if weight['coordinate'] not in ('cutoff', 'log'):
            raise ValueError('declared coordinate')
        positive(weight['alpha']); positive(weight['gamma'])
        rule = 'continuous_positive_powers_at_coordinate_zero'
        premises = [weight['coordinate']+' coordinate tends to0 at every fixed n',
                    'inner and outer dyadic errors <=2^(-4*ceil(log2N)) ->0']
    elif kind == 'vanishing_twist' and set(weight) == {'kind', 'rate', 'level_power'}:
        positive(weight['rate'])
        if type(weight['level_power']) is not int or not 1 <= weight['level_power'] <= 8:
            raise ValueError('resource-bounded positive integer level power')
        rule = 'exp_of_fixed_log_n_times_exponent_tending_zero'
        premises = ['beta(N)=rate/(1+floor(log2N))^level_power ->0',
                    'dyadic rounding error ->0']
    elif kind == 'product' and set(weight) == {'kind', 'left', 'right'}:
        premises = [weight_limit(weight[k], depth+1) for k in ('left', 'right')]
        rule = 'product_of_two_bounded_limit_one_weights'
    else:
        raise ValueError('weight AST has no admitted limit proof')
    return dict(rule=rule, limit='1', range=['0', '1'], premises=premises,
                fixed_index_only=True, global_norm_bound_proved=False)


def envelope_limit(envelope):
    if type(envelope) is not dict:
        raise ValueError('typed auxiliary envelope')
    kind = envelope.get('kind')
    if kind == 'difference' and set(envelope) == {'kind', 'left', 'right'}:
        premises = [weight_limit(envelope[k]) for k in ('left', 'right')]
        rule = 'difference_of_limit_one_weights'
    elif kind in ('power_amplitude', 'log_amplitude') and set(envelope) == {'kind', 'power', 'weight'}:
        positive(envelope['power'])
        premises = [weight_limit(envelope['weight']), 'positive power of reciprocal growing N or L(N) tends to0']
        rule = kind+'_times_bounded_weight'
    elif kind == 'moving_band' and set(envelope) == {'kind', 'cutoff_power', 'weight'}:
        if not positive(envelope['cutoff_power']) < 1:
            raise ValueError('moving cutoff exponent strictly between0 and1')
        premises = [weight_limit(envelope['weight']), 'floor(N^theta) eventually exceeds each fixed n']
        rule = 'eventual_exact_zero_at_each_fixed_index'
    else:
        raise ValueError('envelope AST has no admitted zero-limit proof')
    return dict(rule=rule, limit='0', premises=premises, fixed_index_only=True,
                global_norm_bound_proved=False)


def certify_recipe_limit(recipe):
    if type(recipe) is not dict or set(recipe) != {'id', 'base', 'auxiliary'}:
        raise ValueError('exact044 recipe schema')
    if type(recipe['id']) is not str or not 1 <= len(recipe['id']) <= 100:
        raise ValueError('bounded recipe identifier')
    base = weight_limit(recipe['base'])
    auxiliary = recipe['auxiliary']
    aux_proof = None
    if auxiliary is not None:
        if type(auxiliary) is not dict or set(auxiliary) != {'channel', 'coefficient', 'envelope'}:
            raise ValueError('exact arithmetic auxiliary schema')
        if auxiliary['channel'] not in CHANNELS or rational(auxiliary['coefficient']) == 0:
            raise ValueError('declared actual arithmetic channel and nonzero fixed coefficient')
        aux_proof = envelope_limit(auxiliary['envelope'])
    return dict(schema='fixed-index-coefficient-limit-v1', family=recipe['id'],
                base=base, auxiliary=aux_proof, conclusion='for every fixed n>=2, c_n(N)->-mu(n)',
                formula_scope='unbounded mathematical recipe with exact rounding; evaluator can refuse at resource limits',
                source_scope='ordinary primes, exact integer arithmetic channels',
                necessary_condition_only=True, all_scale_upper_bound_proved=False,
                RH_proved=False)


def taper(coordinate, alpha, gamma='1'):
    return dict(kind='taper', coordinate=coordinate, alpha=alpha, gamma=gamma)


def grammar():
    unit = dict(kind='unit')
    weights = [unit]
    weights += [taper('cutoff', a, g) for a in ('2/7', '1/2', '1', '7/5') for g in ('1/3', '1')]
    weights += [taper('log', a, g) for a in ('1/3', '1', '5/4') for g in ('1/2', '1')]
    weights += [dict(kind='vanishing_twist', rate=a, level_power=1) for a in ('1/5', '2/7', '1', '3/2')]
    weights += [dict(kind='vanishing_twist', rate='1', level_power=2)]
    weights += [dict(kind='product', left=taper('log', '1'),
                     right=dict(kind='vanishing_twist', rate='1/5', level_power=1))]
    envelopes = [
        dict(kind='difference', left=unit, right=taper('cutoff', '1/2')),
        dict(kind='difference', left=taper('cutoff', '2/7'), right=taper('cutoff', '1')),
        dict(kind='difference', left=taper('log', '1'), right=taper('cutoff', '1')),
        dict(kind='difference', left=taper('log', '1/3'), right=taper('log', '1')),
        dict(kind='power_amplitude', power='1/7', weight=unit),
        dict(kind='log_amplitude', power='2/5', weight=taper('cutoff', '1')),
        dict(kind='moving_band', cutoff_power='3/7', weight=taper('cutoff', '1')),
        dict(kind='moving_band', cutoff_power='2/3', weight=taper('log', '1'))]
    # A declared finite production budget, not a permanent API whitelist.
    auxiliary_bases = [unit, taper('cutoff', '2/7'), taper('cutoff', '1'),
                       taper('log', '1'), dict(kind='vanishing_twist', rate='1/5', level_power=1)]
    recipes = [dict(base=w, auxiliary=None) for w in weights]
    recipes += [dict(base=w, auxiliary=dict(channel=a, coefficient=c, envelope=e))
                for w in auxiliary_bases for e in envelopes for a in CHANNELS for c in ('-1/2', '1/2')]
    for i, recipe in enumerate(recipes, 1):
        recipe['id'] = 'compatible_%04d'%i
        certify_recipe_limit(recipe)
    return dict(schema='compatible-floor-auxiliary-grammar-v1', recipes=deepcopy(recipes),
                raw_family_count=len(recipes), refinement_count=len(recipes)*len(MULTIPLIERS)*len(B_VALUES),
                multipliers=list(MULTIPLIERS), b_values=list(B_VALUES),
                log_costs=list(LOG_COSTS), log_etas=list(LOG_ETAS),
                coefficient_formula='-mu(n)*W0(n,N)+fixed_lambda*a(n)*V(n,N)',
                auxiliary_envelope_count=len(envelopes), standalone_base_count=len(weights),
                auxiliary_base_count=len(auxiliary_bases),
                finite_bank_provenance='declared cross-coordinate and moving-support productions before scores',
                log_coordinate='floor(2^p*log(n)/log(N))/2^p, exact rational case or certified Arb floor',
                dyadic_bits='p=4*ceil(log2N); exact rounding is part of each recipe',
                fixed_index_compatibility='symbolic bounded-limit grammar; necessary only',
                root_denominators_are_not_whitelisted=True, root_bit_cap=400000,
                fitted_per_scale_coefficients=False, anticipated_winner=None,
                proof_target='uniform norm(h_N)^2<=A/(1+floor(log2N))^eta,0<eta<=1',
                signed_terms='price auxiliary and refinement crosses before any magnitude replacement')


def factor(n):
    answer = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            answer[p] = answer.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        answer[n] = answer.get(n, 0)+1
    return answer


def log_coordinate(n, N, bits, meter=None):
    meter = meter or Meter()
    if type(n) is not int or type(N) is not int or not 2 <= n <= N <= MAX_N:
        raise ValueError('bounded integer logarithmic coordinate')
    if type(bits) is not int or not 1 <= bits <= 128:
        raise ValueError('bounded coordinate precision')
    fn, fN = factor(n), factor(N)
    if fn.keys() == fN.keys():
        ratios = {Q(fn[p], fN[p]) for p in fn}
        if len(ratios) == 1:
            ratio = ratios.pop()
            meter.charge(10*N.bit_length())
            return Q((1 << bits)*ratio.numerator//ratio.denominator, 1 << bits)
    for precision in (192, 384, 768, 1536, 3072):
        meter.charge(precision*N.bit_length())
        with ctx.workprec(precision):
            integer = (arb(n).log()/arb(N).log()*(1 << bits)).floor().unique_fmpz()
        if integer is not None:
            return Q(int(integer), 1 << bits)
    raise ArithmeticError('logarithmic coordinate floor not uniquely certified')


def moving_cutoff(N, theta, meter):
    exponent = positive(theta)
    if exponent >= 1:
        raise ValueError('moving cutoff must be sublinear')
    u, v = exponent.numerator, exponent.denominator
    cost = N.bit_length()*max(u, v)
    if cost > 400000:
        raise OverflowError('moving cutoff power bit cap')
    meter.max_power_bits = max(meter.max_power_bits, cost)
    meter.charge(cost)
    rhs = pow(N, u)
    lo, hi = 0, N+1
    while lo+1 < hi:
        mid = (lo+hi)//2
        meter.charge(cost)
        if pow(mid, v) <= rhs:
            lo = mid
        else:
            hi = mid
    return lo


def program(identifier, coefficients, steps=None, constant='1'):
    return dict(id=identifier, constant=str(Q(constant)),
                coefficients=[dict(n=n, value=str(Q(c))) for n, c in sorted(coefficients.items()) if c],
                steps=[dict(q=q, value=str(Q(c))) for q, c in sorted((steps or {}).items()) if c])


def semantic_key(p):
    return (p['constant'], tuple((r['n'], r['value']) for r in p['coefficients']),
            tuple((r['q'], r['value']) for r in p['steps']))


def difference_program(left, right, identifier):
    coefficients, steps = {}, {}
    for sign, p in ((1, left), (-1, right)):
        for row in p['coefficients']:
            n = row['n']
            coefficients[n] = coefficients.get(n, Q(0))+sign*rational(row['value'])
        for row in p['steps']:
            q = row['q']
            steps[q] = steps.get(q, Q(0))+sign*rational(row['value'])
    return program(identifier, coefficients, steps, rational(left['constant'])-rational(right['constant']))


def forcing_program(parent, child, q, b_text, identifier=None):
    if parent['constant'] != '1' or child['constant'] != '1' or parent['steps'] or child['steps']:
        raise ValueError('refinement targets must have unit constant and no indicator')
    if type(q) is not int or q < 2:
        raise ValueError('integer dilation>=2')
    b = rational(b_text)
    coefficients = {row['n']: rational(row['value']) for row in child['coefficients']}
    for row in parent['coefficients']:
        n, c = row['n'], rational(row['value'])
        coefficients[q*n] = coefficients.get(q*n, Q(0))-b*c
        coefficients[q] = coefficients.get(q, Q(0))+b*c/n
    return program(identifier or child['id']+'_q'+str(q)+'_b'+b_text, coefficients, {q: b})


class Compiler:
    def __init__(self, maximum, meter=None):
        self.maximum, self.meter = maximum, meter or Meter()
        self.channels = arithmetic_channels(maximum, self.meter)
        self.weights, self.envelopes, self.coordinates = {}, {}, {}

    def weights_at(self, weight, N):
        key = (ast_key(weight), N)
        if key in self.weights:
            return self.weights[key]
        weight_limit(weight)
        bits, kind = 4*(N-1).bit_length(), weight['kind']
        if kind == 'unit':
            answer = [Q(1)]*(N-1)
        elif kind == 'product':
            answer = [a*b for a, b in zip(self.weights_at(weight['left'], N), self.weights_at(weight['right'], N))]
        elif kind == 'vanishing_twist':
            beta = rational(weight['rate'])/N.bit_length()**weight['level_power']
            answer = [root_floor(Q(1, n), str(beta), bits, self.meter) for n in range(2, N+1)]
        else:
            coord_key = (weight['coordinate'], N)
            if coord_key not in self.coordinates:
                self.coordinates[coord_key] = ([Q(n, N) for n in range(2, N+1)] if weight['coordinate'] == 'cutoff'
                    else [log_coordinate(n, N, bits, self.meter) for n in range(2, N+1)])
            answer = [root_floor(1-root_floor(t, weight['alpha'], bits, self.meter),
                                 weight['gamma'], bits, self.meter) for t in self.coordinates[coord_key]]
        self.meter.charge(12*N)
        self.weights[key] = answer
        return answer

    def envelope_at(self, envelope, N):
        key = (ast_key(envelope), N)
        if key in self.envelopes:
            return self.envelopes[key]
        envelope_limit(envelope)
        kind, bits = envelope['kind'], 4*(N-1).bit_length()
        if kind == 'difference':
            answer = [a-b for a, b in zip(self.weights_at(envelope['left'], N), self.weights_at(envelope['right'], N))]
        elif kind == 'moving_band':
            cutoff = moving_cutoff(N, envelope['cutoff_power'], self.meter)
            answer = [Q(0) if n <= cutoff else w for n, w in enumerate(self.weights_at(envelope['weight'], N), 2)]
        else:
            amplitude = root_floor(Q(1, N if kind == 'power_amplitude' else N.bit_length()),
                                   envelope['power'], bits, self.meter)
            answer = [amplitude*w for w in self.weights_at(envelope['weight'], N)]
        self.meter.charge(12*N)
        self.envelopes[key] = answer
        return answer

    def compile(self, recipe, N):
        certify_recipe_limit(recipe)
        if type(N) is not int or not 2 <= N <= self.maximum:
            raise ValueError('support within declared compiler scope')
        coefficients = {n: -self.channels['mu'][n]*w for n, w in enumerate(self.weights_at(recipe['base'], N), 2)}
        aux = recipe['auxiliary']
        if aux is not None:
            scale, arithmetic = rational(aux['coefficient']), self.channels[aux['channel']]
            for n, v in enumerate(self.envelope_at(aux['envelope'], N), 2):
                coefficients[n] += scale*arithmetic[n]*v
        self.meter.charge(24*N)
        return program(recipe['id']+'_N'+str(N), coefficients)


class TrainingNorms:
    """Shared numerical Gram and full signed periodic covariance for ranking."""
    def __init__(self, maximum, H, meter=None):
        self.maximum, self.H, self.meter = maximum, H, meter or Meter()
        if type(maximum) is not int or maximum < 3 or H < maximum:
            raise ValueError('training support covered by head')
        size = maximum+len(MULTIPLIERS)
        self.meter.charge(2*H*size*size+maximum*maximum*10)
        cells = np.arange(1, H+1, dtype=np.int64)
        basis = np.empty((size, H))
        basis[0] = 1
        for n in range(2, maximum+1):
            basis[n-1] = (cells % n)/float(n)
        for i, q in enumerate(MULTIPLIERS):
            basis[maximum+i] = cells >= q
        basis *= np.sqrt(1.0/(cells.astype(float)*(cells+1)))
        self.gram = basis @ basis.T
        means = np.ones(size)
        means[1:maximum] = [(n-1)/(2*n) for n in range(2, maximum+1)]
        self.periodic = np.outer(means, means)
        for m in range(2, maximum+1):
            for n in range(2, maximum+1):
                self.periodic[m-1, n-1] += (math.gcd(m, n)**2-1)/(12*m*n)
        self.magnitudes = np.array([0]+[(n-1)/n for n in range(2, maximum+1)]+[0]*len(MULTIPLIERS))

    def price(self, programs):
        size = self.maximum+len(MULTIPLIERS)
        vs = np.zeros((len(programs), size))
        Ks = []
        for i, p in enumerate(programs):
            vs[i, 0] = float(rational(p['constant']))
            for row in p['coefficients']:
                n = row['n']
                if not 2 <= n <= self.maximum:
                    raise ValueError('only training supports enter ranking')
                vs[i, n-1] = -float(rational(row['value']))
            for row in p['steps']:
                vs[i, self.maximum+MULTIPLIERS.index(row['q'])] = -float(rational(row['value']))
            Ks.append(p['coefficients'][-1]['n'] if p['coefficients'] else 1)
        self.meter.charge(12*len(programs)*size*size)
        head = np.sum((vs @ self.gram)*vs, axis=1)
        periodic = np.sum((vs @ self.periodic)*vs, axis=1)
        av = np.abs(vs)
        htol = 1e-12*(1+np.sum((av @ np.abs(self.gram))*av, axis=1))
        ptol = 1e-12*(1+np.sum((av @ np.abs(self.periodic))*av, axis=1))
        if np.any(head < -htol) or np.any(periodic < -ptol) or not np.all(np.isfinite(head+periodic)):
            raise ArithmeticError('numerical Gram positivity failed')
        M = np.abs(vs[:, 0]+np.sum(vs[:, self.maximum:], axis=1))+av @ self.magnitudes
        tail_abs = M*M/(self.H+1)
        tail_mv = np.maximum(0, periodic+ptol)*(1/(self.H+1)+np.array(Ks, dtype=float)**2/((self.H+1)*(self.H+2)))
        tail = np.minimum(tail_abs, tail_mv)
        return [dict(head_estimate=float(head[i]), periodic_mean_square_proxy=float(periodic[i]),
                     pointwise_tail_proxy=float(tail_abs[i]), large_sieve_tail_proxy=float(tail_mv[i]),
                     tail_upper_proxy=float(tail[i]), ranking_lower_proxy=float(max(0, head[i]-htol[i])),
                     ranking_upper_proxy=float(max(0, head[i])+tail[i]+htol[i]),
                     numerical_roundoff_guard=float(htol[i]), rigorous_norm_certificate=False)
                for i in range(len(programs))]


def cross_diagnostic(total, left, right, bound):
    lo = total['ranking_lower_proxy']-left['ranking_upper_proxy']-right['ranking_upper_proxy']
    hi = total['ranking_upper_proxy']-left['ranking_lower_proxy']-right['ranking_lower_proxy']
    abs_lo = 0 if lo <= 0 <= hi else min(abs(lo), abs(hi))
    unsigned_lo = left['ranking_lower_proxy']+right['ranking_lower_proxy']+abs_lo
    return dict(cross_lower_proxy=lo, cross_upper_proxy=hi,
                unsigned_lower_proxy=unsigned_lo,
                signed_needed_proxy=total['ranking_upper_proxy'] <= bound < unsigned_lo,
                strict_cancellation_proxy=hi < 0)


def scale_norm(value, t):
    return {k: v*t for k, v in value.items() if k in ('ranking_lower_proxy', 'ranking_upper_proxy')}


def log_slope(values):
    return max(math.log(max(y, 1e-300)/max(x, 1e-300))/math.log((1+math.log(b))/(1+math.log(a)))
               for x, y, a, b in zip(values, values[1:], TRAIN_PARENTS, TRAIN_PARENTS[1:]))


def select(assessments, recipes, parents):
    if tuple(parents) != TRAIN_PARENTS:
        raise ValueError('only frozen training partition may select')
    expected = {(r['id'], q, b) for r in recipes for q in MULTIPLIERS for b in B_VALUES}
    actual = [(r['family'], r['q'], r['b']) for r in assessments]
    if len(actual) != len(set(actual)) or set(actual) != expected:
        raise ValueError('complete distinct family/refinement assessment matrix')
    if any([o['N'] for o in r['observations']] != list(parents) for r in assessments):
        raise ValueError('nontraining observations presented for selection')
    def rank(row):
        bound = row['finite_log_bound']
        return (bound is None, -row['auxiliary_signed_needed_count'], -row['refinement_signed_needed_count'],
                -float(Q(bound['eta'])) if bound else 0,
                row['worst_forcing_log_power'], row['worst_target_log_power'],
                row['observations'][-1]['forcing']['ranking_upper_proxy'], row['family'], row['q'], row['b'])
    choices, used = [], set()
    strata = [('signed_auxiliary', lambda r: r['has_auxiliary'] and r['b'] != '0'),
              ('scale_refinement', lambda r: r['b'] != '0'),
              ('baseline_control', lambda r: not r['has_auxiliary'] and r['b'] != '0'),
              ('endpoint_restatement_control', lambda r: r['b'] == '0')]
    for name, condition in strata:
        candidates = [r for r in assessments if condition(r) and (r['family'], r['q'], r['b']) not in used]
        chosen = min(candidates, key=rank)
        used.add((chosen['family'], chosen['q'], chosen['b']))
        choices.append(dict(stratum=name, family=chosen['family'], q=chosen['q'], b=chosen['b'],
                            finite_log_bound=chosen['finite_log_bound'],
                            auxiliary_signed_needed_training=chosen['auxiliary_signed_needed_count'],
                            refinement_signed_needed_training=chosen['refinement_signed_needed_count']))
    return choices


def search(frozen_grammar, meter=None, progress=None):
    meter = meter or Meter()
    if frozen_grammar != grammar():
        raise ValueError('exact frozen044 grammar required')
    recipes = frozen_grammar['recipes']
    compiler = Compiler(max(TRAIN_PARENTS)*max(MULTIPLIERS), meter)
    norms = TrainingNorms(compiler.maximum, TRAIN_H, meter)
    supports = sorted(set(TRAIN_PARENTS) | {q*N for q in MULTIPLIERS for N in TRAIN_PARENTS})
    baselines, assessments = {}, []
    for index, recipe in enumerate(recipes, 1):
        base_key = ast_key(recipe['base'])
        if base_key not in baselines:
            base_recipe = dict(id='base_%03d'%(len(baselines)+1), base=recipe['base'], auxiliary=None)
            base_targets = {N: compiler.compile(base_recipe, N) for N in supports}
            base_forcing = {(q, b, N): forcing_program(base_targets[N], base_targets[q*N], q, b)
                            for q in MULTIPLIERS for b in B_VALUES for N in TRAIN_PARENTS}
            base_prices = norms.price(list(base_forcing.values()))
            baselines[base_key] = (base_targets, base_forcing, dict(zip(base_forcing, base_prices)))
        base_targets, base_forcing, base_prices = baselines[base_key]
        targets = {N: compiler.compile(recipe, N) for N in supports}
        forcing = {(q, b, N): forcing_program(targets[N], targets[q*N], q, b)
                   for q in MULTIPLIERS for b in B_VALUES for N in TRAIN_PARENTS}
        auxiliary = {key: difference_program(p, base_forcing[key], p['id']+'_aux') for key, p in forcing.items()}
        all_programs = list(targets.values())+list(forcing.values())+list(auxiliary.values())
        # Exact tuple deduplication is functional memoization; no artifact hashes.
        distinct = {}
        for p in all_programs:
            distinct.setdefault(semantic_key(p), p)
        distinct_prices = dict(zip(distinct, norms.price(list(distinct.values()))))
        target_prices = {N: distinct_prices[semantic_key(p)] for N, p in targets.items()}
        for q in MULTIPLIERS:
            for b in B_VALUES:
                observations = []
                for N in TRAIN_PARENTS:
                    key = (q, b, N)
                    observations.append(dict(N=N, parent=target_prices[N], child=target_prices[q*N],
                        forcing=distinct_prices[semantic_key(forcing[key])], baseline_forcing=base_prices[key],
                        auxiliary_forcing=distinct_prices[semantic_key(auxiliary[key])]))
                bounds = [dict(A=A, eta=eta) for eta in reversed(LOG_ETAS) for A in LOG_COSTS
                          if all(o['forcing']['ranking_upper_proxy'] <= float(Q(A))/o['N'].bit_length()**float(Q(eta))
                                 for o in observations)]
                bound = bounds[0] if bounds else None
                for o in observations:
                    threshold = float(Q(bound['A']))/o['N'].bit_length()**float(Q(bound['eta'])) if bound else -1
                    o['auxiliary_cross'] = cross_diagnostic(o['forcing'], o['baseline_forcing'], o['auxiliary_forcing'], threshold)
                    o['refinement_cross'] = cross_diagnostic(o['forcing'], o['child'], scale_norm(o['parent'], float(Q(b)**2/q)), threshold)
                assessments.append(dict(family=recipe['id'], q=q, b=b, has_auxiliary=recipe['auxiliary'] is not None,
                    observations=observations, finite_log_bound=bound,
                    auxiliary_signed_needed_count=sum(o['auxiliary_cross']['signed_needed_proxy'] for o in observations),
                    refinement_signed_needed_count=sum(o['refinement_cross']['signed_needed_proxy'] for o in observations),
                    worst_forcing_log_power=log_slope([o['forcing']['ranking_upper_proxy'] for o in observations]),
                    worst_target_log_power=log_slope([o['child']['ranking_upper_proxy'] for o in observations]),
                    endpoint_restatement=b == '0', uniform_inequality_proved=False))
        if progress and (index % 50 == 0 or index == len(recipes)):
            progress('training_progress', families=index, total=len(recipes), operations=meter.operations)
    selections = select(assessments, recipes, TRAIN_PARENTS)
    recipe_by_id = {r['id']: r for r in recipes}
    return dict(schema='compatible-floor-search-v1', assessments=assessments, selections=selections,
                selected_recipes=[recipe_by_id[k] for k in sorted({s['family'] for s in selections})],
                training_parents=list(TRAIN_PARENTS), training_H=TRAIN_H,
                family_count=len(recipes), refinement_count=len(assessments),
                finite_log_bound_matches=sum(r['finite_log_bound'] is not None for r in assessments),
                auxiliary_signed_needed_matches=sum(r['auxiliary_signed_needed_count'] > 0 for r in assessments),
                refinement_signed_needed_matches=sum(r['refinement_signed_needed_count'] > 0 for r in assessments),
                symbolic_limit_certificates=[certify_recipe_limit(r) for r in recipes],
                final_observations_used_in_selection=False, fitted_coefficients=False,
                ranking='log-bound match; auxiliary and refinement signed necessity; eta; worst observed log slopes; final proxy; stable id',
                global_N_convergence_proved=False, RH_proved=False, counts=meter.counts())
