"""Finite discovery of signed scale filters and concrete bound conjectures.

No analytic proof provider is imported. Exact integer source intervals and
Arb weight intervals select inequalities; every uniform inequality stays OPEN.
"""
from fractions import Fraction as Q
from functools import reduce
from itertools import product
from math import gcd
import math
import time
from flint import arb, ctx
import prime_scale_source_053 as SOURCE

DEFAULT = {'alphas': ['1/2', '1/3', '2/3', '1/4', '1/5'], 'scales': [2, 3, 5],
           'max_degree': 3, 'coefficient_limit': 6,
           'log_powers': ['0', '1/4', '1/2', '1', '2'],
           'constant_exponents': list(range(-8, 5)), 'max_candidates': 20000}


class Meter:
    def __init__(self, cap=100_000_000_000, seconds=7200):
        self.cap, self.operations, self.deadline = cap, 0, time.monotonic()+seconds

    def charge(self, n=1):
        if type(n) is not int or n < 0 or n > self.cap-self.operations:
            raise OverflowError('scale search work cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('scale search deadline')


def _rational(text):
    if type(text) is not str or not 1 <= len(text) <= 100:
        raise ValueError('bounded rational grammar parameter')
    value = Q(text)
    if str(value) != text:
        raise ValueError('canonical rational grammar parameter')
    return value


def grammar(spec=None, meter=None):
    spec, meter = DEFAULT if spec is None else spec, meter or Meter()
    if type(spec) is not dict or set(spec) != set(DEFAULT):
        raise ValueError('exact finite grammar specification')
    if any(type(spec[k]) is not list or not spec[k] or len(spec[k]) > 64
           for k in ('alphas', 'scales', 'log_powers', 'constant_exponents')):
        raise ValueError('bounded nonempty grammar lists')
    alphas = [_rational(x) for x in spec['alphas']]
    etas = [_rational(x) for x in spec['log_powers']]
    if any(not 0 < a < 1 for a in alphas) or any(e < 0 for e in etas):
        raise ValueError('fractional exponents and nonnegative log powers')
    if len(set(alphas)) != len(alphas) or len(set(etas)) != len(etas):
        raise ValueError('unique rational grammar values')
    if any(type(q) is not int or not 2 <= q <= 16 for q in spec['scales']) or len(set(spec['scales'])) != len(spec['scales']):
        raise ValueError('distinct bounded integer scales')
    if any(type(k) is not int or not -32 <= k <= 32 for k in spec['constant_exponents']) or sorted(set(spec['constant_exponents'])) != spec['constant_exponents']:
        raise ValueError('ordered distinct dyadic constant exponents')
    degree, limit, cap = spec['max_degree'], spec['coefficient_limit'], spec['max_candidates']
    if type(degree) is not int or not 1 <= degree <= 4 or type(limit) is not int or not 1 <= limit <= 16:
        raise ValueError('finite polynomial complexity ceiling')
    if type(cap) is not int or not 1 <= cap <= 100000:
        raise ValueError('candidate cap')
    if len(spec['scales'])*degree*(2*limit+1)**(degree-1)*limit > 5_000_000:
        raise OverflowError('prospective polynomial enumeration cap')
    polynomials = []
    for q in spec['scales']:
        for d in range(1, degree+1):
            for leading in range(1, limit+1):
                for middle in product(range(-limit, limit+1), repeat=d-1):
                    rest = list(middle)+[leading]
                    c0 = -sum(c*q**(j+1) for j, c in enumerate(rest))
                    cs = [c0]+rest
                    meter.charge(32+16*d)
                    if not c0 or abs(c0) > limit or reduce(gcd, cs) != 1:
                        continue
                    polynomials.append({'q': q, 'coefficients': cs, 'degree': d,
                                        'coefficient_l1': sum(abs(c) for c in cs), 'P_at_one': sum(cs)})
    if len(polynomials)*len(alphas)*len(etas) > cap:
        raise OverflowError('complete bound grammar exceeds declared candidate cap')
    words = []
    for alpha in spec['alphas']:
        for polynomial in polynomials:
            words.append({'id': 'prime_scale_%04d' % len(words), 'alpha': alpha, **polynomial})
    return {'schema': 'prime-scale-filter-grammar-v1', 'spec': spec, 'words': words,
            'polynomials': len(polynomials), 'word_count': len(words),
            'bound_candidate_count': len(words)*len(etas),
            'constant_policy': 'smallest declared dyadic C admitting every training interval; otherwise reject',
            'root_locations_restricted': False, 'proof_provider_used': False}


def _endpoint(value):
    m, e = value.man_exp(); m, e = int(m), int(e)
    return Q(m << e) if e >= 0 else Q(m, 1 << -e)


def bound_weight(N, eta, meter=None):
    meter = meter or Meter()
    if type(N) is not int or not 2 <= N <= 2_000_000:
        raise ValueError('bounded integer scale')
    eta = _rational(eta)
    if eta < 0:
        raise ValueError('nonnegative log power')
    with ctx.workprec(192):
        value = arb(N).sqrt()*(1+arb(N).log())**(arb(eta.numerator)/eta.denominator)
        lo, hi = _endpoint(value.lower()), _endpoint(value.upper())
    meter.charge(192**2)
    return lo, hi


def source_value(source, word, N, cache, meter=None, source_meter=None):
    meter = meter or Meter()
    source_meter = source_meter or SOURCE.Meter()
    if source.alpha != word['alpha']:
        raise ValueError('source exponent binding')
    alpha = Q(word['alpha'])
    lower, upper = 0, 0
    for j, c in enumerate(word['coefficients']):
        if c == 0:
            continue
        n = word['q']**j*N
        key = (source.alpha, source.bits, n)
        if key not in cache:
            cache[key] = SOURCE.evaluate_A(source, n, source_meter)
        row = cache[key]
        lo, hi = row['lower_numerator'], row['upper_numerator']
        if c < 0:
            lo, hi = hi, lo
        lower += c*lo; upper += c*hi
        meter.charge(64)
    denominator = (1 << source.bits)*alpha.numerator
    return Q(lower*alpha.denominator, denominator), Q(upper*alpha.denominator, denominator)


def interval(pair):
    return {'lower': str(pair[0]), 'upper': str(pair[1])}


def absolute_bounds(pair):
    lo, hi = pair
    return (0 if lo <= 0 <= hi else min(abs(lo), abs(hi))), max(abs(lo), abs(hi))


def assess(pair, target):
    lo, hi = absolute_bounds(pair)
    return 'FINITE_PASS' if hi <= target[0] else 'FINITE_REFUTATION' if lo > target[1] else 'UNRESOLVED_INTERVAL'


def search(bank, sources, numbers, meter=None, source_meter=None):
    meter, source_meter = meter or Meter(), source_meter or SOURCE.Meter()
    if type(numbers) is not list or not numbers or len(numbers) > 2048 or len(set(numbers)) != len(numbers):
        raise ValueError('distinct finite training scales')
    if any(type(n) is not int or not 2 <= n <= 2_000_000 for n in numbers):
        raise ValueError('training integer scales')
    spec = bank['spec']
    constants = [Q(2)**k for k in spec['constant_exponents']]
    weights = {(n, e): bound_weight(n, e, meter) for n in numbers for e in spec['log_powers']}
    cache, observations, candidates = {}, [], []
    for word in bank['words']:
        values = [(N, source_value(sources[word['alpha']], word, N, cache, meter, source_meter)) for N in numbers]
        observations.append({'word': word, 'values': [{'N': n, **interval(v)} for n, v in values]})
        for eta in spec['log_powers']:
            required = max(absolute_bounds(v)[1]/weights[n, eta][0] for n, v in values)
            C = next((c for c in constants if c >= required), None)
            row = {'id': word['id']+'_eta_'+eta.replace('/', '_'), 'word_id': word['id'],
                   'word': word, 'log_power': eta, 'required_training_C_upper': str(required),
                   'C': str(C) if C is not None else None,
                   'finite_status': 'FINITE_TRAINING_PASS' if C is not None else 'NO_DECLARED_C_PASSES',
                   'all_training_scales_covered': True, 'uniform_arithmetic_bound_proved': False}
            if C is not None:
                row['request'] = {'alpha': word['alpha'], 'q': word['q'], 'coefficients': word['coefficients'],
                    'bound': {'C': str(C), 'log_power': eta, 'minimum': 2, 'normalization': 'divide_by_alpha'}}
            candidates.append(row)
            meter.charge(128+32*len(values))
    return {'observations': observations, 'candidates': candidates, 'training_scales': numbers,
            'cached_A_values': len(cache), 'source_A_values': [{'alpha': k[0], **v} for k, v in sorted(cache.items())],
            'proof_provider_used': False, 'final_scores_used': False,
            'uniform_arithmetic_bound_proved': False, 'RH_proved': False}


def select(candidates, limit=6):
    if type(limit) is not int or not 0 <= limit <= 64:
        raise ValueError('bounded archive size')
    eligible = [r for r in candidates if r['C'] is not None and r['all_training_scales_covered']]
    def rank(r):
        w = r['word']
        return (Q(r['log_power']), Q(r['C']), w['degree'], w['coefficient_l1'],
                Q(w['alpha']).denominator, w['q'], r['id'])
    eligible.sort(key=rank)
    selected, alpha_used, shape_used, words_used = [], set(), set(), set()
    for phase in ('alpha', 'shape', 'remaining'):
        for row in eligible:
            if len(selected) >= limit:
                break
            w = row['word']; shape = (w['q'], tuple(w['coefficients']))
            if row['word_id'] in words_used:
                continue
            if phase == 'alpha' and w['alpha'] in alpha_used:
                continue
            if phase == 'shape' and shape in shape_used:
                continue
            selected.append(row); alpha_used.add(w['alpha']); shape_used.add(shape); words_used.add(row['word_id'])
    return {'selected': selected, 'eligible_bound_candidates': len(eligible),
            'selection_rule': 'lower logarithmic growth first, then coarse dyadic constant and expression complexity; exponent then filter-shape diversity',
            'proof_provider_used': False, 'final_scores_used': False,
            'all_uniform_bounds_status': 'OPEN'}
