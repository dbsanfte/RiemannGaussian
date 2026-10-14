"""Restricted fixed-index logarithmic rate algebra for typed floor-family ASTs.

Only the frozen043 witness generator is imported. No source arrays, recipe
compiler, old runs or norm evaluator are used. Cancellation is conservative.
"""
from fractions import Fraction as F
import math
import time
from flint import arb, ctx
from floor_residual_recovery_review_043 import generate_witness

CHANNELS = ('mu', 'liouville', 'mu_convolution_mu', 'radical_sign', 'one',
            'mu_plus_half_liouville', 'mu_minus_half_liouville')


class Meter:
    def __init__(self, cap=50_000_000, seconds=600):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer work cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite time cap')
        self.cap, self.operations = cap, 0
        self.deadline = time.monotonic()+seconds

    def charge(self, n=1):
        if type(n) is not int or n < 0 or n > self.cap-self.operations:
            raise OverflowError('log-rate review work cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('log-rate review deadline')

    def counts(self):
        return {'operations': self.operations}


def _meter(meter):
    return meter if meter is not None else Meter()


def rational(text):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational required')
    value = F(text)
    if str(value) != text or max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > 4096:
        raise ValueError('canonical rational within bit cap')
    return value


def _positive(text):
    value = rational(text)
    if value <= 0:
        raise ValueError('positive exponent/rate required')
    return value


def _factor(n, meter):
    if type(n) is not int or not 1 <= n <= 4096:
        raise ValueError('scalar arithmetic index1..4096')
    factors, p = [], 2
    while p*p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
            meter.charge(4)
        if e:
            factors.append((p, e))
        p += 1
        meter.charge(4)
    if n > 1:
        factors.append((n, 1))
    return factors


def mobius(n, meter=None):
    factors = _factor(n, _meter(meter))
    return 0 if any(e > 1 for _, e in factors) else (-1)**len(factors)


def arithmetic(channel, n, meter=None):
    meter = _meter(meter)
    if channel not in CHANNELS:
        raise ValueError('declared arithmetic channel')
    factors = _factor(n, meter)
    mu = 0 if any(e > 1 for _, e in factors) else (-1)**len(factors)
    liouville = (-1)**sum(e for _, e in factors)
    values = {'mu': F(mu), 'liouville': F(liouville), 'radical_sign': F((-1)**len(factors)),
              'one': F(1), 'mu_plus_half_liouville': F(mu)+F(liouville, 2),
              'mu_minus_half_liouville': F(mu)-F(liouville, 2)}
    if channel == 'mu_convolution_mu':
        return F(sum(mobius(d, meter)*mobius(n//d, meter) for d in range(1, n+1) if n % d == 0))
    return values[channel]


def canonical_terms(terms, n):
    """Exact rational coefficients of positive logarithmic monomials."""
    result = {}
    for term in terms:
        c, a, b = rational(term['rational']), rational(term['log_n_power']), rational(term['log_2_power'])
        if n == 2:
            a, b = F(0), a+b
        key = (a, b)
        result[key] = result.get(key, F(0))+c
    return [{'rational': str(c), 'log_n_power': str(a), 'log_2_power': str(b)}
            for (a, b), c in sorted(result.items()) if c]


def _flat(reason):
    return {'status': 'flat', 'rate': None, 'coefficient': [], 'cancellation_barrier': None, 'reason': reason}


def _leading(rate, terms, n, reason):
    terms = canonical_terms(terms, n)
    if not terms:
        return {'status': 'UNRESOLVED', 'rate': None, 'coefficient': [],
                'cancellation_barrier': str(rate), 'reason': 'first-order cancellation; next term not compiled'}
    return {'status': 'leading', 'rate': str(rate), 'coefficient': terms,
            'cancellation_barrier': None, 'reason': reason}


def _scale(expansion, scalar):
    if scalar == 0:
        return _flat('exact zero arithmetic multiplier')
    result = dict(expansion)
    result['coefficient'] = [dict(term, rational=str(scalar*rational(term['rational'])))
                             for term in expansion['coefficient']]
    return result


def combine(expansions, n, reason='sum of typed expansions'):
    """Keep the first provable order; cancelled o-terms cannot be bypassed."""
    known = [e for e in expansions if e['status'] == 'leading']
    barriers = [rational(e['cancellation_barrier']) for e in expansions if e['status'] == 'UNRESOLVED']
    if not known:
        if barriers:
            return {'status': 'UNRESOLVED', 'rate': None, 'coefficient': [],
                    'cancellation_barrier': str(min(barriers)), 'reason': 'next term beyond cancellation not compiled'}
        return _flat('all terms individually proved flat')
    nu = min(rational(e['rate']) for e in known)
    if barriers and min(barriers) < nu:
        return {'status': 'UNRESOLVED', 'rate': None, 'coefficient': [],
                'cancellation_barrier': str(min(barriers)), 'reason': 'uncompiled remainder may dominate later term'}
    terms = [term for e in known if rational(e['rate']) == nu for term in e['coefficient']]
    return _leading(nu, terms, n, reason)


def weight_correction(ast, n, meter=None, depth=0):
    """Formal expansion of W(n,N)-1 with scale L=N.bit_length()."""
    meter = _meter(meter)
    if type(ast) is not dict or depth > 6:
        raise ValueError('bounded typed weight AST')
    meter.charge(64)
    kind = ast.get('kind')
    if kind == 'unit' and set(ast) == {'kind'}:
        return _flat('unit correction is exactly zero')
    if kind == 'taper' and set(ast) == {'kind', 'coordinate', 'alpha', 'gamma'}:
        alpha, gamma = _positive(ast['alpha']), _positive(ast['gamma'])
        if ast['coordinate'] == 'cutoff':
            return _flat('positive N-power cutoff and dyadic errors are flat in every log power')
        if ast['coordinate'] != 'log':
            raise ValueError('typed taper coordinate')
        return _leading(alpha, [{'rational': str(-gamma), 'log_n_power': str(alpha), 'log_2_power': str(-alpha)}], n,
                        'log coordinate and positive root Taylor expansion; rounding flat')
    if kind == 'vanishing_twist' and set(ast) == {'kind', 'rate', 'level_power'}:
        rate, level = _positive(ast['rate']), ast['level_power']
        if type(level) is not int or not 1 <= level <= 8:
            raise ValueError('typed positive level power1..8')
        return _leading(F(level), [{'rational': str(-rate), 'log_n_power': '1', 'log_2_power': '0'}], n,
                        'exp(-rate*log(n)/L^level) first Taylor term; rounding flat')
    if kind == 'product' and set(ast) == {'kind', 'left', 'right'}:
        expansions = [weight_correction(ast[key], n, meter, depth+1) for key in ('left', 'right')]
        return combine(expansions, n, 'product corrections add at first order; correction product is higher order')
    raise ValueError('weight AST has no compiled rate rule')


def envelope_expansion(ast, n, meter=None):
    meter = _meter(meter)
    if type(ast) is not dict:
        raise ValueError('typed envelope AST')
    kind = ast.get('kind')
    if kind == 'difference' and set(ast) == {'kind', 'left', 'right'}:
        return combine([weight_correction(ast['left'], n, meter),
                        _scale(weight_correction(ast['right'], n, meter), F(-1))], n, 'difference of weight corrections')
    if kind in ('log_amplitude', 'power_amplitude') and set(ast) == {'kind', 'power', 'weight'}:
        power = _positive(ast['power'])
        weight_correction(ast['weight'], n, meter)  # validates limit-one typed weight
        if kind == 'power_amplitude':
            return _flat('N^-power times bounded weight and rounding are flat')
        return _leading(power, [{'rational': '1', 'log_n_power': '0', 'log_2_power': '0'}], n,
                        'rounded L^-power amplitude times a weight tending1')
    if kind == 'moving_band' and set(ast) == {'kind', 'cutoff_power', 'weight'}:
        if not _positive(ast['cutoff_power']) < 1:
            raise ValueError('moving cutoff exponent0<theta<1')
        weight_correction(ast['weight'], n, meter)
        return _flat('fixed index eventually excluded exactly by moving lower cutoff')
    raise ValueError('envelope AST has no compiled rate rule')


def coefficient_error(recipe, n, meter=None):
    meter = _meter(meter)
    if type(n) is not int or not 2 <= n <= 64:
        raise ValueError('fixed review index2..64')
    if type(recipe) is not dict or set(recipe) != {'id', 'base', 'auxiliary'} or type(recipe['id']) is not str or not 1 <= len(recipe['id']) <= 100:
        raise ValueError('exact typed044 recipe')
    mu = mobius(n, meter)
    terms = [_scale(weight_correction(recipe['base'], n, meter), F(-mu))]
    auxiliary = recipe['auxiliary']
    aux_value = None
    if auxiliary is not None:
        if type(auxiliary) is not dict or set(auxiliary) != {'channel', 'coefficient', 'envelope'}:
            raise ValueError('exact typed arithmetic auxiliary')
        scalar = rational(auxiliary['coefficient'])
        if not scalar:
            raise ValueError('auxiliary scalar must be nonzero')
        aux_value = arithmetic(auxiliary['channel'], n, meter)
        terms.append(_scale(envelope_expansion(auxiliary['envelope'], n, meter), scalar*aux_value))
    return {'index': n, 'mu': mu, 'auxiliary_arithmetic': None if aux_value is None else str(aux_value),
            'expansion': combine(terms, n, 'coefficient error c_n(N)+mu(n)'),
            'coefficient_limit_is_compatible': True}


def verify_witness(witness, meter=None):
    """Independent rational column/constant/tail replay of imported witness."""
    meter = _meter(meter)
    n = witness['index']
    if type(n) is not int or not 2 <= n <= 64:
        raise ValueError('witness index2..64')
    alpha, previous = {}, 0
    for row in witness['cells']:
        k, a = row['k'], rational(row['alpha'])
        if type(k) is not int or not previous < k <= n or not a:
            raise ValueError('witness cell schema')
        alpha[k], previous = a, k
    if sum(k*a for k, a in alpha.items()) != 0 or witness['higher_support_slope'] != '0':
        raise ValueError('linear higher-support annihilation fails')
    if sum(alpha.values()) != mobius(n, meter) or rational(witness['constant']) != sum(alpha.values()):
        raise ValueError('witness constant fails')
    for j in range(2, n+1):
        if sum(a*F(k % j, j) for k, a in alpha.items()) != -int(j == n):
            raise ValueError('finite witness column fails')
        meter.charge(4*len(alpha))
    if sum(a*a*k*(k+1) for k, a in alpha.items()) != rational(witness['denominator']):
        raise ValueError('witness Cauchy denominator fails')
    return True


def _enclosure(value):
    lo, hi = value.lower().man_exp(), value.upper().man_exp()
    return {'ball': value.str(65), 'lower_dyadic': [str(lo[0]), int(lo[1])],
            'upper_dyadic': [str(hi[0]), int(hi[1])]}


def license_nonzero(terms, n, precision=192, meter=None):
    meter = _meter(meter)
    terms = canonical_terms(terms, n)
    if type(precision) is not int or not 128 <= precision <= 4096:
        raise ValueError('Arb precision128..4096')
    if not terms:
        return {'status': 'UNRESOLVED', 'method': 'cancelled', 'sign': 0, 'precision': precision, 'enclosure': None}
    signs = {1 if rational(term['rational']) > 0 else -1 for term in terms}
    structural = next(iter(signs)) if len(signs) == 1 else 0
    with ctx.workprec(precision):
        total, ln, l2 = arb(0), arb(n).log(), arb(2).log()
        for term in terms:
            c, a, b = (rational(term[key]) for key in ('rational', 'log_n_power', 'log_2_power'))
            total += (arb(c.numerator)/c.denominator)*(ln**(arb(a.numerator)/a.denominator))*(l2**(arb(b.numerator)/b.denominator))
            meter.charge(64+8*precision+a.numerator.bit_length()+a.denominator.bit_length()+b.numerator.bit_length()+b.denominator.bit_length())
        if not total.is_finite():
            return {'status': 'certified' if structural else 'UNRESOLVED',
                    'method': 'structural_sign' if structural else 'Arb', 'sign': structural,
                    'precision': precision, 'enclosure': None}
        sign = 1 if total > 0 else (-1 if total < 0 else 0)
        if structural and sign and sign != structural:
            raise ArithmeticError('structural and interval signs disagree')
        return {'status': 'certified' if (structural or sign) else 'UNRESOLVED',
                'method': 'structural_sign' if structural else 'Arb', 'sign': structural or sign,
                'precision': precision, 'enclosure': _enclosure(total)}


def review_recipe(recipe, rules=None, max_index=16, precision=192, meter=None, witnesses=None):
    meter = _meter(meter)
    if type(max_index) is not int or not 2 <= max_index <= 64:
        raise ValueError('bounded witness scan2..64')
    rules = [] if rules is None else rules
    if type(rules) is not list:
        raise ValueError('list of fixed-family rules')
    cache = {} if witnesses is None else witnesses
    candidates = []
    for n in range(2, max_index+1):
        if n not in cache:
            cache[n] = generate_witness(n, meter)
        verify_witness(cache[n], meter)
        error = coefficient_error(recipe, n, meter)
        expansion = error['expansion']
        license = license_nonzero(expansion['coefficient'], n, precision, meter) if expansion['status'] == 'leading' else None
        status = 'certified_rate_obstruction' if license and license['status'] == 'certified' else ('UNRESOLVED' if expansion['status'] != 'flat' else 'OPEN')
        candidates.append({**error, 'status': status, 'nonzero_license': license,
                           'witness': cache[n],
                           'energy_rate': str(2*rational(expansion['rate'])) if status == 'certified_rate_obstruction' else None,
                           'asymptotic_norm_lower': 'liminf L^(2*nu)*norm_squared >= leading_coefficient^2/witness.denominator' if status == 'certified_rate_obstruction' else None})
    certified = [row for row in candidates if row['status'] == 'certified_rate_obstruction']
    strongest = min(certified, key=lambda row: (rational(row['energy_rate']), row['index'])) if certified else None
    rule_reviews = []
    for rule in rules:
        if rule.get('family') != recipe['id'] or type(rule.get('q')) is not int or not 2 <= rule['q'] <= 64:
            raise ValueError('matching typed refinement rule')
        b = rational(rule['b'])
        bound = rule.get('finite_log_bound')
        if type(bound) is not dict or set(bound) != {'A', 'eta'} or rational(bound['A']) <= 0 or rational(bound['eta']) <= 0:
            raise ValueError('positive exact logarithmic bound A/eta')
        eta, q = rational(bound['eta']), rule['q']
        forcings = []
        for row in candidates:
            response = sum(rational(cell['alpha']) for cell in row['witness']['cells'] if cell['k'] >= q)
            eligible = not b or (row['index'] % q != 0 and response == 0)
            if not eligible:
                forcings.append({'index': row['index'], 'status': 'UNRESOLVED',
                                 'reason': 'divisible forcing index/parent coefficient not compiled', 'step_response': str(response)})
                continue
            rejected = row['energy_rate'] is not None and eta > rational(row['energy_rate'])
            forcing_status = 'analytically_refuted' if rejected else ('UNRESOLVED' if row['status'] == 'UNRESOLVED' else 'OPEN')
            forcings.append({'index': row['index'], 'status': forcing_status,
                             'energy_rate': row['energy_rate'], 'declared_eta': str(eta),
                             'step_response': str(response), 'candidate': row,
                             'gap_binding': 'child coefficient error at qN; parent floor and indicator contributions vanish' if b else 'b0 forcing is child residual',
                             'child_scale_equivalence': 'L(qN)/L(N)->1',
                             'strict_rejection': rejected})
        rejections = [row for row in forcings if row['status'] == 'analytically_refuted']
        best = min(rejections, key=lambda row: (rational(row['energy_rate']), row['index'])) if rejections else None
        rule_reviews.append({'rule': rule, 'status': 'analytically_refuted' if best else 'OPEN',
                             'strongest_rejection': best, 'forcing_candidates': forcings,
                             'strict_eta_rejections': [{'index': row['index'], 'energy_rate': row['energy_rate']} for row in rejections],
                             'equality_or_smaller_eta_proved': False})
    return {'schema': 'floor-log-rate-review-v1', 'recipe': recipe,
            'scan_indices': [2, max_index], 'scale': 'L=N.bit_length()', 'precision': precision,
            'target_candidates': candidates, 'strongest_target_rate_obstruction': strongest,
            'rule_reviews': rule_reviews, 'necessary_rate_obstruction_only': True,
            'convergence_status': 'OPEN', 'uniform_upper_bound_proved': False,
            'additional_norms_evaluated': False, 'source_arrays_read': False,
            'frozen_files_modified': False, 'RH_proved': False, 'RH_refuted': False,
            'counts': meter.counts()}


def audit_selected(selected, max_index=16, precision=192, meter=None):
    meter = _meter(meter)
    if type(selected) is not dict or set(selected) != {'recipes', 'rules'}:
        raise ValueError('frozen selected recipe/rule object')
    recipes = {recipe['id']: recipe for recipe in selected['recipes']}
    if len(recipes) != len(selected['recipes']):
        raise ValueError('unique selected recipes')
    grouped, identities = {identifier: [] for identifier in recipes}, set()
    for rule in selected['rules']:
        if rule.get('family') not in recipes:
            raise ValueError('every rule needs its exact recipe')
        identity = (rule['family'], rule['q'], rule['b'], rule.get('stratum'))
        if identity in identities:
            raise ValueError('duplicate rule identity')
        identities.add(identity)
        grouped[rule['family']].append(rule)
    if any(not rules for rules in grouped.values()):
        raise ValueError('every selected recipe needs a rule')
    cache = {}
    return {'schema': 'floor-selected-log-rate-review-v1',
            'reviews': [review_recipe(recipe, grouped[identifier], max_index, precision, meter, cache) for identifier, recipe in recipes.items()],
            'additional_norms_evaluated': False, 'source_arrays_read': False,
            'convergence_status': 'OPEN', 'RH_proved': False, 'RH_refuted': False,
            'counts': meter.counts()}


def review_frontier(recipes, eta_values, max_index=16, precision=192, meter=None):
    """Per-recipe necessary target-rate restrictions, without ranking/observations."""
    meter = _meter(meter)
    if type(recipes) is not list or len(recipes) > 10000 or len({r['id'] for r in recipes}) != len(recipes):
        raise ValueError('bounded unique recipe list')
    if type(eta_values) is not list or not eta_values or any(rational(eta) <= 0 for eta in eta_values):
        raise ValueError('positive exact eta list')
    cache, rows = {}, []
    for recipe in recipes:
        result = review_recipe(recipe, None, max_index, precision, meter, cache)
        best = result['strongest_target_rate_obstruction']
        rate = rational(best['energy_rate']) if best else None
        rows.append({'recipe': recipe, 'strongest_target_rate_obstruction': best,
                     'refuted_etas': [eta for eta in eta_values if rate is not None and rational(eta) > rate],
                     'OPEN_etas': [eta for eta in eta_values if rate is None or rational(eta) <= rate],
                     'convergence_status': 'OPEN'})
    return {'schema': 'floor-log-rate-frontier-v1', 'rows': rows,
            'eta_values': eta_values, 'necessary_rate_obstruction_only': True,
            'additional_norms_evaluated': False, 'source_arrays_read': False,
            'convergence_status': 'OPEN', 'RH_proved': False, 'RH_refuted': False,
            'counts': meter.counts()}
