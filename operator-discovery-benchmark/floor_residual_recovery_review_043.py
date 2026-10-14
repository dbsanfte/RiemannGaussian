"""Exact finite-cell coefficient recovery and fixed-recipe obstruction review.

No norm evaluation, imported coefficient array or frozen-file mutation occurs.
Witnesses are solved from rational cell equations and independently replayable.
"""
from fractions import Fraction as F
import math
import time

CHANNELS = ('mu', 'liouville', 'mu_convolution_mu', 'radical_sign', 'one',
            'mu_plus_half_liouville', 'mu_minus_half_liouville')
MAX_POWER_BITS = 400_000


class Meter:
    def __init__(self, cap=50_000_000, seconds=600):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer work cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite time cap')
        self.cap, self.operations, self.max_power_bits = cap, 0, 0
        self.deadline = time.monotonic()+seconds

    def charge(self, n=1):
        if type(n) is not int or n < 0 or n > self.cap-self.operations:
            raise OverflowError('recovery review work cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('recovery review deadline')

    def counts(self):
        return {'operations': self.operations, 'max_power_bits': self.max_power_bits}


def _meter(meter):
    return meter if meter is not None else Meter()


def rational(text):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('canonical rational string required')
    value = F(text)
    if str(value) != text or max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > 4096:
        raise ValueError('bounded canonical rational required')
    return value


def factors(n, meter=None):
    meter = _meter(meter)
    if type(n) is not int or not 1 <= n <= 4096:
        raise ValueError('small exact coefficient index1..4096 required')
    result, p = [], 2
    while p*p <= n:
        meter.charge(4)
        e = 0
        while n % p == 0:
            n //= p
            e += 1
            meter.charge(4)
        if e:
            result.append((p, e))
        p += 1
    if n > 1:
        result.append((n, 1))
    return result


def mu(n, meter=None):
    fac = factors(n, meter)
    return 0 if any(e > 1 for _, e in fac) else (-1)**len(fac)


def channel_value(channel, n, meter=None):
    meter = _meter(meter)
    if channel not in CHANNELS:
        raise ValueError('declared arithmetic channel required')
    fac = factors(n, meter)
    mobius = 0 if any(e > 1 for _, e in fac) else (-1)**len(fac)
    liouville = (-1)**sum(e for _, e in fac)
    values = {'mu': F(mobius), 'liouville': F(liouville),
              'radical_sign': F((-1)**len(fac)), 'one': F(1),
              'mu_plus_half_liouville': F(mobius)+F(liouville, 2),
              'mu_minus_half_liouville': F(mobius)-F(liouville, 2)}
    if channel == 'mu_convolution_mu':
        return F(sum(mu(d, meter)*mu(n//d, meter) for d in range(1, n+1) if n % d == 0))
    return values[channel]


def generate_witness(index, meter=None):
    """Solve cell-linear equations; the higher-support slope is killed exactly."""
    meter = _meter(meter)
    if type(index) is not int or not 2 <= index <= 64:
        raise ValueError('witness index2..64 resource domain')
    # Rows: alpha dot k=0; alpha dot f_j=-delta_(j,index),2<=j<=index.
    matrix = [[F(k) for k in range(1, index+1)]+[F(0)]]
    for j in range(2, index+1):
        matrix.append([F(k % j, j) for k in range(1, index+1)]+[F(-int(j == index))])
    meter.charge(index*index)
    for column in range(index):
        pivot = next((row for row in range(column, index) if matrix[row][column]), None)
        if pivot is None:
            raise ArithmeticError('singular recovery equations')
        matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
        scalar = matrix[column][column]
        matrix[column] = [entry/scalar for entry in matrix[column]]
        meter.charge(index+1)
        for row in range(index):
            if row != column and matrix[row][column]:
                scalar = matrix[row][column]
                matrix[row] = [a-scalar*b for a, b in zip(matrix[row], matrix[column])]
                meter.charge(3*(index+1))
    alpha = [matrix[k][-1] for k in range(index)]
    denominator = sum(a*a*k*(k+1) for k, a in enumerate(alpha, 1))
    result = {'schema': 'floor-coefficient-cell-witness-v1', 'index': index,
              'cells': [{'k': k, 'alpha': str(a)} for k, a in enumerate(alpha, 1) if a],
              'constant': str(sum(alpha)), 'denominator': str(denominator),
              'higher_support_slope': '0',
              'identity': 'c_index+mu(index)-sum d_q*step_response(q)=sum alpha_k*e(cell k)',
              'norm_lower': '(c_index+mu(index)-sum d_q*step_response(q))^2/denominator'}
    verify_witness(result, meter)
    return result


def verify_witness(witness, meter=None):
    """Replay supplied rational equations without solving them or trusting mu."""
    meter = _meter(meter)
    expected = {'schema', 'index', 'cells', 'constant', 'denominator', 'higher_support_slope', 'identity', 'norm_lower'}
    if type(witness) is not dict or set(witness) != expected or witness.get('schema') != 'floor-coefficient-cell-witness-v1':
        raise ValueError('cell witness schema required')
    n = witness.get('index')
    if type(n) is not int or not 2 <= n <= 64:
        raise ValueError('bounded witness index')
    alpha, previous = {}, 0
    for row in witness['cells']:
        k, a = row['k'], rational(row['alpha'])
        if type(k) is not int or not previous < k <= n or not a:
            raise ValueError('sorted nonzero rational witness entries required')
        alpha[k], previous = a, k
    if sum(k*a for k, a in alpha.items()) != 0:
        raise ValueError('higher-support slope fails')
    for j in range(2, n+1):
        if sum(a*F(k % j, j) for k, a in alpha.items()) != -int(j == n):
            raise ValueError('finite coefficient elimination fails')
        meter.charge(4*len(alpha))
    constant = sum(alpha.values())
    if constant != mu(n, meter) or rational(witness['constant']) != constant:
        raise ValueError('constant/Mobius recovery fails')
    denominator = sum(a*a*k*(k+1) for k, a in alpha.items())
    if denominator <= 0 or rational(witness['denominator']) != denominator:
        raise ValueError('Cauchy denominator fails')
    if witness['higher_support_slope'] != '0':
        raise ValueError('higher-support scope differs')
    if witness['identity'] != 'c_index+mu(index)-sum d_q*step_response(q)=sum alpha_k*e(cell k)' or witness['norm_lower'] != '(c_index+mu(index)-sum d_q*step_response(q))^2/denominator':
        raise ValueError('witness theorem scope differs')
    return True


def root_bracket(base, exponent_text, bits=24, meter=None):
    """Exact dyadic bracket of a rational power, including exact endpoint proof."""
    meter = _meter(meter)
    exponent = rational(exponent_text)
    if type(base) is not F or not 0 <= base <= 1 or exponent < 0 or type(bits) is not int or not 1 <= bits <= 128:
        raise ValueError('rational unit base, nonnegative exponent and bounded bits')
    if exponent == 0:
        return {'base': str(base), 'exponent': exponent_text, 'bits': bits, 'lower': '1', 'upper': '1',
                'lower_power_comparison': '<=', 'upper_power_comparison': '>='}
    a, b = exponent.numerator, exponent.denominator
    predicted = bits*b+a*max(base.numerator.bit_length(), base.denominator.bit_length())+2
    if predicted > MAX_POWER_BITS:
        raise OverflowError('exact root-bracket power bit cap')
    meter.max_power_bits = max(meter.max_power_bits, predicted)
    meter.charge(predicted)
    D, factor, rhs = 1 << bits, base.denominator**a, (1 << (bits*b))*base.numerator**a
    lo, hi = 0, D
    if base == 1:
        lo = D
    else:
        while lo+1 < hi:
            mid = (lo+hi)//2
            meter.charge(max(1, predicted//16))
            if mid**b*factor <= rhs:
                lo = mid
            else:
                hi = mid
    upper = lo if lo**b*factor == rhs else lo+1
    return {'base': str(base), 'exponent': exponent_text, 'bits': bits,
            'lower': str(F(lo, D)), 'upper': str(F(upper, D)),
            'lower_power_comparison': '<=', 'upper_power_comparison': '>='}


def verify_root_bracket(bracket, meter=None):
    meter = _meter(meter)
    base, exponent = rational(bracket['base']), rational(bracket['exponent'])
    lo, hi = rational(bracket['lower']), rational(bracket['upper'])
    if not 0 <= base <= 1 or exponent < 0 or not 0 <= lo <= hi <= 1:
        raise ValueError('rational root bracket domain')
    if exponent == 0:
        if (lo, hi) != (1, 1):
            raise ValueError('zero-power bracket')
        return True
    a, b = exponent.numerator, exponent.denominator
    predicted = max(lo.denominator.bit_length(), hi.denominator.bit_length())*b+max(base.numerator.bit_length(), base.denominator.bit_length())*a+2
    if predicted > MAX_POWER_BITS:
        raise OverflowError('root replay power cap')
    meter.max_power_bits = max(meter.max_power_bits, predicted)
    meter.charge(predicted)
    value = base**a
    if not lo**b <= value <= hi**b:
        raise ValueError('root-power inequality fails')
    return True


def _recipe(recipe):
    if type(recipe) is not dict or set(recipe) != {'id', 'channel', 'decay', 'taper', 'anchor_cell_one'}:
        raise ValueError('exact fixed-recipe schema')
    if type(recipe['id']) is not str or not recipe['id'] or recipe['channel'] not in CHANNELS or type(recipe['anchor_cell_one']) is not bool:
        raise ValueError('recipe identity/channel/anchor')
    if rational(recipe['decay']) < 0:
        raise ValueError('nonnegative decay')
    if recipe['taper'] is not None:
        if set(recipe['taper']) != {'alpha', 'gamma'} or any(rational(recipe['taper'][key]) <= 0 for key in ('alpha', 'gamma')):
            raise ValueError('positive fixed taper exponents')


def coefficient_limit(recipe, n, bits=24, meter=None):
    meter = _meter(meter)
    _recipe(recipe)
    if recipe['anchor_cell_one'] and n == 2:
        return {'index': n, 'status': 'unresolved', 'reason': 'anchoring changes coefficient2 using the full growing sum'}
    value = channel_value(recipe['channel'], n, meter)
    bracket = root_bracket(F(1, n), recipe['decay'], bits, meter)
    verify_root_bracket(bracket, meter)
    x, y = -value*rational(bracket['lower']), -value*rational(bracket['upper'])
    return {'index': n, 'status': 'certified', 'channel_value': str(value),
            'root_bracket': bracket, 'lower': str(min(x, y)), 'upper': str(max(x, y)),
            'limit_formula': '-a(n)*n^(-beta)',
            'taper_limit': '1', 'dyadic_rounding_error': '<2^(-4*ceil(log2(N))) ->0',
            'anchor_affects_this_index': False}


def _bound(witness, lo, hi):
    distance = lo if lo > 0 else (-hi if hi < 0 else F(0))
    return distance*distance/rational(witness['denominator'])


def review_recipe(recipe, rule=None, max_index=16, bits=24, meter=None, witnesses=None):
    """Scan indices algorithmically; select strongest exact certified obstruction."""
    meter = _meter(meter)
    _recipe(recipe)
    if type(max_index) is not int or not 2 <= max_index <= 64:
        raise ValueError('review index resource cap')
    if rule is not None:
        if rule.get('family') != recipe['id'] or type(rule.get('q')) is not int or not 2 <= rule['q'] <= 64:
            raise ValueError('matching refinement rule required')
        b, q = rational(rule['b']), rule['q']
    cache = {} if witnesses is None else witnesses
    targets, forcings, limits = [], [], {}

    def limit(n):
        if n not in limits:
            limits[n] = coefficient_limit(recipe, n, bits, meter)
        return limits[n]

    for n in range(2, max_index+1):
        if n not in cache:
            cache[n] = generate_witness(n, meter)
        w, c = cache[n], limit(n)
        if c['status'] != 'certified':
            targets.append({'index': n, 'status': 'unresolved', 'reason': c['reason']})
        else:
            lo, hi = rational(c['lower'])+mu(n, meter), rational(c['upper'])+mu(n, meter)
            lower = _bound(w, lo, hi)
            targets.append({'index': n, 'status': 'refuted' if lower else 'open',
                            'coefficient_limit': c, 'gap': [str(lo), str(hi)],
                            'liminf_energy_lower': str(lower), 'witness': w})
        if rule is None:
            continue
        if c['status'] != 'certified' or (b and n == q and not recipe['anchor_cell_one']):
            forcings.append({'index': n, 'status': 'unresolved',
                             'reason': 'forcing coefficient depends on unresolved anchored coefficient or full sum at dilation index'})
            continue
        lo, hi = rational(c['lower']), rational(c['upper'])
        parent = None
        if b and n == q:
            lo, hi = lo+b, hi+b  # Anchoring exactly enforces sum c_n/n=1.
        elif b and n % q == 0 and n//q >= 2:
            parent = limit(n//q)
            if parent['status'] != 'certified':
                forcings.append({'index': n, 'status': 'unresolved', 'reason': parent['reason']})
                continue
            products = [b*rational(parent['lower']), b*rational(parent['upper'])]
            lo, hi = lo-max(products), hi-min(products)
        response = sum(rational(row['alpha']) for row in w['cells'] if row['k'] >= q)
        lo, hi = lo+mu(n, meter)-b*response, hi+mu(n, meter)-b*response
        lower = _bound(w, lo, hi)
        forcings.append({'index': n, 'status': 'refuted' if lower else 'open',
                         'child_coefficient_limit': c, 'parent_coefficient_limit': parent,
                         'step_response': str(response), 'gap': [str(lo), str(hi)],
                         'liminf_forcing_energy_lower': str(lower), 'witness': w})

    def strongest(rows, field):
        admissible = [row for row in rows if row['status'] == 'refuted']
        return max(admissible, key=lambda row: (rational(row[field]), -row['index'])) if admissible else None

    best_target = strongest(targets, 'liminf_energy_lower')
    best_forcing = strongest(forcings, 'liminf_forcing_energy_lower')
    return {'schema': 'floor-fixed-recipe-recovery-review-v1', 'recipe': recipe, 'rule': rule,
            'scan_indices': [2, max_index], 'root_bracket_bits': bits,
            'target_convergence_status': 'analytically_refuted' if best_target else 'OPEN',
            'strongest_target_witness': best_target, 'target_candidates': targets,
            'forcing_bound_status': 'analytically_refuted' if best_forcing else 'OPEN',
            'forcing_claim_scope': 'any forcing energy upper bound tending0 along the growing fixed recipe',
            'strongest_forcing_witness': best_forcing, 'forcing_candidates': forcings,
            'necessary_condition_only': True, 'RH_proved': False, 'RH_refuted': False,
            'rejected_scope': 'only this exact fixed recipe; no rejection of primitives or scale-vanishing mixtures',
            'resource_guards_do_not_truncate_mathematical_recipe': True,
            'additional_norms_evaluated': False, 'source_arrays_read': False,
            'counts': meter.counts()}


def review_selected(selected, max_index=16, bits=24, meter=None):
    meter = _meter(meter)
    if type(selected) is not dict or set(selected) != {'recipes', 'rules'}:
        raise ValueError('frozen selected recipe/rule schema')
    recipes = {row['id']: row for row in selected['recipes']}
    if len(recipes) != len(selected['recipes']):
        raise ValueError('unique selected recipe ids')
    identities, matched = set(), set()
    for row in selected['rules']:
        if row.get('family') not in recipes:
            raise ValueError('every declared rule requires its matching recipe')
        identity = (row['family'], row['q'], row['b'], row.get('stratum'))
        if identity in identities:
            raise ValueError('duplicate selected rule identity')
        identities.add(identity)
        matched.add(row['family'])
    if matched != set(recipes):
        raise ValueError('every selected recipe requires a declared rule')
    witnesses = {}
    reviews = [review_recipe(recipes[rule['family']], rule, max_index, bits, meter, witnesses)
               for rule in selected['rules']]
    return {'schema': 'floor-selected-recovery-review-v1', 'reviews': reviews,
            'counts': meter.counts(), 'additional_norms_evaluated': False,
            'source_arrays_read': False, 'RH_proved': False, 'RH_refuted': False}


def audit_selected(recipes, rules=None, max_index=16, bits=24, meter=None):
    """Accept either the frozen selected object or separate recipe/rule lists."""
    selected = recipes if rules is None else {'recipes': recipes, 'rules': rules}
    return review_selected(selected, max_index, bits, meter)


def review_frontier(recipes, max_index=16, bits=24, meter=None):
    """Apply only the exact necessary-condition gate; never rank or observe norms."""
    meter = _meter(meter)
    if type(recipes) is not list or len(recipes) > 10_000:
        raise ValueError('bounded frozen recipe list required')
    if len({recipe['id'] for recipe in recipes}) != len(recipes):
        raise ValueError('unique frozen recipe ids')
    witnesses, rows, open_recipes = {}, [], []
    for recipe in recipes:
        review = review_recipe(recipe, None, max_index, bits, meter, witnesses)
        rows.append({'id': recipe['id'], 'recipe': recipe,
                     'target_convergence_status': review['target_convergence_status'],
                     'strongest_target_witness': review['strongest_target_witness'],
                     'anchored_coefficient2_limit_status': 'unresolved' if recipe['anchor_cell_one'] else 'certified',
                     'rejected_scope': review['rejected_scope']})
        if review['target_convergence_status'] == 'OPEN':
            open_recipes.append(recipe)
    return {'schema': 'floor-recovery-filtered-frontier-v1',
            'scan_indices': [2, max_index], 'root_bracket_bits': bits,
            'rows': rows, 'OPEN_recipes': open_recipes,
            'total': len(rows), 'refuted': len(rows)-len(open_recipes), 'OPEN': len(open_recipes),
            'necessary_condition_only': True, 'frontier_convergence_proved': False,
            'prior_selection_or_scores_changed': False, 'additional_norms_evaluated': False,
            'source_arrays_read': False, 'RH_proved': False, 'RH_refuted': False,
            'counts': meter.counts()}
