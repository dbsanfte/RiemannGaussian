"""Feedback-generated affine-log arithmetic contrasts and complement bounds.

All shared logarithms are exact symbolic quantities; interval arithmetic only
encloses their values. Candidate covariance prices remain finite conjectures.
"""
from fractions import Fraction as Q
from itertools import combinations, product
import math
import random

import numpy as np

import mobius_scale_flux_079 as OLD

DIM = 10
SLOPES = ('-2', '-1', '-1/2', '1/2', '1', '2')


def log_spec(argument):
    r = Q(argument)
    if not Q(1, 16) <= r <= 16:
        raise ValueError('bounded positive logarithm argument')
    z = (r-1)/(r+1)
    t = abs(z)
    lower = 2*sum((t**(2*k+1)/(2*k+1) for k in range(32)), Q(0))
    upper = lower+2*t**65/(65*(1-t*t))
    if z < 0:
        lower, upper = -upper, -lower
    return dict(argument=str(r), terms=32, lower=str(lower), upper=str(upper))


def ray_key(ray):
    return tuple(tuple(map(Q, pair)) for pair in ray)


def save_ray(ray):
    return [[str(x), str(y)] for x, y in ray]


def zero_ray():
    return [[Q(0), Q(0)] for _ in range(DIM)]


def poly_add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def poly_scale(a, c):
    return tuple(c*x for x in a)


def affine_product(a, b):
    return a[0]*b[0], a[0]*b[1]+a[1]*b[0], a[1]*b[1]


def evaluate(poly, x):
    value = Q(0)
    for a in reversed(poly):
        value = value*x+a
    return value


def polynomial_range(poly, logspec):
    lo, hi = Q(logspec['lower']), Q(logspec['upper'])
    values = [evaluate(poly, lo), evaluate(poly, hi)]
    if len(poly) == 3 and poly[2]:
        vertex = -poly[1]/(2*poly[2])
        if lo <= vertex <= hi:
            values.append(evaluate(poly, vertex))
    return min(values), max(values)


def coefficient_maximum(ray, logspec):
    return max(max(abs(x) for x in polynomial_range(tuple(map(Q, a)), logspec)) for a in ray)


def primitive_rays(active, support_budget=3):
    if (type(active) is not list or any(type(i) is not int or not 0 <= i < DIM for i in active)
            or active != sorted(set(active))):
        raise ValueError('sorted unique active coordinates required')
    if not 1 <= support_budget <= 3:
        raise ValueError('declared primitive support budget')
    result = []
    for size in range(1, min(support_budget, len(active))+1):
        for indices in combinations(active, size):
            for slopes in product(SLOPES, repeat=size-1):
                ray = zero_ray()
                for i, value in zip(indices, ('1',)+slopes):
                    ray[i][0] = Q(value)
                result.append(save_ray(ray))
    return result


def promote(ray, coordinates):
    """Solve the supplied signature (-1,L) by eliminating its first coefficient.

    The normalization is algebraic at the constant second-coordinate anchor.
    Other occupied channels are retained and have separate unpaid signatures.
    """
    i, j = coordinates
    a = [list(map(Q, x)) for x in ray]
    if a[j][1] or not a[j][0]:
        return None
    divisor = a[j][0]
    a = [[x/divisor, y/divisor] for x, y in a]
    a[i] = [Q(0), Q(1)]
    return save_ray(a)


def complement(ray, target):
    return [[str(Q(t)-Q(a[0])), str(-Q(a[1]))] for t, a in zip(target, ray)]


def syntactically_proper(ray, target):
    a = ray_key(ray)
    if not any(any(pair) for pair in a):
        return False
    active = [a[i] for i, x in enumerate(target) if x]
    return bool(active) and not (all(pair == active[0] for pair in active)
                                and all(not any(a[i]) for i, x in enumerate(target) if not x))


def generate_frames(active, mode='baseline', mode_rule=None, meter=None):
    meter = meter or OLD.P.F.S.Meter()
    if len(active) > DIM:
        raise ValueError('ten-coordinate grammar gate')
    count = sum(math.comb(len(active), s)*len(SLOPES)**(s-1) for s in range(1, min(3, len(active))+1))
    meter.reserve(32768*(count+1)); meter.charge(5000*(count+1))
    target = [int(i in active) for i in range(DIM)]
    primitives = primitive_rays(active)
    if mode not in ('baseline', 'promoted') or mode == 'promoted' and not mode_rule:
        raise ValueError('declared generation/promotion mode')
    seen, frames = set(), []
    for index, raw in enumerate(primitives):
        ray = raw if mode == 'baseline' else promote(raw, mode_rule['coordinates'])
        if ray is None:
            continue
        other = complement(ray, target)
        if not syntactically_proper(ray, target) or not syntactically_proper(other, target):
            continue
        key = tuple(sorted((ray_key(ray), ray_key(other))))
        if key in seen:
            continue
        seen.add(key)
        if sum(abs(Q(c)) for a in (ray, other) for pair in a for c in pair) > 128:
            continue
        frames.append(dict(index=len(frames), primitive_index=index, mode=mode, rays=[ray, other],
                           target=target, promotion_rule=mode_rule if mode == 'promoted' else None))
    return frames


def ray_forms(row, ray):
    if row['token_intervals'] != {'1': ['1', '1']}:
        raise ValueError('fixed-kernel exact-unit pilot')
    a = ray_key(ray)
    S, gram = (Q(0), Q(0)), (Q(0), Q(0), Q(0))
    for pair, poly in zip(a, row['flux_features']):
        if any(t != '1' for t in poly):
            raise ValueError('fixed coefficients required')
        S = poly_add(S, poly_scale(pair, Q(poly.get('1', '0'))))
    for entry in row['gram_upper']:
        if any(t['left_token'] != '1' or t['right_token'] != '1' for t in entry['terms']):
            raise ValueError('fixed Gram coefficients required')
        weight = sum((Q(t['coefficient']) for t in entry['terms']), Q(0))
        i, j = entry['i'], entry['j']
        gram = poly_add(gram, poly_scale(affine_product(a[i], a[j]), weight*(1 if i == j else 2)))
    return S, gram


def calibrate(rows, ray, q, logspec):
    required, worst = Q(0), None
    for u, row in sorted(rows.items()):
        S, gram = ray_forms(row, ray)
        _, upper = polynomial_range(affine_product(S, S), logspec)
        diagonal, _ = polynomial_range(gram, logspec)
        if diagonal <= 0:
            if upper:
                return None
            continue
        power, _ = OLD.P.positive_power_bounds(u, str(Q(q)-1))
        ratio = upper/(power*diagonal)
        if ratio > required:
            required, worst = ratio, u
    return dict(kappa=str(max(Q(1, 1 << 40), OLD.round_up(required))), worst_u=worst,
                uniform_correlation_proved=False)


def cover_price(rays, kappas, K, logspec):
    weights = [OLD.sqrt_upper(3*Q(K)*Q(k)*coefficient_maximum(a, logspec)**2)
               for a, k in zip(rays, kappas)]
    return sum(weights, Q(0))**2


def mode_obstruction(kernel, primes, gamma, ray, logspec):
    a = ray_key(ray)
    active = {i for i, pair in enumerate(a) if any(pair)}
    if not active or not active <= {1, 9}:
        return dict(status='UNPAID_OTHER_SIGNED_CHANNELS')
    g = Q(gamma)
    if any(a[9]):
        if not Q(1, 2) < g < Q(3, 4) or Q(logspec['argument']) != (3-2*g)/(2*g):
            return dict(status='UNPAID_OUTSIDE_MODE_DOMAIN')
    elif not 0 < g < 1:
        return dict(status='UNPAID_OUTSIDE_MODE_DOMAIN')
    mass = sum((Q(x['weight'])/x['divisor'] for x in kernel), Q(0))
    delta = Q(1)
    for p in primes:
        delta *= Q(p-1, p)
    poly = poly_scale((-a[1][0], -a[1][1]+a[9][0], a[9][1]), mass*delta/2)
    lo, hi = polynomial_range(poly, logspec)
    if lo <= 0 <= hi:
        return dict(status='UNPAID_ZERO_OR_UNRESOLVED_MODE')
    return dict(status='SYMBOLIC_MODE_OBSTRUCTION_PROPOSAL', certificate=dict(mass=str(mass),
        delta=str(delta), leading_lower=str(lo), leading_upper=str(hi)))


def physical_forms(payload):
    result = []
    for cell in payload['cells']:
        band = payload['bands'][cell['band']]
        delta = [Q(0)]*DIM
        for key, sign, category in [('parent_weight', 1, cell['parent_category']), ('child_weight', -1, cell['child_category'])]:
            if any(t != '1' for t in band[key]):
                raise ValueError('fixed coefficient physical cells required')
            if category < DIM:
                delta[category] += sign*Q(band[key].get('1', '0'))
        result.append((delta, sum(delta, Q(0))))
    return result


def noncircular_witness(payload, ray, logspec, forms=None):
    forms = physical_forms(payload) if forms is None else forms
    a = ray_key(ray)
    pivot = next((i for i, (_, total) in enumerate(forms) if total), None)
    if pivot is None:
        return None
    def applied(delta):
        return tuple(sum((pair[j]*d for pair, d in zip(a, delta)), Q(0)) for j in range(2))
    first = applied(forms[pivot][0])
    for index, (delta, total) in enumerate(forms):
        if index == pivot:
            continue
        determinant = poly_add(poly_scale(first, total), poly_scale(applied(delta), -forms[pivot][1]))
        lo, hi = polynomial_range(determinant, logspec)
        if not lo <= 0 <= hi:
            return dict(first_cell=pivot, second_cell=index)
    return None


def float_arrays(rows):
    us = sorted(rows)
    values, grams = [], []
    for u in us:
        row = rows[u]
        values.append([float(Q(p.get('1', '0'))) for p in row['flux_features']])
        matrix = np.zeros((DIM, DIM))
        for entry in row['gram_upper']:
            v = sum(float(Q(t['coefficient'])) for t in entry['terms'])
            matrix[entry['i'], entry['j']] = matrix[entry['j'], entry['i']] = v
        grams.append(matrix)
    return np.asarray(us), np.asarray(values), np.asarray(grams)


def rank_frames(rows, frames, q, K, logspec, arrays=None, meter=None):
    """Vectorized proposals only; no floating result is a finite certificate."""
    meter = meter or OLD.P.F.S.Meter()
    if not 1 <= len(rows) <= 512 or len(frames) > 8192:
        raise ValueError('bounded discovery rows and frame bank required')
    meter.reserve(256*(len(rows)+1)*(2*len(frames)+1)+16384*(len(frames)+1))
    meter.charge(1000*len(rows)*(2*len(frames)+1))
    us, values, grams = float_arrays(rows) if arrays is None else arrays
    L = (float(Q(logspec['lower']))+float(Q(logspec['upper'])))/2
    rays, index = [], {}
    for frame in frames:
        for ray in frame['rays']:
            key = ray_key(ray)
            if key not in index:
                index[key] = len(rays)
                rays.append([float(a)+float(b)*L for a, b in key])
    if not rays:
        return []
    directions = np.asarray(rays)
    sums = values @ directions.T
    diagonal = np.einsum('ai,uij,aj->ua', directions, grams, directions, optimize=True)
    ratios = np.zeros_like(diagonal)
    np.divide(sums*sums, diagonal*(us.astype(float)**(float(Q(q))-1))[:, None], out=ratios, where=diagonal > 1e-18)
    bad = np.any((diagonal <= 1e-18) & (np.abs(sums) > 1e-8), axis=0)
    kappas = np.maximum(ratios.max(axis=0), 2.0**-40)
    weights = np.sqrt(3*float(Q(K))*kappas)*np.max(np.abs(directions), axis=1)
    result = []
    for frame in frames:
        indices = [index[ray_key(a)] for a in frame['rays']]
        if any(bad[j] for j in indices):
            continue
        result.append(dict(frame_index=frame['index'], approximate_price=float(sum(weights[j] for j in indices)**2)))
    return sorted(result, key=lambda x: (x['approximate_price'], x['frame_index']))


def kernel_intervals(folded_kernel, u):
    events = {}
    for entry in folded_kernel:
        endpoint, weight = u//entry['divisor'], Q(entry['weight'])
        if endpoint:
            events[0] = events.get(0, Q(0))+weight
            events[endpoint] = events.get(endpoint, Q(0))-weight
    points = sorted(events)
    active, output = Q(0), []
    for left, right in zip(points, points[1:]):
        active += events[left]
        if active and right > left:
            if output and output[-1]['right'] == left and output[-1]['weight'] == {'1': str(active)}:
                output[-1]['right'] = right
            else:
                output.append(dict(left=left, right=right, weight={'1': str(active)}))
    return output


def floor_power(base, exponent):
    e = Q(exponent)
    if base < 1 or e < 0 or base.bit_length()*e.numerator+e.denominator > 100000:
        raise ValueError('positive power work gate')
    return int(OLD.P.F.S.B.fmpz(base**e.numerator).root(e.denominator))


def validation_draw(gammas, maximum=5242880, base=6300, seed=20261011080, per_band=12, known_parents=()):
    """Fresh irregular cases plus every first-bin prime entry in the horizon.

    The draw is called only after formula freeze; every rejection/duplicate
    and literal prime-entry witness is returned rather than silently dropped.
    """
    if (not gammas or len(gammas) > 32 or any(not 0 < Q(g) <= Q(2, 3) for g in gammas)
            or not 1 <= per_band <= 64 or not 2*base <= maximum <= 5242880):
        raise ValueError('declared validation draw resource/domain gate')
    rng = random.Random(seed)
    draws = []
    for level in range(14, maximum.bit_length()):
        lo, hi = max(2*base, 1 << level), min(maximum, (1 << (level+1))-1)
        if lo <= hi:
            for _ in range(per_band):
                draws.append(dict(u=rng.randint(lo, hi), kind='irregular', level=level))
    max_cut = max(OLD.P.T.rational_cutoff(maximum//4, str(Q(g)/3)) for g in gammas)
    primes = [p for p in range(2, max_cut+1) if all(p % d for d in range(2, math.isqrt(p)+1)) and p not in (2, 3, 5, 7)]
    for gamma in gammas:
        for p in primes:
            H = floor_power(p-1, str(3/Q(gamma)))+1
            for multiplier, endpoint in ((4, 'parent'), (8, 'half')):
                for offset in (-1, 0, 1):
                    draws.append(dict(u=multiplier*H+offset, kind='prime_entry', gamma=gamma,
                        prime=p, horizon_threshold=H, endpoint=endpoint, offset=offset))
    seen, known = set(), set(known_parents)
    for draw in draws:
        u = draw['u']
        draw['status'] = ('OUTSIDE_DOMAIN' if not 2*base <= u <= maximum else
                          'KNOWN_PARENT_EXCLUDED' if u in known else 'DUPLICATE' if u in seen else 'ACCEPTED')
        if draw['status'] == 'ACCEPTED':
            seen.add(u)
    return dict(seed=seed, draws=draws, parents=sorted(seen),
        newly_drawn_after_formula_freeze=True, new_arithmetic_horizon=False,
        boundary_rows_excluded_if_previously_known=True)


def diagnostics(row, rays, logspec):
    L = (float(Q(logspec['lower']))+float(Q(logspec['upper'])))/2
    values, polys = [], []
    for ray in rays:
        S, _ = ray_forms(row, ray)
        values.append(float(S[0])+float(S[1])*L)
        polys.append(list(map(str, S)))
    u = row['u']
    return dict(u=u, signed_leaf_polynomials=polys, approximate_signed_leaves=values,
        approximate_cross_term=2*values[0]*values[1], approximate_total_square=sum(values)**2,
        heuristic_log2_remainders=[x*math.log(u)**2/u for x in values],
        heuristic_log3_remainders=[x*math.log(u)**3/u for x in values],
        numerical_diagnostic_only=True, asymptotic_rate_proved=False)
