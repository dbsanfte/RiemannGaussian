"""Shared-index signed covariance discovery and conditional scale-flux covers.

The floor-kernel coefficient price is unconditional. Discovered covariance
prices are finite conjectures; a rational cover does not prove their growth.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import isqrt

import numpy as np
from scipy.optimize import linprog

import mobius_rough_energy_078 as P
import mobius_prime_mass_gate_078 as MASS

DIM = 10


def saved(poly):
    return {t: str(a) for t, a in sorted(poly.items()) if a}


def add(target, source, scale=Q(1)):
    for t, raw in source.items():
        value = target.get(t, Q(0)) + scale * Q(raw)
        if value:
            target[t] = value
        else:
            target.pop(t, None)


def coefficient_bands(parent, child, meter):
    states = [P.F.decode(raw, meter) for raw in (parent, child)]
    points = sorted({x for state in states for l, r, _ in state for x in (l, r)})
    index = [0, 0]
    bands = []
    for l, r in zip(points, points[1:]):
        weights = []
        for k, state in enumerate(states):
            while index[k] < len(state) and state[index[k]][1] <= l:
                index[k] += 1
            j = index[k]
            weights.append(state[j][2] if j < len(state) and state[j][0] <= l < state[j][1] else {})
        if any(weights):
            bands.append(dict(left=l, right=r, parent_weight=saved(weights[0]), child_weight=saved(weights[1])))
    return bands


def categories(arithmetic, positions, horizon, gamma):
    g = Q(gamma)
    if g < 0:
        raise ValueError('nonnegative rational cutoff required')
    cuts = [P.T.rational_cutoff(horizon, str(g*k/3)) if horizon else 1 for k in (1, 2, 3)]
    if cuts[-1] < horizon and cuts[-1]**7 < horizon:
        raise ValueError('UNRESOLVED terminal degree exceeds six')
    lp = arithmetic.least[positions]
    category = np.where(lp > cuts[-1], arithmetic.omega[positions],
                        7 + np.searchsorted(cuts, lp, side='left'))
    category[positions == 1] = 0
    category[positions > horizon] = 10
    if np.any(category > 10):
        raise ValueError('incomplete factor partition')
    return category


def cell_deltas(band, cell):
    values = [{} for _ in range(DIM)]
    pc, hc = cell['parent_category'], cell['child_category']
    if pc < DIM:
        add(values[pc], band['parent_weight'])
    if hc < DIM:
        add(values[hc], band['child_weight'], Q(-1))
    return values


def quad_add(poly, left, right, scale):
    for t, x in left.items():
        for s, y in right.items():
            key = tuple(sorted((t, s)))
            value = poly.get(key, Q(0)) + scale*Q(x)*Q(y)
            if value:
                poly[key] = value
            else:
                poly.pop(key, None)


def construct_cells(arithmetic, u, parent, child, primes, gamma):
    """Build every occupied shared-index cell, including outer half support."""
    if type(u) is not int or u < 2:
        raise ValueError('literal parent integer required')
    P.F.admit_primes(primes)
    bands = coefficient_bands(parent, child, arithmetic.meter)
    hp = max((b['right'] for b in parent), default=0)
    hc = max((b['right'] for b in child), default=0)
    H = max(hp, hc)
    if H > arithmetic.horizon or hp > u//4 or hc > (u//2)//4:
        raise ValueError('declared source horizon exceeded')
    prospective = 121*len(bands)
    quadratic_work = sum((len(b['parent_weight'])+len(b['child_weight']))**2 for b in bands)*121
    if quadratic_work > 10**8:
        raise ValueError('prospective token quadratic work gate')
    arithmetic.meter.reserve(192*(arithmetic.horizon+1)+32*1024**2+8192*prospective+4096*quadratic_work)
    arithmetic.meter.charge(60*(H+1)+1000*prospective+quadratic_work)
    pos = np.flatnonzero(arithmetic.mu[:H+1]).astype(np.int64)
    for prime in primes:
        pos = pos[pos % prime != 0]
    pc = categories(arithmetic, pos, hp, gamma)
    cc = categories(arithmetic, pos, hc, gamma)
    cells = []
    if bands and len(pos):
        right = np.array([b['right'] for b in bands], dtype=np.int64)
        left = np.array([b['left'] for b in bands], dtype=np.int64)
        bi = np.searchsorted(right, pos, side='left')
        take = bi < len(bands)
        bi, pos, pc, cc = bi[take], pos[take], pc[take], cc[take]
        take = pos > left[bi]  # the canonical coefficient union may have gaps
        bi, pos, pc, cc = bi[take], pos[take], pc[take], cc[take]
        key = bi*121 + pc*11 + cc
        length = len(bands)*121
        positive = np.bincount(key[arithmetic.mu[pos] > 0], minlength=length)
        negative = np.bincount(key[arithmetic.mu[pos] < 0], minlength=length)
        for raw in np.flatnonzero(positive+negative):
            k = int(raw)
            cells.append(dict(band=k//121, parent_category=(k % 121)//11, child_category=k % 11,
                              count=int(positive[k])+int(negative[k]),
                              signed_count=int(positive[k])-int(negative[k])))
    flux = [{} for _ in range(DIM)]
    gram = {(i, j): {} for i in range(DIM) for j in range(i, DIM)}
    for cell in cells:
        delta = cell_deltas(bands[cell['band']], cell)
        active = [i for i, value in enumerate(delta) if value]
        for i in active:
            add(flux[i], delta[i], Q(cell['signed_count']))
            for j in active:
                if j >= i:
                    quad_add(gram[i, j], delta[i], delta[j], Q(cell['count']))
    return dict(schema='scale-flux-cells-v1', u=u, child_u=u//2, bands=bands, cells=cells,
                flux_features=[saved(x) for x in flux], gram_upper=[dict(i=i, j=j, terms=[
                    dict(left_token=a, right_token=b, coefficient=str(c)) for (a, b), c in sorted(gram[i, j].items())])
                    for i in range(DIM) for j in range(i, DIM)])


def merge_tokens(parent, child):
    """Identical root names remain the same real number across both parents."""
    ranges, definitions = {}, {}
    for compiled in (parent, child):
        for name, definition in compiled['token_definitions'].items():
            if name in definitions and definitions[name] != definition:
                raise ValueError('inconsistent inherited root definition')
            definitions[name] = definition
        for name, pair in compiled['token_intervals'].items():
            lo, hi = map(Q, pair)
            if name in ranges:
                lo, hi = max(lo, ranges[name][0]), min(hi, ranges[name][1])
            if lo > hi:
                raise ValueError('inconsistent inherited root enclosures')
            ranges[name] = (lo, hi)
    if ranges.get('1') != (Q(1), Q(1)):
        raise ValueError('exact unit token required')
    return {name: list(map(str, pair)) for name, pair in sorted(ranges.items())}


def leaf_row(payload, tokens):
    return dict(u=payload['u'], flux_features=payload['flux_features'],
                gram_upper=payload['gram_upper'], token_intervals=tokens)


def fixed_norm(kernel, primes, base):
    folded = {x['divisor']: Q(x['weight']) for x in MASS.canonical_kernel(kernel)}
    for prime in primes:
        old = list(folded.items())
        for d, a in old:
            folded[d*prime] = folded.get(d*prime, Q(0))-a
        folded = {d: a for d, a in folded.items() if a}
    points = sorted({Q(0)} | {Q(1, d) for d in folded})
    I = E = Q(0)
    for l, r in zip(points, points[1:]):
        mid = (l+r)/2
        a = sum((a for d, a in folded.items() if mid <= Q(1, d)), Q(0))
        I += a*a*(r-l)
        E += a*a
    return dict(certificate=dict(I=str(I), E=str(E), K=str(I+E/base)),
                folded_kernel=[dict(divisor=d, weight=str(a)) for d, a in sorted(folded.items())])


def inactive_coordinates(folded_kernel, gamma, base):
    g = Q(gamma)
    inactive = [r for r in range(1, 7) if r*g >= 1]
    if (base >= max(x['divisor'] for x in folded_kernel)
            and not sum((Q(x['weight']) for x in folded_kernel), Q(0))):
        inactive.insert(0, 0)
    return inactive


def ray_dictionary(active):
    bank = []
    for i in active:
        a = ['0']*DIM
        a[i] = '1'
        bank.append(a)
    for i, j in combinations(active, 2):
        for r in ('-2', '-1', '-1/2', '1/2', '1', '2'):
            a = ['0']*DIM
            a[i], a[j] = '1', r
            bank.append(a)
    return bank


def quad_interval(poly, tokens):
    lo = hi = Q(0)
    for (a, b), coefficient in poly.items():
        x, y = map(Q, tokens[a])
        z, w = map(Q, tokens[b])
        left, right = P.square_interval(x, y) if a == b else (min(x*z, x*w, y*z, y*w), max(x*z, x*w, y*z, y*w))
        if coefficient < 0:
            left, right = right, left
        lo, hi = lo+coefficient*left, hi+coefficient*right
    return lo, hi


def ray_forms(row, ray):
    a = list(map(Q, ray))
    linear, quadratic = {}, {}
    for coefficient, value in zip(a, row['flux_features']):
        add(linear, value, coefficient)
    for entry in row['gram_upper']:
        i, j = entry['i'], entry['j']
        scale = a[i]*a[j]*(1 if i == j else 2)
        if scale:
            for term in entry['terms']:
                key = (term['left_token'], term['right_token'])
                value = quadratic.get(key, Q(0))+scale*Q(term['coefficient'])
                if value:
                    quadratic[key] = value
                else:
                    quadratic.pop(key, None)
    return linear, quadratic


def noncircular_witness(payload, tokens, ray):
    a = list(map(Q, ray))
    # Compare against a pivot where the full flux coefficient is nonzero.
    # This is complete in the fixed rational-token pilot; general interval
    # cancellation may leave the gate unresolved, never silently admitted.
    forms = []
    for cell in payload['cells']:
        delta = cell_deltas(payload['bands'][cell['band']], cell)
        proper, total = {}, {}
        for i, value in enumerate(delta):
            add(proper, value, a[i])
            add(total, value)
        forms.append((proper, total))
    pivot = next((i for i, (_, t) in enumerate(forms) if not (P.poly_interval(t, tokens)[0] <= 0 <= P.poly_interval(t, tokens)[1])), None)
    if pivot is None:
        return None
    for j, (proper, total) in enumerate(forms):
        if j == pivot:
            continue
        det = {}
        quad_add(det, forms[pivot][0], total, Q(1))
        quad_add(det, proper, forms[pivot][1], Q(-1))
        lo, hi = quad_interval(det, tokens)
        if not lo <= 0 <= hi:
            return dict(first_cell=pivot, second_cell=j)
    return None


def round_up(value, bits=40):
    scale = 1 << bits
    return Q((value.numerator*scale+value.denominator-1)//value.denominator, scale)


def calibrate_leaf(rows, ray, q):
    threshold, worst = Q(0), None
    for u, row in sorted(rows.items()):
        linear, quadratic = ray_forms(row, ray)
        _, numerator = P.square_interval(*P.poly_interval(linear, row['token_intervals']))
        diagonal, _ = quad_interval(quadratic, row['token_intervals'])
        if diagonal <= 0:
            if numerator:
                return None
            continue
        power, _ = P.positive_power_bounds(u, str(Q(q)-1))
        ratio = numerator/(diagonal*power)
        if ratio > threshold:
            threshold, worst = ratio, u
    return dict(kappa=str(max(Q(1, 1 << 40), round_up(threshold))), worst_u=worst,
                finite_discovery_only=True, uniform_correlation_proved=False)


def sqrt_upper(value, precision=24):
    value = Q(value)
    if value < 0:
        raise ValueError('nonnegative square root')
    scale = 1 << precision
    root = isqrt((value.numerator*scale*scale)//value.denominator)
    if root*root*value.denominator != value.numerator*scale*scale:
        root += 1
    return Q(root, scale)


def exact_solve(columns, target):
    """Exact small rational RREF; free coefficients are set to zero."""
    n = len(columns)
    A = [[Q(columns[j][i]) for j in range(n)]+[Q(target[i])] for i in range(DIM)]
    pivots, row = [], 0
    for col in range(n):
        pivot = next((r for r in range(row, DIM) if A[r][col]), None)
        if pivot is None:
            continue
        A[row], A[pivot] = A[pivot], A[row]
        leading = A[row][col]
        A[row] = [x/leading for x in A[row]]
        for r in range(DIM):
            if r != row and A[r][col]:
                factor = A[r][col]
                A[r] = [x-factor*y for x, y in zip(A[r], A[row])]
        pivots.append(col)
        row += 1
        if row == DIM:
            break
    if any(not any(r[:n]) and r[-1] for r in A):
        return None
    solution = [Q(0)]*n
    for r, col in enumerate(pivots):
        solution[col] = A[r][-1]
    return solution


def cover_price(leaves, coefficients, K):
    return sum((abs(Q(t))*sqrt_upper(Q(leaf['kappa'])*3*Q(K)*max(abs(Q(a)) for a in leaf['a'])**2)
                for leaf, t in zip(leaves, coefficients)), Q(0))**2


def discover_cover(leaves, target, K):
    if not leaves:
        return dict(status='NO_ADMITTED_LOCAL_RAYS', uniform_bound_proved=False)
    if len(leaves) > 512:
        raise ValueError('bounded local cover grammar')
    matrix = np.array([[float(Q(a)) for a in leaf['a']] for leaf in leaves]).T
    weights = np.array([float(sqrt_upper(Q(leaf['kappa'])*3*Q(K)*max(abs(Q(a)) for a in leaf['a'])**2)) for leaf in leaves])
    scale = max(float(weights.max()), 1e-30)
    result = linprog(np.r_[weights, weights]/scale, A_eq=np.c_[matrix, -matrix],
                     b_eq=np.array(list(map(float, target))), bounds=(0, None), method='highs', options={'time_limit': 60})
    if not result.success:
        return dict(status='NUMERICAL_COVER_UNAVAILABLE', message=result.message, uniform_bound_proved=False)
    numerical = result.x[:len(leaves)]-result.x[len(leaves):]
    indices = [j for j, t in enumerate(numerical) if abs(t) > 1e-9]
    coefficients = exact_solve([leaves[j]['a'] for j in indices], target)
    if coefficients is None:
        # Recovery changes only the exact representation; all added axes have
        # their own independently calibrated and witnessed arithmetic leaves.
        indices = sorted(set(indices) | {j for j, leaf in enumerate(leaves) if sum(Q(x) != 0 for x in leaf['a']) == 1})
        coefficients = exact_solve([leaves[j]['a'] for j in indices], target)
    if coefficients is None:
        return dict(status='EXACT_COVER_UNAVAILABLE', uniform_bound_proved=False)
    chosen = [(leaves[j], t) for j, t in zip(indices, coefficients) if t]
    selected, coefficients = [x[0] for x in chosen], [str(x[1]) for x in chosen]
    return dict(status='CONDITIONAL_COVER_PROPOSAL', target=target, leaves=selected, coefficients=coefficients,
                certificate=dict(price=str(cover_price(selected, coefficients, K))),
                proposed_leaf_count=len(leaves), floating_objective=float(result.fun*scale),
                all_uniform_covariance_leaves_unpaid=True, uniform_bound_proved=False)


def floating_leaf_bank(rows, rays, q):
    """Cheap proposals; selected prices must subsequently be calibrated exactly."""
    us = sorted(rows)
    directions = np.array([[float(Q(x)) for x in ray] for ray in rays])
    values, matrices = [], []
    for u in us:
        row = rows[u]
        tokens = {name: (float(Q(v[0]))+float(Q(v[1])))/2 for name, v in row['token_intervals'].items()}
        values.append([sum(float(Q(a))*tokens[t] for t, a in poly.items()) for poly in row['flux_features']])
        matrix = np.zeros((DIM, DIM))
        for entry in row['gram_upper']:
            value = sum(float(Q(t['coefficient']))*tokens[t['left_token']]*tokens[t['right_token']] for t in entry['terms'])
            matrix[entry['i'], entry['j']] = matrix[entry['j'], entry['i']] = value
        matrices.append(matrix)
    sums = np.asarray(values) @ directions.T
    diagonal = np.einsum('ai,uij,aj->ua', directions, np.asarray(matrices), directions, optimize=True)
    scale = np.asarray(us, dtype=float)**(float(Q(q))-1)
    ratios = np.zeros_like(diagonal)
    np.divide(sums*sums, diagonal*scale[:, None], out=ratios, where=diagonal > 1e-20)
    bad = np.any((diagonal <= 1e-20) & (np.abs(sums) > 1e-9), axis=0)
    prices = np.maximum(ratios.max(axis=0), 2.0**-40)
    return [dict(a=ray, kappa=str(Q(float(prices[j]))), dictionary_index=j,
                 floating_proposal_only=True, uniform_correlation_proved=False)
            for j, ray in enumerate(rays) if not bad[j]]
