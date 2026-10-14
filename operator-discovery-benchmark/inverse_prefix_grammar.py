"""Exact truncated inverse polynomials and sparse nonnegative scale potentials.

The supplied basis is explicit. Reconstruction weights and recurrence weights
are inferred from responses; no binomial coefficient vector is supplied.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, product
import hashlib
import json

VERSION = 'anonymous-truncated-inverse-polynomial-and-signed-potential-v1'


def digest(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


@lru_cache(maxsize=16)
def divisors(N):
    rows = [[] for _ in range(N + 1)]
    for d in range(1, N + 1):
        for n in range(d, N + 1, d):
            rows[n].append(d)
    return rows


def convolution(a, b, N):
    D = divisors(N)
    return [0] + [sum(a[d] * b[n // d] for d in D[n]
                     if d < len(a) and n // d < len(b)) for n in range(1, N + 1)]


def inverse(h):
    if len(h) < 2 or h[1] != 1:
        raise ValueError('Unit-normalized reference required')
    N = len(h) - 1
    a = [0] * (N + 1)
    a[1] = 1
    D = divisors(N)
    for n in range(2, N + 1):
        a[n] = -sum(a[d] * h[n // d] for d in D[n] if d < n)
    return a


def prefix(a):
    out, total = [0], 0
    for value in a[1:]:
        total += value
        out.append(total)
    return out


def root_floor(n, k):
    if type(n) is not int or n < 0 or type(k) is not int or k < 1:
        raise ValueError('Nonnegative integer index and positive integer arity required')
    if n < 2 or k == 1:
        return n
    if k >= n.bit_length():
        return 1  # 1**k<=n<2**k, without materializing a huge power
    low, high = 0, n + 1
    while high - low > 1:
        mid = (low + high) // 2
        if mid ** k <= n:
            low = mid
        else:
            high = mid
    return low


def unit(N):
    return [0, 1] + [0] * (N - 1)


def components(h, a, u, k, N):
    if type(k) is not int or k < 1 or u < 0 or N < 1:
        raise ValueError('Declared integer arity, cutoff and evaluation range required')
    small = a[:min(u, N) + 1]
    if len(small) < 2:
        small = [0]
    apower, hpower = unit(N), unit(N)
    out, wrong = [], []
    for r in range(1, k + 1):
        apower = convolution(apower, small, N)
        out.append(prefix(convolution(apower, hpower, N)))
        hpower = convolution(hpower, h, N)
        wrong.append(prefix(convolution(apower, hpower, N)))
    return out, wrong


def reference(seed, N):
    # Local deterministic integer generator avoids hidden random state.
    state, values = seed, [0, 1]
    for n in range(2, N + 1):
        state = (1664525 * state + 1013904223) % (2 ** 32)
        values.append((state >> 11) % 5 - 2)
    return values


def feature_table(seed, N, arities, indices):
    h = reference(seed, N)
    a = inverse(h)
    A = prefix(a)
    rows = []
    for k in arities:
        for x in indices:
            for offset in [0, 1]:
                u = min(x, root_floor(x, k) + offset)
                good, wrong = components(h, a, u, k, x)
                columns = [r[x] for r in good] + [r[x] for r in wrong] + [1, sum(h[1:x + 1])]
                rows.append({'arity': k, 'x': x, 'u': u, 'columns': columns,
                             'anonymous_target': A[x], 'reference_id': digest(h)})
    return {'seed': seed, 'cutoff': N, 'reference': h, 'inverse_sha256': digest(a), 'rows': rows,
            'prime_or_factor_oracle_used': False, 'target_coefficients_supplied': False}


def solve_unique(A, b):
    if not A:
        return None
    m = len(A[0])
    T = [[Q(v) for v in row] + [Q(y)] for row, y in zip(A, b)]
    pivots, row = [], 0
    for col in range(m):
        i = next((i for i in range(row, len(T)) if T[i][col]), None)
        if i is None:
            continue
        T[row], T[i] = T[i], T[row]
        p = T[row][col]
        T[row] = [v / p for v in T[row]]
        for j in range(len(T)):
            if j != row and T[j][col]:
                p = T[j][col]
                T[j] = [x - p * y for x, y in zip(T[j], T[row])]
        pivots.append(col)
        row += 1
    if any(not any(r[:m]) and r[m] for r in T) or len(pivots) != m:
        return None
    return [T[j][m] for j in range(m)]


RECURRENCE_FEATURES = ['one', 'k', 'r', 'r_is_one', 'same', 'left', 'right',
                       'previous', 'previous_left', 'k_same', 'r_same']


def recurrence_features(table, k, r):
    def c(j, s):
        return Q(table[str(j)][s - 1]) if str(j) in table and 1 <= s <= j else Q(0)
    same = c(k, r)
    return [1, k, r, int(r == 1), same, c(k, r - 1), c(k, r + 1),
            c(k - 1, r), c(k - 1, r - 1), k * same, r * same]


def infer(rows, arities, support_budget=3):
    learned, failures, retained, attempts = {}, [], {}, {}
    for k in arities:
        data = [r for r in rows if r['arity'] == k]
        fits, tried = [], 0
        width = len(data[0]['columns'])
        # Overcomplete dictionaries contain zero relations. Search exact sparse
        # supports in ascending complexity; retain EVERY fit at the first
        # successful support size. The stopping rule does not name an answer.
        for size in range(1, k + 1):
            for support in combinations(range(width), size):
                tried += 1
                w = solve_unique([[r['columns'][j] for j in support] for r in data],
                                 [r['anonymous_target'] for r in data])
                if w is None or any(not v for v in w):
                    continue
                full = [Q(0)] * width
                for j, value in zip(support, w):
                    full[j] = value
                fits.append({'support': list(support), 'weights': [str(v) for v in full],
                             'expected_coefficients_supplied': False})
            if fits:
                break
        fits.sort(key=lambda f: (len(str(f['weights'])), digest(f)))
        retained[str(k)], attempts[str(k)] = fits, tried
        if not fits:
            failures.append({'arity': k, 'reason': 'inconsistent_or_nonunique_exact_response_fit'})
        else:
            learned[str(k)] = fits[0]['weights']
    table = {k: v[:int(k)] for k, v in learned.items()}
    relations = []
    examples = [(recurrence_features(table, k, r), Q(table[str(k + 1)][r - 1]) if r <= k + 1 else Q(0))
                for k in arities if str(k + 1) in table for r in range(1, k + 3)]
    for size in range(1, support_budget + 1):
        for support in combinations(range(len(RECURRENCE_FEATURES)), size):
            w = solve_unique([[x[j] for j in support] for x, y in examples], [y for x, y in examples])
            if w is None or any(not c for c in w):
                continue
            relations.append({'terms': [[RECURRENCE_FEATURES[j], str(c)] for j, c in zip(support, w)],
                              'support_size': size, 'exact_response_fit': True,
                              'expected_recurrence_supplied': False})
    relations.sort(key=lambda p: (p['support_size'], len(str(p['terms'])), digest(p)))
    return {'learned_vectors': learned, 'coefficient_table': table, 'rejected_arity_fits': failures,
            'retained_minimum_support_arity_fits': retained, 'arity_supports_checked': attempts,
            'retained_recurrence_fits': relations, 'selected_recurrence': relations[0] if relations else None,
            'initial_arity': min(arities), 'initial_weights': table.get(str(min(arities))),
            'global_reconstruction_proved': False}


def continued_weights(model, k):
    table = dict(model['coefficient_table'])
    if str(k) in table:
        return [Q(v) for v in table[str(k)]]
    relation = model['selected_recurrence']
    if relation is None:
        return None
    start = max(map(int, table))
    for j in range(start, k):
        table[str(j + 1)] = [str(sum(Q(c) * dict(zip(RECURRENCE_FEATURES,
                            recurrence_features(table, j, r)))[name]
                            for name, c in relation['terms'])) for r in range(1, j + 2)]
    return [Q(v) for v in table[str(k)]]


def block_energy(A, X):
    parent = sum(A[n] ** 2 for n in range(X, 2 * X))
    child = sum(A[n] ** 2 for n in range(2 * X, 4 * X))
    return {'energy': parent, 'child_energy': child, 'signed_defect': child - 4 * parent}


def actual_profile(scales, arities, model):
    N = 4 * max(scales)
    h = [0] + [1] * N
    a = inverse(h)
    A = prefix(a)
    output = []
    for X in scales:
        for k in arities:
            u = root_floor(4 * X - 1, k)
            good, _ = components(h, a, u, k, 4 * X - 1)
            weights = continued_weights(model, k)
            if weights is None:
                output.append({'X': X, 'arity': k, 'missing': True})
                continue
            recovered = [sum(c * row[n] for c, row in zip(weights, good)) for n in range(4 * X)]
            observations = []
            for r, row in enumerate(good, 1):
                observations.append({'slot': r, **block_energy(row, X),
                    'cross_with_actual': sum(row[n] * A[n] for n in range(X, 2 * X)),
                    'child_cross_with_actual': sum(row[n] * A[n] for n in range(2 * X, 4 * X))})
            output.append({'X': X, 'arity': k, 'cutoff': u, 'cutoff_condition': (u + 1) ** k > 4 * X - 1,
                'missing': False, 'weights': [str(c) for c in weights],
                'actual_prefix_sha256': digest(A[:4 * X]), 'recovered_prefix_sha256': digest([
                    int(v) if v.denominator == 1 else str(v) for v in recovered]),
                'all_coefficients_recovered_exactly': recovered == A[:4 * X],
                **block_energy(A, X), 'component_moments': observations,
                'tuple_term_coefficient_charge': str(sum(abs(c) for c in weights)),
                'no_prime_or_factor_oracle_used': True, 'new_actual_coefficient_holdout_claimed': False,
                'global_signed_upper_bound_proved': False})
    return {'cutoff': N, 'complete_inverse_sha256': digest(a), 'rows': output}


def ceiling(n, p, bit_budget=1000000):
    p = Q(p)
    if type(n) is not int or n < 1 or p < 0:
        raise ValueError('Positive base and nonnegative rational power required')
    if n == 1:
        return 1
    integer, fraction = divmod(p.numerator, p.denominator)
    if integer * n.bit_length() > bit_budget:
        return None
    base = n ** integer
    if fraction == 0:
        return base
    # Exact comparison is cheap for tiny rational powers, including arbitrary
    # denominator sizes; numeric budgets never impose a semantic arity limit.
    if fraction == 1 and p.denominator >= base * (n - 1):
        # Bernoulli: (1+1/base)^denominator >= n, so the full power
        # lies strictly above base and no higher than base+1.
        return base + 1
    if p.numerator * n.bit_length() > bit_budget or p.denominator > 4096:
        import flint
        from rational_fractional_evaluator import rational_power
        from mellin_kernel_grammar import real
        # For denominator > bit_length(n), a reduced noninteger exponent
        # cannot give an integer at n>1. Otherwise exact perfect-power
        # boundaries are handled by the integer path below.
        if p.denominator <= n.bit_length():
            return None
        old_precision = flint.ctx.prec
        try:
            for bits in [256, 512, 1024, 2048, 4096]:
                flint.ctx.prec = bits
                value = rational_power(real(n), p)
                low = value.lower().ceil().unique_fmpz()
                high = value.upper().ceil().unique_fmpz()
                if low is not None and high is not None and low == high:
                    return int(low)
        finally:
            flint.ctx.prec = old_precision
        return None  # numeric resources, no semantic denominator restriction
    low, high = 0, n + 1
    target = n ** fraction
    while high - low > 1:
        mid = (low + high) // 2
        if mid ** p.denominator < target:
            low = mid
        else:
            high = mid
    # Preserve ceil of the FULL power when its integer factor is >1.
    if integer:
        low, high = base, base * high
        full_target = n ** p.numerator
        while high - low > 1:
            mid = (low + high) // 2
            if mid ** p.denominator < full_target:
                low = mid
            else:
                high = mid
    return high


def potential_dictionary(arities=(2, 3), powers=('1', '3/2', '2', '5/2', '3')):
    return [{'arity': k, 'slot': r, 'normalizing_power': p}
            for k in arities for r in range(1, k + 1) for p in powers]


def potential_value(feature, rows, X):
    row = next(r for r in rows if r['X'] == X and r['arity'] == feature['arity'])
    energy = row['component_moments'][feature['slot'] - 1]['energy']
    return Q(energy, ceiling(X, feature['normalizing_power']))


def potential_candidates(features, coefficient_grid, support_budget):
    result = [{'terms': []}]
    for size in range(1, support_budget + 1):
        for slots in combinations(range(len(features)), size):
            for weights in product(coefficient_grid, repeat=size):
                result.append({'terms': [{'feature': features[j], 'weight': str(Q(w))}
                                          for j, w in zip(slots, weights)]})
    return result


def potential(p, rows, X):
    return sum((Q(t['weight']) * potential_value(t['feature'], rows, X)
                for t in p['terms']), Q(0))


def innovation(p, rows, X):
    row = next(r for r in rows if r['X'] == X)
    return Q(row['child_energy'], 4 * X * X) - Q(row['energy'], X * X) + potential(p, rows, 2 * X) - potential(p, rows, X)


def fit_potential(p, rows, scales, levels):
    out = dict(p)
    out['fitted_constants'] = {str(q): str(Q(5, 4) * max([Q(0)] +
         [innovation(p, rows, X) / ceiling(X, Q(1, q)) for X in scales]) + Q(1, 2 ** 64)) for q in levels}
    return out


def score_potential(p, rows, scales, levels):
    observed = []
    for X in scales:
        value = innovation(p, rows, X)
        for q in levels:
            bound = Q(p['fitted_constants'][str(q)]) * ceiling(X, Q(1, q))
            observed.append({'X': X, 'level': q, 'signed_innovation': str(value),
                'bound': str(bound), 'margin': str(bound - value), 'finite_pass': value <= bound,
                'global_signed_upper_bound_proved': False})
    return {'observations': observed, 'finite_passes': sum(r['finite_pass'] for r in observed),
            'finite_cases': len(observed), 'largest_constant': str(max(map(Q, p['fitted_constants'].values()))),
            'global_signed_upper_bound_proved': False}
