"""Exact auxiliary search on prime-assignment states and transported kernels.

The states describe a squarefree product. They are signed projections, not
positive energies. All source recovery, repeated valuations, and centering
are separate obligations. No arithmetic response table is evaluated here.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb, gcd, lcm

BINS = ((0, 2), (0, 4), (1, 2), (1, 4))  # hu, hv, ku, kv; powers of q^-1/6


def canonical(row):
    values = list(map(Q, row))
    if not any(values):
        raise ValueError('nonzero potential')
    denominator = lcm(*(v.denominator for v in values))
    integers = [int(v * denominator) for v in values]
    common = gcd(*integers)
    if next(v for v in integers if v) < 0:
        common = -common
    return [Q(v, common) for v in integers]


def generators(meter, bins=BINS):
    size = 1 << len(bins)
    matrices = []
    for power in (2, 4):
        matrix = [[Q(0)] * size for _ in range(size)]
        for mask in range(size):
            for index, (_, exponent) in enumerate(bins):
                if exponent == power:
                    matrix[mask][mask | (1 << index)] += 1
                    meter.charge(2)
        matrices.append(matrix)
    meter.live(2 * size * size)
    return matrices


def rref(rows, columns, meter):
    matrix = [list(map(Q, row)) for row in rows]
    if any(len(row) != columns for row in matrix):
        raise ValueError('rectangular exact matrix')
    pivot_columns = []
    for column in range(columns):
        pivot = next((i for i in range(len(pivot_columns), len(matrix))
                      if matrix[i][column]), None)
        meter.charge(1 + len(matrix))
        if pivot is None:
            continue
        index = len(pivot_columns)
        matrix[index], matrix[pivot] = matrix[pivot], matrix[index]
        divisor = matrix[index][column]
        matrix[index] = [x / divisor for x in matrix[index]]
        meter.charge(columns)
        for i, row in enumerate(matrix):
            if i == index or not row[column]:
                continue
            scalar = row[column]
            matrix[i] = [a - scalar * b for a, b in zip(row, matrix[index])]
            meter.charge(2 * columns)
        pivot_columns.append(column)
        if len(pivot_columns) == len(matrix):
            break
    meter.live(len(matrix) * columns)
    return matrix, pivot_columns


def nullspace(rows, columns, meter):
    reduced, pivots = rref(rows, columns, meter)
    out = []
    for free in range(columns):
        if free in pivots:
            continue
        vector = [Q(0)] * columns
        vector[free] = 1
        for i, pivot in enumerate(pivots):
            vector[pivot] = -reduced[i][free]
        out.append(canonical(vector))
        meter.charge(columns)
    return out


def spectral_search(grid, meter, bins=BINS):
    """Generic simultaneous rational-eigenvalue search, without seeded modes."""
    first, second = generators(meter, bins)
    size = len(first)
    rejected = []
    modes = []
    for a, b in product(map(Q, grid), repeat=2):
        equations = []
        for matrix, value in ((first, a), (second, b)):
            equations.extend([[coefficient - (value if i == j else 0)
                               for j, coefficient in enumerate(row)]
                              for i, row in enumerate(matrix)])
        meter.charge(2 * size * size)
        basis = nullspace(equations, size, meter)
        if not basis:
            rejected.append([str(a), str(b)])
        for vector in basis:
            constant = 1 - a - b
            envelope = max(abs(constant), abs(constant + Q(4, 5)*a + Q(16, 25)*b)) if a >= 0 and b >= 0 else None
            modes.append(dict(id=len(modes), potential=list(map(str, vector)),
                              eigen_u=str(a), eigen_v=str(b),
                              bulk_polynomial=list(map(str, (constant, a, b))),
                              bulk_envelope=str(envelope) if envelope is not None else None,
                              stable=envelope is not None and envelope <= 1,
                              algebraic_envelope_only=True,
                              energy_contraction_proved=False,
                              full_target_recovered=False))
    return modes, rejected


def recover(modes, target, meter):
    vectors = [list(map(Q, row['potential'])) for row in modes]
    target = list(map(Q, target))
    equations = [[v[i] for v in vectors] + [target[i]] for i in range(len(target))]
    reduced, pivots = rref(equations, len(vectors) + 1, meter)
    if len(vectors) in pivots:
        return None
    result = [Q(0)] * len(vectors)
    for i, pivot in enumerate(pivots):
        result[pivot] = reduced[i][-1]
    return list(map(str, result))


def compile_kernel(potential, meter, bins=BINS):
    """Complete fresh-prime bulk and both exit terms, per occupancy mask."""
    vector = list(map(Q, potential))
    if len(vector) != 1 << len(bins):
        raise ValueError('complete occupancy state')
    rows = []
    for mask, value in enumerate(vector):
        left = [Q(0)] * 3
        right = [Q(0)] * 3
        for bit, (leg, power) in enumerate(bins):
            shifted = vector[mask | (1 << bit)]
            correction = left if leg == 0 else right
            correction[0] += shifted
            correction[power // 2] -= shifted
            meter.charge(3)
        bulk = [(value if i == 0 else 0) - left[i] - right[i] for i in range(3)]
        rows.append(dict(mask=mask, bulk=list(map(str, bulk)),
                         left_exit=list(map(str, left)), right_exit=list(map(str, right))))
    return rows


def kernel_counts(X, q, h, k, meter):
    if any(type(n) is not int or n < 1 for n in (X, q, h, k)) or q < 2:
        raise ValueError('positive integer prefix geometry')
    W = max(0, 2*X - max(X, h, k))
    L = max(0, 2*X - max(X, q*h, k))
    R = max(0, 2*X - max(X, h, q*k))
    # Closed exits are checked independently by literal prefix enumeration.
    EL = max(0, min(2*X, q*h) - max(X, h, k))
    ER = max(0, min(2*X, q*k) - max(X, h, k))
    meter.charge(28)
    if W - L != EL or W - R != ER:
        raise AssertionError('complete exits')
    return dict(W=W, W_L=L, W_R=R, left_exit=EL, right_exit=ER)


def weighted_polynomial(a, b, gamma):
    a, b, gamma = map(Q, (a, b, gamma))
    if gamma < 0 or (6 * gamma).denominator != 1:
        raise ValueError('nonnegative sixth-root lattice')
    power = int(6 * gamma)
    coefficients = {0: Q(1)}
    for degree, value in ((power, -a-b), (power+2, a), (power+4, b)):
        coefficients[degree] = coefficients.get(degree, Q(0)) + value
    return [[degree, str(value)] for degree, value in sorted(coefficients.items()) if value]


def bernstein_coefficients(poly, left, right, meter):
    """Convert monomials to Bernstein coefficients after affine substitution."""
    coefficients = {int(i): Q(c) for i, c in poly}
    degree = max(coefficients, default=0)
    left, right = Q(left), Q(right)
    width = right - left
    monomials = [Q(0)] * (degree + 1)
    for exponent, value in coefficients.items():
        for i in range(exponent + 1):
            monomials[i] += value * comb(exponent, i) * left**(exponent-i) * width**i
            meter.charge(7)
    values = []
    for j in range(degree + 1):
        values.append(sum(monomials[i] * Q(comb(j, i), comb(degree, i)) for i in range(j + 1)))
        meter.charge(3 * (j + 1))
    return values


def prove_bulk_envelope(poly, meter, max_depth=4):
    """Exact bounded certificate search, never a sampled inequality fit."""
    for depth in range(max_depth + 1):
        count = 1 << depth
        segments = []
        for index in range(count):
            left, right = Q(9*index, 10*count), Q(9*(index+1), 10*count)
            values = bernstein_coefficients(poly, left, right, meter)
            if any(abs(x) > 1 for x in values):
                break
            segments.append(dict(left=str(left), right=str(right), coefficients=list(map(str, values))))
        if len(segments) == count:
            return dict(status='CERTIFIED_ALGEBRAIC_BULK_ENVELOPE', depth=depth, segments=segments)
    return dict(status='NO_CERTIFICATE_IN_FROZEN_PARTITIONS', depth_limit=max_depth, segments=[])


def fractional_search(modes, gammas, meter):
    pairs = sorted({(Q(row['eigen_u']), Q(row['eigen_v'])) for row in modes})
    records = []
    for (a, b), gamma_text in product(pairs, gammas):
        gamma = Q(gamma_text)
        poly = weighted_polynomial(a, b, gamma)
        certificate = prove_bulk_envelope(poly, meter)
        records.append(dict(id=len(records), eigen_u=str(a), eigen_v=str(b),
                            gamma=str(gamma), polynomial=poly, certificate=certificate,
                            product_recovery_power=str(2 * gamma),
                            product_recovery_factor='(2X)^(2*gamma) on h,k<2X',
                            recovery_factor_scope='pointwise inverse weight only; not a bound between signed sums',
                            signed_sum_recovery_from_scalar_factor=False,
                            kernel_phase_multiplier='1-q^(-gamma)*(R*exp(i*xi*log(q))+S*exp(i*eta*log(q)))',
                            phase_free_absolute_envelope='1+q^(-gamma)*(eigen_u+eigen_v)',
                            boundary_terms_retained=True, energy_contraction_proved=False,
                            original_target_recovered=False, whole_signed_bound_proved=False))
    return records


def individual_union_modes(modes, meter):
    """Check whether a discovered row admits scalar two-leg phase transport."""
    records = []
    for row in modes:
        vector = list(map(Q, row['potential']))
        pivot = next(i for i, value in enumerate(vector) if value)
        values = []
        for bit in range(4):
            eigenvalue = vector[pivot | (1 << bit)] / vector[pivot]
            valid = all(vector[mask | (1 << bit)] == eigenvalue * vector[mask] for mask in range(16))
            meter.charge(36)
            if not valid or eigenvalue not in (0, 1):
                values = None
                break
            values.append(str(eigenvalue))
        records.append(dict(mode_id=row['id'], individual_union_eigenvalues=values,
                            scalar_phase_admissible=values is not None))
    return records


def phase_search(fractional, angles, meter):
    records = []
    for source, angle_text in product(fractional, angles):
        delta = Q(angle_text)
        if not 0 < delta <= 1:
            raise ValueError('positive rational phase half-width at most one radian')
        center = delta*delta/2
        width = 1-center
        coefficients = {int(power): Q(c) for power, c in source['polynomial']}
        coefficients[0] = coefficients.get(0, Q(0)) - center
        transformed = [[power, str(value/width)] for power,value in sorted(coefficients.items()) if value]
        certificate = prove_bulk_envelope(transformed, meter)
        records.append(dict(id=len(records), fractional_id=source['id'],
                            gamma=source['gamma'], eigen_u=source['eigen_u'],eigen_v=source['eigen_v'],
                            phase_half_width=str(delta), transformed_polynomial=transformed,
                            certificate=certificate, sufficient_rho_bound=str(2-delta*delta),
                            source_recovery_power=source['product_recovery_power'],
                            frequency_scope='|xi*log(q)|,|eta*log(q)|<=delta for the formal two-leg dilation symbol',
                            arithmetic_operator_norm_proved=False,
                            prime_free_projection_closure=False,
                            energy_contraction_proved=False,whole_signed_bound_proved=False))
    return records
