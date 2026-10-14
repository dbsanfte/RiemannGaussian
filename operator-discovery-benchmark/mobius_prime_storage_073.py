"""Signed prime/composite state construction and conjectural storage discovery.

Only domination is a universal certificate. No numerical drift is a theorem.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd, lcm
import time

import numpy as np
from flint import fmpz
from scipy.optimize import linprog


SOURCE_SPEC = dict(profile=[['8', '10', '1'], ['16', '20', '-1']],
                   theta=['2/7', '3/7', '1/2', '4/7', '2/3', '5/7', '4/5', '7/8'])


class Meter:
    def __init__(self, limit=300_000_000_000):
        self.limit = limit
        self.ops = 0
        self.peak_bytes = 0

    def charge(self, n):
        self.ops += int(n)
        if self.ops > self.limit:
            raise RuntimeError('073 work limit')

    def reserve(self, n):
        self.peak_bytes = max(self.peak_bytes, int(n))
        if n > 4 * 1024**3:
            raise MemoryError('073 per-task prospective allocation limit')


def rational(s):
    if not isinstance(s, str):
        raise ValueError('canonical rational string required')
    a = Q(s)
    if str(a) != s or max(a.numerator.bit_length(), a.denominator.bit_length()) > 4096:
        raise ValueError('canonical bounded rational required')
    return a


def admit_spec(spec):
    if set(spec) != {'profile', 'theta'} or not 1 <= len(spec['profile']) <= 16:
        raise ValueError('source specification')
    bands = [tuple(map(rational, row)) for row in spec['profile']]
    last = Q(0)
    for lo, hi, value in bands:
        if not last <= lo < hi <= 100 or not value:
            raise ValueError('disjoint increasing nonzero source bands')
        last = hi
    theta = list(map(rational, spec['theta']))
    if len(theta) > 32 or theta != sorted(set(theta)) or any(not 0 < t < 1 for t in theta):
        raise ValueError('increasing rational smooth cutoffs')
    return bands, theta


def labels(spec):
    return ['Z', 'unit', 'omega1', 'omega2', 'omega3', 'omega_ge4'] + [
        'smooth:' + t for t in spec['theta']]


def floor_power(n, q):
    if type(n) is not int or n < 1 or q < 0:
        raise ValueError('positive power base and nonnegative exponent')
    a, b = q.numerator, q.denominator
    if max(1, n.bit_length()) * a > 100000 or b > 100000:
        raise ValueError('power intermediate bit/work limit')
    return int(fmpz(n**a).root(b))


@lru_cache(maxsize=200000)
def power_bounds(n, q, precision=20):
    if type(n) is not int or n < 1 or not 1 <= q <= 2 or not 8 <= precision <= 24:
        raise ValueError('normalization domain')
    a, b = q.numerator, q.denominator
    bits = n.bit_length() * a + precision * b
    if bits > 100000:
        raise ValueError('power intermediate bit limit')
    if b == 1:
        return Q(n**a), Q(n**a)
    value = (n**a) << (precision * b)
    r = int(fmpz(value).root(b))
    if not r**b <= value < (r + 1)**b:
        raise ArithmeticError('integer root admission')
    lo = Q(r, 1 << precision)
    return lo, lo if r**b == value else Q(r + 1, 1 << precision)


def arithmetic(n, meter):
    """Linear sieve; independent checker uses an Eratosthenes construction."""
    meter.reserve(64 * (n + 1))
    least = [0] * (n + 1)
    largest = [0] * (n + 1)
    omega = [0] * (n + 1)
    mu = [0] * (n + 1)
    primes = []
    mu[1] = largest[1] = 1
    for i in range(2, n + 1):
        if not least[i]:
            least[i] = largest[i] = i
            omega[i] = 1
            mu[i] = -1
            primes.append(i)
        for p in primes:
            v = p * i
            if v > n:
                break
            least[v] = p
            largest[v] = largest[i]
            if p == least[i]:
                omega[v] = omega[i]
                break
            mu[v] = -mu[i]
            omega[v] = omega[i] + 1
            meter.charge(8)
        meter.charge(10)
    return mu, omega, largest


def make_data(spec, scales, meter=None):
    meter = meter or Meter()
    bands, theta = admit_spec(spec)
    ks = sorted(set(scales))
    if not ks or any(type(k) is not int or k < 1 for k in ks):
        raise ValueError('positive integer source scales')
    end = bands[-1][1]
    n = (end.numerator * ks[-1]) // end.denominator
    if n < 1 or n > 4_000_000:
        raise ValueError('source horizon limit')
    denominator = lcm(*(v.denominator for _, _, v in bands))
    coeffs = [int(v * denominator) for _, _, v in bands]
    mu, omega, largest = arithmetic(n, meter)
    sector_prefix = [[0] * (n + 1) for _ in range(6)]
    for t in range(1, n + 1):
        for col in range(6):
            sector_prefix[col][t] = sector_prefix[col][t - 1]
        sector_prefix[0][t] += mu[t]
        sector_prefix[1 if t == 1 else min(omega[t], 4) + 1][t] += mu[t]
    rows = []
    queries = []
    for i, k in enumerate(ks):
        X = (end.numerator * k) // end.denominator
        if X < 1:
            raise ValueError('source horizon at least one at every scale')
        cuts = [floor_power(X, t) for t in theta]
        state = [0] * (6 + len(theta))
        for (lo, hi, _), c in zip(bands, coeffs):
            left, right = (lo.numerator * k) // lo.denominator, (hi.numerator * k) // hi.denominator
            for j in range(6):
                state[j] += c * (sector_prefix[j][right] - sector_prefix[j][left])
            for j, cut in enumerate(cuts):
                queries.append((cut, right, i, 6 + j, c))
                if left:
                    queries.append((cut, left, i, 6 + j, -c))
        if sum(state[1:6]) != state[0]:
            raise ArithmeticError('complete prime/composite sectors')
        rows.append(dict(k=k, X=X, cuts=cuts, state=state))
    meter.reserve(160 * (n + 1) + 160 * len(queries) + 256 * len(rows))
    # Offline 2D queries: insert signed coefficients in largest-prime order.
    order = sorted((largest[t], t) for t in range(1, n + 1) if mu[t])
    queries.sort()
    bit = [0] * (n + 1)
    pos = 0
    for cut, endpoint, row, column, coefficient in queries:
        while pos < len(order) and order[pos][0] <= cut:
            index = order[pos][1]
            value = mu[index]
            pos += 1
            while index <= n:
                bit[index] += value
                index += index & -index
                meter.charge(3)
        value = 0
        while endpoint:
            value += bit[endpoint]
            endpoint -= endpoint & -endpoint
            meter.charge(3)
        rows[row]['state'][column] += coefficient * value
    meter.charge(12 * n + len(queries) * 8)
    return dict(schema='signed-prime-storage-data-v1', spec=spec, labels=labels(spec),
                denominator=denominator, rows=rows, operations=meter.ops)


def data_map(data):
    return {r['k']: r['state'] for r in data['rows']}


def join_data(*datasets):
    first = datasets[0]
    rows = {}
    for data in datasets:
        if any(data[key] != first[key] for key in ('spec', 'labels', 'denominator')):
            raise ValueError('same complete signed source')
        for row in data['rows']:
            k = row['k']
            if k in rows and row != rows[k]:
                raise ValueError('inconsistent shared source scale')
            rows[k] = row
    return dict(schema=first['schema'], spec=first['spec'], labels=first['labels'],
                denominator=first['denominator'], rows=[rows[k] for k in sorted(rows)],
                operations=sum(data['operations'] for data in datasets))


def direction_key(u):
    values = tuple(Q(v) for v in u)
    first = next((x for x in values if x), None)
    if first is None:
        raise ValueError('nonzero square direction')
    if first < 0:
        values = tuple(-x for x in values)
    return values


def initial_directions(d):
    result = []
    for i in range(d):
        u = [Q(0)] * d
        u[i] = Q(1)
        result.append(tuple(u))
        for j in range(i + 1, d):
            for sign in (-1, 1):
                v = list(u)
                v[j] = Q(sign)
                result.append(tuple(v))
    return result


def exact_nullspace(rows, columns):
    """Generic rational elimination; no expected basis vectors are supplied."""
    matrix = [list(map(Q, row)) for row in rows if any(row)]
    if any(len(row) != columns for row in matrix):
        raise ValueError('complete linear-mode rows')
    pivots = []
    rank = 0
    for column in range(columns):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][column]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        divisor = matrix[rank][column]
        matrix[rank] = [x / divisor for x in matrix[rank]]
        for i in range(len(matrix)):
            if i != rank and matrix[i][column]:
                multiple = matrix[i][column]
                matrix[i] = [a - multiple*b for a,b in zip(matrix[i], matrix[rank])]
        pivots.append(column)
        rank += 1
    basis = []
    for free in range(columns):
        if free in pivots:
            continue
        vector = [Q(0)] * columns
        vector[free] = Q(1)
        for i, pivot in enumerate(pivots):
            vector[pivot] = -matrix[i][free]
        basis.append(tuple(vector))
    return basis


def bulk_modes(spec, q):
    """Supplied independent asymptotic modes, not searched candidate answers."""
    bands, _ = admit_spec(spec)
    mass = sum((value*(hi-lo) for lo,hi,value in bands), Q(0))
    if not mass or Q(q) >= 2:
        return [], mass
    modes = []
    for r in (1,2,3):
        mode = [Q(0)] * len(labels(spec))
        mode[r+1] = mass
        mode[5] = -mass
        modes.append(mode)
    return modes, mass


def admissible_basis(spec, scaling, q):
    modes, _ = bulk_modes(spec,q)
    return exact_nullspace([[a/s for a,s in zip(row,scaling)] for row in modes], len(scaling))


def lift_direction(free, basis):
    return direction_key([sum((a*row[j] for a,row in zip(free,basis)),Q(0))
                          for j in range(len(basis[0]))])


def verify_bulk_centering(cert):
    modes, _ = bulk_modes(cert['spec'], Q(cert['q']))
    return all(sum((a*b for a,b in zip(row,map(Q,ray['direction']))),Q(0)) == 0
               for ray in cert['rays'] for row in modes)


def fit_scales(data, scales):
    rows = data_map(data)
    den = data['denominator']
    d = len(data['labels'])
    result = []
    for j in range(d):
        size = 1
        for k in scales:
            value = rows[k][j]
            while value * value > size * size * k * den * den:
                size *= 2
        result.append(size)
    return result


def compiled_rays(cert):
    result = []
    for ray in cert['rays']:
        v = list(map(Q, ray['direction']))
        den = lcm(*(a.denominator for a in v))
        result.append((Q(ray['weight']), [int(a * den) for a in v], den))
    return result


def energy(state, denominator, rays):
    value = Q(state[0]**2, denominator**2)
    for weight, v, den in rays:
        dot = sum(a * b for a, b in zip(v, state))
        value += weight * Q(dot * dot, (den * denominator)**2)
    return value


def evaluate(cert, data, scales):
    rows = data_map(data)
    rays = compiled_rays(cert)
    q = Q(cert['q'])
    energies = {}
    values = []
    for k in scales:
        p = k // 2
        if k < 2 or p not in rows or k not in rows or 1 not in rows:
            raise ValueError('complete child, parent and base source')
        for t in (k, p):
            if t not in energies:
                energies[t] = energy(rows[t], data['denominator'], rays)
        lo, hi = power_bounds(k, q, cert['precision'])
        pl, pu = power_bounds(p, q, cert['precision'])
        lower = energies[k] / hi - energies[p] / pl
        upper = energies[k] / lo - energies[p] / pu
        values.append(dict(k=k, lower=str(lower), upper=str(upper)))
    C = Q(cert['C'])
    failures = [r for r in values if Q(r['lower']) > C]
    ambiguous = [r for r in values if Q(r['lower']) <= C < Q(r['upper'])]
    return dict(status='REFUTED' if failures else 'UNRESOLVED_ROUNDING' if ambiguous else 'VERIFIED_ON_FINITE_DOMAIN',
                values=values, violating_scales=[r['k'] for r in failures],
                inconclusive_scales=[r['k'] for r in ambiguous],
                worst_lower=max((Q(r['lower']) for r in values), default=Q(0)),
                worst_upper=max((Q(r['upper']) for r in values), default=Q(0)))


def fit(data, train, q, scaling, directions, meter, pricing_rounds=3,
        trace_budget=128, precision=20):
    """LP columns are nonnegative squares. Duals only guide new directions."""
    rows = data_map(data)
    den = data['denominator']
    dim = len(data['labels'])
    train = sorted(set(train))
    q = Q(q)
    if not 1 <= q <= 2:
        raise ValueError('normalization exponent')
    basis = admissible_basis(data['spec'], scaling, q)
    projection = np.array(basis, dtype=float).T
    normalized = {k: np.asarray(v, dtype=float) / den / np.asarray(scaling) for k, v in rows.items()}
    x = np.array([normalized[k] for k in train])
    parent = np.array([normalized[k // 2] for k in train])
    lower = np.array([float(power_bounds(k, q, precision)[0]) for k in train])
    p_upper = np.array([float(power_bounds(k // 2, q, precision)[1]) for k in train])
    base = np.array([rows[k][0]**2 / den**2 for k in train]) / lower
    base -= np.array([rows[k // 2][0]**2 / den**2 for k in train]) / p_upper
    catalog = list(dict.fromkeys(direction_key(u) for u in directions))
    priced = []
    solver_runs = []
    solution = None
    for iteration in range(pricing_rounds + 1):
        U = np.array(catalog, dtype=float).T
        columns = (x @ U)**2 / lower[:, None] - (parent @ U)**2 / p_upper[:, None]
        costs = np.sum(U * U, axis=0)
        base_columns = (normalized[1] @ U)**2
        A = np.vstack([np.column_stack([columns, -np.ones(len(train))]), np.r_[costs, 0.]])
        b = np.r_[-base, float(trace_budget)]
        objective = np.r_[base_columns / 64 + costs / 2**20, 1.]
        meter.reserve(8 * (A.size * 5 + columns.size * 4 + x.size * 4))
        meter.charge(A.size * 8 + len(train) * dim * dim)
        start = time.monotonic()
        proposed = linprog(objective, A_ub=A, b_ub=b, bounds=(0, None), method='highs')
        solver_runs.append(dict(iteration=iteration, success=bool(proposed.success),
                                status=int(proposed.status), columns=len(catalog),
                                elapsed_seconds=time.monotonic() - start))
        if not proposed.success:
            solution = np.zeros(len(catalog))
            break
        solution = proposed.x[:-1]
        if iteration == pricing_rounds:
            break
        y = -proposed.ineqlin.marginals[:-1]
        eta = -proposed.ineqlin.marginals[-1]
        H = x.T @ ((y / lower)[:, None] * x) - parent.T @ ((y / p_upper)[:, None] * parent)
        H += np.outer(normalized[1], normalized[1]) / 64 + (eta + 2**-20) * np.eye(dim)
        H_free = projection.T @ H @ projection
        eig, vectors = np.linalg.eigh((H_free + H_free.T) / 2)
        new = []
        for j in range(min(3, len(basis))):
            if eig[j] >= -1e-9:
                continue
            u = lift_direction([Q(int(round(float(v) * 1024)), 1024) for v in vectors[:, j]], basis)
            if u not in catalog and u not in new:
                new.append(u)
                priced.append(dict(round=iteration, proposed_eigenvalue=float(eig[j]),
                                   direction=[str(v) for v in u]))
        if not new:
            break
        catalog += new
    # The final LP must correspond to the final catalog; no unscored directions.
    if len(solution) != len(catalog):
        raise ArithmeticError('candidate dictionary not solved')
    weights = [Q(max(0, int(round(float(v) * 4096))), 4096) for v in solution]
    trace = sum((w * sum(a * a for a in u) for w, u in zip(weights, catalog)), Q(0))
    if trace > trace_budget:
        weights = [w * Q(trace_budget, 1) / trace for w in weights]
    rays = [dict(weight=str(w), direction=[str(v / s) for v, s in zip(u, scaling)])
            for u, w in zip(catalog, weights) if w]
    if len(rays) > 256:
        raise RuntimeError('storage positive-ray limit')
    cert = dict(schema='signed-prime-storage-candidate-v1', spec=data['spec'], labels=data['labels'],
                q=str(q), precision=precision, rays=rays, C='0', base_upper='0',
                training_scales=train, training_upper='0', uniform_domination_proved=True,
                uniform_recurrence_proved=False, uniform_head_bound_proved=False, RH_proved=False,
                search_metadata=dict(scaling=scaling, trace_budget=trace_budget, solver_runs=solver_runs,
                                     learned_directions=priced, numerical_duals_are_proofs=False,
                                     objective='C+F(1)/64+normalized_trace/2^20'))
    evaluated = evaluate(cert, data, train)
    C = max(Q(0), evaluated['worst_upper'])
    cert['C'] = cert['training_upper'] = str(C)
    cert['base_upper'] = str(energy(rows[1], den, compiled_rays(cert)))
    modes, mass = bulk_modes(data['spec'], q)
    cert['search_metadata'].update(asymptotic_mode_rows=[[str(x) for x in row] for row in modes],
                                   source_density_mass=str(mass), admissible_dimension=len(basis),
                                   asymptotic_gate_applied=bool(modes))
    if not verify_bulk_centering(cert):
        raise ArithmeticError('all active directions must annihilate supplied bulk modes')
    meter.charge(len(train) * max(1, len(rays)) * dim * 12)
    return cert, catalog


def discover(discovery_data, adaptation_data, q='1', meter=None, adaptive_rounds=3):
    meter = meter or Meter()
    data = join_data(discovery_data, adaptation_data)
    train = [r['k'] for r in discovery_data['rows'] if r['k'] >= 2]
    adaptation = sorted(set(r['k'] for r in adaptation_data['rows']) - {1} - set(train))
    scaling = fit_scales(discovery_data, [r['k'] for r in discovery_data['rows']])
    basis = admissible_basis(data['spec'], scaling, Q(q))
    catalog = [lift_direction(u,basis) for u in initial_directions(len(basis))]
    history = []
    for iteration in range(adaptive_rounds):
        cert, catalog = fit(data, train, q, scaling, catalog, meter)
        verdict = evaluate(cert, data, adaptation)
        failed = [r for r in verdict['values'] if Q(r['lower']) > Q(cert['C'])]
        failed.sort(key=lambda r: (-Q(r['lower']), r['k']))
        added = [r['k'] for r in failed if r['k'] not in train][:32]
        history.append(dict(round=iteration, candidate=cert, adaptation_status=verdict['status'],
                            adaptation_violations=len(failed), added_next_scales=added,
                            worst_adaptation_lower=str(verdict['worst_lower']),
                            worst_adaptation_upper=str(verdict['worst_upper'])))
        if not added or iteration + 1 == adaptive_rounds:
            break
        train = sorted(set(train + added))
    # A retained zero-auxiliary baseline uses exactly the same final training domain.
    baseline = dict(cert, rays=[], C='0', training_upper='0', search_metadata=dict(baseline=True))
    baseline['base_upper'] = str(Q(data_map(data)[1][0]**2, data['denominator']**2))
    ev = evaluate(baseline, data, train)
    baseline['C'] = baseline['training_upper'] = str(max(Q(0), ev['worst_upper']))
    return dict(candidate=cert, baseline=baseline, history=history,
                catalog_directions=len(catalog), operations=meter.ops,
                prospective_bytes=meter.peak_bytes, uniform_recurrence_proved=False, RH_proved=False)
