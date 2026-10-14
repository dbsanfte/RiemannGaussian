"""Discover signed rough-state energies and explicit dyadic drift conjectures.

Positive auxiliary squares prove domination, not their arithmetic drift.
Floating LPs invent programs; an independent exact checker decides finite scope.
"""
from array import array
from fractions import Fraction as Q
from itertools import combinations
from functools import lru_cache

import numpy as np
from scipy.optimize import linprog

import mobius_residual_fold_077 as F
import mobius_rough_transport_077 as T

DIMENSION = 10
MAX_TERMINAL_DEGREE = 6
MAX_RAYS = 2048


class Arithmetic:
    """One compact Euler factor source, reused for NEW rough decompositions."""
    def __init__(self, horizon, meter=None):
        self.meter = meter or F.S.Meter()
        if type(horizon) is not int or not 1 <= horizon <= F.MAX_HORIZON:
            raise ValueError('bounded arithmetic horizon')
        self.horizon = horizon
        self.meter.reserve(96 * (horizon + 1) + 32 * 1024**2)
        least = array('I', [0]) * (horizon + 1)
        mu = array('b', [0]) * (horizon + 1)
        omega = array('B', [0]) * (horizon + 1)
        primes = array('I')
        mu[1] = 1
        for n in range(2, horizon + 1):
            if not least[n]:
                least[n] = n
                primes.append(n)
                mu[n], omega[n] = -1, 1
            for p in primes:
                v = n * p
                if v > horizon:
                    break
                least[v] = p
                if p == least[n]:
                    break
                mu[v], omega[v] = -mu[n], omega[n] + 1
        least[1] = horizon + 1  # the unit has no least prime
        self.least = np.frombuffer(least, dtype=np.uint32)
        self.mu = np.frombuffer(mu, dtype=np.int8)
        self.omega = np.frombuffer(omega, dtype=np.uint8)
        self.meter.charge(40 * (horizon + 1))
        self._query_key = None
        self._queries = None

    def queries(self, horizon, excluded, gamma):
        T.excluded_primes(excluded)
        key = (horizon, tuple(excluded), gamma)
        if self._query_key == key:
            return self._queries
        if not 0 <= horizon <= self.horizon:
            raise ValueError('source horizon exhausted')
        g = F.S.B.rational(gamma)
        if g < 0:
            raise ValueError('nonnegative rational cutoff')
        cuts = [T.rational_cutoff(horizon, str(g * k / 3)) if horizon else 1 for k in (1, 2, 3)]
        if cuts[-1]**7 < horizon:
            raise ValueError('UNRESOLVED terminal degree exceeds six')
        self.meter.reserve(128 * (self.horizon + 1) + 32 * 1024**2)
        pos = np.flatnonzero(self.mu[:horizon + 1]).astype(np.int64)
        for p in excluded:
            pos = pos[pos % p != 0]
        lp = self.least[pos]
        category = np.where(lp > cuts[-1], self.omega[pos], 7 + np.searchsorted(cuts, lp, side='left'))
        category[pos == 1] = 0  # P^-(1)=infinity even for gamma>1
        if np.any(category >= DIMENSION):
            raise ArithmeticError('incomplete rough partition')
        queries = []
        for j in range(DIMENSION):
            values = pos[category == j]
            prefix = np.empty(len(values) + 1, dtype=np.int64)
            prefix[0] = 0
            np.cumsum(self.mu[values], dtype=np.int64, out=prefix[1:])
            queries.append((values, prefix))
        self.meter.charge(40 * (horizon + 1))
        self._query_key, self._queries = key, (cuts, queries)
        return self._queries

    def features(self, intervals, excluded, gamma):
        state = F.decode(intervals, self.meter)
        horizon = max((r for _, r, _ in state), default=0)
        cuts, queries = self.queries(horizon, excluded, gamma)
        left = np.array([l for l, _, _ in state], dtype=np.int64)
        right = np.array([r for _, r, _ in state], dtype=np.int64)
        features = []
        for positions, prefix in queries:
            counts = prefix[np.searchsorted(positions, right, side='right')] - prefix[np.searchsorted(positions, left, side='right')]
            poly = {}
            for count, (_, _, weight) in zip(counts, state):
                if count:
                    for token, a in weight.items():
                        value = F.bounded_add(poly.get(token, Q(0)), F.bounded_mul(Q(int(count)), a, self.meter), self.meter)
                        if value:
                            poly[token] = value
                        else:
                            poly.pop(token, None)
            features.append(F.OLD.saved(poly))
        self.meter.charge(30 * len(state) * DIMENSION)
        return features


def residual_polynomial(program, source_row):
    """Literal old source G-L, with the SAME parent tokens as compilation."""
    result = {'1': Q(source_row['z'])} if source_row['z'] else {}
    for atom, raw in zip(program['atoms'], program['operator']):
        n = source_row['counts'][atom['column']]
        g = Q(atom['gamma'])
        token = '1' if n <= 1 or not g else 'count:' + str(n) + '^(-' + str(g) + ')'
        value = -Q(raw) * source_row['components'][atom['column']]
        result[token] = result.get(token, Q(0)) + value
        if not result[token]:
            del result[token]
    return F.OLD.saved(result)


def sum_features(features):
    result = {}
    for poly in features:
        for token, value in poly.items():
            result[token] = result.get(token, Q(0)) + Q(value)
            if not result[token]:
                del result[token]
    return F.OLD.saved(result)


def rational_grid(lower, upper, denominator):
    if type(denominator) is not int or not 1 <= denominator <= 128:
        raise ValueError('rational grammar denominator budget')
    lo, hi = Q(lower), Q(upper)
    if not 0 <= lo <= hi <= 2:
        raise ValueError('bounded rational search interval')
    return [str(g) for g in sorted({Q(a, b) for b in range(1, denominator + 1)
        for a in range(2*b + 1) if lo <= Q(a, b) <= hi})]


def ray_dictionary():
    """Small algebraic grammar; no arithmetic values choose its directions."""
    bank = set()
    def put(a):
        first = next((x for x in a if x), 0)
        if not first:
            return
        a = tuple(Q(x, first) for x in a)
        if len(set(a)) > 1:  # not zero or the unresolved target renamed
            bank.add(a)
    for i in range(DIMENSION):
        a = [0] * DIMENSION
        a[i] = 1
        put(a)
    for i, j in combinations(range(DIMENSION), 2):
        for sign in (-1, 1):
            a = [0] * DIMENSION
            a[i], a[j] = 1, sign
            put(a)
    # Whole prime/composite and prime-child channels, with cross terms.
    groups = [[0], [1], list(range(2, 7)), list(range(7)), list(range(7, 10)), [7, 8], [8, 9]]
    for group in groups:
        put([int(i in group) for i in range(DIMENSION)])
    for left, right in combinations(groups, 2):
        for sign in (-1, 1):
            put([int(i in left) + sign * int(i in right) for i in range(DIMENSION)])
    return [[str(x) for x in a] for a in sorted(bank)]


def atom_dictionary():
    etas = rational_grid('0', '1', 4)
    result = [dict(a=a, eta=eta) for a in ray_dictionary() for eta in etas]
    if len(result) > MAX_RAYS:
        raise ValueError('ray grammar work budget')
    return result


def float_features(row):
    # Approximate proposal only. Exact finite certification uses full polynomials.
    mid = {t: (float(Q(v[0])) + float(Q(v[1]))) / 2 for t, v in row['token_intervals'].items()}
    return np.array([sum(float(Q(a)) * mid[t] for t, a in p.items()) for p in row['features']])


def search_energy(rows, parents, bases, q, tau, atoms=None, coefficient_budget=64, meter=None):
    """Fixed-tau LP jointly selects auxiliary squares and a drift price.

    Minimize the numerical closure score, charging observed base states too.
    A missing complete base and uniform recurrence remain explicit obligations.
    """
    meter = meter or F.S.Meter()
    atoms = atom_dictionary() if atoms is None else atoms
    if not atoms or len(atoms) > MAX_RAYS or not rows or len(rows) > 20000:
        raise ValueError('finite search work budget')
    if not parents or not bases or len(parents)>20000 or len(bases)>20000 or len(set(parents))!=len(parents) or len(set(bases))!=len(bases):
        raise ValueError('bounded nonempty distinct parent/base rows')
    if type(coefficient_budget) is not int or not 1 <= coefficient_budget <= 1024:
        raise ValueError('bounded coefficient budget')
    # Include concurrent dense arrays, presolve copies, and source residency.
    meter.reserve(256*1024**2 + 128*(len(rows)+len(parents)+len(bases)+4)*(len(atoms)+3))
    meter.charge(100*(len(rows)+len(parents)+len(bases))*(len(atoms)+3))
    qf, tf = float(Q(q)), float(Q(tau))
    if not 1 <= Q(q) < 2 or not 0 <= Q(tau) <= 1:
        raise ValueError('normalized dyadic drift domain')
    us = sorted(rows)
    index = {u: i for i, u in enumerate(us)}
    if any(u not in index or u//2 not in index for u in parents) or any(u not in index for u in bases):
        raise ValueError('every parent, literal half and observed base required')
    values = np.stack([float_features(rows[u]) for u in us])
    scales = np.asarray(us, dtype=float)
    directions = np.array([[float(Q(x)) for x in a['a']] for a in atoms])
    eta = np.array([float(Q(a['eta'])) for a in atoms])
    raw = (values @ directions.T)**2 / scales[:, None]**(qf + 2 * eta[None, :])
    residual = values.sum(axis=1)**2 / scales**qf
    pi, ci, bi = [index[u] for u in parents], [index[u//2] for u in parents], [index[u] for u in bases]
    drift0 = residual[pi] - tf * residual[ci]
    drift = raw[pi] - tf * raw[ci]
    active = np.flatnonzero(raw.max(axis=0) > 1e-18)
    if not len(active):
        active = np.array([], dtype=int)
    # Normalize columns to improve LP conditioning. The exact program carries
    # unscaled rational coefficients and is recalibrated independently.
    scale = np.maximum(np.max(np.abs(drift[:, active]), axis=0), np.max(raw[bi][:, active], axis=0)) if len(active) else np.zeros(0)
    scale = np.maximum(scale, 1e-12)
    costs = np.sum(np.abs(directions[active]), axis=1)**2
    n = len(active)
    # Variables: scaled lambda, nonnegative C, nonnegative observed base B,
    # and nonnegative overall score J.
    A = np.zeros((len(pi) + len(bi) + 3, n + 3))
    b = np.zeros(len(A))
    A[:len(pi), :n] = drift[:, active] / scale
    A[:len(pi), n] = -1
    b[:len(pi)] = -drift0
    off = len(pi)
    A[off:off+len(bi), :n] = raw[bi][:, active] / scale
    A[off:off+len(bi), n+1] = -1
    b[off:off+len(bi)] = -residual[bi]
    A[-3, :n] = costs / scale
    b[-3] = coefficient_budget
    if tf < 1:
        A[-2, n] = 1 / (1 - tf)
        A[-2, n+2] = -1
        A[-1, n+1], A[-1, n+2] = 1, -1
    else:
        A[-2, n:n+3] = [1, 1, -1]
        # A duplicate zero row is benign; this is a numerical drift score,
        # never a bound on normalized energy in the tau=1 mode.
    objective = np.zeros(n+3)
    objective[-1] = 1
    result = linprog(objective, A_ub=A, b_ub=b, bounds=(0, None), method='highs',
                     options={'time_limit': 60})
    base0 = max(residual[bi], default=0.0)
    C0 = max(0.0, max(drift0, default=0.0))
    baseline_score = max(base0, C0/(1-tf)) if tf < 1 else base0+C0
    if not result.success:
        return dict(status='NUMERICAL_PROPOSAL_UNAVAILABLE', message=result.message,
                    q=q, tau=tau, baseline_score=baseline_score, uniform_bound_proved=False)
    selected = []
    for j, k in enumerate(active):
        coefficient = float(result.x[j]) / scale[j]
        if coefficient > 1e-10:
            lam = Q(int(coefficient * (1 << 24)), 1 << 24)
            if lam > 0:
                selected.append(dict(atoms[int(k)], **{'lambda': str(lam)}))
    exact_cost = sum((Q(a['lambda'])*sum(abs(Q(x)) for x in a['a'])**2 for a in selected), Q(0))
    if exact_cost > coefficient_budget:
        for a in selected:
            a['lambda'] = str(Q(a['lambda'])*coefficient_budget/exact_cost)
        exact_cost = Q(coefficient_budget)
    program = dict(schema='rough-energy-program-v1', q=q, tau=tau, rays=selected, innovation_C='0')
    return dict(status='FLOATING_PROPOSAL_ONLY', program=program,
        approximate_score=float(result.fun), approximate_C=float(result.x[n]),
        approximate_observed_base=float(result.x[n+1]), baseline_score=float(baseline_score),
        approximate_score_ratio=float(result.fun/baseline_score) if baseline_score else None,
        total_dictionary_atoms=len(atoms), active_dictionary_atoms=n,
        positive_rays=len(selected), coefficient_budget=coefficient_budget, exact_coefficient_cost=str(exact_cost),
        complete_base_proved=False, uniform_bound_proved=False)


def poly_interval(poly, tokens):
    lo = hi = Q(0)
    for t, raw in poly.items():
        a = Q(raw)
        x, y = (a*Q(v) for v in tokens[t])
        lo, hi = lo + min(x, y), hi + max(x, y)
    return lo, hi


@lru_cache(maxsize=20000)
def positive_power_bounds(u, exponent):
    e = Q(exponent)
    if e < 0 or type(u) is not int or u < 1:
        raise ValueError('bounded positive power domain')
    a, b = e.numerator, e.denominator
    precision = 24
    if u.bit_length()*a + precision*b > 100000:
        raise ValueError('power intermediate bit gate')
    target = (u**a) << (precision*b)
    root = int(F.S.B.fmpz(target).root(b))
    lo = Q(root, 1 << precision)
    return lo, lo if root**b == target else Q(root+1, 1 << precision)


def square_interval(lo, hi):
    return (Q(0) if lo <= 0 <= hi else min(lo*lo, hi*hi), max(lo*lo, hi*hi))


def energy_bounds(program, row):
    """Producer enclosure. Final decisions must agree with independent checker."""
    total = sum_features(row['features'])
    lo, hi = square_interval(*poly_interval(total, row['token_intervals']))
    for atom in program['rays']:
        poly = {}
        for weight, p in zip(atom['a'], row['features']):
            for token, raw in p.items():
                poly[token] = poly.get(token, Q(0)) + Q(weight)*Q(raw)
        x, y = square_interval(*poly_interval(poly, row['token_intervals']))
        scale_lo, scale_hi = positive_power_bounds(row['u'], str(2*Q(atom['eta'])))
        coefficient = Q(atom['lambda'])
        lo += coefficient*x/scale_hi
        hi += coefficient*y/scale_lo
    scale_lo, scale_hi = positive_power_bounds(row['u'], program['q'])
    return lo/scale_hi, hi/scale_lo


def calibrate(program, rows, parents, bases):
    p = dict(program)
    bounds = {u: energy_bounds(p, row) for u, row in rows.items()}
    tau = Q(p['tau'])
    C = max([Q(0)] + [bounds[u][1]-tau*bounds[u//2][0] for u in parents])
    C = Q((C.numerator*(1 << 40)+C.denominator-1)//C.denominator, 1 << 40)
    p['innovation_C'] = str(C)
    base = max(bounds[u][1] for u in bases)
    score = max(base, C/(1-tau)) if tau < 1 else base+C
    return p, dict(discovery_C=str(C), observed_base_upper=str(base), discovery_score=str(score),
        recurrence_mode='contractive' if tau < 1 else 'logarithmic',
        complete_base_proved=False, uniform_drift_proved=False)
