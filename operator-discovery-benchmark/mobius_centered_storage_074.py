"""Generate signed storage directions subject to proved, conditional bulk rules.

Frozen073 supplies arithmetic, exact normalization and linear-algebra helpers.
Only the search grammar changes. Unknown mixed modes are retained explicitly.
"""
from fractions import Fraction as Q
import time

import numpy as np
from scipy.optimize import linprog

import mobius_prime_storage_073 as B


PROFILE = [['8', '10', '1'], ['16', '20', '-1']]
BRANCHES = ('centered_high', 'open_mixed')


def admit(spec, q, branch):
    _, theta = B.admit_spec(spec)
    if spec['profile'] != PROFILE or not 1 <= Q(q) < 2 or branch not in BRANCHES:
        raise ValueError('registered source, fixed rational 1<=q<2 and declared branch required')
    return theta


def constraints(spec, q, branch):
    theta = admit(spec, q, branch)
    dim = len(B.labels(spec))
    # Balanced factor sectors equal Z exactly; unit=0 on this source. Every
    # admitted ray therefore has an equivalent representative with slots1..5=0.
    rows = []
    for i in range(1, 6):
        row = [Q(0)] * dim
        row[i] = Q(1)
        rows.append(row)
    if branch == 'centered_high':
        for i, t in enumerate(theta, 6):
            if t < Q(1, 2):
                row = [Q(0)] * dim
                row[i] = Q(1)
                rows.append(row)
        # At theta=1/2 the registered profile has y^2=20k>=all endpoints.
        rows.append([Q(0)] * 6 + [Q(t >= Q(1, 2)) for t in theta])
    return rows


def basis(spec, scaling, q, branch):
    return B.exact_nullspace([[a / s for a, s in zip(row, scaling)]
                             for row in constraints(spec, q, branch)], len(scaling))


def allowed(direction, spec, q, branch):
    theta = admit(spec, q, branch)
    v = tuple(map(Q, direction))
    if len(v) != len(theta) + 6 or not v[2] == v[3] == v[4] == v[5]:
        return False
    unknown = any(a and t < Q(1, 2) for a, t in zip(v[6:], theta))
    if branch == 'centered_high' and unknown:
        return False
    return unknown or sum(v[6:], Q(0)) == 0


def catalog(spec, scaling, q, branch):
    spaces = [basis(spec, scaling, q, branch)]
    if branch == 'open_mixed':
        # Exact centered directions must be available even when unequal feature
        # scaling would make the naive coordinate pairs fail the physical rule.
        spaces.append(basis(spec, scaling, q, 'centered_high'))
    result = []
    for space in spaces:
        for free in B.initial_directions(len(space)):
            u = B.lift_direction(free, space)
            if allowed([a / s for a, s in zip(u, scaling)], spec, q, branch):
                result.append(u)
    return list(dict.fromkeys(result))


def fit(data, train, q, scaling, directions, meter, branch,
        pricing_rounds=3, trace_budget=128, precision=20):
    """Search positive squares; reject proved bulk obstructions before scoring."""
    admit(data['spec'], q, branch)
    rows, den, dim = B.data_map(data), data['denominator'], len(data['labels'])
    train, q = sorted(set(train)), Q(q)
    space = basis(data['spec'], scaling, q, branch)
    projection = np.asarray(space, dtype=float).T
    normalized = {k: np.asarray(v, dtype=float) / den / np.asarray(scaling)
                  for k, v in rows.items()}
    x = np.array([normalized[k] for k in train])
    parent = np.array([normalized[k // 2] for k in train])
    lower = np.array([float(B.power_bounds(k, q, precision)[0]) for k in train])
    p_upper = np.array([float(B.power_bounds(k // 2, q, precision)[1]) for k in train])
    base = np.array([rows[k][0]**2 / den**2 for k in train]) / lower
    base -= np.array([rows[k // 2][0]**2 / den**2 for k in train]) / p_upper
    directions = list(dict.fromkeys(B.direction_key(u) for u in directions))
    for u in directions:
        if not allowed([v / s for v, s in zip(u, scaling)], data['spec'], q, branch):
            raise ValueError('inadmissible initial physical direction')
    if not directions:
        raise ValueError('nonempty search dictionary')
    priced, solver_runs = [], []
    rejected_proposals = 0
    solution = None
    for iteration in range(pricing_rounds + 1):
        U = np.array(directions, dtype=float).T
        columns = (x @ U)**2 / lower[:, None] - (parent @ U)**2 / p_upper[:, None]
        costs = np.sum(U * U, axis=0)
        base_columns = (normalized[1] @ U)**2
        A = np.vstack([np.column_stack([columns, -np.ones(len(train))]), np.r_[costs, 0.]])
        b = np.r_[-base, float(trace_budget)]
        objective = np.r_[base_columns / 64 + costs / 2**20, 1.]
        meter.reserve(8 * (A.size * 5 + columns.size * 4 + x.size * 4))
        meter.charge(A.size * 8 + len(train) * dim * dim)
        start = time.monotonic()
        proposal = linprog(objective, A_ub=A, b_ub=b, bounds=(0, None), method='highs')
        solver_runs.append(dict(iteration=iteration, success=bool(proposal.success),
                                status=int(proposal.status), columns=len(directions),
                                elapsed_seconds=time.monotonic() - start))
        if not proposal.success:
            solution = np.zeros(len(directions))
            break
        solution = proposal.x[:-1]
        if iteration == pricing_rounds:
            break
        y, eta = -proposal.ineqlin.marginals[:-1], -proposal.ineqlin.marginals[-1]
        H = x.T @ ((y / lower)[:, None] * x) - parent.T @ ((y / p_upper)[:, None] * parent)
        H += np.outer(normalized[1], normalized[1]) / 64 + (eta + 2**-20) * np.eye(dim)
        H_free = projection.T @ H @ projection
        eig, vectors = np.linalg.eigh((H_free + H_free.T) / 2)
        new = []
        for j in range(min(3, len(space))):
            if eig[j] >= -1e-9:
                continue
            free = [Q(int(round(float(v) * 1024)), 1024) for v in vectors[:, j]]
            if not any(free):
                continue
            u = B.lift_direction(free, space)
            if not allowed([v / s for v, s in zip(u, scaling)], data['spec'], q, branch):
                rejected_proposals += 1
                continue
            if u not in directions and u not in new:
                new.append(u)
                priced.append(dict(round=iteration, proposed_eigenvalue=float(eig[j]),
                                   direction=[str(v) for v in u]))
        if not new:
            break
        directions += new
    if len(solution) != len(directions):
        raise ArithmeticError('final dictionary was not solved')
    weights = [Q(max(0, int(round(float(v) * 4096))), 4096) for v in solution]
    trace = sum((w * sum(a * a for a in u) for w, u in zip(weights, directions)), Q(0))
    if trace > trace_budget:
        weights = [w * Q(trace_budget, 1) / trace for w in weights]
    rays = [dict(weight=str(w), direction=[str(v / s) for v, s in zip(u, scaling)])
            for u, w in zip(directions, weights) if w]
    if len(rays) > 256:
        raise RuntimeError('positive-ray limit')
    cert = dict(schema='signed-prime-storage-candidate-v1', spec=data['spec'], labels=data['labels'],
                q=str(q), precision=precision, rays=rays, C='0', base_upper='0',
                training_scales=train, training_upper='0', uniform_domination_proved=True,
                uniform_recurrence_proved=False, uniform_head_bound_proved=False, RH_proved=False,
                search_metadata=dict(branch=branch, scaling=scaling, trace_budget=trace_budget,
                                     solver_runs=solver_runs, learned_directions=priced,
                                     rejected_priced_directions=rejected_proposals,
                                     numerical_duals_are_proofs=False, admissible_dimension=len(space),
                                     grammar_is_only_necessary_filter=True,
                                     unknown_cutoff_predicate='theta<1/2',
                                     exact_sector_reduction=True,
                                     objective='C+F(1)/64+normalized_trace/2^20'))
    evaluation = B.evaluate(cert, data, train)
    cert['C'] = cert['training_upper'] = str(max(Q(0), evaluation['worst_upper']))
    cert['base_upper'] = str(B.energy(rows[1], den, B.compiled_rays(cert)))
    if not all(allowed(ray['direction'], data['spec'], q, branch) for ray in rays):
        raise ArithmeticError('output violates declared necessary grammar')
    meter.charge(len(train) * max(1, len(rays)) * dim * 12)
    return cert, directions


def discover(discovery, adaptation, q, branch, meter=None, adaptive_rounds=3):
    meter = meter or B.Meter()
    data = B.join_data(discovery, adaptation)
    train = [row['k'] for row in discovery['rows'] if row['k'] >= 2]
    adapt = sorted(set(row['k'] for row in adaptation['rows']) - {1} - set(train))
    scaling = B.fit_scales(discovery, [row['k'] for row in discovery['rows']])
    directions = catalog(data['spec'], scaling, q, branch)
    initial_count = len(directions)
    history = []
    for iteration in range(adaptive_rounds):
        cert, directions = fit(data, train, q, scaling, directions, meter, branch)
        evaluation = B.evaluate(cert, data, adapt)
        failed = [r for r in evaluation['values'] if Q(r['lower']) > Q(cert['C'])]
        failed.sort(key=lambda r: (-Q(r['lower']), r['k']))
        added = [r['k'] for r in failed if r['k'] not in train][:32]
        history.append(dict(round=iteration, candidate=cert, adaptation_status=evaluation['status'],
                            adaptation_violations=len(failed), added_next_scales=added,
                            worst_adaptation_lower=str(evaluation['worst_lower']),
                            worst_adaptation_upper=str(evaluation['worst_upper'])))
        if not added or iteration + 1 == adaptive_rounds:
            break
        train = sorted(set(train + added))
    baseline = dict(cert, rays=[], C='0', training_upper='0', search_metadata=dict(baseline=True))
    baseline['base_upper'] = str(Q(B.data_map(data)[1][0]**2, data['denominator']**2))
    evaluation = B.evaluate(baseline, data, train)
    baseline['C'] = baseline['training_upper'] = str(max(Q(0), evaluation['worst_upper']))
    return dict(candidate=cert, baseline=baseline, history=history, branch=branch, q=str(q),
                initial_directions=initial_count, final_directions=len(directions),
                producer_operations=meter.ops, prospective_bytes=meter.peak_bytes,
                uniform_recurrence_proved=False, uniform_head_bound_proved=False, RH_proved=False)
