"""Exact replay of joint signed-cost proposals, including crossed groups.

The input is a COMPLETE vector of already joined signed cutoff blocks and
exact zero-sum correction columns. The optimizer proposes a global vector;
rational replay, not the floating objective, supplies every reported bound.
This does not construct prime populations or certify real logarithms/phase.
"""

from fractions import Fraction
import random

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, eye, hstack


def cost(values):
    return sum((max(-x, 0) for x in values), Fraction())


def replay(baseline, columns, parameters):
    """The exact Lean signed-gain identity, with zero blocks retained."""
    shifted = [t+sum((a*v for a, v in zip(parameters, row)), Fraction())
               for t, row in zip(baseline, columns)]
    change = [x-t for x, t in zip(shifted, baseline)]
    correlation = sum((v for t, v in zip(baseline, change) if t < 0), Fraction())
    crossing = sum((max(x, 0) if t < 0 else max(-x, 0)
                    for t, x in zip(baseline, shifted)), Fraction())
    gain = cost(baseline)-cost(shifted)
    assert gain == correlation-crossing
    return dict(shifted=shifted, cost=cost(shifted), gain=gain,
                signedAdverseCorrelation=correlation, exactCrossingCost=crossing,
                signCrossings=sum((t < 0 and x > 0) or (t >= 0 and x < 0)
                                  for t, x in zip(baseline, shifted)))


def matrix_rank(rows):
    """Exact rational direction rank, not a Hessian or a covariance."""
    rows = [list(map(Fraction, row)) for row in rows]
    pivot = 0
    for j in range(len(rows[0]) if rows else 0):
        i = next((i for i in range(pivot, len(rows)) if rows[i][j]), None)
        if i is None:
            continue
        rows[pivot], rows[i] = rows[i], rows[pivot]
        scale = rows[pivot][j]
        rows[pivot] = [x/scale for x in rows[pivot]]
        for i in range(pivot+1, len(rows)):
            scale = rows[i][j]
            if scale:
                rows[i] = [x-scale*y for x, y in zip(rows[i], rows[pivot])]
        pivot += 1
        if pivot == len(rows):
            break
    return pivot


def rational_proposal(value, lower, upper):
    value = Fraction(float(value)).limit_denominator(10**7)
    return max(lower, min(upper, value))


def one_direction(baseline, values, bound):
    """Exact line optimum, including every kink and both box endpoints."""
    points = {-bound, Fraction(), bound}
    points.update(-t/v for t, v in zip(baseline, values)
                  if v and -bound <= -t/v <= bound)
    step = min(points, key=lambda a: (cost([t+a*v for t, v in zip(baseline, values)]), abs(a)))
    result = replay(baseline, [[v] for v in values], [step])
    return dict(step=step, cost=result['cost'], gain=result['gain'])


def solve(baseline, columns, bound=4):
    baseline = list(map(Fraction, baseline))
    columns = [list(map(Fraction, row)) for row in columns]
    bound = Fraction(bound)
    if not baseline or len(columns) != len(baseline) or bound < 0:
        raise ValueError('complete nonempty blocks and a nonnegative bound required')
    dimension = len(columns[0])
    if not dimension or any(len(row) != dimension for row in columns):
        raise ValueError('a rectangular correction matrix is required')
    totals = [sum((row[j] for row in columns), Fraction()) for j in range(dimension)]
    if any(totals):
        raise ValueError('correction columns must be EXACT whole-population nulls')
    magnitude = max(map(abs, [*baseline, *(x for row in columns for x in row)]))
    magnitude = magnitude or Fraction(1)
    scaled_t = np.array([float(x/magnitude) for x in baseline])
    scaled_v = np.array([[float(x/magnitude) for x in row] for row in columns])
    objective = np.r_[np.zeros(dimension), np.ones(len(baseline))]
    constraints = hstack((-csr_matrix(scaled_v), -eye(len(baseline))), format='csr')
    fit = linprog(objective, A_ub=constraints, b_ub=scaled_t,
                  bounds=[(-float(bound), float(bound))]*dimension+[(0, None)]*len(baseline),
                  method='highs')
    if not fit.success:
        raise RuntimeError(fit.message)
    parameters = [rational_proposal(x, -bound, bound) for x in fit.x[:dimension]]
    candidate = replay(baseline, columns, parameters)
    if candidate['gain'] < 0:
        parameters = [Fraction()]*dimension
        candidate = replay(baseline, columns, parameters)
    coordinate = [one_direction(baseline, [row[j] for row in columns], bound)
                  for j in range(dimension)]
    for j, choice in enumerate(coordinate):
        if choice['cost'] < candidate['cost']:
            parameters = [Fraction()]*dimension
            parameters[j] = choice['step']
            candidate = replay(baseline, columns, parameters)
    # A rounded dual remains valid WITHOUT exact complementary slackness.
    # The explicit box penalty pays its residual directional correlations.
    dual = [rational_proposal(-x, Fraction(), Fraction(1))
            for x in fit.ineqlin.marginals]
    residuals = [sum((h*row[j] for h, row in zip(dual, columns)), Fraction())
                 for j in range(dimension)]
    lower = (-sum((h*t for h, t in zip(dual, baseline)), Fraction())-
             bound*sum(map(abs, residuals), Fraction()))
    lower = max(lower, Fraction(), -sum(baseline))
    assert lower <= candidate['cost']
    assert sum(candidate['shifted']) == sum(baseline)
    adverse = [sum((row[j] for t, row in zip(baseline, columns) if t < 0), Fraction())
               for j in range(dimension)]
    active = [row for x, row in zip(candidate['shifted'], columns) if x == 0]
    return dict(parameters=parameters, baselineCost=cost(baseline), **candidate,
                certifiedBoxLowerBound=lower, rationalDual=dual,
                dualDirectionResiduals=residuals,
                exactPrimalDualGap=candidate['cost']-lower,
                boxOptimumCertified=candidate['cost'] == lower,
                completeSignedTotal=sum(baseline), directionRank=matrix_rank(columns),
                signedAdverseCorrelations=adverse,
                coordinateOptima=coordinate, activeKinkRank=matrix_rank(active),
                jointSavingExceedsEveryCoordinate=candidate['gain'] > max(r['gain'] for r in coordinate),
                zeroBaselineGroups=sum(t == 0 for t in baseline),
                originalGroupsRetained=True, allColumnsExactlyNull=True,
                floatingSolverOnlyProposes=True, finiteInputCertificate=True,
                nativePopulationOrFloorCertified=False)


def self_test():
    rng = random.Random(101)
    identities = 0
    # A cubic null must be restricted to count >=4. The count-three
    # response is genuinely nonzero; fitting it away would alter the sum.
    for count in range(3, 7):
        xs = list(map(Fraction, range(2, count+2)))
        value = sum(((-1)**mask.bit_count()*sum(x for i, x in enumerate(xs)
                      if mask & (1 << i))**3 for mask in range(1 << count)), Fraction())
        assert value == (-6*np.prod(xs) if count == 3 else 0)
    for _ in range(300):
        count, dimension = rng.randrange(2, 10), rng.randrange(1, 6)
        t = [Fraction(rng.randrange(-10, 11), rng.randrange(1, 8)) for _ in range(count)]
        v = [[Fraction(rng.randrange(-8, 9), rng.randrange(1, 8))
              for _ in range(dimension)] for _ in range(count-1)]
        v.append([-sum(row[j] for row in v) for j in range(dimension)])
        a = [Fraction(rng.randrange(-8, 9), 3) for _ in range(dimension)]
        replay(t, v, a)
        identities += 1
    # Nonsmooth coordinate search gets stuck here. The joint direction is
    # necessary; the null columns still preserve the exact signed total.
    t = [0, 0, 1, -1]
    v = [[1, -1], [-1, 1], [-1, -1], [1, 1]]
    joint = solve(t, v, 1)
    assert joint['baselineCost'] == 1 and joint['cost'] == 0
    assert joint['jointSavingExceedsEveryCoordinate']
    assert joint['activeKinkRank'] == 2
    assert all(replay(t, v, [Fraction(k, 8), 0])['cost'] >= 1 for k in range(-8, 9))
    assert all(replay(t, v, [0, Fraction(k, 8)])['cost'] >= 1 for k in range(-8, 9))
    unmatched = solve([-2, 1], [[1], [-1]], 4)
    assert unmatched['cost'] == unmatched['certifiedBoxLowerBound'] == 1
    # Zero blocks cannot disappear from the crossing price.
    crossing = replay([Fraction(0), Fraction(-1)], [[1], [-1]], [Fraction(-1)])
    assert crossing['exactCrossingCost'] == 1 and crossing['gain'] == 0
    rejected = False
    try:
        solve([-2, 1], [[1], [0]], 4)
    except ValueError:
        rejected = True
    assert rejected
    for _ in range(20):
        dimension = rng.randrange(1, 5)
        v = [[rng.randrange(-5, 6) for _ in range(dimension)] for _ in range(7)]
        v.append([-sum(row[j] for row in v) for j in range(dimension)])
        r = solve([rng.randrange(-10, 11) for _ in v], v, 2)
        assert r['gain'] >= 0 and r['exactPrimalDualGap'] >= 0
    return dict(exactCrossingIdentities=identities, exactReplayedLPs=22,
                jointDirectionEscapesCoordinateTrap=True,
                cubicCountThreeNotDiscarded=True,
                signedUnmatchedLowerBoundRetained=True, zeroBlocksCharged=True,
                nonnullDirectionRejected=True, scope='independent unit regressions, not population scans')
