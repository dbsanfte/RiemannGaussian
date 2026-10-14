"""Exact minimax synthesis for scale-splitting proof obligations.

An error term contributes R**(intercept + slope*t), R >= 1.  Neither
the optimizing split nor its exponent is supplied to this solver.  The
analytic meaning of the error terms belongs to a separately checked rule.
"""
from fractions import Fraction as Q


def rational(value):
    if type(value) is not str or not 0 < len(value) <= 128:
        raise ValueError('bounded canonical rational string')
    result = Q(value)
    if str(result) != value:
        raise ValueError('canonical rational string')
    return result


def solve(problem, meter):
    if set(problem) != {'lower', 'upper', 'terms'}:
        raise ValueError('complete affine envelope problem')
    lo, hi = rational(problem['lower']), rational(problem['upper'])
    if lo >= hi or not 1 <= len(problem['terms']) <= 64:
        raise ValueError('nonempty bounded split grammar')
    lines = []
    for term in problem['terms']:
        if set(term) != {'intercept', 'slope'}:
            raise ValueError('affine power schema')
        lines.append((rational(term['intercept']), rational(term['slope'])))
    points = {lo, hi}
    for i, (a, b) in enumerate(lines):
        for c, d in lines[:i]:
            meter.charge(20)
            if b != d:
                x = (c-a)/(b-d)
                if lo <= x <= hi:
                    points.add(x)
    vertices = []
    for x in sorted(points):
        y = max(a+b*x for a, b in lines)
        vertices.append(dict(parameter=str(x), power=str(y)))
        meter.charge(10*len(lines))
    best = min(vertices, key=lambda v: (Q(v['power']), Q(v['parameter'])))
    x, y = Q(best['parameter']), Q(best['power'])
    active = [i for i, (a, b) in enumerate(lines) if a+b*x == y]
    weights = [Q(0)]*len(lines)
    flat = [i for i in active if lines[i][1] == 0]
    rising = [i for i in active if lines[i][1] > 0]
    falling = [i for i in active if lines[i][1] < 0]
    if flat:
        weights[flat[0]] = Q(1)
    elif x == lo and rising:
        weights[rising[0]] = Q(1)
    elif x == hi and falling:
        weights[falling[0]] = Q(1)
    elif rising and falling:
        i, j = falling[0], rising[0]
        b, d = lines[i][1], lines[j][1]
        weights[i], weights[j] = d/(d-b), -b/(d-b)
    else:
        raise ArithmeticError('missing convex lower-bound witness')
    slope = sum(w*b for w, (_, b) in zip(weights, lines))
    meter.charge(20*len(lines))
    return dict(problem=problem, vertices=vertices, parameter=str(x), power=str(y),
                active=active, dual_weights=list(map(str, weights)), dual_slope=str(slope),
                tie_rule='smallest parameter among minimizers',
                domain='scale ratio R>=1; analytic error inequality checked separately')


def power_kernel_problem(theta):
    theta = rational(theta)
    if not 0 < theta < 1:
        raise ValueError('power kernel requires 0<theta<1')
    return dict(lower='0', upper='1', terms=[
        dict(intercept='0', slope='1'),
        dict(intercept=str(theta), slope=str(-theta))])
