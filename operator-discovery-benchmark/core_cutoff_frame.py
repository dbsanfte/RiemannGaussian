"""Discover signed drift eliminators by generic polynomial coefficient solving.

The language (degree-one syzygies and square pooling) is supplied. The
nullspace, pooled formulas, recovery costs, and open proof obligations are
generated. No source moments or anticipated pairwise formula enter discovery.
"""
from fractions import Fraction as Q
from math import gcd, lcm
from flint import arb, ctx


def add(a, b):
    out = dict(a)
    for key, value in b.items():
        out[key] = out.get(key, Q(0)) + value
        if not out[key]:
            del out[key]
    return out


def mul(a, b, meter):
    out = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(sorted(ka + kb))
            out[key] = out.get(key, Q(0)) + va * vb
            meter.charge(20)
    return {k: v for k, v in out.items() if v}


def linear(row):
    return {(() if j == 0 else (j-1,)): Q(v) for j, v in enumerate(row) if Q(v)}


def encode(poly):
    return [dict(monomial=list(k), coefficient=str(v)) for k, v in sorted(poly.items()) if v]


def nullspace(matrix, meter):
    """RREF with free columns; no preassigned solution coefficients."""
    a = [list(map(Q, row)) for row in matrix]
    width = len(a[0])
    pivots = []
    for col in range(width):
        row = len(pivots)
        found = next((i for i in range(row, len(a)) if a[i][col]), None)
        if found is None:
            continue
        a[row], a[found] = a[found], a[row]
        scale = a[row][col]
        a[row] = [v/scale for v in a[row]]
        for i in range(len(a)):
            if i != row and a[i][col]:
                scale = a[i][col]
                a[i] = [x-scale*y for x, y in zip(a[i], a[row])]
                meter.charge(8*width)
        pivots.append(col)
        meter.charge(8*width)
        if len(pivots) == len(a):
            break
    solutions = []
    for free in range(width):
        if free in pivots:
            continue
        v = [Q(0)]*width
        v[free] = Q(1)
        for row, col in enumerate(pivots):
            v[col] = -a[row][free]
        denominator = lcm(*(x.denominator for x in v))
        integers = [int(x*denominator) for x in v]
        divisor = gcd(*integers)
        sign = 1 if next(x for x in integers if x) > 0 else -1
        solutions.append([Q(sign*x//divisor) for x in integers])
    return len(pivots), solutions


def catalogue(dimension, meter):
    if type(dimension) is not int or not 2 <= dimension <= 5:
        raise ValueError('bounded generic dimension2..5')
    width = dimension*(dimension+1)
    coefficients = {}
    for i in range(dimension):
        for j in range(dimension+1):
            monomial = (i,) if not j else tuple(sorted((i, j-1)))
            coefficients.setdefault(monomial, [Q(0)]*width)[i*(dimension+1)+j] += 1
            meter.charge(10)
    rank, solutions = nullspace([coefficients[k] for k in sorted(coefficients)], meter)
    basis = []
    for index, flat in enumerate(solutions):
        vector = [flat[i*(dimension+1):(i+1)*(dimension+1)] for i in range(dimension)]
        sums = [sum(row[j] for row in vector) for j in range(dimension+1)]
        basis.append(dict(id=index, vector=[list(map(str, row)) for row in vector], sum=list(map(str, sums))))
    candidates = []
    decoded = [([linear(row) for row in item['vector']], linear(item['sum'])) for item in basis]
    for mask in range(1, 1 << len(basis)):
        chosen = [j for j in range(len(basis)) if mask & (1 << j)]
        weights, normalizer = [{} for _ in range(dimension)], {}
        for j in chosen:
            v, s = decoded[j]
            normalizer = add(normalizer, mul(s, s, meter))
            for i in range(dimension):
                weights[i] = add(weights[i], mul(s, v[i], meter))
        candidates.append(dict(id=mask-1, basis_ids=chosen,
            active_coordinates=[i for i, w in enumerate(weights) if w],
            weights=[encode(w) for w in weights], normalizer=encode(normalizer),
            sos_linear_forms=[basis[j]['sum'] for j in chosen],
            normalizer_nonnegative_proved=True, normalizer_positive_proved=False))
    meter.live(1000*len(candidates)+width*width)
    return dict(schema='core-cutoff-frame-v1', dimension=dimension, constraint_rank=rank,
        basis=basis, candidates=candidates,
        weak_fact_countermodel=dict(drifts=['1']*dimension, normalizer='0',
            scope='upper magnitude bounds alone cannot prove the recovery denominator positive',
            actual_mobius_counterexample=False),
        supplied=['polynomial degree limit', 'square-and-pool construction', 'Cauchy recovery rule'],
        generated=['complete rational nullspace', 'all pooled expressions', 'exact signed cancellation'],
        model_calls=0, whole_signed_bound_proved=False, RH_proved=False)


def cutoff(N, exponent):
    """floor(N**r) using integer inequalities, including root boundaries."""
    r = Q(exponent)
    if type(N) is not int or N < 1 or not 0 < r < 1:
        raise ValueError('positive integer horizon and strict rational cutoff')
    target = N**r.numerator
    lo, hi = 1, N+1
    while hi-lo > 1:
        middle = (lo+hi)//2
        if middle**r.denominator <= target:
            lo = middle
        else:
            hi = middle
    return lo


def moments(mu, requests, meter):
    if ctx.prec != 192:
        raise ValueError('producer precision192')
    if set(requests) != {'a', 'b'} or any(v != sorted(set(v)) or
            any(type(n) is not int or n < 1 for n in v) for v in requests.values()):
        raise ValueError('sorted exact moment requests')
    wanted = {name: set(v) for name, v in requests.items()}
    union = wanted['a'] | wanted['b']
    H = max(union)
    if len(mu) != H+1 or H > 1048575 or mu[:2] != [0, 1] or any(type(v) is not int or v not in (-1, 0, 1) for v in mu):
        raise ValueError('complete exact Mobius prefix and unit')
    inverse = [0]*(H+1)
    for d in range(1, H+1):
        for n in range(d, H+1, d):
            inverse[n] += mu[d]
        meter.charge(2*(H//d))
    if inverse[1:] != [1]+[0]*(H-1):
        raise ValueError('every divisor-inverse equation must hold')
    meter.charge(2*H)
    meter.live(12*(H+1))
    output = dict(a={}, b={}, effective_cutoffs={})
    a, b, effective = arb(0), arb(0), 0
    for n in range(1, H+1):
        if mu[n]:
            t = arb(n).root(3)
            w = 1/(t*t)
            a += mu[n]*w
            b += mu[n]*w*w
            effective = n
            meter.charge(500)
        if n in wanted['a']:
            output['a'][str(n)] = a
        if n in wanted['b']:
            output['b'][str(n)] = b
        if n in union:
            output['effective_cutoffs'][str(n)] = effective
        meter.charge(5)
    return output


def alias_linear(row, aliases):
    coefficients = {None: Q(row[0])}
    first = {}
    for i, coefficient in enumerate(row[1:]):
        representative = first.setdefault(tuple(aliases[i]), i)
        coefficients[representative] = coefficients.get(representative, Q(0))+Q(coefficient)
    return {i: v for i, v in coefficients.items() if v}


def eval_linear(coefficients, drifts, meter):
    result = arb(0)
    for index, q in coefficients.items():
        result += (arb(q.numerator)/q.denominator)*(1 if index is None else drifts[index])
        meter.charge(70)
    return result


def evaluate(candidate, basis, drifts, aliases, meter):
    if ctx.prec != 192 or not 2 <= len(drifts) <= 5 or len(aliases) != len(drifts):
        raise ValueError('complete producer frame input')
    for i, a in enumerate(aliases):
        for j, b in enumerate(aliases[:i]):
            if a == b and not drifts[i].overlaps(drifts[j]):
                raise ArithmeticError('equal effective cutoffs must overlap')
    W, S, any_form = [arb(0) for _ in drifts], arb(0), False
    for j in candidate['basis_ids']:
        v = basis[j]
        exact_s = alias_linear(v['sum'], aliases)
        any_form |= bool(exact_s)
        s = eval_linear(exact_s, drifts, meter)
        S += s*s
        for i, row in enumerate(v['vector']):
            W[i] += s*eval_linear(alias_linear(row, aliases), drifts, meter)
        meter.charge(150)
    if not any_form:
        return dict(status='exact_singular', normalizer=arb(0), weights=[arb(0)]*len(drifts), **{'lambda': None, 'K': None})
    if not S > 0:
        return dict(status='unresolved_positive', normalizer=S, weights=W, **{'lambda': None, 'K': None})
    weights = [w/S for w in W]
    K = sum((v*v for v in weights), arb(0))
    if not (sum(weights, arb(0))-1).contains(0) or not sum((v*d for v, d in zip(weights, drifts)), arb(0)).contains(0):
        raise ArithmeticError('certified affine recovery and drift cancellation')
    meter.charge(500*len(drifts))
    return dict(status='certified_positive', normalizer=S, weights=W, **{'lambda': weights, 'K': K})


def drift(polynomial, a, b, Ru, meter):
    """Evaluate the SAVED complete signed source polynomial; no nominated answer."""
    value = arb(0)
    for term in polynomial:
        powers = term['powers']
        if len(powers) != 4 or powers[2] != 0 or any(type(k) is not int or k < 0 for k in powers):
            raise ValueError('this numerical moment worker does not implement a c_U moment')
        q = Q(term['coefficient'])
        value += (arb(q.numerator)/q.denominator)*a**powers[0]*b**powers[1]*Ru**powers[3]
        meter.charge(500)
    return value


def feedback(candidate, binding_ids, finite_status):
    """A construction emits its unsolved inequalities, not a claim of closure."""
    return dict(id='cutoff_frame_'+str(candidate['id']), candidate_id=candidate['id'],
        construction=dict(weights='lambda_i=W_i(d(N))/S(d(N))', catalogue_id=candidate['id'],
                          common_horizon='N=4X-1', domain='S(d(N))>0'),
        source_binding_ids=binding_ids, finite_status=finite_status,
        required=[
            dict(id='eventual_nonsingularity', status='open', expression='S(d(N))>0 for every dyadic X>=X0',
                 quantifiers='one fixed finite dyadic X0; N=4X-1', search_target='arithmetic lower bound or exact zero-drift branch'),
            dict(id='recovery_cost', status='open', depends_on=['eventual_nonsingularity'],
                 expression='K(N)=sum_i lambda_i(N)^2 <= C_K*(1+log2X)^q_K',
                 quantifiers='fixed finite C_K,q_K>=0 for every dyadic X>=X0',
                 search_target='relative signed moment separation or bound on exact weighted paid energy'),
            dict(id='signed_residual', status='open', depends_on=['eventual_nonsingularity'],
                 expression='E_(sum_i lambda_i R_i)(X) <= C_R*(1+log2X)^q_R',
                 quantifiers='fixed finite C_R,q_R>=0 for every dyadic X>=X0',
                 search_target='full joined residual correlations, weighted energies, or scale recurrences'),
            dict(id='finite_head', status='open', expression='certify original full core bound on dyadic X<X0',
                 search_target='finite complete source evaluation after a fixed X0 is proved')],
        recovery='E_g <= 2 E_(sum_i lambda_i R_i) + 2 K sum_i C_Pi',
        conditional_log_degree='max(q_K,q_R); retain inherited transport/channel recovery and target-degree cost',
        all_residual_crosses_retained=True, exact_transport_error_retained=True,
        supplied_rules=['linear recovery', 'Cauchy inequality'],
        construction_generated=True, uniform_recovery_proved=False, uniform_signed_residual_proved=False,
        whole_signed_bound_proved=False, RH_proved=False)
