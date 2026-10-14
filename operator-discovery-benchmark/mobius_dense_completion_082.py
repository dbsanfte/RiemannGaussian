"""Complete drift certificate discovery using geometry, never Mobius signs.

Floating LPs propose coefficients; all published upper and lower prices are
recomputed with exact rational arithmetic. Every squarefree coordinate stays
in the model. Grouping loses sign information, not physical cross terms.
"""
from copy import deepcopy
from fractions import Fraction as Q
from math import gcd, isqrt, isfinite
import time

import numpy as np
from flint import fmpz, fmpq, fmpq_mat
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

MAX_N = 4_000_000
MAX_GROUPS = 1024
MAX_BITS = 100_000
MAX_BYTES = 4*1024**3
MAX_LP_NONZEROS = 25_000_000


class ResourceLimit(ValueError):
    pass


class Meter:
    def __init__(self, limit=300_000_000_000):
        self.ops = 0
        self.limit = limit
        self.peak_bytes = 0

    def charge(self, n=1):
        self.ops += int(n)
        if self.ops > self.limit:
            raise ResourceLimit('producer work budget')

    def reserve(self, n):
        self.peak_bytes = max(self.peak_bytes, int(n))
        if n > MAX_BYTES:
            raise ResourceLimit('producer prospective memory budget')


def rational(x):
    if type(x) is not str or len(x) > MAX_BITS:
        raise ValueError('canonical rational string required')
    q = Q(x)
    if str(q) != x or max(q.numerator.bit_length(), q.denominator.bit_length()) > 4096:
        raise ValueError('noncanonical or excessive rational')
    return q


def floor_scaled_power(u, scale, eta):
    """Exact arbitrary positive rational powers, with a prospective bit gate."""
    s, e = Q(scale), Q(eta)
    if type(u) is not int or u < 1 or s <= 0 or not 0 < e <= 1:
        raise ValueError('scaled power domain')
    bits = e.denominator*(s.numerator.bit_length()+s.denominator.bit_length()) + e.numerator*u.bit_length()
    if bits > MAX_BITS:
        raise ResourceLimit('scaled power prospective bit budget')
    numerator = s.numerator**e.denominator*u**e.numerator
    denominator = s.denominator**e.denominator
    value = int(fmpz(numerator//denominator).root(e.denominator))
    if not value**e.denominator*denominator <= numerator < (value+1)**e.denominator*denominator:
        raise ArithmeticError('native integer root verification')
    return value


def parse_program(raw):
    keys = {'schema', 'kernel', 'memory', 'rays', 'drift_multiplier', 'profiles', 'theta', 'gram_weights'}
    if type(raw) is not dict or set(raw) != keys or raw['schema'] != 'dense-divisor-completion-v1':
        raise ValueError('dense program schema')
    d = raw['memory']
    if type(d) is not int or not 1 <= d <= 3:
        raise ValueError('memory 1..3')
    if type(raw['kernel']) is not list or not 1 <= len(raw['kernel']) <= 128:
        raise ValueError('kernel budget')
    kernel, last = [], 0
    for row in raw['kernel']:
        if type(row) is not dict or set(row) != {'divisor', 'weight'}:
            raise ValueError('kernel row')
        v, w = row['divisor'], rational(row['weight'])
        if type(v) is not int or not last < v or v.bit_length() > 4096 or not w:
            raise ValueError('ordered nonzero kernel')
        kernel.append((v, w)); last = v
    if type(raw['rays']) is not list or len(raw['rays']) > 10000:
        raise ValueError('ray budget')
    rays = []
    for row in raw['rays']:
        if type(row) is not dict or set(row) != {'a', 'weight'} or type(row['a']) is not list or len(row['a']) != d:
            raise ValueError('ray shape')
        a, w = tuple(map(rational, row['a'])), rational(row['weight'])
        if w <= 0:
            raise ValueError('positive energy weight')
        rays.append((a, w))
    r = rational(raw['drift_multiplier'])
    if not 1 <= r <= 2:
        raise ValueError('drift multiplier domain')
    if type(raw['profiles']) is not list or len(raw['profiles']) > 32:
        raise ValueError('profile budget')
    profiles = []
    for row in raw['profiles']:
        if type(row) is not dict or set(row) != {'scale', 'eta'}:
            raise ValueError('profile schema')
        s, e = rational(row['scale']), rational(row['eta'])
        if s <= 0 or not 0 < e <= 1:
            raise ValueError('profile domain')
        profiles.append((s, e))
    if type(raw['theta']) is not list or len(raw['theta']) != len(profiles):
        raise ValueError('theta shape')
    theta = []
    for row in raw['theta']:
        if type(row) is not list or len(row) != d+1:
            raise ValueError('theta row shape')
        values = tuple(map(rational, row))
        if any(abs(x) > 16 for x in values):
            raise ValueError('theta box')
        theta.append(values)
    if type(raw['gram_weights']) is not list or len(raw['gram_weights']) != d+1+len(profiles):
        raise ValueError('Gram shape')
    gram = tuple(map(rational, raw['gram_weights']))
    if any(not 0 <= w <= 16 for w in gram):
        raise ValueError('Gram box')
    return dict(kernel=kernel, memory=d, rays=rays, drift_multiplier=r,
                profiles=profiles, theta=theta, gram_weights=gram)


def rational_budget(values, meter, power=1, terms=1):
    common = 1; biggest = 1
    for q in values:
        if max(q.numerator.bit_length(), q.denominator.bit_length()) > 4096:
            raise ResourceLimit('individual rational bit budget')
        factor = q.denominator//gcd(common, q.denominator)
        if common.bit_length()+factor.bit_length() > MAX_BITS//max(1, power):
            raise ResourceLimit('prospective rational denominator budget')
        common *= factor
        biggest = max(biggest, abs(q.numerator).bit_length())
        meter.charge()
    bits = power*(common.bit_length()+biggest)+max(1, terms.bit_length())+16
    if bits > MAX_BITS:
        raise ResourceLimit('prospective rational arithmetic bit budget')
    return bits


def drift_matrix(p, meter=None):
    meter = meter or Meter()
    d = p['memory']
    values = [p['drift_multiplier']]+[q for a,w in p['rays'] for q in (w,)+a]
    bits = rational_budget(values, meter, power=4, terms=len(p['rays'])+1)
    meter.reserve(16384+(d+1)**2*(256+bits))
    meter.charge((len(p['rays'])+1)*d*d*4)
    H = [[Q(int(i == j == 0)) for j in range(d)] for i in range(d)]
    for a, w in p['rays']:
        for i in range(d):
            for j in range(d):
                H[i][j] += w*a[i]*a[j]
    T = [[Q(0) for _ in range(d+1)] for _ in range(d+1)]
    for i in range(d):
        for j in range(d):
            T[i][j] += H[i][j]
            T[i+1][j+1] -= p['drift_multiplier']*H[i][j]
    return T


def build_model(program, u, meter=None):
    """Literal coordinate construction, independent of checker's breakpoint sweep."""
    meter = meter or Meter()
    p = parse_program(program)
    if type(u) is not int or u < 1 or u.bit_length() > 4096:
        raise ValueError('u domain')
    N = u//p['kernel'][0][0]
    if N > MAX_N:
        raise ResourceLimit('complete arithmetic horizon budget')
    dim = p['memory']+1
    T = drift_matrix(p, meter)  # Gate growing exact denominators before coordinate allocation.
    cuts = [min(N, floor_scaled_power(u, s, e)) for s, e in p['profiles']]
    denominator = 1
    for _, w in p['kernel']:
        denominator = denominator//gcd(denominator, w.denominator)*w.denominator
        if denominator.bit_length() > 4096:
            raise ResourceLimit('kernel denominator budget')
    integer_weights = [(v, w.numerator*(denominator//w.denominator)) for v, w in p['kernel']]
    feature_bound = max([sum(abs(w) for _, w in integer_weights)] + [denominator*K for K in cuts] + [1])
    if feature_bound*max(1, N) >= 2**62:
        raise ResourceLimit('literal feature int64 budget')
    m = dim+len(cuts)
    meter.reserve(16384+(N+1)*(80+32*m))
    sf = np.ones(N+1, dtype=bool); sf[0] = False
    for k in range(2, isqrt(N)+1):
        sf[k*k::k*k] = False
        meter.charge(N//(k*k))
    n = np.flatnonzero(sf)
    features = np.zeros((len(n), m), dtype=np.int64)
    for i in range(dim):
        for divisor, weight in integer_weights:
            features[:, i] += (n <= u//((1 << i)*divisor))*weight
    for j, K in enumerate(cuts):
        if K:
            features[:, dim+j] = denominator*(K//n-(n == 1))
    groups, counts = np.unique(features, axis=0, return_counts=True)
    if len(groups) > MAX_GROUPS:
        raise ResourceLimit('complete group budget, target not truncated')
    meter.charge((N+1)*m+len(n)*m*max(1, len(n).bit_length()))
    return dict(program=p, raw=deepcopy(program), u=u, N=N, cuts=cuts,
                denominator=denominator, features=groups, counts=counts,
                squarefree_count=len(n), group_count=len(groups), T=T, meter=meter)


def coefficient_matrix(model):
    p = model['program']; d = p['memory']+1; size = d+len(p['profiles'])
    M = [[Q(0) for _ in range(size)] for _ in range(size)]
    for i in range(d):
        for j in range(d):
            M[i][j] = model['T'][i][j]
    for j, row in enumerate(p['theta']):
        for i, value in enumerate(row):
            M[i][d+j] += value; M[d+j][i] += value
    for i, value in enumerate(p['gram_weights']):
        M[i][i] += value
    return M


def native_weighted_features(model):
    # Integer feature admission above prospectively covers this multiplication.
    return fmpq_mat((model['features']*model['counts'][:, None]).tolist())


def exact_matrix(model):
    M = coefficient_matrix(model); n = model['group_count']; m = len(M)
    bits = sum(max(q.numerator.bit_length(), q.denominator.bit_length()) for row in M for q in row)
    if bits > MAX_BITS:
        raise ResourceLimit('prospective exact matrix bit budget')
    model['meter'].reserve(16384+model['N']*(80+32*m)+n*n*(256+bits))
    model['meter'].charge(n*n*m+m*m*n)
    V = native_weighted_features(model)
    if n == 0:
        return fmpq_mat(0, 0)
    matrix = fmpq_mat([[fmpq(q.numerator, q.denominator) for q in row] for row in M])
    return (V*matrix*V.transpose()) / fmpq(model['denominator']**2)


def as_q(x):
    return Q(int(x.numerator), int(x.denominator))


def upper_certificate(model):
    A = exact_matrix(model); rows = []
    for g in range(model['group_count']):
        value = A[g, g]
        for h in range(model['group_count']):
            if h != g:
                value += abs(A[g, h])
        rows.append(max(Q(0), as_q(value)))
    return dict(group_count=model['group_count'], squarefree_count=model['squarefree_count'],
                price=str(sum(rows, Q(0))), row_prices=list(map(str, rows)))


def small_dual_contraction(model, lambdas, nus):
    """S=V^T D V, Ddiag=lambda, Dgh=nu/2, including denominator."""
    n = model['group_count']; size = model['features'].shape[1]
    bits = rational_budget(lambdas+nus, model['meter'], terms=max(1,n*n))
    bits += 2*(model['denominator'].bit_length()+max(1,model['N'].bit_length())+64)
    if bits > MAX_BITS:
        raise ResourceLimit('dual feature contraction bit budget')
    model['meter'].reserve(16384+n*n*(256+bits)+size*size*(1024+bits))
    model['meter'].charge(n*n*size+size*size*n)
    if n == 0:
        return [[Q(0) for _ in range(size)] for _ in range(size)]
    D = fmpq_mat(n, n)
    for i, q in enumerate(lambdas):
        D[i, i] = fmpq(q.numerator, q.denominator)
    k = 0
    for i in range(n):
        for j in range(i+1, n):
            q = nus[k]/2; k += 1
            D[i, j] = D[j, i] = fmpq(q.numerator, q.denominator)
    V = native_weighted_features(model)
    S = V.transpose()*D*V / fmpq(model['denominator']**2)
    return [[as_q(S[i, j]) for j in range(size)] for i in range(size)]


def dual_certificate(model, lambdas, nus):
    n = model['group_count']
    if len(lambdas) != n or len(nus) != n*(n-1)//2:
        raise ValueError('dual shape')
    def admitted(value):
        if type(value) is str:
            return rational(value)
        if type(value) not in (int, Q):
            raise ValueError('dual exact rational required')
        q = Q(value)
        if max(q.numerator.bit_length(), q.denominator.bit_length()) > 4096:
            raise ResourceLimit('dual individual rational bit budget')
        return q
    lambdas, nus = list(map(admitted, lambdas)), list(map(admitted, nus))
    if len(lambdas) != n or len(nus) != n*(n-1)//2 or any(not 0 <= q <= 1 for q in lambdas):
        raise ValueError('dual shape/lambda')
    k = 0
    for g in range(n):
        for h in range(g+1, n):
            if abs(nus[k]) > lambdas[g]+lambdas[h]:
                raise ValueError('dual pair feasibility')
            k += 1
    S = small_dual_contraction(model, lambdas, nus)
    d = model['program']['memory']+1
    base = sum((model['T'][i][j]*S[i][j] for i in range(d) for j in range(d)), Q(0))
    theta_penalty = 16*sum((abs(2*S[i][d+j]) for j in range(len(model['cuts'])) for i in range(d)), Q(0))
    gram_penalty = 16*sum((min(Q(0), S[i][i]) for i in range(len(S))), Q(0))
    return {'lambda': list(map(str, lambdas)), 'nu': list(map(str, nus)),
            'lower_bound': str(base-theta_penalty+gram_penalty)}


def rounded(x, bits=24):
    if not isfinite(float(x)):
        raise ValueError('nonfinite LP proposal')
    return Q(round(float(x)*(1 << bits)), 1 << bits)


def parameter_basis(model):
    V = (model['features']*model['counts'][:, None]).astype(float)/model['denominator']
    d = model['program']['memory']+1
    T = np.array([[float(q) for q in row] for row in model['T']])
    A0 = V[:, :d]@T@V[:, :d].T
    n, m = V.shape; g, h = np.triu_indices(n, 1)
    count = len(model['cuts'])*d+m
    diag = np.empty((n, count)); off = np.empty((len(g), count))
    k = 0
    for j in range(len(model['cuts'])):
        for i in range(d):
            diag[:, k] = 2*V[:, i]*V[:, d+j]
            off[:, k] = V[g, i]*V[h, d+j]+V[g, d+j]*V[h, i]
            k += 1
    for i in range(m):
        diag[:, k] = V[:, i]**2
        off[:, k] = V[g, i]*V[h, i]
        k += 1
    return A0, diag, off, g, h


def optimize(program, u, time_limit=120):
    """Search the complete SDD cone. No observed arithmetic values are inputs."""
    start = time.monotonic(); model = build_model(program, u)
    n = model['group_count']; m = model['features'].shape[1]
    ptheta = len(model['cuts'])*(model['program']['memory']+1)
    pcount = ptheta+m; edges = n*(n-1)//2
    prospective = (n+2*edges)*pcount+6*edges+n
    if prospective > MAX_LP_NONZEROS:
        raise ResourceLimit('complete LP sparse entry budget')
    model['meter'].reserve(16384+prospective*96+edges*pcount*16)
    A0, diag, off, g, h = parameter_basis(model)
    scale = float(u*u)
    # Parameters remain in original units. Only matrix prices are normalized.
    diag /= scale; off /= scale; A0 /= scale
    rr, cc, vv = [], [], []
    def append(rows, cols, values):
        rr.append(np.asarray(rows).ravel()); cc.append(np.asarray(cols).ravel()); vv.append(np.asarray(values).ravel())
    dr, dc = np.nonzero(diag)
    append(dr, dc, diag[dr, dc])
    ar, ac = np.nonzero(off)
    append(n+2*ar, ac, off[ar, ac]); append(n+2*ar+1, ac, -off[ar, ac])
    es = np.arange(edges); ns = np.arange(n)
    append(g, pcount+n+es, np.ones(edges)); append(h, pcount+n+es, np.ones(edges))
    append(n+2*es, pcount+n+es, -np.ones(edges)); append(n+2*es+1, pcount+n+es, -np.ones(edges))
    append(ns, pcount+ns, -np.ones(n))
    matrix = coo_matrix((np.concatenate(vv), (np.concatenate(rr), np.concatenate(cc))),
                        shape=(n+2*edges, pcount+n+edges)).tocsr()
    rhs = np.empty(n+2*edges); rhs[:n] = -np.diag(A0)
    rhs[n::2] = -A0[g, h]; rhs[n+1::2] = A0[g, h]
    objective = np.zeros(pcount+n+edges); objective[pcount:pcount+n] = 1
    bounds = [(-16, 16)]*ptheta+[(0, 16)]*m+[(0, None)]*(n+edges)
    fit = linprog(objective, A_ub=matrix, b_ub=rhs, bounds=bounds, method='highs',
                  options={'time_limit': time_limit, 'dual_feasibility_tolerance': 1e-8, 'primal_feasibility_tolerance': 1e-8})
    result = dict(status='LP_PROPOSAL' if fit.success else 'LP_NO_PROPOSAL',
                  solver_status=int(fit.status), solver_message=str(fit.message),
                  group_count=n, squarefree_count=model['squarefree_count'],
                  nonzeros=int(matrix.nnz), scale_normalization='u^2',
                  elapsed_seconds=time.monotonic()-start, ops=model['meter'].ops,
                  prospective_peak_bytes=model['meter'].peak_bytes,
                  signs_or_source_values_used=False, uniform_growth_proved=False, RH_proved=False)
    if not fit.success:
        return result
    proposal = deepcopy(program)
    values = [max(Q(-16), min(Q(16), rounded(x))) for x in fit.x[:ptheta]]
    d = model['program']['memory']+1
    proposal['theta'] = [[str(q) for q in values[j*d:(j+1)*d]] for j in range(len(model['cuts']))]
    proposal['gram_weights'] = [str(max(Q(0), min(Q(16), rounded(x)))) for x in fit.x[ptheta:pcount]]
    fitted_model = dict(model, program=parse_program(proposal), raw=proposal)
    cert = upper_certificate(fitted_model)
    marginals = fit.ineqlin.marginals
    lambdas = [max(Q(0), min(Q(1), rounded(-x))) for x in marginals[:n]]
    nus = []
    for edge, (i, j) in enumerate(zip(g, h)):
        value = rounded(-marginals[n+2*edge]+marginals[n+2*edge+1])
        bound = lambdas[i]+lambdas[j]
        nus.append(max(-bound, min(bound, value)))
    dual = dual_certificate(model, lambdas, nus)
    if Q(dual['lower_bound']) > Q(cert['price']):
        raise ArithmeticError('exact primal/dual ordering')
    result.update(program=proposal, certificate=cert, dual=dual,
                  float_optimum_normalized=float(fit.fun),
                  exact_gap=str(Q(cert['price'])-Q(dual['lower_bound'])),
                  elapsed_seconds=time.monotonic()-start, ops=model['meter'].ops,
                  prospective_peak_bytes=model['meter'].peak_bytes)
    return result


def sublinear_obstruction(program):
    """Reviewed all-scale obstruction, restricted to the exact two source families."""
    p = parse_program(program)
    base = [(4, Q(-1)), (5, Q(1)), (8, Q(1)), (10, Q(-1))]
    extended = sorted(base+[(12, Q(-3547,8192)), (15, Q(3547,8192)),
                            (24, Q(3547,8192)), (30, Q(-3547,8192))])
    if p['kernel'] not in (base, extended):
        return dict(status='NOT_APPLICABLE', reason='outer source band not established for this kernel')
    if any(e == 1 for _, e in p['profiles']):
        return dict(status='NOT_APPLICABLE', reason='linear profile requires full dense search')
    threshold = 58081
    for s, e in p['profiles']:
        a, b = e.numerator, e.denominator
        exponent = b-a
        t = 6*s
        if b*(t.numerator.bit_length()+t.denominator.bit_length()) > MAX_BITS:
            raise ResourceLimit('uniform obstruction threshold bit budget')
        num, den = t.numerator**b, t.denominator**b
        value = int(fmpz(num//den).root(exponent))
        if value**exponent*den < num:
            value += 1
        threshold = max(threshold, value)
    return dict(status='PROVED_SUBLINEAR_PROFILE_PRICE_OBSTRUCTION',
                threshold=threshold, quadratic_coefficient=str(drift_matrix(p)[0][0]/6400),
                lower_bound='B(u)>=H00*u^2/6400 for every integer u>=threshold',
                excluded_price_exponents='every q<2 with a fixed finite constant',
                proof='outer squarefree group has all incidence profiles zero; single-group dual; elementary squarefree interval density',
                formal_theorem_prover_checked=False, source_bound_proved=False, RH_proved=False)
