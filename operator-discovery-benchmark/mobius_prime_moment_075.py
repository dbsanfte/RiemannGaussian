"""Search an arithmetic operator together with its two unpaid control lemmas.

The all-scale transfer is conditional. Floating optimization invents formulas;
exact arithmetic certifies finite inequalities, never the uniform premises.
"""
from array import array
from fractions import Fraction as Q
from functools import lru_cache
from math import ceil, isqrt

import numpy as np
from scipy.optimize import linprog

import mobius_prime_storage_073 as B


SOURCE_SPEC = dict(grid=80, theta=['1/2', '17/31', '4/7', '2/3', '5/7', '4/5', '7/8'],
                   multipliers=[2, 3, 5, 6])


class Meter(B.Meter):
    """Inherited operation and prospective per-task allocation gates."""


def parse_spec(spec):
    if type(spec) is not dict or set(spec) != {'grid', 'theta', 'multipliers'} or type(spec['grid']) is not int or spec['grid'] != 80:
        raise ValueError('exact source grid80 required')
    ts, ds = spec['theta'], spec['multipliers']
    if type(ts) is not list or not 2 <= len(ts) <= 32 or type(ds) is not list or len(ds) > 16:
        raise ValueError('bounded source dimensions')
    theta = list(map(B.rational, ts))
    if theta != sorted(set(theta)) or any(not Q(1, 2) <= t < 1 for t in theta):
        raise ValueError('increasing rational cutoffs in [1/2,1)')
    if ds != sorted(set(ds)) or any(type(d) is not int or not 2 <= d <= 64 for d in ds):
        raise ValueError('distinct integer dilation multipliers2..64')
    return theta, ds


def labels(spec):
    theta, ds = parse_spec(spec)
    return ['prime:(' + str(a) + ',' + str(b) + ']' for a, b in zip(theta, theta[1:])] + ['dilate:' + str(d) for d in ds]


def arithmetic(n, meter):
    """Compact Euler sieve, independent of the checker's two factor sieves."""
    if not 1 <= n <= 4_000_000:
        raise ValueError('arithmetic horizon1..4000000')
    meter.reserve(40 * (n + 1))
    least = array('i', [0]) * (n + 1)
    mu = array('b', [0]) * (n + 1)
    prefix = array('q', [0]) * (n + 1)
    pi = array('i', [0]) * (n + 1)
    primes = []
    mu[1] = 1
    for i in range(2, n + 1):
        if not least[i]:
            least[i] = i
            primes.append(i)
            mu[i] = -1
        for p in primes:
            v = i * p
            if v > n:
                break
            least[v] = p
            if p == least[i]:
                break
            mu[v] = -mu[i]
            meter.charge(4)
        meter.charge(5)
    count = total = 0
    for i in range(1, n + 1):
        count += least[i] == i
        total += mu[i]
        pi[i], prefix[i] = count, total
    meter.charge(5 * n)
    return prefix, pi


def G(u, prefix):
    return prefix[u // 8] - prefix[u // 10] - prefix[u // 4] + prefix[u // 5]


def make_data(spec, scales, meter=None):
    meter = meter or Meter()
    theta, ds = parse_spec(spec)
    if not scales or any(type(u) is not int or u <= 0 for u in scales):
        raise ValueError('positive integer parent scales')
    us = sorted(set(scales))
    n = max(1, us[-1] // 4)
    dimension = len(theta) - 1 + len(ds)
    meter.reserve(40 * (n + 1) + (1024 + 160*dimension + 80*len(theta))*len(us))
    prefix, pi = arithmetic(n, meter)
    rows = []
    for u in us:
        X = u // 4
        cuts = [B.floor_power(X, t) if X else 0 for t in theta]
        sums, moments, counts = [], [], []
        for lo, hi in zip(cuts, cuts[1:]):
            left = lo + 1
            total = moment = count = 0
            # Walk prime intervals by their constant quotient; no prime is
            # treated as an independent sample and no multiplicity is lost.
            while left <= hi:
                child = u // left
                right = min(hi, u // child)
                multiplicity = pi[right] - pi[left - 1]
                value = G(child, prefix)
                total += multiplicity * value
                moment += multiplicity * value * value
                count += multiplicity
                left = right + 1
                meter.charge(16)
            sums.append(total)
            moments.append(moment)
            counts.append(count)
        for d in ds:
            value = G(u // d, prefix)
            sums.append(value)
            moments.append(value * value)
            counts.append(1)
        rows.append(dict(u=u, X=X, cuts=cuts, z=G(u, prefix), components=sums,
                         moments=moments, counts=counts))
    return dict(schema='prime-grid-moment-data-v1', spec=spec, rows=rows)


def join_data(*datasets):
    spec = datasets[0]['spec']
    rows = {}
    for data in datasets:
        if data['schema'] != 'prime-grid-moment-data-v1' or data['spec'] != spec:
            raise ValueError('same exact source required')
        for row in data['rows']:
            if row['u'] in rows and rows[row['u']] != row:
                raise ValueError('conflicting source row')
            rows[row['u']] = row
    return dict(schema='prime-grid-moment-data-v1', spec=spec, rows=[rows[u] for u in sorted(rows)])


def ceiling_grid(value, denominator):
    return Q((value.numerator * denominator + value.denominator - 1) // value.denominator, denominator)


def price_bounds(spec, base_u):
    theta, ds = parse_spec(spec)
    if type(base_u) is not int or base_u < 16:
        raise ValueError('complete induction base>=16')
    lower_log = Q(2, 3) * ((base_u // 4).bit_length() - 1)
    prices = []
    for lo, hi in zip(theta, theta[1:]):
        z = (hi - lo) / (hi + lo)
        upper_log = 2 * sum((z ** (2*j+1) / (2*j+1) for j in range(12)), Q(0)) + 2*z**25 / (25*(1-z*z))
        prices.append(ceiling_grid(2*(upper_log + 1/(hi*lower_log)), 1 << 20))
    return prices + [Q(1, d) for d in ds]


def sqrt_upper(value, denominator=1 << 20):
    if value < 0:
        raise ValueError('nonnegative square-root argument')
    k = isqrt((value.numerator * denominator**2) // value.denominator)
    if Q(k, denominator)**2 < value:
        k += 1
    return Q(k, denominator)


def canonical_direction(values):
    values = tuple(map(Q, values))
    first = next((v for v in values if v), None)
    if first is None:
        raise ValueError('nonzero operator shape')
    scale = max(map(abs, values)) * (1 if first > 0 else -1)
    return tuple(v / scale for v in values)


def operator_class(shape, spec):
    cut = len(spec['theta']) - 1
    prime, direct = any(shape[:cut]), any(shape[cut:])
    return 'prime_composite' if prime and direct else 'prime_only' if prime else 'direct_only'


def catalog(spec, obligations):
    """The previous exact obstruction changes the generated operator language."""
    theta, ds = parse_spec(spec)
    d = len(theta) - 1 + len(ds)
    dictionary = {}

    def insert(shape, origin):
        key = canonical_direction(shape)
        dictionary.setdefault(key, []).append(origin)

    for v in B.initial_directions(d):
        insert(v, 'single_or_signed_pair')
    for candidate in obligations.get('candidates', []):
        for ray in candidate['obligation']['rays']:
            if ray['status'] != 'EXACT_SIGNED_PRIME_DILATION_IDENTITY':
                continue
            shape = [Q(0)] * d
            for block in ray['prime_blocks']:
                lo, hi = Q(block['lower_theta']), Q(block['upper_theta'])
                if lo not in theta or hi not in theta:
                    raise ValueError('new grammar must retain exported block endpoints')
                for j, (a, b) in enumerate(zip(theta, theta[1:])):
                    if lo <= a < b <= hi:
                        shape[j] += Q(block['coefficient'])
            if any(shape):
                insert(shape, candidate['candidate_file'] + ':ray' + str(ray['ray']))
    return [dict(shape=list(map(str, key)), origins=origins, kind=operator_class(key, spec))
            for key, origins in dictionary.items()]


def minimax_directions(data, exponents, meter):
    """Finite LP proposals for signed operators, rounded before any certificate."""
    meter.reserve(4096*len(data['rows'])*len(labels(data['spec'])))
    values = np.array([r['components'] for r in data['rows']], dtype=float)
    target = np.array([r['z'] for r in data['rows']], dtype=float)
    parents = np.array([r['u'] for r in data['rows']], dtype=float)
    d = values.shape[1]
    split = len(data['spec']['theta']) - 1
    result = []
    for qs in exponents:
        normalizer = parents ** (float(Q(qs))/2)
        for kind, active in [('prime_only', list(range(split))),
                             ('direct_only', list(range(split, d))),
                             ('prime_composite', list(range(d)))]:
            if not active:
                continue
            A = values[:, active] / normalizer[:, None]
            y = target / normalizer
            matrix = np.vstack([np.column_stack([A, -np.ones(len(y))]),
                                np.column_stack([-A, -np.ones(len(y))])])
            sol = linprog([0.0]*len(active)+[1.0], A_ub=matrix,
                          b_ub=np.concatenate([y, -y]),
                          bounds=[(-8, 8)]*len(active)+[(0, None)], method='highs',
                          options={'time_limit': 120})
            meter.charge(int(matrix.size) * max(1, sol.nit or 0))
            if not sol.success:
                result.append(dict(origin='minimax:' + qs + ':' + kind,
                                   status='LP_PROPOSAL_UNAVAILABLE', message=sol.message))
                continue
            v = [Q(0)] * d
            for j, value in zip(active, sol.x[:-1]):
                v[j] = Q(round(float(value)*4096), 4096)
            if any(v):
                key = canonical_direction(v)
                result.append(dict(shape=list(map(str, key)), origins=['minimax:' + qs + ':' + kind],
                                   kind=operator_class(key, data['spec']), proposal_objective=float(sol.fun)))
    return result


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), Q(0))


def fit_beta(shape, rows, prices, meter):
    """Least uniform induction price among finite diagonal-moment controls."""
    meter.reserve(4096*len(rows)*len(shape))
    values = np.array([r['components'] for r in rows], dtype=float)
    moments = np.array([r['moments'] for r in rows], dtype=float)
    target = (values @ np.array(list(map(float, shape)))) ** 2
    normalizer = np.maximum(1.0, np.maximum(target, moments.max(axis=1)))
    sol = linprog(list(map(float, prices)), A_ub=-moments/normalizer[:, None],
                  b_ub=-target/normalizer, bounds=(0, None), method='highs',
                  options={'time_limit': 120})
    meter.charge(int(moments.size) * max(1, sol.nit or 0))
    if not sol.success:
        raise ArithmeticError('moment LP failed: ' + sol.message)
    beta = [Q(ceil(max(0.0, float(v))*4096), 4096) for v in sol.x]
    repair = Q(0)
    for row in rows:
        left = dot(shape, row['components'])**2
        gap = left - dot(beta, row['moments'])
        if gap > 0:
            total = sum(row['moments'])
            if not total:
                raise ArithmeticError('nonzero sum with zero complete square moments')
            repair = max(repair, gap / total)
        meter.charge(10*len(shape))
    repair = ceiling_grid(repair, 4096)
    beta = [b + repair for b in beta]
    if any(dot(shape, r['components'])**2 > dot(beta, r['moments']) for r in rows):
        raise ArithmeticError('exact finite correlation admission after rounding')
    return beta, dict(lp_objective=float(sol.fun), exact_repair=str(repair),
                      exact_training_price=str(dot(beta, prices)))


def cauchy_beta(shape):
    total = sum(map(abs, shape), Q(0))
    return [total*abs(a) for a in shape]


def correlation_assessment(shape, beta, rows, meter):
    failures, worst = [], None
    for row in rows:
        left, right = dot(shape, row['components'])**2, dot(beta, row['moments'])
        gap = left - right
        meter.charge(10*len(shape))
        if gap > 0:
            witness = dict(u=row['u'], lemma='correlation', left=str(left), right=str(right), gap=str(gap))
            failures.append(witness)
            if worst is None or gap > Q(worst['gap']):
                worst = witness
    return dict(status='REFUTED' if failures else 'VERIFIED_ON_FINITE_DOMAIN',
                failures=len(failures), first=failures[0] if failures else None,
                worst=worst, uniform_correlation_proved=False)


@lru_cache(maxsize=64)
def base_upper(base_u, q, precision):
    prefix, _ = arithmetic(base_u//4, Meter())
    return max(Q(G(u, prefix)**2) / B.power_bounds(u, q, precision)[0] for u in range(1, base_u+1))


def make_program(spec, shape, beta, q, rows, base_u=4096, precision=20, meter=None):
    meter = meter or Meter()
    q = B.rational(q)
    if not 1 <= q < 2:
        raise ValueError('power target1<=q<2')
    dimension = len(labels(spec))
    if len(shape) != dimension or len(beta) != dimension or any(b < 0 for b in beta):
        raise ValueError('complete operator/moment vectors')
    if not rows or any(r['u'] <= base_u for r in rows):
        raise ValueError('nonempty training domain above complete base')
    prices = price_bounds(spec, base_u)
    rho = dot(beta, prices)
    r = sqrt_upper(rho)
    if not 0 <= r < 1:
        raise ValueError('no conditional contraction')
    C = max((Q(row['z'])-dot(shape, row['components']))**2 /
            B.power_bounds(row['u'], q, precision)[0] for row in rows)
    base = base_upper(base_u, q, precision)
    bound = max(base, C/(1-r)**2)
    meter.charge(len(rows)*10*dimension + 10*base_u)
    return dict(schema='prime-grid-control-program-v1', spec=spec, q=str(q),
                operator=list(map(str, shape)), beta=list(map(str, beta)), base_u=base_u,
                price_bounds=list(map(str, prices)), rho_upper=str(rho), sqrt_rho_upper=str(r),
                innovation_C=str(C), base_upper=str(base), bound_B=str(bound), precision=precision,
                training_scales=[r['u'] for r in rows], uniform_innovation_proved=False,
                uniform_correlation_proved=False, uniform_source_bound_proved=False, RH_proved=False)


def amplitudes(unit_price):
    """Fixed nonzero exposure ladder; shrinking a formula cannot repair a failed correlation."""
    top = Q(1)
    while top*top*unit_price > Q(1, 4):
        top /= 2
    return [sign*top/divisor for divisor in (1, 2, 4, 8) for sign in (-1, 1)]


def propose_programs(records, discovery, q, base_u, precision, meter):
    """Choose two distinct objectives per structural class, using discovery only."""
    rows = discovery['rows']
    spec = discovery['spec']
    meter.reserve(4096*len(rows)*len(labels(spec)) + 16384*len(records))
    values = np.array([r['components'] for r in rows], dtype=float)
    target = np.array([r['z'] for r in rows], dtype=float)
    normal = np.array([r['u'] for r in rows], dtype=float)**float(Q(q))
    offers = []
    for record in records:
        shape, beta = list(map(Q, record['shape'])), list(map(Q, record['beta']))
        rho = Q(record['price'])
        direction = values @ np.array(list(map(float, shape)))
        for amplitude in amplitudes(rho):
            r = sqrt_upper(amplitude*amplitude*rho)
            C = float(np.max((target-float(amplitude)*direction)**2/normal))
            offers.append(dict(record=record['id'], amplitude=str(amplitude), kind=record['kind'],
                               innovation_score=C, transfer_score=C/float((1-r)**2)))
    selected = {}
    for kind in ('direct_only', 'prime_only', 'prime_composite'):
        group = [o for o in offers if o['kind'] == kind]
        for objective in ('transfer_score', 'innovation_score'):
            if group:
                offer = min(group, key=lambda o: (o[objective], o['transfer_score'], o['record'], Q(o['amplitude'])))
                key = (offer['record'], offer['amplitude'])
                selected.setdefault(key, dict(offer, selected_by=[]))['selected_by'].append(objective)
    # Reserve a known-theorem recovery slot; it is reported separately from
    # arithmetic-dependent controls and still owes its residual estimate.
    recovery_ids = {r['id'] for r in records if r['mode'] == 'universal_direct_cauchy' and sum(bool(Q(a)) for a in r['shape']) == 2}
    recovery_offers = [o for o in offers if o['record'] in recovery_ids]
    if recovery_offers:
        offer = min(recovery_offers, key=lambda o: (o['innovation_score'], o['transfer_score'], o['record']))
        key = (offer['record'], offer['amplitude'])
        selected.setdefault(key, dict(offer, selected_by=[]))['selected_by'].append('known_theorem_recovery')
    indexed = {r['id']: r for r in records}
    programs = []
    for offer in selected.values():
        record = indexed[offer['record']]
        amplitude = Q(offer['amplitude'])
        shape = [amplitude*Q(a) for a in record['shape']]
        beta = [amplitude*amplitude*Q(b) for b in record['beta']]
        program = make_program(spec, shape, beta, q, rows, base_u, precision, meter)
        programs.append(dict(selection=offer, program=program, parent_record=record['id'],
                             correlation_mode=record['mode'], origins=record['origins']))
    zero = [Q(0)]*len(labels(spec))
    baseline = make_program(spec, zero, zero, q, rows, base_u, precision, meter)
    meter.charge(len(offers)*len(rows)*len(zero))
    return dict(q=q, offers_scored=len(offers), programs=programs, baseline=baseline,
                selection_data='discovery only; adaptation cannot alter formulas',
                numerical_scores_are_not_proofs=True)


def next_obligations(program_result, evaluation):
    """Failed costs become concrete, typed lemma inputs, not new fitted constants."""
    program = program_result['program']
    failed = sorted({w['lemma'] for w in evaluation.get('failures', []) if w['status'] == 'REFUTED'})
    leaves = []
    for lemma in ('correlation', 'innovation'):
        if lemma == 'correlation' and evaluation.get('universal_direct_correlation_proved'):
            continue
        ambiguous = any(w['lemma'] == lemma and w['status'] == 'UNRESOLVED_ROUNDING' for w in evaluation.get('failures', []))
        status = 'FINITE_COUNTEREXAMPLE' if lemma in failed else 'FINITE_ROUNDING_UNRESOLVED' if ambiguous else 'UNIFORM_PROOF_REQUIRED'
        leaves.append(dict(lemma=lemma, status=status,
                           formula='(a dot B)^2 <= beta dot Q' if lemma == 'correlation' else '(G-a dot B)^2 <= C u^q',
                           all_integer_domain_above=program['base_u'], q=program['q'],
                           operator=program['operator'], beta=program['beta'], C=program['innovation_C'],
                           source_spec=program['spec'],
                           first_witness=next((w for w in evaluation.get('failures', []) if w['lemma'] == lemma and (lemma not in failed or w['status'] == 'REFUTED')), None),
                           next_construction='coherent quotient groups, signed cross moments or a different operator' if lemma == 'correlation' else 'a new residual identity, composed dilation or signed auxiliary control',
                           parent_target_may_not_be_assumed=True))
    return leaves
