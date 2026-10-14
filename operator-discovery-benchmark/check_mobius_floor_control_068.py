"""Independent integer audit of bounded full-floor auxiliary certificates.

No producer, NumPy, SciPy, LP solver, or historical checker is imported.
Pointwise original sources and quotient-block events supply separate replay.
Finite valid upper bounds do not establish an all-scale growth theorem.
"""
from fractions import Fraction as Q
from math import isqrt
import time

SCHEMA = 'mobius-floor-control-v1'
MAX_N = 65536
MAX_H = 4096
MAX_BITS = 4096
MAX_POWER_BITS = 100000
MAX_WORK = 300_000_000_000
MAX_MEMORY_BYTES = 512 * 1024 * 1024
MAX_ENTRIES = 4_000_000
MAX_HORIZONS = 512
GRID = 1 << 20


class Meter:
    def __init__(self, cap=MAX_WORK, seconds=7200):
        if type(cap) is not int or not 0 <= cap <= MAX_WORK:
            raise ValueError('bounded nonnegative work cap')
        if type(seconds) not in (int, float) or not 0 < seconds <= 7200:
            raise ValueError('bounded positive deadline')
        self.cap, self.operations = cap, 0
        self.deadline = time.monotonic()+seconds

    def charge(self, n=1):
        if type(n) is not int or not 0 <= n <= self.cap-self.operations:
            raise OverflowError('floor checker work cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('floor checker deadline')


class _Context:
    def __init__(self, meter):
        self.m, self.work, self.entries, self.storage = meter, 0, 0, 8192

    def charge(self, n=1):
        if type(n) is not int or not 0 <= n <= MAX_WORK-self.work:
            raise OverflowError('independent floor checker work capacity')
        self.work += n
        self.m.charge(n)

    def reserve(self, count, size=96):
        self.charge(count)
        self.entries += count
        self.storage += count*size
        if self.entries > MAX_ENTRIES:
            raise OverflowError('floor checker entry capacity')
        if self.storage > MAX_MEMORY_BYTES:
            raise MemoryError('floor checker storage capacity')

    def bounded(self, value):
        value = Q(value)
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        self.charge(bits+1)
        if bits > MAX_BITS:
            raise OverflowError('floor checker rational capacity')
        return value

    def q(self, value):
        if type(value) is not str or not 1 <= len(value) <= 2500:
            raise ValueError('bounded rational text')
        self.charge(len(value)+1)
        try:
            result = Q(value)
        except (ValueError, ZeroDivisionError):
            raise ValueError('rational text') from None
        if str(result) != value:
            raise ValueError('canonical rational required')
        return self.bounded(result)


def _fields(obj, names):
    if type(obj) is not dict or set(obj) != set(names):
        raise ValueError('exact floor control schema')


def _integer(value, lo, hi, description):
    if type(value) is not int or not lo <= value <= hi:
        raise ValueError(description)
    return value


def _parameters(obj, c):
    if type(obj) is not dict or set(obj) not in (
            {'primes', 'p', 'q', 'alpha', 'gamma'},
            {'primes', 'p', 'q', 'alpha', 'gamma', 'tau'}):
        raise ValueError('source parameter schema')
    alpha, gamma = c.q(obj['alpha']), c.q(obj['gamma'])
    if not 0 < alpha < 1 or gamma <= 0:
        raise ValueError('source fractional gates')
    if 'tau' in obj and not 0 < c.q(obj['tau']) < 1:
        raise ValueError('source tau gate')
    primes = obj['primes']
    if type(primes) is not list or not 2 <= len(primes) <= 8:
        raise ValueError('bounded prime registration')
    c.reserve(len(primes))
    for prime in primes:
        _integer(prime, 2, 1000000, 'actual bounded prime')
        for divisor in range(2, isqrt(prime)+1):
            c.charge(4)
            if prime % divisor == 0:
                raise ValueError('actual prime required')
    if primes != sorted(set(primes)):
        raise ValueError('canonical prime registration')
    p, q = obj['p'], obj['q']
    if type(p) is not int or type(q) is not int or p not in primes or q not in primes or p >= q:
        raise ValueError('ordered registered source primes')
    return p, q


def _squarefree(D, c):
    """Unsigned mask: delete multiples of EVERY integer square independently."""
    c.reserve(D+1, 1)
    mask = bytearray([1])*(D+1)
    mask[0] = 0
    for divisor in range(2, isqrt(D)+1):
        square = divisor*divisor
        for n in range(square, D+1, square):
            c.charge(2)
            mask[n] = 0
    return mask


def _ordinary_mu(D, c):
    """Independent sieve used only for the final actual-value audit."""
    c.reserve(2*(D+1), 40)
    mu, composite = [1]*(D+1), bytearray(D+1)
    mu[0] = 0
    for prime in range(2, D+1):
        c.charge()
        if composite[prime]:
            continue
        for n in range(prime, D+1, prime):
            c.charge(3)
            mu[n] = -mu[n]
            if n != prime:
                composite[n] = 1
        for n in range(prime*prime, D+1, prime*prime):
            c.charge(2)
            mu[n] = 0
    return mu


def _source(N, y, D, p, q, ratio, c):
    """Scaled truncated source, tail, full atoms, and actual pointwise jumps."""
    den, num = ratio.denominator, ratio.numerator
    c.reserve(2*(D+2), 40)
    f, g = [0]*(D+2), [0]*(D+2)
    for d in range(1, D+1):
        c.charge(24)
        Wp = 4*N//(p*d)-3*(2*N//(p*d))+2*(N//(p*d))
        Wq = 4*N//(q*d)-3*(2*N//(q*d))+2*(N//(q*d))
        if abs(Wp) > 1 or abs(Wq) > 1:
            raise ArithmeticError('elementary floor channel amplitude')
        joined = den*Wp-num*Wq
        if d <= y:
            f[d] = joined
        else:
            g[d] = -joined
    floors = {}
    for base, scale in ((p, den), (q, -num)):
        for v, a in ((4, 1), (2, -3), (1, 2)):
            Z = v*N//base
            if Z:
                floors[Z] = floors.get(Z, 0)+scale*a
                c.charge(8)
    floors = {Z: a for Z, a in floors.items() if a}
    steps = [T for T in range(1, D+1) if g[T] != g[T+1]]
    c.charge(4*D)
    return f, g, floors, steps


def _power_floor(N, theta, c):
    """Exact binary integer root, with explicit intermediate bit capacity."""
    theta = c.q(theta)
    if not 0 <= theta <= 1:
        raise ValueError('theta in closed unit interval')
    bits = N.bit_length()*max(theta.numerator, theta.denominator)
    if bits > MAX_POWER_BITS:
        raise OverflowError('exact power intermediate bit capacity')
    c.charge(3*(1+bits*max(1, bits.bit_length())))
    target = N**theta.numerator
    lo, hi = 1, N+1
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**theta.denominator <= target:
            lo = mid
        else:
            hi = mid
    return lo


def _floor_events(horizons, numerators, length, c):
    """Replay sum x_X floor(X/n) by disjoint quotient intervals and events."""
    events = {}
    for X, value in zip(horizons, numerators):
        at = 1
        while at <= min(X, length):
            quotient = X//at
            end = min(length, X//quotient)
            events[at] = events.get(at, 0)+value*quotient
            events[end+1] = events.get(end+1, 0)-value*quotient
            c.charge(24)
            at = end+1
    answer, running = [0]*(length+1), 0
    for n in range(1, length+1):
        running += events.get(n, 0)
        answer[n] = running
        c.charge(4)
    if running+events.get(length+1, 0):
        raise ArithmeticError('quotient events close')
    return answer


def _boxed_costs(k, direct, den, horizons, x, eps, z, mask, c):
    """Exact primal and box-penalized dual costs on common grid GRID."""
    length = len(k)-1
    C = 4*den*max(1, len(horizons))
    if type(x) is not list or len(x) != len(horizons):
        raise ValueError('complete primal coefficient vector')
    for value in x:
        _integer(value, -C*GRID, C*GRID, 'coefficient inside declared box')
    _integer(eps, -GRID, GRID, 'bounded unit witness')
    if type(z) is not list or len(z) != sum(mask[2:length+1]):
        raise ValueError('complete squarefree witness vector')
    for value in z:
        _integer(value, -GRID, GRID, 'bounded squarefree witness')
    replay = _floor_events(horizons, x, length, c)
    center = GRID*(direct+k[1])+sum(value*(1-X) for X, value in zip(horizons, x))
    residual = sum(abs(GRID*k[n]-replay[n]) for n in range(2, length+1) if mask[n])
    upper = c.bounded(Q(abs(center)+residual, den*GRID))
    prefix, position = [0]*(length+1), 0
    product = eps*(direct+k[1])
    for n in range(1, length+1):
        value = 0
        if n >= 2 and mask[n]:
            value = z[position]
            product += value*k[n]
            position += 1
        prefix[n] = prefix[n-1]+value
        c.charge(8)
    penalty = 0
    for X in horizons:
        total, at = 0, 2
        while at <= min(X, length):
            quotient = X//at
            end = min(length, X//quotient)
            total += quotient*(prefix[end]-prefix[at-1])
            at = end+1
            c.charge(16)
        penalty += abs(eps*(1-X)-total)
    lower = c.bounded(Q(product-C*penalty, den*GRID))
    if lower > upper:
        raise ArithmeticError('boxed weak duality')
    return dict(coefficient_box=C, center_numerator=center,
                residual_l1_numerator=residual, dual_defect_l1_numerator=penalty,
                center=Q(center, den*GRID),
                residual_l1=Q(residual, den*GRID), upper=upper, lower=lower,
                gap=upper-lower)


def _dictionary(anchors, depth, limit, c):
    """Replay distinct quotient union and equal-rank capacity selection."""
    generated = set()
    for A in anchors:
        divisor, stop = 1, min(depth, A//2)
        while divisor <= stop:
            X = A//divisor
            generated.add(X)
            divisor = A//X+1
            c.charge(8)
    full = sorted(generated)
    truncated = len(full) > limit
    if not truncated:
        horizons = full
    elif limit == 1:
        horizons = [full[-1]]
    else:
        horizons = [full[i*(len(full)-1)//(limit-1)] for i in range(limit)]
    # Enumerate the complete quotient set independently of the depth loop.
    required = set()
    for A in anchors:
        divisor = 1
        while divisor <= A//2:
            X = A//divisor
            required.add(X)
            divisor = A//X+1
            c.charge(8)
    return horizons, truncated, required <= set(horizons)


def _equal_q(obj, name, expected, c):
    if c.q(obj[name]) != c.bounded(expected):
        raise ValueError('exact floor control field '+name)


def verify_control(cert, meter=None):
    """Verify grammar, rational witnesses, all costs, and actual raw rows."""
    c = _Context(Meter() if meter is None else meter)
    _fields(cert, ('schema', 'N', 'y', 'max_j', 'parameters', 'exponent_requests',
                   'horizon_limit', 'coefficient_grid', 'endpoints',
                   'learner_mobius_signs_accessed', 'uniform_head_bound_proved', 'RH_proved'))
    if cert['schema'] != SCHEMA:
        raise ValueError('floor control schema')
    for flag in ('learner_mobius_signs_accessed', 'uniform_head_bound_proved', 'RH_proved'):
        if cert[flag] is not False:
            raise ValueError('floor control scope flag '+flag)
    p, q = _parameters(cert['parameters'], c)
    N = _integer(cert['N'], 2, MAX_N, 'bounded source scale')
    D = 4*N//p
    y = _integer(cert['y'], 1, D, 'bounded original prefix')
    max_j = _integer(cert['max_j'], 0, min(D, MAX_H), 'complete bounded row domain')
    limit = _integer(cert['horizon_limit'], 1, MAX_HORIZONS, 'bounded horizon capacity')
    _integer(cert['coefficient_grid'], GRID, GRID, 'fixed common coefficient grid')
    requests = cert['exponent_requests']
    if type(requests) is not list or not 1 <= len(requests) <= 128:
        raise ValueError('bounded nonempty exponent requests')
    depths, unique = [], set()
    for text in requests:
        depths.append(_power_floor(N, text, c))
        if text in unique:
            raise ValueError('distinct exponent requests')
        unique.add(text)
    endpoints = cert['endpoints']
    if type(endpoints) is not list or len(endpoints) != 2:
        raise ValueError('both ordered ratio endpoints required')
    sf, mu = _squarefree(D, c), _ordinary_mu(D, c)
    if any(sf[n] != abs(mu[n]) for n in range(1, D+1)):
        raise ArithmeticError('independent unsigned squarefree audit')
    c.reserve(8*(D+2), 40)  # maximum transient replay scratch, once per audit
    checked_endpoints = []
    for endpoint, ratio in zip(endpoints, (Q(p, q), Q(1))):
        _fields(endpoint, ('ratio', 'denominator', 'rows'))
        if c.q(endpoint['ratio']) != ratio:
            raise ValueError('ordered exact ratio endpoints')
        den = ratio.denominator
        _integer(endpoint['denominator'], den, den, 'reduced endpoint denominator')
        rows = endpoint['rows']
        if type(rows) is not list or len(rows) != max_j:
            raise ValueError('complete raw row domain')
        f, g, floors, _steps = _source(N, y, D, p, q, ratio, c)
        checked_rows, actual_l1, upper_l1 = [], Q(0), Q(0)
        for j, row in enumerate(rows, 1):
            _fields(row, ('j', 'direct_scaled', 'unit_kernel_scaled', 'anchors',
                          'models', 'plans', 'selected_model'))
            _integer(row['j'], j, j, 'canonical complete row order')
            length = D//j
            k = [0]+[g[j*n]-(g[(j+1)*n] if (j+1)*n <= D else 0)
                     for n in range(1, length+1)]
            c.charge(24*length)
            direct = floors.get(j, 0)
            _integer(row['direct_scaled'], direct, direct, 'actual full atom contribution')
            _integer(row['unit_kernel_scaled'], k[1], k[1], 'actual retained unit kernel')
            # Actual coalesced row indicator endpoints arise from pointwise
            # jumps of k, independent of the producer's tail-step algebra.
            anchors = [n for n in range(length, 0, -1)
                       if k[n] != (k[n+1] if n < length else 0)]
            supplied = row['anchors']
            if type(supplied) is not list or any(type(a) is not int for a in supplied) or supplied != anchors:
                raise ValueError('pointwise coalesced row endpoints')
            plans = row['plans']
            if type(plans) is not list or len(plans) != len(requests)+1:
                raise ValueError('complete grammar plans')
            dictionaries, cache = [], {}
            for plan, exponent, depth in zip(plans, [None]+requests, [0]+depths):
                _fields(plan, ('exponent', 'depth', 'model_index', 'dictionary_truncated',
                               'complete_endpoint_quotients'))
                if type(plan['exponent']) is not type(exponent) or plan['exponent'] != exponent:
                    raise ValueError('exact declared exponent order')
                _integer(plan['depth'], depth, depth, 'exact declared rational power depth')
                horizons, clipped, complete = _dictionary(anchors, depth, limit, c)
                key = tuple(horizons)
                if key not in cache:
                    cache[key] = len(dictionaries)
                    dictionaries.append(horizons)
                _integer(plan['model_index'], cache[key], cache[key], 'reuse identical realized dictionary')
                if plan['dictionary_truncated'] is not clipped:
                    raise ValueError('deterministic dictionary clipping')
                if plan['complete_endpoint_quotients'] is not complete:
                    raise ValueError('complete indicator quotient span scope')
            models = row['models']
            if type(models) is not list or len(models) != len(dictionaries):
                raise ValueError('one model per realized dictionary')
            costs = []
            for model, horizons in zip(models, dictionaries):
                _fields(model, ('horizons', 'coefficient_box', 'primal_numerators',
                                'dual_constant_numerator', 'dual_weight_numerators',
                                'center_numerator', 'residual_l1_numerator',
                                'dual_defect_l1_numerator', 'bound', 'box_optimum_lower',
                                'box_gap', 'solver'))
                actual_horizons = model['horizons']
                if type(actual_horizons) is not list or any(type(X) is not int for X in actual_horizons) or actual_horizons != horizons:
                    raise ValueError('source-bound deterministic dictionary')
                _integer(model['coefficient_box'], 4*den*max(1, len(horizons)),
                         4*den*max(1, len(horizons)), 'fixed scaled coefficient box')
                c.reserve(2*len(horizons)+sum(sf[2:length+1])+16, 64)
                cost = _boxed_costs(k, direct, den, horizons, model['primal_numerators'],
                                    model['dual_constant_numerator'],
                                    model['dual_weight_numerators'], sf, c)
                for field in ('center_numerator', 'residual_l1_numerator', 'dual_defect_l1_numerator'):
                    _integer(model[field], cost[field], cost[field], 'every exact replay numerator')
                for field, expected in (('bound', cost['upper']),
                                        ('box_optimum_lower', cost['lower']), ('box_gap', cost['gap'])):
                    _equal_q(model, field, expected, c)
                solver = model['solver']
                _fields(solver, ('status', 'iterations', 'message'))
                allowed = ('empty_dictionary_exact',) if not horizons else (
                    'optimal_float_proposal', 'failed_zero_fallback')
                if solver['status'] not in allowed or type(solver['status']) is not str:
                    raise ValueError('bounded proposal status metadata')
                _integer(solver['iterations'], 0, 300_000_000_000, 'bounded proposal iteration metadata')
                if type(solver['message']) is not str or len(solver['message']) > 10000:
                    raise ValueError('bounded proposal message metadata')
                if not horizons and (solver['iterations'] != 0 or solver['message'] != ''):
                    raise ValueError('empty dictionary proposal metadata')
                costs.append(cost)
            selected = min(range(len(models)), key=lambda i: (costs[i]['upper'],
                sum(v != 0 for v in models[i]['primal_numerators']), len(dictionaries[i]), i))
            _integer(row['selected_model'], selected, selected, 'declared deterministic selection')
            signed = direct+sum(mu[n]*k[n] for n in range(1, length+1))
            raw = sum(mu[n]*(f[j*n]-(f[(j+1)*n] if (j+1)*n <= D else 0))
                      for n in range(1, length+1))
            c.charge(24*length)
            if signed != raw:
                raise ArithmeticError('original source raw inverse identity')
            actual = Q(raw, den)
            if any(abs(actual) > cost['upper'] for cost in costs):
                raise ArithmeticError('actual raw coefficient exceeds certified upper')
            actual_l1 += abs(actual)
            upper_l1 += costs[selected]['upper']
            checked_rows.append(dict(j=j, actual_coefficient=str(actual),
                selected_bound=str(costs[selected]['upper']), selected_model=selected,
                models=[dict(bound=str(cost['upper']), box_optimum_lower=str(cost['lower']),
                             box_gap=str(cost['gap'])) for cost in costs]))
        checked_endpoints.append(dict(ratio=str(ratio), denominator=den, rows=checked_rows,
            actual_head_variation=str(actual_l1), selected_head_upper=str(upper_l1)))
    return dict(verified=True, schema='verified-'+SCHEMA, N=N, y=y, max_j=max_j, D=D,
        parameters=cert['parameters'], endpoints=checked_endpoints,
        grammar_before_scores_independently_verified=True,
        quotient_block_primal_replay=True, exact_boxed_dual_replay=True,
        ordinary_mu_unit_retained=True, squareful_mu_zero_retained=True,
        original_source_inverse_identity_proved=True,
        independent_parent_source_admission_required=True, original_source_binding_proved=False,
        learner_mobius_signs_accessed=False, checker_actual_mobius_signs_evaluated=True,
        raw_head_only=True, arithmetic_query_horizon=D,
        uniform_head_bound_proved=False, uniform_N_growth_proved=False,
        whole_signed_target_bound_proved=False, RH_proved=False,
        charged_work_units=c.work, prospective_peak_storage_bytes=c.storage)


verify_floor_control = verify_control
