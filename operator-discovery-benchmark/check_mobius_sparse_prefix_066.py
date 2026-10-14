"""Independent exact sparse prefix inverse for ordinary Mobius arithmetic.

Only synthetic/supplied certificates are read. The six full floor atoms are
contracted using mu*One=delta_1; tail steps retain actual ordinary mu, including
the unit and squareful zero values. This proves raw short rows, not a repaired
inverse or a growth bound for the full scientific target.
"""
from fractions import Fraction as Q
from math import isqrt
from check_fractional_prime_rh_bridge_052 import Meter

MAX_N = 65536
MAX_H = 4096
MAX_BITS = 4096
MAX_ENTRIES = 900000
MAX_MEMORY_BYTES = 512 * 1024 * 1024
MAX_WORK = 500000000
SCHEMA = 'mobius-sparse-prefix-inverse-v1'


class _Context:
    def __init__(self, meter):
        self.m = meter
        self.work = 0
        self.entries = 0
        self.storage = 8192

    def charge(self, n=1):
        if type(n) is not int or n < 0 or n > MAX_WORK-self.work:
            raise OverflowError('sparse prefix independent work cap')
        self.work += n
        self.m.charge(n)

    def reserve(self, n, size=512):
        self.charge(n)
        self.entries += n
        self.storage += n*size
        if self.entries > MAX_ENTRIES:
            raise OverflowError('sparse prefix entry capacity')
        if self.storage > MAX_MEMORY_BYTES:
            raise MemoryError('sparse prefix prospective storage cap')

    def bounded(self, value):
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        self.charge(1+bits)
        if bits > MAX_BITS:
            raise OverflowError('sparse prefix rational intermediate capacity')
        return value

    def q(self, value):
        if type(value) is not str or not 1 <= len(value) <= 2500:
            raise ValueError('canonical bounded rational text')
        self.charge(len(value)+1)
        try:
            result = Q(value)
        except (ValueError, ZeroDivisionError):
            raise ValueError('rational text') from None
        if str(result) != value:
            raise ValueError('canonical rational required')
        return self.bounded(result)

    def add(self, a, b):
        return self.bounded(a+b)

    def mul(self, a, b):
        a, b = Q(a), Q(b)
        self.charge(1+max(abs(a.numerator).bit_length(), a.denominator.bit_length()) *
                    max(abs(b.numerator).bit_length(), b.denominator.bit_length()))
        return self.bounded(a*b)


def _fields(obj, names):
    if type(obj) is not dict or set(obj) != set(names):
        raise ValueError('exact sparse prefix schema')


def _integer(value, lo, hi, description):
    if type(value) is not int or not lo <= value <= hi:
        raise ValueError(description)
    return value


def _parameters(obj, c):
    if type(obj) is not dict or set(obj) not in (
            {'primes', 'p', 'q', 'alpha', 'gamma'},
            {'primes', 'p', 'q', 'alpha', 'gamma', 'tau'}):
        raise ValueError('source parameter schema with optional tau')
    alpha, gamma = (c.q(obj[k]) for k in ('alpha', 'gamma'))
    if not 0 < alpha < 1 or gamma <= 0:
        raise ValueError('fixed fractional source gates')
    if 'tau' in obj and not 0 < c.q(obj['tau']) < 1:
        raise ValueError('fractional tau gate')
    primes = obj['primes']
    if type(primes) is not list or not 2 <= len(primes) <= 8:
        raise ValueError('bounded registered prime mask')
    c.reserve(len(primes))
    for prime in primes:
        _integer(prime, 2, 1000000, 'bounded actual prime')
        for divisor in range(2, isqrt(prime)+1):
            c.charge(4)
            if prime % divisor == 0:
                raise ValueError('actual prime required')
    if primes != sorted(set(primes)):
        raise ValueError('canonical ascending prime mask')
    p, q = obj['p'], obj['q']
    if type(p) is not int or type(q) is not int or p not in primes or q not in primes or p >= q:
        raise ValueError('ordered source primes in registered mask')
    return p, q


def _add(mapping, key, value, c):
    if key not in mapping:
        c.reserve(1)
    mapping[key] = c.add(mapping.get(key, Q(0)), value)


def _source_atoms(N, y, p, q, ratio, c):
    """Direct i enumeration, without the producer's quotient grouping."""
    floors, steps = {}, {}
    for base, scale in ((p, Q(1)), (q, -ratio)):
        for v, a in ((4, 1), (2, -3), (1, 2)):
            horizon = v*N//base
            coefficient = c.mul(scale, a)
            if horizon:
                _add(floors, horizon, coefficient, c)
            for i in range(1, horizon//(y+1)+1):
                c.charge(4)
                tail = horizon//i
                if tail <= y:
                    raise ArithmeticError('tail threshold must exceed prefix')
                _add(steps, tail, -coefficient, c)
                _add(steps, y, coefficient, c)
    return ({k: a for k, a in floors.items() if a},
            {k: a for k, a in steps.items() if a})


def _atoms(items, D, c):
    if type(items) is not list or len(items) > D:
        raise ValueError('bounded atom list')
    c.reserve(len(items))
    output, last = {}, 0
    for atom in items:
        _fields(atom, ('horizon', 'coefficient'))
        horizon = _integer(atom['horizon'], 1, D, 'positive bounded atom horizon')
        coefficient = c.q(atom['coefficient'])
        if horizon <= last or not coefficient:
            raise ValueError('nonzero sorted coalesced atoms')
        output[horizon] = coefficient
        last = horizon
    return output


def _ordinary_mu(D, c):
    """Eratosthenes sign sieve; no factor/multiplicative-character library."""
    c.reserve(3*(D+1), 40)
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
        square = prime*prime
        for n in range(square, D+1, square):
            c.charge(2)
            mu[n] = 0
    prefix = [0]*(D+1)
    for n in range(1, D+1):
        c.charge(2)
        prefix[n] = prefix[n-1]+mu[n]
    return mu, prefix


def _source_channels(N, y, p, q, c):
    c.reserve(2*(y+1), 40)
    channels = []
    for base in (p, q):
        values = [0]*(y+1)
        for d in range(1, y+1):
            c.charge(12)
            values[d] = 4*N//(base*d)-3*(2*N//(base*d))+2*(N//(base*d))
        channels.append(values)
    return channels


def _raw_inverse(j, y, channels, mu, ratio, c):
    totals = [0, 0]
    for n in range(1, y//j+1):
        c.charge(12)
        if not mu[n]:
            continue
        d, e = j*n, (j+1)*n
        for k, values in enumerate(channels):
            totals[k] += mu[n]*(values[d]-(values[e] if e <= y else 0))
    return c.add(Q(totals[0]), -c.mul(ratio, totals[1]))


def _row_kernel(j, steps, c):
    """Signed integer interval sweep, independent from producer grouping."""
    events = {}
    for horizon, coefficient in steps.items():
        c.charge(5)
        lo, hi = horizon//(j+1)+1, horizon//j
        if lo <= hi:
            _add(events, lo, coefficient, c)
            _add(events, hi+1, -coefficient, c)
    segments, active, previous = [], Q(0), None
    c.charge(len(events)*max(1, len(events).bit_length()))
    for position in sorted(events):
        c.charge(2)
        if previous is not None and previous < position and active:
            lo, hi = previous, position-1
            if segments and segments[-1][1]+1 == lo and segments[-1][2] == active:
                segments[-1] = (segments[-1][0], hi, active)
            else:
                c.reserve(1)
                segments.append((lo, hi, active))
        active = c.add(active, events[position])
        previous = position
    if active:
        raise ArithmeticError('interval sweep must close')
    return segments


def _segments(items, D, c):
    if type(items) is not list or len(items) > D:
        raise ValueError('bounded row segments')
    c.reserve(len(items))
    result, last, previous_coefficient = [], 0, None
    for segment in items:
        _fields(segment, ('lo', 'hi', 'coefficient'))
        lo = _integer(segment['lo'], 1, D, 'positive bounded interval start')
        hi = _integer(segment['hi'], lo, D, 'ordered bounded interval end')
        coefficient = c.q(segment['coefficient'])
        if not coefficient or lo <= last or (lo == last+1 and coefficient == previous_coefficient):
            raise ValueError('maximal disjoint nonzero signed intervals')
        result.append((lo, hi, coefficient))
        last, previous_coefficient = hi, coefficient
    return result


def verify_sparse(cert, meter=None):
    """Verify the complete finite certificate and the schema's tail rule."""
    c = _Context(Meter(cap=MAX_WORK) if meter is None else meter)
    _fields(cert, ('schema', 'parameters', 'N', 'y', 'H', 'endpoints'))
    if cert['schema'] != SCHEMA:
        raise ValueError('sparse prefix certificate schema')
    p, q = _parameters(cert['parameters'], c)
    N = _integer(cert['N'], 2, MAX_N, 'bounded source scale')
    D = 4*N//p
    if D < 1:
        raise ValueError('nonempty arithmetic horizon')
    y = _integer(cert['y'], 1, D, 'prefix inside full arithmetic horizon')
    H = _integer(cert['H'], 1, min(D, MAX_H), 'bounded complete short inverse horizon')
    endpoints = cert['endpoints']
    if type(endpoints) is not list or len(endpoints) != 2:
        raise ValueError('both source ratio endpoints required')
    mu, mertens = _ordinary_mu(D, c)
    channels = _source_channels(N, y, p, q, c)
    outputs = []
    for endpoint, expected_ratio in zip(endpoints, (Q(p, q), Q(1))):
        _fields(endpoint, ('ratio', 'floors', 'steps', 'rows', 'step_first_moment',
                          'floor_l1', 'coefficient_l1', 'tail_bounds'))
        ratio = c.q(endpoint['ratio'])
        if ratio != expected_ratio:
            raise ValueError('fixed p/q and unit ratio endpoints')
        floors, steps = _source_atoms(N, y, p, q, ratio, c)
        if _atoms(endpoint['floors'], D, c) != floors or _atoms(endpoint['steps'], D, c) != steps:
            raise ValueError('complete exact signed source rewrite atoms')
        floor_l1 = Q(0)
        moment = Q(0)
        for value in floors.values():
            floor_l1 = c.add(floor_l1, abs(value))
        for horizon, value in steps.items():
            moment = c.add(moment, c.mul(abs(value), horizon))
        if c.q(endpoint['floor_l1']) != floor_l1 or c.q(endpoint['step_first_moment']) != moment:
            raise ValueError('exact coalesced floor mass and absolute step first moment')
        rows = endpoint['rows']
        if type(rows) is not list or len(rows) != H:
            raise ValueError('complete ascending raw short rows required')
        costs, variations = [], []
        for j, row in enumerate(rows, 1):
            c.reserve(1)
            _fields(row, ('j', 'direct', 'segments', 'coefficient', 'interval_l1'))
            if type(row['j']) is not int or row['j'] != j:
                raise ValueError('ascending complete row indices including unit')
            direct = floors.get(j, Q(0))
            if c.q(row['direct']) != direct:
                raise ValueError('full floor mu*One delta contraction')
            segments = _row_kernel(j, steps, c)
            if _segments(row['segments'], D, c) != segments:
                raise ValueError('exact signed coalesced row interval kernel')
            coefficient, cost = direct, abs(direct)
            for lo, hi, value in segments:
                coefficient = c.add(coefficient, c.mul(value, mertens[hi]-mertens[lo-1]))
                cost = c.add(cost, c.mul(abs(value), hi-lo+1))
            if c.q(row['coefficient']) != coefficient or c.q(row['interval_l1']) != cost:
                raise ValueError('ordinary mu coefficient and joined interval L1')
            if coefficient != _raw_inverse(j, y, channels, mu, ratio, c):
                raise ValueError('independent original prefix raw inverse identity')
            costs.append(cost)
            variations.append(abs(coefficient))
        coefficient_l1 = sum(variations, Q(0))
        c.bounded(coefficient_l1)
        if c.q(endpoint['coefficient_l1']) != coefficient_l1:
            raise ValueError('complete raw short coefficient variation')
        tails = endpoint['tail_bounds']
        if type(tails) is not list or len(tails) != H:
            raise ValueError('complete tail coverage J=1..H required')
        c.reserve(2*H)
        joined = [Q(0)]*(H+1)
        actual = [Q(0)]*(H+1)
        for k in range(H-1, -1, -1):
            joined[k] = c.add(joined[k+1], costs[k])
            actual[k] = c.add(actual[k+1], variations[k])
        checked_tails = []
        for J, tail in enumerate(tails, 1):
            _fields(tail, ('J', 'H', 'joined_interval_upper', 'coarse_upper', 'actual_variation'))
            if type(tail['J']) is not int or tail['J'] != J or type(tail['H']) is not int or tail['H'] != H:
                raise ValueError('complete exact tail interval')
            coarse = sum((abs(a) for Z, a in floors.items() if J <= Z <= H), Q(0))
            for T, a in steps.items():
                c.charge(4)
                coarse = c.add(coarse, c.mul(abs(a), T//J-T//(H+1)))
            for name, value in (('joined_interval_upper', joined[J-1]),
                                ('coarse_upper', coarse), ('actual_variation', actual[J-1])):
                if c.q(tail[name]) != value:
                    raise ValueError('exact complete tail aggregate '+name)
            universal = c.add(floor_l1, c.bounded(moment/J))
            if not actual[J-1] <= joined[J-1] <= coarse <= universal:
                raise ArithmeticError('joined/telescoping/first-moment tail inequality')
            checked_tails.append(dict(J=J, H=H, joined_interval_upper=str(joined[J-1]),
                                      coarse_upper=str(coarse), actual_variation=str(actual[J-1])))
        outputs.append(dict(ratio=str(ratio), floor_atom_count=len(floors), step_atom_count=len(steps),
                            floor_l1=str(floor_l1), step_first_moment=str(moment),
                            coefficient_l1=str(coefficient_l1), joined_interval_l1=str(joined[0]),
                            tail_bounds=checked_tails))
    return dict(verified=True, schema='verified-'+SCHEMA, parameters=cert['parameters'],
                N=N, y=y, H=H, D=D, endpoints=outputs,
                budget=str(max(Q(e['joined_interval_l1']) for e in outputs)),
                coefficient_l1=str(max(Q(e['coefficient_l1']) for e in outputs)),
                source_rewrite_proved=True, actual_mobius_inverse_identity_proved=True,
                raw_short_only=True, ordinary_mu_unit_retained=True, squareful_mu_zero_retained=True,
                endpoint_convexity_proved=True, uniform_tail_rule_reviewed=True,
                uniform_tail_rule='For every 1<=J<=H: sum_(j=J..H)|c_j| <= floor_l1 + step_first_moment/J',
                moment_rule='M1 <= 12*(1/p+r/q)*N*(2+log(max(1,D/(y+1))))',
                moment_rule_method='triangle inequality before coalescing; harmonic sum over each atom tail index',
                arithmetic_query_horizon=D, original_sqrt_radius_preserved=False,
                source_binding_condition='The SAME 063 raw source admission must independently bind this prefix; repaired core_inverse is not accepted here',
                independent_parent_063_admission_required=True, original_source_binding_proved=False,
                uniform_full_variation_proved=False, uniform_N_growth_proved=False,
                whole_signed_target_bound_proved=False, RH_proved=False,
                scientific_source_or_LP_evaluated=False,
                charged_work_units=c.work, prospective_peak_storage_bytes=c.storage)
