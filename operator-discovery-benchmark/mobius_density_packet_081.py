"""Invent growing, exactly density-balanced signed arithmetic pair packets.

The complete source energy drift is retained.  A uniform bound for its
extracted packet never silently becomes a bound for the unlinked remainder.
Producer uses integer event sweeps; independent checker uses max denominators.
"""
from collections import OrderedDict
from fractions import Fraction as Q
from itertools import product
from math import gcd, lcm
import random

import numpy as np

import mobius_symbolic_cover_080 as OLD

Meter = OLD.OLD.P.F.S.Meter
MAX_LABEL = 1024
MAX_PAIRS = 200000
MAX_OMEGA_HORIZON = 1000000
MAX_CACHE_BYTES = 128*1024**2


def rational(value):
    return OLD.OLD.P.F.S.B.rational(value)


def bounded(value):
    if max(value.numerator.bit_length(), value.denominator.bit_length()) > 4096:
        raise ValueError('rational intermediate bit gate')
    return value


def common_denominator(values):
    result = 1
    for value in values:
        result = lcm(result, value.denominator)
        if result.bit_length() > 4096:
            raise ValueError('common denominator bit gate')
    return result


def parse(program):
    keys = {'schema', 'kernel', 'memory', 'rays', 'drift_multiplier', 'epsilon', 'eta', 'q'}
    if type(program) is not dict or set(program) != keys or program['schema'] != 'growing-density-packet-v1':
        raise ValueError('exact density packet schema')
    depth = program['memory']
    if type(depth) is not int or not 1 <= depth <= 3:
        raise ValueError('memory domain')
    if type(program['kernel']) is not list or not 1 <= len(program['kernel']) <= 128:
        raise ValueError('prefix kernel budget')
    kernel = {}
    for row in program['kernel']:
        if type(row) is not dict or set(row) != {'divisor', 'weight'}:
            raise ValueError('prefix kernel row')
        d, value = row['divisor'], rational(row['weight'])
        if type(d) is not int or not 1 <= d <= 10**12 or not value or d in kernel:
            raise ValueError('canonical prefix kernel')
        kernel[d] = value
    if list(kernel) != sorted(kernel):
        raise ValueError('ordered prefix kernel')
    if type(program['rays']) is not list or len(program['rays']) > 10000:
        raise ValueError('ray budget')
    rays = []
    for row in program['rays']:
        if type(row) is not dict or set(row) != {'a', 'weight'} or type(row['a']) is not list or len(row['a']) != depth:
            raise ValueError('memory ray')
        weight = rational(row['weight'])
        if weight <= 0:
            raise ValueError('positive Gram weight')
        rays.append((tuple(map(rational, row['a'])), weight))
    r, eps, eta, q = (rational(program[k]) for k in ('drift_multiplier', 'epsilon', 'eta', 'q'))
    if not 1 <= r <= 2 or not 0 < eps <= 1 or not 0 < eta <= 1 or not 1 <= q < 2:
        raise ValueError('drift/exponent domain')
    return dict(kernel=kernel, memory=depth, rays=rays, drift_multiplier=r, epsilon=eps, eta=eta, q=q)


def matrices(parsed):
    depth = parsed['memory']
    H = [[Q(int(i == j == 0)) for j in range(depth)] for i in range(depth)]
    for a, weight in parsed['rays']:
        for i in range(depth):
            for j in range(depth):
                H[i][j] = bounded(H[i][j]+bounded(weight*a[i]*a[j]))
    T = [[Q(0) for _ in range(depth+1)] for _ in range(depth+1)]
    for i in range(depth):
        for j in range(depth):
            T[i][j] += H[i][j]
            T[i+1][j+1] = bounded(T[i+1][j+1]-parsed['drift_multiplier']*H[i][j])
    return H, T


def ceil24(value):
    return Q(-((-value.numerator*2**24)//value.denominator), 2**24)


_OMEGA = {}


def omega_price(epsilon, meter=None):
    """Exact finite exceptional-prime product; no exponent whitelist."""
    meter = meter or Meter()
    eps = Q(epsilon)
    if not 0 < eps <= 1:
        raise ValueError('positive epsilon at most one')
    if eps in _OMEGA:
        meter.charge(1)
        return _OMEGA[eps]
    if eps.denominator > 100000 or eps.numerator > 100000:
        raise ValueError('omega power bit/work gate')
    horizon = int(OLD.OLD.P.F.S.B.fmpz(2**eps.denominator).root(eps.numerator))
    if horizon > MAX_OMEGA_HORIZON:
        raise MemoryError('omega prime horizon exceeds1000000')
    meter.reserve(64*(horizon+1)+4096)
    composite = bytearray(horizon+1)
    price, primes = Q(1), []
    target = 2**eps.denominator
    for p in range(2, horizon+1):
        if composite[p]:
            continue
        if p*p <= horizon:
            length = (horizon-p*p)//p+1
            composite[p*p:horizon+1:p] = b'\1'*length
            meter.charge(length)
        if p**eps.numerator >= target:
            continue
        lower, _ = OLD.OLD.P.positive_power_bounds(p, str(eps))
        price = ceil24(price*2/lower)
        if max(price.numerator.bit_length(), price.denominator.bit_length()) > 4096:
            raise ValueError('omega rational bit gate')
        primes.append(p)
    meter.charge((horizon+1)*1000)
    _OMEGA[eps] = dict(price=price, primes=primes, horizon=horizon)
    return _OMEGA[eps]


def bound_certificate(program, meter=None):
    meter = meter or Meter()
    p = parse(program)
    _, T = matrices(p)
    omega = omega_price(p['epsilon'], meter)
    jump = 2*sum((abs(t) for row in T for t in row), Q(0))*sum(map(abs, p['kernel'].values()), Q(0))**2
    exponent = Q(1, 2)+p['eta']*(Q(3, 2)+2*p['epsilon'])
    return dict(omega_price=str(omega['price']), jump_price=str(jump),
        constant=str(jump*(omega['price']+2)), exponent=str(exponent))


def integer_matrix(T):
    denominator = common_denominator(v for row in T for v in row)
    return [[int(v*denominator) for v in row] for row in T], denominator


def pair_kernel(parsed, a, b, meter=None, prepared=None):
    """Prefix jumps from simultaneous endpoint events, using integer algebra."""
    meter = meter or Meter()
    if type(a) is not int or type(b) is not int or not 1 <= a < b <= MAX_LABEL or gcd(a, b) != 1:
        raise ValueError('canonical reduced ratio')
    if prepared is None:
        _, T = matrices(parsed)
        A, td = integer_matrix(T)
        kd = common_denominator(parsed['kernel'].values())
        kernel = {d: int(v*kd) for d, v in parsed['kernel'].items()}
    else:
        A, td, kd, kernel = prepared
    dimension = len(A)
    events = {}
    for i in range(dimension):
        for d, value in kernel.items():
            events.setdefault(a*2**i*d, []).append((0, i, value))
            events.setdefault(b*2**i*d, []).append((1, i, value))
    meter.reserve(4096+1024*len(events))
    meter.charge(100*dimension**2*(1+len(events)))
    left, right = [0]*dimension, [0]*dimension
    last, jumps = 0, []
    denominator = td*kd*kd
    for d in sorted(events):
        for side, i, value in events[d]:
            (left if side == 0 else right)[i] += value
        current = 2*sum(left[i]*A[i][j]*right[j] for i in range(dimension) for j in range(dimension))
        if current != last:
            jumps.append((d, bounded(Q(current-last, denominator))))
        last = current
    return tuple(jumps)


class Arithmetic:
    """Compact linear sieve plus bounded LRU squarefree-coprime positions."""
    def __init__(self, horizon, meter=None):
        self.meter = meter or Meter()
        self.source = OLD.OLD.P.Arithmetic(horizon, self.meter)
        self.horizon = horizon
        self.prefix = np.cumsum(self.source.mu, dtype=np.int64)
        self.cache = OrderedDict()
        self.cache_bytes = 0

    def factors(self, n):
        values = []
        while n > 1:
            p = int(self.source.least[n])
            values.append(p)
            while n % p == 0:
                n //= p
        return tuple(values)

    def residual(self, kernel, u):
        if u < 0 or u//min(kernel) > self.horizon:
            raise ValueError('source prefix domain')
        self.meter.charge(100*len(kernel))
        return sum((v*int(self.prefix[u//d]) for d, v in kernel.items()), Q(0))

    def counts(self, primes, xs):
        high = max(xs, default=0)
        if high < 0 or high > self.horizon:
            raise ValueError('squarefree count horizon')
        key = tuple(sorted(primes))
        old = self.cache.pop(key, None)
        if old is None or old[0] < high:
            if old is not None:
                self.cache_bytes -= old[1].nbytes
            self.meter.reserve(128*(self.horizon+1)+32*1024**2+self.cache_bytes+32*(high+1))
            positions = np.flatnonzero(self.source.mu[:high+1]).astype(np.int32)
            for p in key:
                positions = positions[positions % p != 0]
            self.meter.charge((30+10*len(key))*(high+1))
            while self.cache and self.cache_bytes+positions.nbytes > MAX_CACHE_BYTES:
                _, removed = self.cache.popitem(last=False)
                self.cache_bytes -= removed[1].nbytes
            old = (high, positions)
            if positions.nbytes <= MAX_CACHE_BYTES:
                self.cache_bytes += positions.nbytes
            else:
                self.meter.charge(100*(1+len(xs)))
                return [int(n) for n in np.searchsorted(positions, xs, side='right')]
        self.cache[key] = old
        self.meter.charge(100*(1+len(xs)))
        return [int(n) for n in np.searchsorted(old[1], xs, side='right')]


class PairBank:
    """A structural energy bank, shared by every epsilon/eta proof schedule."""
    def __init__(self, program, max_D, arithmetic, meter=None):
        self.p = parse(program)
        self.H, self.T = matrices(self.p)
        self.meter = meter or arithmetic.meter
        if type(max_D) is not int or not 1 <= max_D <= min(MAX_LABEL, arithmetic.horizon):
            raise ValueError('prospective label horizon')
        if max_D*(max_D-1)//2 > MAX_PAIRS:
            raise MemoryError('prospective pair count gate')
        A, td = integer_matrix(self.T)
        kd = common_denominator(self.p['kernel'].values())
        integer_kernel = {d: int(v*kd) for d, v in self.p['kernel'].items()}
        prepared = A, td, kd, integer_kernel
        integer_bits = max(abs(x).bit_length() for row in A for x in row)+2*max(abs(x).bit_length() for x in integer_kernel.values())+16
        per_pair = 2048+2*len(A)*len(integer_kernel)*(256+4*((integer_bits+td.bit_length()+2*kd.bit_length()+7)//8))
        self.meter.reserve(128*(arithmetic.horizon+1)+max_D*(max_D-1)//2*per_pair+32*1024**2)
        self.max_D, self.arithmetic = max_D, arithmetic
        self.rows = {b: [] for b in range(2, max_D+1)}
        self.stats = {1: (Q(0), Q(0), 0, 0, 0, 0, 0)}
        positive, negative, count, nonzero, pc, nc, zc = Q(0), Q(0), 0, 0, 0, 0, 0
        for b in range(2, max_D+1):
            if arithmetic.source.mu[b]:
                for a in range(1, b):
                    if not arithmetic.source.mu[a] or gcd(a, b) != 1:
                        continue
                    sign = int(arithmetic.source.mu[a])*int(arithmetic.source.mu[b])
                    primes = tuple(sorted(arithmetic.factors(a)+arithmetic.factors(b)))
                    jumps = pair_kernel(self.p, a, b, self.meter, prepared)
                    integral = sum((v/d for d, v in jumps), Q(0))
                    density = Q(sign)
                    for p in primes:
                        density *= Q(p, p+1)
                    v = bounded(density*integral)
                    self.rows[b].append(dict(a=a, b=b, primes=primes, sign=sign, kernel=jumps, density=v))
                    count += 1
                    nonzero += bool(jumps)
                    if v > 0:
                        positive = bounded(positive+v)
                        pc += bool(jumps)
                    elif v < 0:
                        negative = bounded(negative-v)
                        nc += bool(jumps)
                    else:
                        zc += bool(jumps)
            self.stats[b] = (positive, negative, count, nonzero, pc, nc, zc)
        self.cache = {}

    def packet_values(self, u, Ds):
        Ds = sorted(set(Ds))
        if type(u) is not int or u < 1 or not Ds or not 1 <= Ds[0] <= Ds[-1] <= self.max_D:
            raise ValueError('packet evaluation domain')
        # Evaluate each pair just once at a parent; every schedule reuses it.
        old = self.cache.get(u)
        if old is not None and max(Ds) <= old[0]:
            return {D: old[1][D] for D in Ds}
        positive, negative, zero = Q(0), Q(0), Q(0)
        values = {1: dict(packet=Q(0), weighted_density=Q(0), weighted_pairs=0)}
        for b in range(2, max(Ds)+1):
            for row in self.rows[b]:
                jumps = row['kernel']
                counts = self.arithmetic.counts(row['primes'], [u//d for d, _ in jumps])
                value = row['sign']*sum((c*v for c, (_, v) in zip(counts, jumps)), Q(0))
                if row['density'] > 0:
                    positive += value
                elif row['density'] < 0:
                    negative += value
                else:
                    zero += value
            P, N, _, _, pc, nc, zc = self.stats[b]
            wp = min(Q(1), N/P) if P else Q(0)
            wn = min(Q(1), P/N) if N else Q(0)
            values[b] = dict(packet=bounded(wp*positive+wn*negative+zero),
                weighted_density=wp*P-wn*N, weighted_pairs=int(wp > 0)*pc+int(wn > 0)*nc+zc)
        self.cache[u] = (max(Ds), values)
        return {D: values[D] for D in Ds}

    def state(self, u):
        x = [self.arithmetic.residual(self.p['kernel'], u//2**j) for j in range(self.p['memory']+1)]
        depth = self.p['memory']
        energy = sum((self.H[i][j]*x[i]*x[j] for i in range(depth) for j in range(depth)), Q(0))
        half = sum((self.H[i][j]*x[i+1]*x[j+1] for i in range(depth) for j in range(depth)), Q(0))
        return x, energy, half, energy-self.p['drift_multiplier']*half

    def finite_certificate(self, program, u):
        p = parse(program)
        if any(p[k] != self.p[k] for k in ('kernel', 'memory', 'rays', 'drift_multiplier')):
            raise ValueError('bank program binding')
        D = OLD.floor_power(u, program['eta'])
        value = self.packet_values(u, [D])[D]
        P, N, count, nonzero, _, _, _ = self.stats[D]
        x, energy, half, drift = self.state(u)
        return dict(D=D, pair_count=count, positive_mass=str(P), negative_mass=str(N),
            weighted_density=str(value['weighted_density']), packet=str(value['packet']),
            energy=str(energy), half_energy=str(half), drift=str(drift),
            unlinked=str(drift-value['packet']), state=list(map(str, x)),
            nonzero_pairs=nonzero, weighted_pairs=value['weighted_pairs'])

    def witness(self, D):
        """Two nonzero density signs witness actual balancing before mu data."""
        result = {}
        for b in range(2, D+1):
            for row in self.rows[b]:
                label = 'positive' if row['density'] > 0 else 'negative' if row['density'] < 0 else 'zero'
                if row['kernel'] and label not in result:
                    result[label] = dict(a=row['a'], b=b, density=str(row['density']),
                        kernel=[dict(divisor=d, weight=str(v)) for d, v in row['kernel']])
        return result


def energy_grammar():
    """Small declared first pilot, not a language restriction on rational rays."""
    result = [dict(memory=1, rays=[], kind='baseline')]
    for depth in (2, 3):
        rows = [(Q(1),)+tail for tail in product((Q(-1), Q(0), Q(1)), repeat=depth-1)
                if tail[-1]]  # exclude zero-padded copies of shorter memories
        for a in rows:
            for weight in (Q(1, 4), Q(1)):
                result.append(dict(memory=depth, rays=[dict(a=list(map(str, a)), weight=str(weight))], kind='memory_cross_term'))
    for index, row in enumerate(result):
        row['index'] = index
    return result


def proof_schedules(max_denominator=8, fractions=('1/2', '3/4', '1'), q='1'):
    """Solve the symbolic exponent obligation to propose growing rosters."""
    epsilons = sorted({Q(a, b) for b in range(1, max_denominator+1) for a in range(1, b+1)
                       if Q(1, 8) <= Q(a, b) <= Q(1, 2)})
    return [dict(epsilon=str(eps), eta=str(Q(f)*(Q(q)-Q(1, 2))/(Q(3, 2)+2*eps)), q=q)
            for eps in epsilons for f in fractions]


def validation_draw(etas, known, seed=20261011081, maximum=5242880, per_band=3):
    """Draw only after program freeze; preserve every rejection and boundary."""
    rng = random.Random(seed)
    draws = []
    for level in range(14, maximum.bit_length()):
        low, high = 1 << level, min(maximum, (1 << (level+1))-1)
        if low <= high:
            for _ in range(per_band):
                draws.append(dict(u=rng.randint(low, high), kind='irregular', level=level))
    # Each selected exponent gets one interior exact ratio-entry boundary.
    for eta in sorted(set(map(Q, etas))):
        Dmax = OLD.floor_power(maximum, str(eta))
        b = max(2, Dmax//2)
        target = b**eta.denominator
        boundary = int(OLD.OLD.P.F.S.B.fmpz(target).root(eta.numerator))
        if boundary**eta.numerator < target:
            boundary += 1
        for delta in (-1, 0, 1):
            draws.append(dict(u=boundary+delta, kind='ratio_entry', eta=str(eta), label=b, boundary=boundary))
    occupied, admitted = set(known), []
    for row in draws:
        u = row['u']
        if not 1 <= u <= maximum:
            row['status'] = 'OUTSIDE_DOMAIN'
        elif u in occupied:
            row['status'] = 'PREVIOUSLY_KNOWN_OR_DUPLICATE'
        else:
            row['status'] = 'ACCEPTED'
            admitted.append(u)
            occupied.add(u)
    return dict(seed=seed, parents=sorted(admitted), draws=draws, drawn_after_formula_freeze=True,
        new_arithmetic_horizon=False, all_ratio_entry_boundaries_covered=False)
