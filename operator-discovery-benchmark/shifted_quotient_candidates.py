"""Complete signed shifted-quotient products; finite evidence only.

H_b(s) = (zeta(s+b)/zeta(s)-1)/b.  Programs multiply distinct H_b by
Dirichlet convolution.  Every real-pole main term and every coefficient
is retained.  The numerical evaluator does not assert a uniform bound.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import isqrt
import time

from flint import arb, ctx

SHIFTS = ['1/6', '1/3', '1/2', '2/3', '5/6']
SOURCES = ['mu', 'one', 'partial_prime_13']
MAX_HORIZON = 262143
FLAGS = dict(uniform_signed_bound_proved=False, RH_proved=False,
             finite_prefix_inverse_claimed=False, historical_novelty_claimed=False)


class Meter:
    def __init__(self, cap=300000000, seconds=7200):
        self.cap = cap
        self.operations = 0
        self.peak_cells = 0
        self.deadline = time.monotonic() + seconds

    def charge(self, n=1):
        if type(n) is not int or n < 0:
            raise ValueError('nonnegative integer work charge')
        if n > self.cap - self.operations:
            raise OverflowError('study operation cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('study runtime cap')

    def live(self, cells):
        self.charge()
        self.peak_cells = max(self.peak_cells, cells)
        if cells > 6000000:
            raise MemoryError('six million live scalar cells')

    def counts(self):
        return dict(operations=self.operations, peak_cells=self.peak_cells)


def validate(program):
    if type(program) is not dict or set(program) != {'shifts'}:
        raise ValueError('shifts-only program')
    items = program['shifts']
    if type(items) is not list or not 1 <= len(items) <= 3:
        raise ValueError('one through three distinct shifts')
    values = []
    for item in items:
        if type(item) is not str or not 1 <= len(item) <= 32:
            raise ValueError('bounded rational text')
        value = Q(item)
        if str(value) != item or not 0 < value < 1 or value.denominator > 24:
            raise ValueError('canonical positive shift below one, denominator at most24')
        values.append(value)
    if tuple(values) != tuple(sorted(set(values))):
        raise ValueError('strictly increasing distinct shifts')
    return tuple(values)


def catalogue():
    return [dict(id=i, degree=len(shifts), program={'shifts': list(shifts)})
            for i, shifts in enumerate(c for k in (1, 2, 3)
                                       for c in combinations(SHIFTS, k))]


def real(value):
    value = Q(value)
    return arb(value.numerator) / value.denominator


def precision():
    if not 128 <= ctx.prec <= 256:
        raise ValueError('128 through256 bit interval arithmetic')


def horizon(H):
    if type(H) is not int or not 1 <= H <= MAX_HORIZON:
        raise ValueError('complete horizon1..262143')


def sieve(H, meter):
    horizon(H)
    meter.charge(H + 1)
    spf = list(range(H + 1))
    for p in range(2, isqrt(H) + 1):
        if spf[p] == p:
            meter.charge((H - p*p)//p + 1)
            for n in range(p*p, H + 1, p):
                if spf[n] == n:
                    spf[n] = p
    meter.live(2*(H + 1))
    return spf


def source(name, H, meter, spf=None):
    horizon(H)
    if name not in SOURCES:
        raise ValueError('declared source')
    spf = sieve(H, meter) if spf is None else spf
    values = [0]*(H + 1)
    values[1] = 1
    meter.charge(4*H)
    for n in range(2, H + 1):
        p = spf[n]
        m = n//p
        if name == 'one':
            values[n] = 1
        elif m % p:
            values[n] = values[m]*(-1 if name == 'mu' or p <= 13 else 1)
    return values


def normalizer(program, meter):
    precision()
    shifts = validate(program)
    rows = []
    for b in shifts:
        z = real(1-b).zeta()
        meter.charge(256)
        residue = 1/(real(b)*z)
        for other in shifts:
            if other != b:
                residue *= (real(1-b+other).zeta()/z - 1)/real(other)
                meter.charge(264)
        coefficient = residue/real(1-b)
        if not coefficient.is_finite():
            raise ArithmeticError('uncertified finite normalizer')
        rows.append(dict(shift=str(b), residue=residue, coefficient=coefficient))
    return rows


def convolution(left, right, meter):
    """Zero-unit dense multiples path, distinct from checker divisor rows."""
    if len(left) != len(right) or left[1] != 0 or right[1] != 0:
        raise ValueError('equal complete zero-unit prefixes')
    H = len(left)-1
    horizon(H)
    out = [arb(0)]*(H + 1)
    meter.charge(H + 1)
    for d in range(2, H//2 + 1):
        meter.charge()
        if not left[d]:
            continue
        meter.charge(2*(H//d - 1))
        for m in range(2, H//d + 1):
            out[d*m] += left[d]*right[m]
    return out


class Workspace:
    def __init__(self, name, H, meter):
        precision()
        self.name, self.H, self.meter = name, H, meter
        self.spf = sieve(H, meter)
        self.values = source(name, H, meter, self.spf)
        self.cache = {}
        self.reference_cache = {}

    def live(self, extra=0):
        self.meter.live((4 + len(self.cache) + len(self.reference_cache) + extra)*(self.H + 1))

    def atom(self, b):
        key = (b,)
        if key in self.cache:
            return self.cache[key]
        H, meter = self.H, self.meter
        a = [arb(0)]*(H + 1)
        a[1] = arb(1)
        powers = {}
        self.live(5)
        for n in range(2, H + 1):
            meter.charge(5)
            p = self.spf[n]
            if p == n:
                t = arb(p)**(-real(b))
                meter.charge(64)
                powers[p] = t
                a[n] = t + self.values[p]
                continue
            r = n
            e = 0
            while r % p == 0:
                meter.charge(2)
                r //= p
                e += 1
            if r != 1:
                a[n] = a[r]*a[n//r]
            elif self.name == 'one':
                a[n] = a[n//p]*powers[p] + 1
            else:
                a[n] = a[n//p]*powers[p]
        a[1] = arb(0)
        scale = 1/real(b)
        meter.charge(H)
        for n in range(2, H + 1):
            a[n] *= scale
        self.cache[key] = a
        self.live()
        return a

    def coefficients(self, shifts):
        key = tuple(shifts)
        if key in self.cache:
            return self.cache[key]
        if len(key) == 1:
            return self.atom(key[0])
        self.cache[key] = convolution(self.coefficients(key[:-1]), self.atom(key[-1]), self.meter)
        self.live()
        return self.cache[key]

    def evaluate(self, program):
        shifts = validate(program)
        coeff = self.coefficients(shifts)
        return centered(coeff, normalizer(program, self.meter), self.meter)

    def baseline(self, degree):
        if type(degree) is not int or degree not in (1, 2, 3):
            raise ValueError('baseline degree1..3')
        if 1 not in self.reference_cache:
            mu = source('mu', self.H, self.meter, self.spf)
            mu[1] = 0
            self.reference_cache[1] = list(map(arb, mu))
            self.meter.charge(self.H)
        for k in range(2, degree + 1):
            if k not in self.reference_cache:
                self.reference_cache[k] = convolution(self.reference_cache[k-1], self.reference_cache[1], self.meter)
        self.live(5)
        return centered(self.reference_cache[degree], [], self.meter)


def centered(coeff, rows, meter):
    precision()
    H = len(coeff)-1
    horizon(H)
    signed = [arb(0)]*(H + 1)
    absolute = [arb(0)]*(H + 1)
    total, magnitude = arb(0), arb(0)
    exponents = [(1-real(row['shift']), row['coefficient']) for row in rows]
    for n in range(1, H + 1):
        meter.charge(4 + 68*len(rows))
        total += coeff[n]
        magnitude += abs(coeff[n])
        main, envelope = arb(0), arb(0)
        for exponent, coefficient in exponents:
            factor = arb(n)**exponent
            main += coefficient*factor
            envelope += abs(coefficient)*factor
        signed[n] = total-main
        absolute[n] = magnitude+envelope
    return dict(coefficients=coeff, centered=signed, absolute=absolute, normalizer=rows)


def moments(state, scales, meter):
    out = []
    H = len(state['centered'])-1
    for X in scales:
        if type(X) is not int or X < 1 or 2*X-1 > H:
            raise ValueError('complete integer doubling block required')
        energy, envelope = arb(0), arb(0)
        meter.charge(4*X + 2)
        for n in range(X, 2*X):
            energy += state['centered'][n]**2
            envelope += state['absolute'][n]**2
        out.append(dict(X=X, energy=energy/(X*X), absolute_energy=envelope/(X*X)))
    return out


def encoded(rows):
    return [dict(X=r['X'], energy=r['energy'].str(45, radius=True),
                 absolute_energy=r['absolute_energy'].str(45, radius=True)) for r in rows]
