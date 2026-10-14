"""Complete candidate-10 largest-prime banks, using independent event sweeps.

Finite Arb evaluations do not prove the open cofinal signed moment.  The
smooth sector is built from its own admission events, never by subtraction
from the proposed decomposition.  No frozen producer is imported.
"""
from fractions import Fraction
import math
import time

from flint import arb, ctx

MAX_HORIZON = 1048575
MAX_CELLS = 48000000
_ARRAYS = ('p', 'a_u', 'a_v', 'd', 'a', 'z0', 'zu', 'zv', 'R', 'main')


class Meter:
    def __init__(self, cap=1500000000, seconds=7200):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer operation cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite runtime cap')
        self.cap, self.operations, self.peak_cells = cap, 0, 0
        self.deadline = time.monotonic() + seconds

    def charge(self, n=1):
        if type(n) is not int or n < 0:
            raise ValueError('nonnegative integer work charge')
        if n > self.cap - self.operations:
            raise OverflowError('prime-bank operation cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('prime-bank runtime cap')

    def live(self, cells):
        if type(cells) is not int or cells < 0:
            raise ValueError('nonnegative integer live cells')
        self.charge()
        self.peak_cells = max(self.peak_cells, cells)
        if cells > MAX_CELLS:
            raise MemoryError('48 million scalar-cell cap')

    def counts(self):
        return dict(operations=self.operations, peak_cells=self.peak_cells)


def _horizon(H):
    if type(H) is not int or not 1 <= H <= MAX_HORIZON:
        raise ValueError('complete horizon1..1048575')


def _precision():
    if not 128 <= ctx.prec <= 256:
        raise ValueError('128 through256 bit Arb arithmetic')


def theta(theta_text):
    if type(theta_text) is not str or not 1 <= len(theta_text) <= 32:
        raise ValueError('bounded canonical rational theta')
    value = Fraction(theta_text)
    if str(value) != theta_text or not Fraction(1, 2) <= value < 1 or value.denominator > 12:
        raise ValueError('canonical theta in[1/2,1), denominator<=12')
    return value


def _finite(value):
    if not value.is_finite():
        raise ArithmeticError('nonfinite Arb arithmetic')
    return value


def _sieve(H, meter, resident):
    meter.live(resident)
    meter.charge(2*(H+1))
    spf, lpf = [0]*(H+1), [0]*(H+1)
    primes = []
    for p in range(2, H+1):
        meter.charge(3)
        if spf[p]:
            continue
        primes.append(p)
        meter.charge(3*(H//p))
        for n in range(p, H+1, p):
            if not spf[n]:
                spf[n] = p
            lpf[n] = p
    return spf, lpf, primes


def source_state(H, meter):
    """Actual-source complete coefficients and independent direct R prefix."""
    _horizon(H)
    _precision()
    # Fourteen dense arrays and conservative two prime dictionaries + list.
    meter.live(19*(H+1)+64)
    spf, lpf, primes = _sieve(H, meter, 19*(H+1)+64)
    zero = arb(0)
    meter.charge(12*(H+1))
    power = [0]*(H+1)
    a_u, a_v, product = [[zero]*(H+1) for _ in range(3)]
    p, d, a, z0, zu, zv, R, main = [[zero]*(H+1) for _ in range(8)]
    a_u[1] = a_v[1] = product[1] = arb(1)
    prime_u, prime_v = {}, {}
    beta = arb(9)/2
    meter.charge(524)
    z = (arb(2)/3).zeta()
    w = (arb(4)/3).zeta()
    if not z.is_finite() or z.contains(0) or not w.is_finite():
        raise ArithmeticError('uncertified candidate10 residue')
    m_u = _finite((arb(3)/2)*beta*(w/(z*z)-1/z))
    total = zero
    for n in range(1, H+1):
        meter.charge(60)
        if n >= 2:
            prime = spf[n]
            previous = n//prime
            if previous == 1:
                meter.charge(66)
                q = 1/arb(prime).root(3)
                q2 = q*q
                prime_u[prime], prime_v[prime] = q, q2
                power[n] = prime
                a_u[n], a_v[n] = q-1, q2-1
                product[n] = a_u[n]+a_v[n]
                # The zero prime coefficient is exact, not a rounded cancellation.
            else:
                q, q2 = prime_u[prime], prime_v[prime]
                power[n] = power[previous]*prime if previous % prime == 0 else prime
                core = n//power[n]
                if core == 1:
                    a_u[n] = a_u[previous]*q
                    a_v[n] = a_v[previous]*q2
                    product[n] = (q+q2)*product[previous] - (q*q2)*product[n//(prime*prime)]
                    if n == prime*prime:
                        product[n] += 1
                    p[n] = beta*(product[n]-a_u[n]-a_v[n])
                    d[n] = p[n]
                    # Complete same-prime branch removed, retaining exact zero a.
                else:
                    a_u[n] = a_u[core]*a_u[power[n]]
                    a_v[n] = a_v[core]*a_v[power[n]]
                    product[n] = product[core]*product[power[n]]
                    p[n] = beta*(product[n]-a_u[n]-a_v[n])
                    a[n] = p[n]
            zu[n] = p[n]+beta*a_v[n]
            zv[n] = p[n]+beta*a_u[n]
            z0[n] = zu[n]+zv[n]
        meter.charge(66)
        cube = arb(n).root(3)
        main[n] = m_u*cube*cube
        total += a[n]
        R[n] = total-main[n]
        for value in (a_u[n], a_v[n], product[n], p[n], d[n], a[n], z0[n], zu[n], zv[n], R[n], main[n]):
            _finite(value)
    resident = 12*(H+1)+5*len(primes)+64
    meter.live(resident)
    return dict(H=H, precision=ctx.prec, p=p, a_u=a_u, a_v=a_v, d=d, a=a,
                z0=z0, zu=zu, zv=zv, R=R, main=main, m_u=m_u,
                spf=spf, lpf=lpf, primes=primes, prime_u=prime_u, prime_v=prime_v,
                _resident_cells=resident)


def _state(state, meter):
    if type(state) is not dict:
        raise ValueError('source-state mapping')
    H = state.get('H')
    _horizon(H)
    _precision()
    if type(state.get('precision')) is not int or state['precision'] != ctx.prec:
        raise ValueError('source precision must match current Arb precision')
    for key in _ARRAYS:
        values = state.get(key)
        if type(values) is not list or len(values) != H+1 or values[0] != 0:
            raise ValueError('complete index-zero source arrays')
        meter.charge(4*(H+1))
        for value in values:
            if not isinstance(value, arb) or not value.is_finite():
                raise ValueError('finite Arb source scalars')
    for key in ('spf', 'lpf'):
        values = state.get(key)
        if type(values) is not list or len(values) != H+1 or values[0] != 0:
            raise ValueError('complete factor arrays')
        meter.charge(5*(H+1))
        for n, value in enumerate(values):
            if type(value) is not int or (n >= 2 and not 2 <= value <= n):
                raise ValueError('integer source factors')
    primes = state.get('primes')
    if type(primes) is not list:
        raise ValueError('prime list')
    meter.charge(5*len(primes)+10)
    previous = 1
    for q in primes:
        if type(q) is not int or not previous < q <= H or state['spf'][q] != q or state['lpf'][q] != q:
            raise ValueError('ordered prime factor rows')
        for key in ('prime_u', 'prime_v'):
            value = state.get(key, {}).get(q)
            if not isinstance(value, arb) or not value.is_finite() or not value > 0:
                raise ValueError('positive finite cached prime roots')
        previous = q
    if state['a_u'][1] != 1 or state['a_v'][1] != 1 or any(state[key][1] != 0 for key in ('p','d','a','z0','zu','zv')):
        raise ValueError('complete unit correction')
    if not isinstance(state.get('m_u'), arb) or not state['m_u'].is_finite():
        raise ValueError('finite original residue')
    resident = 12*(H+1)+5*len(primes)+64
    meter.live(resident)
    return H, resident


def _expiry(q, exponent, H, meter):
    """First n with n^num>=q^den, clipped to H+1. Exact strict cutoff."""
    num, den = exponent.numerator, exponent.denominator
    meter.charge(64+num+den)
    target = q**den
    if H**num < target:
        return H+1
    low, high = 1, H
    while low < high:
        meter.charge(num+4)
        middle = (low+high)//2
        if middle**num >= target:
            high = middle
        else:
            low = middle+1
    return low


def evaluate(theta_text, state, meter):
    """Independent smooth admission and three signed prime/cofactor sweeps."""
    exponent = theta(theta_text)
    H, resident = _state(state, meter)
    meter.live(resident+6*(H+1)+64)
    meter.charge(6*(H+1))
    expiry = [0]*(H+1)
    zero = arb(0)
    K, L0, Lu, Lv, reduced = [[zero]*(H+1) for _ in range(5)]
    for q in state['primes']:
        expiry[q] = _expiry(q, exponent, H, meter)
    # Smooth-sector events are derived directly from a(k), k and lpf(k).
    for k in range(2, H+1):
        meter.charge(4)
        if not state['a'][k]:
            continue
        prime = state['lpf'][k]
        admission = max(k, expiry[prime])
        if admission <= H:
            meter.charge()
            K[admission] += state['a'][k]
    # Each large-prime coefficient pair is born at qm and expires exactly
    # when the pointwise cutoff reaches q. All m=1 corrections are excluded.
    for q in state['primes']:
        meter.charge(6)
        end = expiry[q]
        limit = min(q-1, H//q, (end-1)//q)
        if limit < 2:
            continue
        qu, qv = state['prime_u'][q], state['prime_v'][q]
        total0, totalu, totalv = zero, zero, zero
        for m in range(2, limit+1):
            meter.charge(8)
            born = q*m
            term0 = state['z0'][m]
            termu = qu*state['zu'][m]
            termv = qv*state['zv'][m]
            L0[born] += term0
            Lu[born] += termu
            Lv[born] += termv
            total0 += term0
            totalu += termu
            totalv += termv
        if end <= H:
            meter.charge(3)
            L0[end] -= total0
            Lu[end] -= totalu
            Lv[end] -= totalv
    runK, run0, runu, runv = zero, zero, zero, zero
    for n in range(1, H+1):
        meter.charge(20)
        runK += K[n]
        run0 += L0[n]
        runu += Lu[n]
        runv += Lv[n]
        K[n], L0[n], Lu[n], Lv[n] = runK, run0, runu, runv
        reduced[n] = runK-run0+runu-state['main'][n]
        for value in (runK, run0, runu, runv, reduced[n]):
            _finite(value)
        if not (reduced[n]+runv).overlaps(state['R'][n]):
            raise ArithmeticError('complete bank identity inconsistent')
    meter.live(resident+5*(H+1)+64)
    return dict(theta=theta_text, H=H, K=K, L0=L0, Lu=Lu, Lv=Lv,
                reduced=reduced, R=state['R'], main=state['main'],
                _resident_cells=resident+5*(H+1)+64)
