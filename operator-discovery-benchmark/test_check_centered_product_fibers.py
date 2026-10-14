"""Tiny direct ordered-pair references for complete centered cutoff sectors."""
from fractions import Fraction as Q
from math import gcd
import unittest
from flint import arb, ctx
import check_centered_product_fibers as C

METERS = []
SECTORS = ('aa_sf', 'aa_ns', 'cross_sf', 'cross_ns', 'mm_sf', 'mm_ns')


class Meter:
    def __init__(self, cap=2000000, cells=6000000):
        self.operations = 0; self.cap = cap; self.peak_cells = 0; self.cells = cells; METERS.append(self)

    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('strict work')
        if n > self.cap - self.operations: raise OverflowError('synthetic work cap')
        self.operations += n

    def live(self, cells):
        self.charge(); self.peak_cells = max(self.peak_cells, cells)
        if cells > self.cells: raise MemoryError('resident cap')


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_centered_product_fibers operations=' + str(sum(m.operations for m in METERS)))


def trial_mu(n, m):
    sign = 1; p = 2
    while p * p <= n:
        m.charge()
        if n % p == 0:
            sign = -sign; n //= p; m.charge(2)
            if n % p == 0: return 0
        p += 1
    if n > 1: sign = -sign; m.charge()
    return sign


def synthetic(a, center, m):
    H = len(a) - 1; mu = [0] + [trial_mu(n, m) for n in range(1, H + 1)]
    m.charge(2 * (H + 1))
    return C.State(H=H, precision=ctx.prec, a=list(map(arb, a)), m=list(map(arb, center)),
                   mu=mu, squarefree=[bool(value) for value in mu])


def literal(X, T, gamma, state, m):
    N = 2 * X - 1; weights = [arb(0)] * (N + 1)
    for n in range(1, N + 1):
        if gamma == '0': weights[n] = arb(1); m.charge()
        else:
            b = Q(gamma); m.charge(C.POWER_WORK + 3)
            weights[n] = arb(n) ** (-arb(b.numerator) / b.denominator)
    result = {key: arb(0) for key in SECTORS}
    for h in range(1, N + 1):
        for k in range(1, N + 1):
            m.charge(5)
            if h * k > T: continue
            W = sum(int(h <= n and k <= n) for n in range(X, 2 * X)); m.charge(2 * X)
            sf = bool(state['mu'][h]) and bool(state['mu'][k]) and gcd(h, k) == 1
            suffix = '_sf' if sf else '_ns'; m.charge(20)
            weight = weights[h] * weights[k] * W / (X * X)
            ah, ak, mh, mk = state['a'][h], state['a'][k], state['m'][h], state['m'][k]
            result['aa' + suffix] += ah * ak * weight
            result['cross' + suffix] += -(ah * mk + mh * ak) * weight
            result['mm' + suffix] += mh * mk * weight
    result['centered_sf'] = result['aa_sf'] + result['cross_sf'] + result['mm_sf']
    result['centered_ns'] = result['aa_ns'] + result['cross_ns'] + result['mm_ns']
    result['centered'] = result['centered_sf'] + result['centered_ns']; m.charge(5)
    return result


class CenteredProductCheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old_precision = ctx.prec; ctx.prec = 192
        cls.shared_meter = Meter(); cls.actual = C.source(31, cls.shared_meter)

    @classmethod
    def tearDownClass(cls): ctx.prec = cls.old_precision

    def assertBall(self, value, reference):
        self.assertTrue(value.is_finite()); self.assertTrue(value.overlaps(reference), (value, reference))

    def test_source_direct_divisors_and_increment_product(self):
        m = Meter(); s = self.actual; H = 31
        mu = [0] + [trial_mu(n, m) for n in range(1, H + 1)]
        self.assertEqual(s['mu'], mu)
        atoms = []
        for b in (Q(1, 3), Q(2, 3)):
            values = [arb(0)] * (H + 1)
            for n in range(1, H + 1):
                for d in range(1, n + 1):
                    m.charge()
                    if n % d or not mu[d]: continue
                    m.charge(C.POWER_WORK + 4)
                    values[n] += mu[d] * arb(n // d) ** (-arb(b.numerator) / b.denominator)
            atoms.append(values)
        for n in range(H + 1):
            self.assertBall(s['a_u'][n], atoms[0][n]); self.assertBall(s['a_v'][n], atoms[1][n])
        for n in range(2, H + 1):
            p = arb(0)
            for d in range(2, n):
                m.charge()
                if n % d == 0:
                    m.charge(5); p += arb(9) / 2 * atoms[0][d] * atoms[1][n // d]
            self.assertBall(s['p'][n], p)
        for n in (1, 2, 3, 4, 8, 9, 16, 25, 27): self.assertTrue(s['a'][n].is_zero())
        self.assertFalse(s['a'][12].is_zero())
        for key in ('a', 'm', 'R', 'p', 'a_u', 'a_v'): self.assertTrue(s[key][0].is_zero())

    def test_deterministic_center_and_complete_prefix(self):
        m = Meter(); s = self.actual; m.charge(2 * C.ZETA_WORK + 15)
        z = (arb(2) / 3).zeta(); c = arb(27) / 4 * ((arb(4) / 3).zeta() / z ** 2 - 1 / z)
        self.assertBall(s['c'], c); prefix = center_prefix = arb(0); previous = arb(0)
        for n in range(1, 32):
            m.charge(C.POWER_WORK + 8); power = arb(n) ** (arb(2) / 3)
            self.assertBall(s['m'][n], c * (power - previous))
            prefix += s['a'][n]; center_prefix += s['m'][n]
            self.assertBall(center_prefix, c * power); self.assertBall(s['R'][n], prefix - c * power)
            previous = power
        self.assertBall(s['R'][1], -c)

    def test_all_six_actual_sectors_and_cutoff_boundaries(self):
        m = Meter()
        for X in (4, 8):
            N = 2 * X - 1
            for gamma in C.GAMMAS:
                for T in (0, 1, 4, 9, N, N * N, N * N + 7):
                    result = C.cutoff(X, T, gamma, self.actual, self.shared_meter)
                    reference = literal(X, T, gamma, self.actual, m)
                    for key, value in reference.items(): self.assertBall(result[key], value)
                    self.assertFalse(result['centered_projection_positive_claimed']); self.assertFalse(result['RH_proved'])

    def test_synthetic_signed_sequences_and_sf_center_transport(self):
        m = Meter(); a = [0] + [(-1) ** n * (n % 5) for n in range(1, 16)]
        center = [0] + [Q(n % 3 - 1, 3) for n in range(1, 16)]
        # Arb accepts exact rational numerator/denominator explicitly.
        m.charge(30)
        s = synthetic(a, [0] * 16, m)
        s['m'] = [arb(v.numerator) / v.denominator if type(v) is Q else arb(v) for v in center]
        for gamma in C.GAMMAS:
            for T in (3, 12, 49, 225):
                result = C.cutoff(8, T, gamma, s, m); reference = literal(8, T, gamma, s, m)
                for key, value in reference.items(): self.assertBall(result[key], value)
                m.charge(8)
                self.assertBall(result['centered_sf'], result['aa_sf'] + result['cross_sf'] + result['mm_sf'])
                self.assertBall(result['centered_ns'], result['aa_ns'] + result['cross_ns'] + result['mm_ns'])

    def test_full_cutoff_equals_weighted_prefix_squared_moment(self):
        m = Meter(); X = 8; s = self.actual
        for gamma in C.GAMMAS:
            result = C.cutoff(X, (2 * X - 1) ** 2, gamma, s, self.shared_meter)
            prefix = arb(0); total = arb(0)
            for n in range(1, 2 * X):
                if gamma == '0': weight = arb(1); m.charge()
                else:
                    b = Q(gamma); m.charge(C.POWER_WORK + 3)
                    weight = arb(n) ** (-arb(b.numerator) / b.denominator)
                prefix += (s['a'][n] - s['m'][n]) * weight; m.charge(5)
                if n >= X: total += prefix ** 2; m.charge(2)
            m.charge(); self.assertBall(result['centered'], total / (X * X))
            if gamma == '0':
                m.charge(2 * X + 1)
                self.assertBall(result['centered'], sum((s['R'][n] ** 2 for n in range(X, 2 * X)), arb(0)) / (X * X))

    def test_unit_diagonal_and_projection_not_positive(self):
        m = Meter(); s = synthetic([0, 0, 1, -1], [0, 0, 0, 0], m)
        result = C.cutoff(2, 9, '0', s, m)
        self.assertBall(result['centered_sf'], -arb(1) / 2)
        self.assertBall(result['centered_ns'], arb(3) / 4)
        self.assertBall(result['centered'], arb(1) / 4)
        unit = C.cutoff(1, 1, '0', self.actual, self.shared_meter)
        self.assertTrue(unit['aa_sf'].contains(0)); self.assertTrue(unit['cross_sf'].contains(0))
        self.assertBall(unit['mm_sf'], self.actual['m'][1] ** 2)
        self.assertBall(unit['centered'], self.actual['R'][1] ** 2)
        none = C.cutoff(1, 0, '0', self.actual, self.shared_meter)
        for key in SECTORS: self.assertTrue(none[key].contains(0))

    def test_cache_shared_meter_and_residency(self):
        m = Meter(); s = synthetic([0, 1, -1, 2, -2, 0, 1, 1], [0, 1, 1, 1, 1, 1, 1, 1], m)
        C.cutoff(4, 10, '1/6', s, m); cells = s._cache_cells; before = m.operations
        C.cutoff(4, 20, '1/6', s, m)
        self.assertEqual(s._cache_cells, cells); self.assertGreater(m.operations, before)
        with self.assertRaises(ValueError): C.cutoff(4, 20, '1/6', s, Meter())
        self.assertLess(m.peak_cells, 6000000)

    def test_invalid_domains_precision_and_caps(self):
        m = Meter()
        for H in (True, 0, -1, 2048):
            with self.assertRaises(ValueError): C.source(H, m)
        for X, T, gamma in ((0, 1, '0'), (True, 1, '0'), (32, 1, '0'), (4, -1, '0'),
                            (4, True, '0'), (4, 1, '2/6'), (4, 1, '1/2'), (4, 1, 0)):
            with self.assertRaises(ValueError): C.cutoff(X, T, gamma, self.actual, self.shared_meter)
        with self.assertRaises(ValueError): C.cutoff(4, 1, '0', dict(self.actual), m)
        ctx.prec = 128
        try:
            with self.assertRaises(ValueError): C.source(7, m)
        finally: ctx.prec = 192
        with self.assertRaises(OverflowError): C.source(7, Meter(cap=1))
        with self.assertRaises(MemoryError): C.source(7, Meter(cells=1))


if __name__ == '__main__': unittest.main()
