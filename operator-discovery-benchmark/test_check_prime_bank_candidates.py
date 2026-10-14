"""Tiny independent divisor/prime-bank fixtures; no producer or study reads."""
from fractions import Fraction as Q
import unittest
from flint import arb, ctx
import check_prime_bank_candidates as C

METERS = []


class Meter:
    def __init__(self, cap=2000000, cells=48000000):
        self.operations = 0; self.cap = cap; self.peak_cells = 0; self.cell_cap = cells
        METERS.append(self)

    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('strict nonnegative charge')
        if n > self.cap - self.operations: raise OverflowError('synthetic cap')
        self.operations += n

    def live(self, cells):
        self.charge(); self.peak_cells = max(self.peak_cells, cells)
        if cells > self.cell_cap: raise MemoryError('resident cap')

    def counts(self):
        return dict(operations=self.operations, peak_cells=self.peak_cells)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_prime_bank_candidates operations=' +
          str(sum(m.operations for m in METERS)))


def trial_factors(n, m):
    result = []; p = 2
    while p * p <= n:
        m.charge()
        if n % p == 0:
            exponent = 0
            while n % p == 0:
                m.charge(2); n //= p; exponent += 1
            result.append((p, exponent))
        p += 1
    if n > 1: result.append((n, 1)); m.charge()
    return result


def manual_source(H, m):
    mu = [0, 1] + [0] * (H - 1); factors = [[], []]
    for n in range(2, H + 1):
        f = trial_factors(n, m); factors.append(f)
        mu[n] = 0 if any(e > 1 for _, e in f) else (-1) ** len(f)
    atoms = []
    for b in (Q(1, 3), Q(2, 3)):
        a = [arb(0)] * (H + 1)
        for n in range(1, H + 1):
            for d in range(1, n + 1):
                m.charge()
                if n % d or not mu[d]: continue
                m.charge(C.POWER_WORK + 4)
                a[n] += mu[d] * arb(n // d) ** (-arb(b.numerator) / b.denominator)
        atoms.append(a)
    p = [arb(0)] * (H + 1); a = [arb(0)] * (H + 1)
    for n in range(2, H + 1):
        for d in range(2, n):
            m.charge()
            if n % d == 0:
                m.charge(4); p[n] += arb(9) / 2 * atoms[0][d] * atoms[1][n // d]
        a[n] = arb(0) if len(factors[n]) == 1 else p[n]
    return atoms, p, a, factors


def manual_banks(theta, state, m):
    H = state['horizon']; primes = []
    largest = [0] * (H + 1)
    for n in range(2, H + 1):
        f = trial_factors(n, m); largest[n] = f[-1][0]
        if f == [(n, 1)]: primes.append(n)
    out = {key: [arb(0)] * (H + 1) for key in ('K', 'L0', 'Lu', 'Lv')}
    for n in range(1, H + 1):
        for t in range(2, n + 1):
            m.charge(3)
            if largest[t] ** theta.denominator <= n ** theta.numerator:
                out['K'][n] += state['a'][t]; m.charge()
        for k in range(2, n + 1):
            for q in primes:
                m.charge(4)
                if q * k > n or q ** theta.denominator <= n ** theta.numerator: continue
                # Independent direct prime/cofactor rectangles, including endpoints.
                m.charge(2 * C.POWER_WORK + 12)
                out['L0'][n] += state['z0'][k]
                out['Lu'][n] += state['zu'][k] * arb(q) ** (-arb(1) / 3)
                out['Lv'][n] += state['zv'][k] * arb(q) ** (-arb(2) / 3)
    return out


class PrimeBankCheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old_precision = ctx.prec; ctx.prec = 192
        cls.shared = C.source_state(63, Meter())

    @classmethod
    def tearDownClass(cls): ctx.prec = cls.old_precision

    def assertBall(self, actual, expected):
        self.assertTrue(actual.is_finite()); self.assertTrue(actual.overlaps(expected), (actual, expected))

    def test_complete_factor_rows_and_same_prime_complement(self):
        m = Meter(); atoms, p, a, factors = manual_source(63, m)
        for n in range(64):
            self.assertBall(self.shared['a_u'][n], atoms[0][n])
            self.assertBall(self.shared['a_v'][n], atoms[1][n])
            self.assertBall(self.shared['p'][n], p[n]); self.assertBall(self.shared['a'][n], a[n])
            self.assertBall(self.shared['d'][n], p[n] - a[n])
        for n in (4, 8, 9, 16, 25, 27, 32, 49):
            self.assertTrue(self.shared['a'][n].is_zero())
            self.assertFalse(self.shared['p'][n].is_zero())
        self.assertFalse(self.shared['a'][12].is_zero())  # repeated prime in mixed sector retained
        self.assertEqual(self.shared['lpf'][60], 5)
        self.assertNotIn(49, self.shared['primes']); self.assertIn(61, self.shared['primes'])

    def test_units_and_all_cofactor_channels(self):
        m = Meter(); s = self.shared
        for key in C.SOURCE_KEYS: self.assertTrue(s[key][0].is_zero())
        for key in ('p', 'd', 'a', 'z0', 'zu', 'zv'): self.assertTrue(s[key][1].is_zero())
        self.assertTrue(s['a_u'][1] == 1); self.assertTrue(s['a_v'][1] == 1)
        for n in range(2, 64):
            m.charge(12)
            self.assertBall(s['zu'][n], s['p'][n] + arb(9) / 2 * s['a_v'][n])
            self.assertBall(s['zv'][n], s['p'][n] + arb(9) / 2 * s['a_u'][n])
            self.assertBall(s['z0'][n], 2 * s['p'][n] + arb(9) / 2 * (s['a_u'][n] + s['a_v'][n]))

    def test_true_main_and_original_centered_prefix(self):
        m = Meter(); m.charge(2 * C.ZETA_WORK + 15)
        z = (arb(2) / 3).zeta()
        coefficient = arb(27) / 4 * ((arb(4) / 3).zeta() / z ** 2 - 1 / z)
        self.assertBall(self.shared['m_u'], coefficient)
        prefix = arb(0)
        for n in range(1, 64):
            m.charge(C.POWER_WORK + 5); prefix += self.shared['a'][n]
            main = coefficient * arb(n) ** (arb(2) / 3)
            self.assertBall(self.shared['main'][n], main)
            self.assertBall(self.shared['R'][n], prefix - main)
        self.assertBall(self.shared['R'][1], -coefficient)
        self.assertFalse(self.shared['R'][1].is_zero())

    def test_actual_prime_transfer_full_three_channels(self):
        m = Meter(); s = self.shared
        for q, k in ((2, 3), (3, 4), (5, 6), (7, 8), (11, 4), (13, 3), (19, 3)):
            m.charge(2 * C.POWER_WORK + 10)
            predicted = -s['z0'][k] + arb(q) ** (-arb(1) / 3) * s['zu'][k] + arb(q) ** (-arb(2) / 3) * s['zv'][k]
            self.assertBall(s['a'][q * k], predicted)
        # Transfer requires q-free cofactor; repeated-prime terms live in K.
        self.assertFalse(s['a'][12].is_zero())

    def test_all_cutoff_regimes_against_direct_rectangles(self):
        m = Meter()
        for theta in ('1/2', '2/3', '3/4', '4/5', '5/6'):
            result = C.evaluate(theta, self.shared, m)
            reference = manual_banks(Q(theta), self.shared, m)
            self.assertEqual(result['theta'], theta); self.assertEqual(result['horizon'], 63)
            self.assertIs(result['R'], self.shared['R']); self.assertIs(result['main'], self.shared['main'])
            for n in range(64):
                for key in reference: self.assertBall(result[key][n], reference[key][n])
                m.charge(4)
                self.assertBall(result['reduced'][n] + result['Lv'][n], self.shared['R'][n])
                if n: self.assertBall(result['reduced'][n], result['K'][n] - result['L0'][n] + result['Lu'][n] - self.shared['main'][n])
            # Complete residual is not defined by recombining the banks.
            self.assertIs(result['R'], self.shared['R'])

    def test_strict_square_boundary_and_old_bank_gains(self):
        m = Meter(); half = C.evaluate('1/2', self.shared, m)
        # q=3 at n=9 is smooth, equality is NOT admitted to a large-prime bank.
        for key in ('L0', 'Lu', 'Lv'): self.assertTrue(half[key][9].contains(0))
        # At n=9 the old coefficient6 becomes newly smooth when cutoff crosses3.
        m.charge(4)
        self.assertBall(half['K'][8], arb(0))
        self.assertBall(half['K'][9], self.shared['a'][6])
        # Full unit bank is excluded even when a large prime is present.
        for key in ('L0', 'Lu', 'Lv'): self.assertTrue(half[key][3].is_zero())
        self.assertFalse(half['K'][63].is_zero())

    def test_strict_schema_precision_and_horizon(self):
        m = Meter()
        for text in (True, '0', '1', '1/3', '2/4', '6/13', '7/13', ' 1/2', '1/0', '1' * 33):
            with self.assertRaises(ValueError): C.validate(text)
        for H in (True, 0, -1, 1048576):
            with self.assertRaises(ValueError): C.source_state(H, m)
        with self.assertRaises(ValueError): C.evaluate('1/2', dict(self.shared), m)
        ctx.prec = 64
        try:
            with self.assertRaises(ValueError): C.source_state(7, m)
            with self.assertRaises(ValueError): C.evaluate('1/2', self.shared, m)
        finally: ctx.prec = 192

    def test_shared_cost_memory_failure_and_initial_range(self):
        m = Meter(); s = C.source_state(1, m); before = m.operations
        out = C.evaluate('5/6', s, m)
        self.assertGreater(m.operations, before)
        for key in ('K', 'L0', 'Lu', 'Lv'): self.assertTrue(out[key][1].is_zero())
        self.assertBall(out['reduced'][1], -s['main'][1])
        with self.assertRaises(OverflowError): C.source_state(7, Meter(cap=5))
        with self.assertRaises(MemoryError): C.source_state(7, Meter(cells=1))
        self.assertLess(m.peak_cells, 48000000)
        self.assertNotIn('RH_proved', out)


if __name__ == '__main__': unittest.main()
