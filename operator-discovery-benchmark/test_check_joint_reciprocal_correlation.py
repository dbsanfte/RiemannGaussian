"""Independent tiny literal-pair/reference-source tests; no study arithmetic."""
from math import isqrt
import unittest
from flint import arb, ctx
import check_joint_reciprocal_correlation as C

METERS = []


class Meter:
    def __init__(self, cap=2000000, cells=6000000):
        self.operations = 0; self.cap = cap; self.cells = cells; self.peak_cells = 0; METERS.append(self)

    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('strict work counter')
        if n > self.cap - self.operations: raise OverflowError('synthetic work cap')
        self.operations += n

    def live(self, cells):
        self.charge(); self.peak_cells = max(self.peak_cells, cells)
        if cells > self.cells: raise MemoryError('resident cap')


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_joint_reciprocal_correlation operations=' + str(sum(m.operations for m in METERS)))


def trial_mu(n, meter):
    sign = 1; p = 2
    while p * p <= n:
        meter.charge()
        if n % p == 0:
            n //= p; sign = -sign; meter.charge(2)
            if n % p == 0: return 0
        p += 1
    if n > 1: meter.charge(); sign = -sign
    return sign


def synthetic(raw, power_center, error_increments, meter):
    H = len(raw) - 1; meter.charge(3 * (H + 1))
    raw = list(map(arb, raw)); center = list(map(arb, power_center))
    t = [arb(0)] * (H + 1); T = [arb(0)] * (H + 1); R = [arb(0)] * (H + 1)
    prefix = error = arb(0)
    for n in range(1, H + 1):
        meter.charge(5); t[n] = raw[n] - center[n]; prefix += t[n]; error += error_increments[n]
        T[n] = prefix; R[n] = prefix - error
    return C.State(H=H, precision=192, a=raw, power_center=center, tilde_b=t, tilde_R=T, R=R)


def literal(X, state, meter):
    N = 2 * X - 1; c = isqrt(X)
    result = {key: arb(0) for key in ('O', 'reciprocal', 'triangle', 'low_head', 'high_diagonal', 'O_aa', 'O_cross', 'O_mm', 'energy_R', 'energy_tilde', 'center_cross', 'center_square')}
    t, T, R = state['tilde_b'], state['tilde_R'], state['R']
    a, center = state['a'], state['power_center']
    for n in range(X, N + 1):
        meter.charge(10); result['energy_R'] += R[n] ** 2; result['energy_tilde'] += T[n] ** 2
        error = T[n] - R[n]; result['center_cross'] += -2 * T[n] * error; result['center_square'] += error ** 2
        for h in range(1, n + 1):
            for k in range(1, n + 1):
                meter.charge(3)
                product = t[h] * t[k]
                if h * k <= X: result['low_head'] += product; meter.charge()
                elif h == k: result['high_diagonal'] += product; meter.charge()
                else:
                    result['O'] += product; meter.charge(8)
                    result['O_aa'] += a[h] * a[k]
                    result['O_cross'] += -a[h] * center[k] - center[h] * a[k]
                    result['O_mm'] += center[h] * center[k]
                    if min(h, k) <= c: result['reciprocal'] += product
                    else: result['triangle'] += product
    for key in result: result[key] /= X * X; meter.charge()
    return result


class JointReciprocalCheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old_precision = ctx.prec; ctx.prec = 192
        cls.shared_meter = Meter(); cls.actual = C.source(31, cls.shared_meter)

    @classmethod
    def tearDownClass(cls): ctx.prec = cls.old_precision

    def assertBall(self, actual, reference):
        self.assertTrue(actual.is_finite()); self.assertTrue(actual.overlaps(reference), (actual, reference))

    def test_direct_source_against_trial_divisor_increment_rows(self):
        m = Meter(); H = 31; s = self.actual
        mu = [0] + [trial_mu(n, m) for n in range(1, H + 1)]
        self.assertEqual(s['mu'], mu)
        atoms = []
        for numerator in (1, 2):
            rows = [arb(0)] * (H + 1)
            for n in range(1, H + 1):
                for d in range(1, n + 1):
                    m.charge()
                    if n % d or not mu[d]: continue
                    m.charge(C.POWER_WORK + 4)
                    rows[n] += mu[d] * arb(n // d) ** (-arb(numerator) / 3)
            atoms.append(rows)
        for n in range(H + 1):
            self.assertBall(s['au'][n], atoms[0][n]); self.assertBall(s['av'][n], atoms[1][n])
        for n in range(2, H + 1):
            reference = arb(0)
            for d in range(2, n):
                m.charge()
                if n % d == 0: reference += arb(9) / 2 * atoms[0][d] * atoms[1][n // d]; m.charge(5)
            self.assertBall(s['p'][n], reference)
            self.assertBall(s['a'][n] + s['d'][n], s['p'][n]); m.charge()
        for n in (2, 3, 4, 8, 9, 16, 25, 27, 31):
            self.assertTrue(s['prime_power'][n]); self.assertTrue(s['a'][n].is_zero())
        for n in (6, 12, 18, 20, 30): self.assertFalse(s['prime_power'][n]); self.assertTrue(s['d'][n].is_zero())

    def test_exact_constants_units_and_center_mass(self):
        m = Meter(); s = self.actual; m.charge(3 * C.ZETA_WORK + 20)
        z = (arb(2) / 3).zeta()
        main = arb(27) / 4 * ((arb(4) / 3).zeta() / z ** 2 - 1 / z)
        residue = arb(2) / 3 * main; mass = -residue * (arb(1) / 3).zeta()
        self.assertBall(s['m'], main); self.assertBall(s['R_u'], residue); self.assertBall(s['E0'], mass)
        self.assertTrue(s['a'][1].is_zero()); self.assertTrue(s['p'][1].is_zero()); self.assertTrue(s['d'][1].is_zero())
        self.assertBall(s['tilde_b'][1], -residue); self.assertBall(s['R'][1], -main)
        A = power_sum = arb(0)
        for n in range(1, 32):
            m.charge(2 * C.POWER_WORK + 10)
            inverse = arb(n) ** (-arb(1) / 3); power = arb(n) ** (arb(2) / 3)
            A += s['a'][n]; power_sum += inverse
            self.assertBall(s['tilde_b'][n], s['a'][n] - residue * inverse)
            self.assertBall(s['R'][n], A - main * power)
            self.assertBall(s['tilde_R'][n], A - residue * power_sum)
            self.assertBall(s['center_error'][n], main * power - residue * power_sum)
            self.assertTrue(s['center_error'][n] > 0); self.assertTrue(s['center_error'][n] < mass)

    def test_actual_complete_intervals_odd_X_and_all_sectors(self):
        m = Meter()
        for X in (1, 2, 3, 5, 8, 16):
            result = C.query(X, self.actual, self.shared_meter); reference = literal(X, self.actual, m)
            for key, value in reference.items(): self.assertBall(result[key], value)
            self.assertTrue(result['identity_residual'].contains(0)); self.assertTrue(result['sector_residual'].contains(0))
            self.assertFalse(result['RH_proved']); self.assertFalse(result['uniform_signed_bound_proved'])

    def test_adversarial_signs_units_and_crosses(self):
        for pattern in range(3):
            m = Meter(); H = 15
            raw = [0] + [(-1) ** n * (n % 4) if pattern == 0 else (1 if n == 1 else n % 3 - 1) for n in range(1, H + 1)]
            center = [0] + [(n % 3 - 1) if pattern == 1 else 1 for n in range(1, H + 1)]
            error = [0] + [(-1) ** n if pattern == 2 else (1 if n % 3 == 0 else 0) for n in range(1, H + 1)]
            state = synthetic(raw, center, error, m)
            for X in (1, 3, 5, 8):
                result = C.query(X, state, m); reference = literal(X, state, m)
                for key, value in reference.items(): self.assertBall(result[key], value)
                self.assertTrue(result['identity_residual'].contains(0)); self.assertTrue(result['sector_residual'].contains(0))
                m.charge(4); self.assertBall(result['triangle'], result['triangle_square'] - result['triangle_diagonal'])
                self.assertBall(result['center_correction'], result['center_cross'] + result['center_square'])

    def test_strict_product_equality_and_triangle_not_dropped(self):
        m = Meter(); raw = [0, 0, 2, -3, 0, 0, 0, 0]; state = synthetic(raw, [0] * 8, [0] * 8, m)
        result = C.query(4, state, m)
        # At X4 the pair(2,2) lies in the LOW product equality sector.
        self.assertBall(result['low_head'], arb(1)); self.assertBall(result['O'], -arb(3))
        self.assertBall(result['reciprocal'], -arb(3)); self.assertBall(result['triangle'], 0 * arb(1))
        state2 = synthetic([0, 0, 0, 2, -3, 0, 0, 0], [0] * 8, [0] * 8, m)
        triangle = C.query(4, state2, m)
        self.assertTrue(triangle['reciprocal'].is_zero()); self.assertFalse(triangle['triangle'].is_zero())
        unit = C.query(1, self.actual, self.shared_meter)
        self.assertTrue(unit['O'].contains(0)); self.assertTrue(unit['high_diagonal'].contains(0))
        self.assertBall(unit['low_head'], self.actual['R_u'] ** 2)
        self.assertBall(unit['center_correction'], self.actual['m'] ** 2 - self.actual['R_u'] ** 2)

    def test_cache_binding_mutation_and_shared_meter(self):
        m = Meter(); s = synthetic([0, 1, -1, 2], [0, 0, 1, 1], [0, 1, 0, 0], m)
        C.query(2, s, m); before = m.operations; cached = s._prefixes
        C.query(2, s, m); self.assertGreater(m.operations, before); self.assertIs(s._prefixes, cached)
        with self.assertRaises(ValueError): C.query(2, s, Meter())
        bad = synthetic([0, 1, 0, 0], [0] * 4, [0] * 4, m); bad['tilde_R'][2] = arb(99)
        with self.assertRaises(ValueError): C.query(2, bad, m)
        bad2 = synthetic([0, 1, 0, 0], [0] * 4, [0] * 4, m); bad2['tilde_b'][2] = arb(1)
        with self.assertRaises(ValueError): C.query(2, bad2, m)
        self.assertLess(m.peak_cells, 6000000)

    def test_invalid_domains_precision_and_resource_caps(self):
        m = Meter()
        for H in (True, 0, -1, 131072):
            with self.assertRaises(ValueError): C.source(H, m)
        for X in (True, 0, -1, 17):
            with self.assertRaises(ValueError): C.query(X, self.actual, self.shared_meter)
        with self.assertRaises(ValueError): C.query(2, dict(self.actual), m)
        ctx.prec = 160
        try:
            with self.assertRaises(ValueError): C.source(3, m)
            with self.assertRaises(ValueError): C.query(2, self.actual, m)
        finally: ctx.prec = 192
        with self.assertRaises(OverflowError): C.source(3, Meter(cap=1))
        with self.assertRaises(MemoryError): C.source(3, Meter(cells=1))


if __name__ == '__main__': unittest.main()
