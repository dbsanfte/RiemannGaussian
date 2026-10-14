import unittest
from fractions import Fraction as Q
from flint import arb, ctx
import shifted_quotient_candidates as P

METERS = []


def meter():
    result = P.Meter()
    METERS.append(result)
    return result


class ProducerChecks(unittest.TestCase):
    def setUp(self):
        ctx.prec = 128

    def test_all_source_atoms_against_divisor_definition(self):
        for name in P.SOURCES:
            m = meter()
            w = P.Workspace(name, 48, m)
            for b in (Q(1, 6), Q(2, 3)):
                h = w.atom(b)
                self.assertEqual(h[1], 0)
                for n in range(2, 49):
                    expected = arb(0)
                    for d in range(1, n+1):
                        m.charge()
                        if n % d == 0:
                            expected += w.values[d]*arb(n//d)**(-P.real(b))/P.real(b)
                            m.charge(70)
                    self.assertTrue(h[n].overlaps(expected), (name, b, n))

    def test_products_keep_overlap_and_lag(self):
        m = meter()
        w = P.Workspace('mu', 48, m)
        a, b = w.atom(Q(1, 6)), w.atom(Q(1, 2))
        c = w.coefficients((Q(1, 6), Q(1, 2)))
        self.assertTrue(c[4].overlaps(a[2]*b[2]))
        self.assertTrue(c[12].overlaps(a[2]*b[6]+a[3]*b[4]+a[4]*b[3]+a[6]*b[2]))
        self.assertEqual(c[2], 0)
        self.assertEqual(c[3], 0)
        self.assertEqual(c[47], 0)
        self.assertFalse(a[6].contains(0))

    def test_baseline_unit_subtraction_before_product(self):
        m = meter()
        w = P.Workspace('one', 32, m)
        state = w.baseline(3)
        self.assertEqual(state['coefficients'][7], 0)
        self.assertEqual(state['coefficients'][8], -1)
        self.assertEqual(state['normalizer'], [])
        total = 0
        for n in range(1, 33):
            expected = 0
            for a in range(2, n+1):
                for b in range(2, n//a+1):
                    m.charge()
                    if n % (a*b) == 0 and n//(a*b) >= 2:
                        expected += w.reference_cache[1][a]*w.reference_cache[1][b]*w.reference_cache[1][n//(a*b)]
            self.assertEqual(state['coefficients'][n], expected)
            total += expected
            self.assertEqual(state['centered'][n], total)

    def test_full_center_and_energy(self):
        m = meter()
        w = P.Workspace('mu', 31, m)
        p = {'shifts': ['1/3', '2/3']}
        s = w.evaluate(p)
        n = 12
        main = sum((r['coefficient']*arb(n)**(1-P.real(r['shift'])) for r in s['normalizer']), arb(0))
        expected = sum(s['coefficients'][1:n+1], arb(0))-main
        self.assertTrue(s['centered'][n].overlaps(expected))
        rows = P.moments(s, [8, 16], m)
        for row in rows:
            X = row['X']
            manual = sum((v*v for v in s['centered'][X:2*X]), arb(0))/(X*X)
            self.assertTrue(row['energy'].overlaps(manual))
            self.assertTrue(row['energy'] < row['absolute_energy'])
        with self.assertRaises(ValueError):
            P.moments(s, [17], m)

    def test_controls_and_residue_binding(self):
        m = meter()
        actual = P.Workspace('mu', 31, m)
        control = P.Workspace('partial_prime_13', 31, m)
        self.assertEqual(actual.values[:14], control.values[:14])
        self.assertEqual(control.values[17], 1)
        self.assertEqual(actual.values[17], -1)
        self.assertEqual(control.values[25], 0)
        p = {'shifts': ['1/6']}
        first, second = actual.evaluate(p), control.evaluate(p)
        self.assertTrue(first['normalizer'][0]['coefficient'].overlaps(second['normalizer'][0]['coefficient']))
        self.assertFalse(first['centered'][31].overlaps(second['centered'][31]))

    def test_domain_and_work_guards(self):
        for p in ({'shifts': []}, {'shifts': ['0']}, {'shifts': ['1']},
                  {'shifts': ['2/6']}, {'shifts': ['1/2','1/3']},
                  {'shifts': ['1/3','1/3']}, {'shifts': ['1/25']},
                  {'shifts': ['1/2'], 'extra': True}):
            with self.assertRaises(ValueError):
                P.validate(p)
        with self.assertRaises(ValueError):
            P.horizon(True)
        with self.assertRaises(OverflowError):
            P.Meter(1).charge(2)
        self.assertEqual(len(P.catalogue()), 25)
        self.assertFalse(any(P.FLAGS.values()))


def tearDownModule():
    print('SYNTHETIC_WORK module=test_shifted_quotient_candidates operations=' + str(sum(m.operations for m in METERS)))


if __name__ == '__main__':
    unittest.main()
