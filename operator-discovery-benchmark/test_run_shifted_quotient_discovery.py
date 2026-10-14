import unittest
from flint import arb, ctx
import run_shifted_quotient_discovery as R

OPERATIONS = 0


class WorkflowChecks(unittest.TestCase):
    def setUp(self):
        ctx.prec = 128

    def test_fit_is_upward_and_validation_does_not_refit(self):
        global OPERATIONS
        rows = [dict(X=x, energy=arb(3)/7, absolute_energy=arb(8)) for x in R.TRAIN]
        fitted = R.constants(rows)
        before = dict(fitted)
        for r in rows:
            for q in R.LEVELS:
                self.assertTrue(r['energy'] <= R.P.real(fitted[str(q)])*arb(r['X'])**(arb(1)/q))
                OPERATIONS += 70
        result = R.scores([dict(X=768, energy=arb(100), absolute_energy=arb(1000))], fitted,
                          {768: dict(energy=arb(1))})
        self.assertEqual(fitted, before)
        self.assertEqual(result['growth_failures'], 4)
        self.assertFalse(result['numerical_lead'])
        OPERATIONS += 300

    def test_cancellation_proxy_cannot_promote_bad_full_energy(self):
        global OPERATIONS
        fitted = {str(q): '100' for q in R.LEVELS}
        out = R.scores([dict(X=768, energy=arb(2), absolute_energy=arb(100000))], fitted,
                       {768: dict(energy=arb(1))})
        self.assertEqual(out['growth_failures'], 0)
        self.assertFalse(out['numerical_lead'])
        self.assertEqual(out['worst_full_energy_ratio'], 2)
        OPERATIONS += 300

    def test_tightness_and_interval_disagreement(self):
        global OPERATIONS
        self.assertTrue(R.tight(arb(1)/3))
        self.assertFalse(R.tight(arb('1 +/- 0.1')))
        expected = [dict(X=8, energy='1', absolute_energy='4')]
        R.compare_rows(expected, [dict(X=8, energy=arb(1), absolute_energy=arb(4))])
        with self.assertRaises(ArithmeticError):
            R.compare_rows(expected, [dict(X=8, energy=arb(2), absolute_energy=arb(4))])
        with self.assertRaises(ValueError):
            R.compare_rows(expected, [])
        with self.assertRaises(ValueError):
            R.compare_rows(expected, [dict(X=9, energy=arb(1), absolute_energy=arb(4))])
        OPERATIONS += 100


def tearDownModule():
    print('SYNTHETIC_WORK module=test_run_shifted_quotient_discovery operations='+str(OPERATIONS))


if __name__ == '__main__':
    unittest.main()
