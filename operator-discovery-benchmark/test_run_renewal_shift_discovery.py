import unittest
from flint import arb, ctx
import run_renewal_shift_discovery as R

METERS = []


class WorkflowChecks(unittest.TestCase):
    def setUp(self):
        ctx.prec = 128
        self.m = R.P.Meter()
        METERS.append(self.m)

    def test_upward_training_fit_is_unchanged_by_failed_validation(self):
        rows = [dict(X=x, energy=arb(3)/7, absolute_energy=arb(8)) for x in R.TRAIN]
        fitted = R.constants(rows, self.m)
        before = dict(fitted)
        for row in rows:
            for q in R.LEVELS:
                self.m.charge(72)
                self.assertTrue(row['energy'] <= R.P.real(fitted[str(q)])*arb(row['X'])**(arb(1)/q))
        result = R.scores([dict(X=896, energy=arb(100), absolute_energy=arb(1000))], fitted,
                          {896: dict(energy=arb(1))}, self.m)
        self.assertEqual(fitted, before)
        self.assertEqual(result['growth_failures'], 4)
        self.assertFalse(result['numerical_lead'])

    def test_absolute_envelope_cannot_promote_bad_full_energy(self):
        fitted = {str(q): '100' for q in R.LEVELS}
        result = R.scores([dict(X=896, energy=arb(2), absolute_energy=arb(100000))], fitted,
                          {896: dict(energy=arb(1))}, self.m)
        self.assertEqual(result['growth_failures'], 0)
        self.assertFalse(result['numerical_lead'])
        self.assertEqual(result['worst_full_energy_ratio'], 2)

    def test_interval_checks_require_tight_complete_agreement(self):
        self.assertTrue(R.tight(arb(1)/3))
        self.assertFalse(R.tight(arb('1 +/- 0.1')))
        expected = [dict(X=8, energy='1', absolute_energy='4')]
        R.compare_rows(expected, [dict(X=8, energy=arb(1), absolute_energy=arb(4))])
        with self.assertRaises(ArithmeticError):
            R.compare_rows(expected, [dict(X=8, energy=arb(2), absolute_energy=arb(4))])
        with self.assertRaises(ValueError): R.compare_rows(expected, [])
        with self.assertRaises(ValueError):
            R.compare_rows(expected, [dict(X=9, energy=arb(1), absolute_energy=arb(4))])
        normalizer = [dict(shift='1/6', residue='1', coefficient='6/5')]
        actual = [dict(shift='1/6', residue=arb(1), coefficient=arb(6)/5)]
        R.compare_normalizer(normalizer, actual)
        with self.assertRaises(ValueError): R.compare_normalizer(normalizer, [])
        actual[0]['coefficient'] = arb('1.2 +/- 0.01')
        with self.assertRaises(ArithmeticError): R.compare_normalizer(normalizer, actual)
        self.m.charge(150)

    def test_challenger_selection_does_not_imply_admission(self):
        records = []
        for depth in range(1, 5):
            for i, ratio in enumerate((3, 2, 1)):
                records.append(dict(id=10*depth+i, depth=depth, source='mu', program={'shifts':['1/6']},
                                    stencil=[['0', -1], ['1/6', 1]], normalization='1/6', constants={},
                                    scores=dict(growth_failures=1 if i == 2 else 0,
                                                worst_full_energy_ratio=ratio, numerical_lead=False)))
        choices = R.selected(records)
        self.assertEqual([c['id'] for c in choices], [11, 21, 31, 41])
        self.assertTrue(all(not c['scores']['numerical_lead'] for c in choices))


def tearDownModule():
    print('SYNTHETIC_WORK module=test_run_renewal_shift_discovery operations='+str(sum(m.operations for m in METERS)))


if __name__ == '__main__': unittest.main()
