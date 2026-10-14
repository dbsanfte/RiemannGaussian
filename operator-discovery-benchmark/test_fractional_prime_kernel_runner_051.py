from copy import deepcopy
import unittest
import run_fractional_prime_kernel_051 as R

OPERATIONS = 0


class RunnerTests(unittest.TestCase):
    def test_receipt_formats_and_preserved_fixture_correction(self):
        global OPERATIONS
        for key in ('invocations', 'runs'):
            value = {key: [{'returncode': 0, 'tests': 3, 'operations': 7}]}
            self.assertEqual(R.check_receipt(value), 7); OPERATIONS += 7
        value = {'invocations': [{'returncode': 1, 'tests': 3, 'operations': 7},
                                 {'returncode': 0, 'tests': 1, 'operations': 2}],
                 'final_status': 'PASS', 'prior_failure_preserved': True,
                 'correction': 'changed no-op synthetic mutation'}
        self.assertEqual(R.check_receipt(value), 9); OPERATIONS += 9

    def test_failed_or_unmetered_receipt_not_admitted(self):
        for value in ({'invocations': []}, {'invocations': [{'returncode': 1, 'tests': 1, 'operations': 1}]},
                      {'runs': [{'returncode': 0, 'tests': 1, 'operations': None}]},
                      {'runs': [{'returncode': False, 'tests': 1, 'operations': 1}]}):
            with self.assertRaises(ValueError): R.check_receipt(value)

    def test_disjoint_fixed_final_and_training_sets(self):
        self.assertFalse(set(R.FINAL) & set(R.TRAIN+R.SPEC['irregular_numbers']))
        self.assertEqual(len(R.FINAL), len(set(R.FINAL)))
        self.assertEqual(len(R.FINAL), 23)
        self.assertTrue({2, 6, 30}.issubset(R.TRAIN))

    def test_numeric_and_symbolic_disagreement_is_not_silenced(self):
        row = {'id': 'synthetic', 'request': {}, 'role': 'discovery',
               'finite_status': 'FINITE_NEGATIVE_COUNTEREXAMPLE', 'finite_negative_witness': {'n': 2}}
        with self.assertRaises(ValueError):
            R.assess_proof(row, {}, {'verified': True, 'uniform_pointwise_control_proved': True})
        row['finite_negative_witness'] = None
        with self.assertRaises(ValueError):
            R.assess_proof(row, {}, {'verified': True, 'uniform_pointwise_control_proved': False})
        with self.assertRaises(ValueError): R.assess_proof(row, {}, {'verified': False})

    def test_consistent_proofs_keep_finite_and_uniform_status_separate(self):
        row = {'id': 'synthetic', 'request': {}, 'role': 'discovery',
               'finite_status': 'NO_FINITE_NEGATIVE_WITH_UNRESOLVED', 'finite_negative_witness': None}
        result = R.assess_proof(row, {'branch': 'synthetic'},
                               {'verified': True, 'uniform_pointwise_control_proved': True})
        self.assertEqual(result['finite_status'], 'NO_FINITE_NEGATIVE_WITH_UNRESOLVED')
        self.assertTrue(result['finite_and_symbolic_status_consistent'])


def tearDownModule():
    print('SYNTHETIC_WORK operations=%d; no source values or bank observations' % OPERATIONS)


if __name__ == '__main__': unittest.main()
