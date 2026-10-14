from copy import deepcopy
import unittest
import run_prime_scale_dense_054 as R


REQUEST = {'alpha': '1/5', 'q': 2, 'coefficients': [2, -3, 1],
    'bound': {'C': '2', 'log_power': '0', 'minimum': 2, 'normalization': 'divide_by_alpha'}}


class DenseRunnerTests(unittest.TestCase):
    def counts(self, n=None):
        scope = R.expected_coverage(REQUEST, n)
        return {k: scope[k] for k in ('tested', 'skipped_prior', 'untested_after_stop')}

    def test_complete_new_domain(self):
        scope = R.expected_coverage(REQUEST)
        self.assertEqual(scope['maximum'], 32000)
        self.assertEqual(scope['skipped_prior'], 270)
        self.assertEqual(scope['tested'], 31729)
        result = R.admit_scope(REQUEST, self.counts())
        self.assertEqual(result['status'], 'OPEN_AFTER_DENSE_FINITE_TESTS')
        self.assertFalse(result['uniform_arithmetic_bound_proved'])

    def test_stop_at_first_new_endpoint_counts_unvisited_tail(self):
        scope = R.expected_coverage(REQUEST, 257)
        self.assertEqual(scope['tested'], 1)
        self.assertEqual(scope['untested_after_stop'], 31728)
        with self.assertRaises(ValueError): R.expected_coverage(REQUEST, 263)
        with self.assertRaises(ValueError): R.expected_coverage(REQUEST, 32001)

    def test_witness_cannot_promote_without_independent_same_source_refutation(self):
        witness = {'N': 257}
        check = {'verified': True, 'status': 'FINITE_REFUTATION', 'request': REQUEST, 'N': 257}
        result = R.admit_scope(REQUEST, self.counts(257), witness, check)
        self.assertEqual(result['status'], 'REFUTED_FIXED_UNIFORM_BOUND')
        self.assertFalse(result['RH_refuted'])
        for key, value in [('verified', False), ('status', 'FINITE_PASS'), ('N', 258), ('request', {})]:
            bad = deepcopy(check); bad[key] = value
            with self.assertRaises(ValueError): R.admit_scope(REQUEST, self.counts(257), witness, bad)
        with self.assertRaises(ValueError): R.admit_scope(REQUEST, self.counts(257), witness)

    def test_missing_or_repeated_coverage_rejected(self):
        for change in (-1, 1):
            bad = self.counts(); bad['tested'] += change
            with self.assertRaises(ValueError): R.admit_scope(REQUEST, bad)


def tearDownModule(): print('SYNTHETIC_WORK operations=72; coverage and admission metadata only')


if __name__ == '__main__': unittest.main()
