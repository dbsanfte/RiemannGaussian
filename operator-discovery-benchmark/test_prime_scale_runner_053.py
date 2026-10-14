from copy import deepcopy
import unittest
import run_prime_scale_search_053 as R


class RunnerTests(unittest.TestCase):
    def rows(self, status='FINITE_PASS'):
        return [{'id': 'synthetic', 'N': n, 'bound_verification': {'status': status}} for n in R.FINAL]

    def test_fresh_partition_and_all_integer_training(self):
        self.assertFalse(set(R.TRAIN)&set(R.FINAL))
        self.assertEqual(R.TRAIN[:255], list(range(2, 257)))
        self.assertEqual(len(R.FINAL), 11)

    def test_finite_passes_cannot_pay_uniform_lemma(self):
        result = R.summarize_candidate({'id': 'synthetic', 'request': {}}, self.rows())
        self.assertEqual(result['status'], 'OPEN_AFTER_FINITE_TESTS')
        self.assertFalse(result['uniform_arithmetic_bound_proved']); self.assertFalse(result['RH_proved'])

    def test_strict_finite_counterexample_refutes_only_fixed_bound(self):
        rows = self.rows(); rows[0]['bound_verification']['status'] = 'FINITE_REFUTATION'
        result = R.summarize_candidate({'id': 'synthetic', 'request': {}}, rows)
        self.assertEqual(result['status'], 'REFUTED_FIXED_UNIFORM_BOUND')
        self.assertEqual(result['counterexample_scales'], [R.FINAL[0]])
        self.assertFalse(result['RH_refuted'])

    def test_unresolved_interval_and_missing_coverage(self):
        result = R.summarize_candidate({'id': 'synthetic', 'request': {}}, self.rows('UNRESOLVED_INTERVAL'))
        self.assertEqual(result['status'], 'OPEN_AFTER_FINITE_TESTS')
        with self.assertRaises(ValueError): R.summarize_candidate({'id': 'synthetic', 'request': {}}, self.rows()[:-1])


def tearDownModule(): print('SYNTHETIC_WORK operations=44; status/partition metadata only')


if __name__ == '__main__': unittest.main()
