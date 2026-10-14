import unittest
from unittest.mock import patch
import run_cancellation_gram_probe as R


class Tests(unittest.TestCase):
    def test_training_preparation_failure_is_missing(self):
        with patch.object(R.R, 'build', side_effect=OverflowError('injected preparation cap')):
            row = R.train({'claim': 'critical'}, [1, 2], R.LIMITS)
        self.assertEqual(row['synthesis']['status'], 'missing_resource')
        self.assertEqual(row['case_hashes'], [])
        self.assertEqual(row['budgets'], [])
        self.assertIsNone(row['independent_check'])
        self.assertIsNone(row['gamma'])

    def test_transfer_keeps_all_resource_failures(self):
        attempt = dict(program={}, synthesis=dict(status='finite_PSD_certificate',
            weights={'square_weights': [], 'relation_weights': []}, grams={}))
        with patch.object(R.R, 'build', side_effect=TimeoutError('injected transfer cap')):
            final = R.transfer(attempt, [11, 13], R.LIMITS)
        self.assertFalse(final['refitted'])
        self.assertEqual([r['X'] for r in final['observations']], [11, 13])
        for row in final['observations']:
            self.assertEqual(row['status'], 'missing_resource')
            self.assertIsNone(row['case_sha256'])
            self.assertIsNone(row['scalar_budget'])


if __name__ == '__main__':
    unittest.main()
