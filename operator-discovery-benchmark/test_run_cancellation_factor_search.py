import unittest
from unittest.mock import patch
import run_cancellation_factor_search as R


class Tests(unittest.TestCase):
    def test_preparation_resource_failure_cannot_admit(self):
        with patch.object(R, 'build', side_effect=OverflowError('injected factor domain cap')):
            row = R.train({}, [1,2], R.LIMITS)
        self.assertEqual(row['synthesis']['status'], 'missing_resource')
        self.assertEqual(row['case_hashes'], [])
        self.assertEqual(row['factor_archive_hashes'], [])
        self.assertEqual(row['budgets'], [])
        self.assertIsNone(row['independent_check'])

    def test_final_resource_missingness_keeps_all_scales(self):
        attempt = dict(program={}, synthesis=dict(status='finite_PSD_certificate', weights={}, grams={}))
        with patch.object(R, 'build', side_effect=TimeoutError('injected factor transfer cap')):
            result = R.transfer(attempt, [7,11], R.LIMITS)
        self.assertEqual([r['X'] for r in result['observations']], [7,11])
        self.assertFalse(result['refitted'])
        for row in result['observations']:
            self.assertEqual(row['status'], 'missing_resource')
            self.assertIsNone(row['case_sha256'])
            self.assertIsNone(row['factor_archive_sha256'])
            self.assertIsNone(row['scalar_budget'])


if __name__ == '__main__':
    unittest.main()
