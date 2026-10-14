"""Metadata-only continuation guards, charged to the original root reserve."""
from copy import deepcopy
import unittest

from potential_candidate_language import Meter
from complete_permuted_circuit_audit import pending_cases

WORK = 0


def tearDownModule():
    print('CONTINUATION_METADATA_WORK operations=' + str(WORK))


class ContinuationTests(unittest.TestCase):
    def setUp(self):
        self.m = Meter(10000)
        self.rows = [dict(id=i, source='one', horizon=31, status='available') for i in range(3)]
        self.checked = [dict(r, kind='completed_evaluation', finite_verified=True,
                             counts=dict(operations=10 * (r['id'] + 1))) for r in self.rows[:2]]

    def tearDown(self):
        global WORK
        WORK += self.m.operations

    def test_skip_only_exact_successful_prefix(self):
        self.assertEqual(pending_cases(self.rows, self.checked, self.m), self.rows[2:])

    def test_reject_reordered_or_different_source(self):
        with self.assertRaises(ValueError):
            pending_cases(self.rows, self.checked[::-1], self.m)
        bad = deepcopy(self.checked); bad[1]['source'] = 'mu'
        with self.assertRaises(ValueError):
            pending_cases(self.rows, bad, self.m)

    def test_reject_unverified_or_reset_counter(self):
        bad = deepcopy(self.checked); bad[1]['finite_verified'] = False
        with self.assertRaises(ValueError):
            pending_cases(self.rows, bad, self.m)
        bad = deepcopy(self.checked); bad[1]['counts']['operations'] = 1
        with self.assertRaises(ValueError):
            pending_cases(self.rows, bad, self.m)

    def test_reject_extra_checkpoint_or_coerced_identity(self):
        with self.assertRaises(ValueError):
            pending_cases(self.rows[:1], self.checked, self.m)
        bad = deepcopy(self.checked); bad[0]['id'] = False
        with self.assertRaises(ValueError):
            pending_cases(self.rows, bad, self.m)


if __name__ == '__main__':
    unittest.main()
