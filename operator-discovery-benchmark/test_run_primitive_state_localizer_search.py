import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import run_primitive_state_localizer_search as R


class SearchRunner(unittest.TestCase):
    def test_resource_and_complete_language(self):
        self.assertEqual(R.PARALLEL['workers'], 1)
        self.assertEqual(R.PARALLEL['worker_memory_bytes'], 6*1024**3)
        self.assertEqual(R.PARALLEL['memory_budget_bytes'], 6*1024**3)
        self.assertEqual(R.DUAL_LIMITS['max_work'], 450000000)
        self.assertEqual(R.P.gram_specs(), {'full_child':15, 'full_parent':15,'storage_K':15})
        self.assertIn('cancellation_primitive_state_backend.py', R.sources())

    def test_terminal_status_requires_exact_admission_and_binding(self):
        with tempfile.TemporaryDirectory() as td:
            d = Path(td); record = dict(status='exact_separator', independent_check={'verified':True})
            R.R.write(d / 'result.json', record)
            execution = dict(results=[dict(status='available', value=dict(file='result.json', sha256=R.R.sha(d / 'result.json')))])
            self.assertEqual(R.terminal_status(d, execution), 'exact_separator')
            changed = copy.deepcopy(execution); changed['results'][0]['value']['sha256'] = 'bad'
            with self.assertRaises(ValueError):
                R.terminal_status(d, changed)
            self.assertEqual(R.terminal_status(d, dict(results=[dict(status='missing_resource')])), 'missing_resource')


if __name__ == '__main__':
    unittest.main()
