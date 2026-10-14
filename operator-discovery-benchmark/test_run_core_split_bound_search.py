import tempfile
import unittest
from pathlib import Path

import run_core_split_bound_search as R


class RunnerTests(unittest.TestCase):
    def test_receipts_preserve_failed_work(self):
        runs = [dict(returncode=1, operations=7), dict(returncode=0, operations=11)]
        self.assertEqual(R.validate_receipts([dict(runs=runs, operations=18)]), 18)
        with self.assertRaises(ValueError):
            R.validate_receipts([dict(runs=runs, operations=11)])
        with self.assertRaises(ValueError):
            R.validate_receipts([dict(runs=runs[:1], operations=7)])

    def test_current_input_requires_exact_published_bytes(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            parent = root/'prior'
            (parent/'publication-001').mkdir(parents=True)
            (root/R.INPUT).write_text('{}\n')
            (parent/'publication-001/next_search_input.json').write_text('{}\n')
            R.write(parent/'report.json', dict(status='FRAME_RECOVERY_BOUND_REDUCTIONS_AND_COMMON_MODE_OBSTRUCTION_VERIFIED'))
            R.require_current_input(root, parent)
            (root/R.INPUT).write_text('{}')
            with self.assertRaises(ValueError):
                R.require_current_input(root, parent)

    def test_artifacts_never_overwrite_a_terminal_result(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)/'result.json'
            R.write(p, {'status': 'failed'})
            with self.assertRaises(FileExistsError):
                R.write(p, {'status': 'passed'})
            self.assertEqual(R.read(p), {'status': 'failed'})
