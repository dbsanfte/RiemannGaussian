import json
from pathlib import Path
import tempfile
import unittest

import run_core_bound_goal_search as R


class RunnerTests(unittest.TestCase):
    def test_exact_parent_bytes_and_status(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            parent = root/'parent'
            (parent/'publication-001').mkdir(parents=True)
            payload = b'{"open":true}\n'
            (root/R.INPUT).write_bytes(payload)
            (parent/'publication-001/next_search_input.json').write_bytes(payload)
            (parent/'report.json').write_text(json.dumps(dict(status='SPLIT_AND_PROOF_ROUTE_COMPONENT_CONTROLS_VERIFIED_WITH_OPEN_SIGNED_CORE')))
            R.require_current_input(root, parent)
            (root/R.INPUT).write_bytes(payload+b' ')
            with self.assertRaises(ValueError):
                R.require_current_input(root, parent)

    def test_all_failure_costs_in_development_receipt(self):
        receipt = dict(operations=12, runs=[dict(returncode=1, operations=5), dict(returncode=0, operations=7)])
        self.assertEqual(R.validate_receipts([receipt]), 12)
        with self.assertRaises(ValueError):
            R.validate_receipts([dict(receipt, operations=7)])

    def test_immutable_artifact_writer(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'artifact.json'
            R.write(path, dict(status='open'))
            with self.assertRaises(FileExistsError):
                R.write(path, dict(status='proved'))
            self.assertEqual(R.read(path), dict(status='open'))


if __name__ == '__main__':
    unittest.main()
