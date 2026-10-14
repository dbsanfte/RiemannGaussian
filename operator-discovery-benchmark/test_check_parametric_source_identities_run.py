import json
from pathlib import Path
import shutil
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import run_parametric_source_identities as R
import check_parametric_source_identities_run as C


class WholeCalibrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # An ephemeral test fixture only. Mock the subprocess to avoid recursive
        # unittest invocation; exercise all actual 74 producers/checks/artifacts.
        cls.temp = tempfile.TemporaryDirectory()
        cls.base = Path(cls.temp.name) / 'fixture'
        R.freeze(cls.base)
        simulated = SimpleNamespace(returncode=0, stdout='', stderr='Ran 1 test in 0.000s\n\nOK\n')
        with patch.object(R.subprocess, 'run', return_value=simulated), \
             patch.object(R.resource, 'setrlimit'), \
             patch.object(R.resource, 'getrlimit', return_value=(2*1024**3, 2*1024**3)):
            R.run(cls.base)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def copied(self):
        destination = Path(self.temp.name) / self.id().split('.')[-1]
        shutil.copytree(self.base, destination)
        return destination

    def rebind_test_file(self, directory, name, value):
        # Deliberately mutate only a fresh ephemeral fixture copy, to ensure the
        # auditor checks semantics after a file hash is recomputed.
        path = directory / name
        path.write_bytes(R.P.encoded(value))
        receipt = R.read(directory / 'receipt.json')
        receipt['files_sha256'][name] = R.sha(path)
        (directory / 'receipt.json').write_bytes(R.P.encoded(receipt))

    def test_complete_archive_and_exclusive_review(self):
        d = self.copied()
        result = C.audit(d, write=True)
        self.assertTrue(result['all_passed'])
        self.assertEqual(result['formal_identities_verified'], 74)
        self.assertFalse(result['full_source_compiler_equivalence_formally_proved'])
        self.assertFalse(result['global_bound_proved'])
        with self.assertRaises(FileExistsError):
            C.audit(d, write=True)

    def test_rehashed_theorem_claim_rejected(self):
        d = self.copied()
        execution = R.read(d / 'execution.json')
        execution['RH_proved'] = True
        self.rebind_test_file(d, 'execution.json', execution)
        with self.assertRaises(ValueError):
            C.audit(d)

    def test_missing_recipe_result_rejected(self):
        d = self.copied()
        execution = R.read(d / 'execution.json')
        execution['results'].pop()
        self.rebind_test_file(d, 'execution.json', execution)
        with self.assertRaises(ValueError):
            C.audit(d)

    def test_nested_receipt_cannot_hide_from_inventory(self):
        d = self.copied()
        self.rebind_test_file(d, 'jobs/000/receipt.json', {})
        with self.assertRaises(ValueError):
            C.audit(d)

    def test_caps_and_source_closures(self):
        self.assertEqual(R.sources(), C.sources())
        self.assertEqual(R.RESOURCES, C.RESOURCES)
        self.assertEqual(R.LIMITS, C.LIMITS)
        for kwargs in (dict(max_operations=True), dict(max_operations=100000001), dict(time_limit=301)):
            with self.assertRaises(ValueError):
                C.audit(self.base, **kwargs)


if __name__ == '__main__':
    unittest.main()
