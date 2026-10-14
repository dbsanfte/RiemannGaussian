import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import run_grouped_arithmetic as runner


class Tests(unittest.TestCase):
    def test_program_coverage(self):
        cases = runner.programs()
        self.assertEqual(len(cases), 10)
        self.assertEqual(len({runner.digest(c) for c in cases}), 10)
        self.assertEqual(sum(c['claim'] == 'critical' for c in cases), 8)

    def test_exclusive_freeze_and_integrity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'src'
            root.mkdir()
            (root / 'fixture').write_text('immutable source')
            prior = root / 'arithmetic-cycle-results/pilot-001'
            prior.mkdir(parents=True)
            (prior / 'independent_verification.json').write_text('{}')
            dest = Path(directory) / 'run'
            with patch.object(runner, 'ROOT', root), patch.object(runner, 'CODE', ['fixture']):
                runner.freeze(dest)
                runner.validate_sources(dest)
                with self.assertRaises(FileExistsError):
                    runner.freeze(dest)
                (root / 'fixture').write_text('changed')
                with self.assertRaises(ValueError):
                    runner.validate_sources(dest)

    def test_no_candidate_is_not_a_pass(self):
        result = runner.transfer(dict(program=runner.programs()[0],
                                      synthesis=dict(status='no_certificate_found')), [8, 11], runner.LIMITS)
        self.assertEqual(result['status'], 'no_candidate')
        self.assertEqual(result['observations'], [])
        self.assertFalse(result['refitted'])


if __name__ == '__main__':
    unittest.main()
