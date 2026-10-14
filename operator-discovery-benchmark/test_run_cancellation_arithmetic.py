import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import run_cancellation_arithmetic as R


class Tests(unittest.TestCase):
    def test_all_ablations_and_constraints(self):
        ps = R.programs()
        self.assertEqual(len(ps), 29)
        self.assertEqual(len({R.digest(p) for p in ps}), 29)
        self.assertEqual(sum(p['constraint'] == 'zero_cubic' for p in ps), 9)
        self.assertEqual(sum(p['claim'] == 'unsigned_calibration' for p in ps), 2)
        self.assertEqual(R.constraints(ps[0]), [])
        self.assertEqual(len(R.constraints(ps[18])), 1)
        self.assertEqual(len(R.constraints(ps[18])[0]['square_groups']), 106)

    def test_exclusive_freeze_and_tamper_detection(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)/'source'; root.mkdir()
            (root/'fixture').write_text('test')
            dest = Path(d)/'run'
            with patch.object(R, 'ROOT', root), patch.object(R, 'CODE', ['fixture']):
                R.freeze(dest); R.validate_sources(dest)
                with self.assertRaises(FileExistsError): R.freeze(dest)
                (root/'fixture').write_text('changed')
                with self.assertRaises(ValueError): R.validate_sources(dest)

    def test_absent_candidate_cannot_pass_transfer(self):
        row = R.transfer(dict(program=R.programs()[0], synthesis=dict(status='missing_resource')), [7, 11], R.LIMITS)
        self.assertEqual(row['status'], 'no_candidate')
        self.assertEqual(row['observations'], [])
        self.assertFalse(row['refitted'])

    def test_preparation_resource_failures_are_archived(self):
        p = R.programs()[0]
        with patch.object(R, 'build', side_effect=OverflowError('template cap')):
            row = R.train(p, [1, 2], R.LIMITS)
            self.assertEqual(row['synthesis']['status'], 'missing_resource')
            self.assertTrue(row['external_resource_failure'])
            self.assertEqual(row['requested_scales'], [1, 2])
            result = dict(status='finite_certificate', weights=dict(square_weights=[], relation_weights=[]))
            final = R.transfer(dict(program=p, synthesis=result), [7, 11], R.LIMITS)
            self.assertEqual([o['status'] for o in final['observations']], ['missing_resource']*2)
            self.assertEqual([o['X'] for o in final['observations']], [7, 11])
            self.assertTrue(all(o['case_sha256'] is None for o in final['observations']))


if __name__ == '__main__': unittest.main()
