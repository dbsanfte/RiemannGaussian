import tempfile
import time
from pathlib import Path
import unittest
from unittest.mock import patch
import run_primitive_state_feedback_affine as R
from test_primitive_state_feedback_affine import tiny_complete_inputs

class RunnerTests(unittest.TestCase):
    def test_protocol_actual_metadata_and_caps_without_math_evaluation(self):
        self.assertEqual(R.parent_metadata()['necessary_row'],R.CONSTRAINT);self.assertLess(len(R.P.encoded(R.protocol())),65536)
        for name,cap in R.CAPS.items():self.assertLessEqual((R.ROOT/name).stat().st_size,cap)
        self.assertEqual(R.ledger()['total_work_reserve'],450000000);self.assertEqual(R.protocol()['worker_independent_replay_count'],0);self.assertIn('check_primitive_state_feedback_affine_run.py',R.sources())
    def test_full_mocked_worker_terminal_serialization(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate'),patch.object(R,'load_inputs',return_value=tiny_complete_inputs()):
            t=R.worker(dict(directory=d,index=0,phase='affine'));out=R.read(Path(d)/t['file']);self.assertTrue(out['producer_complete']);self.assertEqual(out['status'],'affine_complete');self.assertIn('peak_rss_kib',out['cost']);self.assertFalse(out['exact_admission']);self.assertTrue((Path(d)/'jobs/chart.json').exists());self.assertEqual(R.read(Path(d)/'jobs/progress.json')['phase'],'terminal_affine_complete')
    def test_pending_and_unknown_reserve_final_independent_work(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R.P,'build',return_value=(None,dict(complete=False,classification=None,chart_available=False,counts={'operations':150000000},reason='operation cap'))):
            out=R.process_affine((),directory=d,deadline=time.monotonic()+30);self.assertFalse(out['producer_complete']);self.assertEqual(out['ledger']['allocations']['final_independent_affine'],250000000);self.assertEqual(out['ledger']['remaining_work'],0)
    def test_terminal_exception_never_promotes(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate',side_effect=ValueError('input error')):
            t=R.worker(dict(directory=d,index=0,phase='affine'));out=R.read(Path(d)/t['file']);self.assertFalse(out['producer_complete']);self.assertFalse(out['chart_available']);self.assertEqual(out['status'],'UNKNOWN');self.assertEqual(out['ledger'],R.ledger())
    def test_final_deadline_revokes_success(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate'),patch.object(R,'load_inputs',return_value=()),patch.object(R,'process_affine',return_value=dict(status='affine_complete',producer_complete=True,chart_available=True)),patch.object(R.time,'monotonic',side_effect=[0.,3601.,3601.]):
            t=R.worker(dict(directory=d,index=0,phase='affine'));out=R.read(Path(d)/t['file']);self.assertTrue(out['deadline_exceeded']);self.assertFalse(out['producer_complete']);self.assertFalse(out['chart_available']);self.assertEqual(out['status'],'UNKNOWN')

if __name__=='__main__':unittest.main()
