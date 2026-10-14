import tempfile
import time
from pathlib import Path
import unittest
from unittest.mock import patch
import run_primitive_state_backtracking_cone_search as R

class RunnerTests(unittest.TestCase):
    def test_actual_metadata_protocol_and_caps_only(self):
        self.assertEqual(R.load_parent_metadata()['warm_publication'],R.WARM_PUBLICATION);self.assertLess(len(R.P.encoded(R.protocol())),65536)
        for name,cap in R.CAPS.items():self.assertLessEqual((R.ROOT/name).stat().st_size,cap)
        self.assertEqual(R.protocol()['search']['power_steps'],0);self.assertEqual(R.protocol()['search']['armijo_trials'],12);self.assertEqual(R.ledger()['allocations'],dict(preparation=50000000,map_setup=5000000,proposal=220000000,exact_endpoint=25000000,final_independent=150000000))
    def test_full_mocked_worker_lifecycle_serializes_cost_terminal(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate'),patch.object(R,'load_inputs',return_value=tuple(range(7))),patch.object(R.P,'setup',return_value=({},dict(complete=True,counts={'operations':1}))),patch.object(R.P,'propose',return_value=dict(complete=True,counts={'operations':2},stop_reason='budget_stop')),patch.object(R.P,'exact_endpoint',return_value=dict(complete=True,counts={'operations':3})):
            transport=R.worker(dict(directory=d,index=0,phase='search'));job=R.read(Path(d)/transport['file']);self.assertEqual(job['status'],'endpoint_complete');self.assertTrue(job['endpoint_complete']);self.assertEqual(set(job['artifacts']),{'map','proposal','endpoint'});self.assertEqual(R.read(Path(d)/'jobs/progress.json')['phase'],'terminal_endpoint_complete');self.assertIn('peak_rss_kib',job['cost']);self.assertFalse(job['exact_admission'])
    def test_setup_and_proposal_failure_never_retry_or_refine(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R.P,'setup',side_effect=OverflowError('setup cap')),patch.object(R.P,'propose',side_effect=AssertionError('no fallback')):
            out=R.process_search(tuple(range(7)),directory=d,deadline=time.monotonic()+30);self.assertEqual(out['status'],'UNKNOWN');self.assertFalse(out['endpoint_complete']);self.assertEqual(out['ledger']['total_work_reserve'],450000000)
        with tempfile.TemporaryDirectory()as d,patch.object(R.P,'setup',return_value=({},dict(complete=True,counts={'operations':1}))),patch.object(R.P,'propose',return_value=dict(complete=False,counts={'operations':2},reason='native proposal failure')),patch.object(R.P,'exact_endpoint',side_effect=AssertionError('no endpoint')):
            out=R.process_search(tuple(range(7)),directory=d,deadline=time.monotonic()+30);self.assertFalse(out['endpoint_complete']);self.assertEqual(out['ledger']['allocations']['final_independent'],150000000);self.assertEqual(R.read(Path(d)/'progress.json')['phase'],'terminal_UNKNOWN')
    def test_terminal_exception_and_clock_do_not_promote(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate',side_effect=ValueError('bad input')):
            t=R.worker(dict(directory=d,index=0,phase='search'));job=R.read(Path(d)/t['file']);self.assertEqual(job['status'],'UNKNOWN');self.assertFalse(job['endpoint_complete']);self.assertEqual(job['ledger'],R.ledger())
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate'),patch.object(R,'load_inputs',return_value=()),patch.object(R,'process_search',return_value=dict(status='endpoint_complete',producer_complete=True,endpoint_complete=True)),patch.object(R.time,'monotonic',side_effect=[0.,3601.,3601.]):
            t=R.worker(dict(directory=d,index=0,phase='search'));job=R.read(Path(d)/t['file']);self.assertTrue(job['deadline_exceeded']);self.assertFalse(job['endpoint_complete']);self.assertEqual(job['status'],'UNKNOWN')

if __name__=='__main__':unittest.main()
