import tempfile
import time
from pathlib import Path
import unittest
from unittest.mock import patch
import run_primitive_state_augmented_cone_search as R

class RunnerTests(unittest.TestCase):
    def test_actual_metadata_and_literal_resource_envelopes_only(self):
        self.assertEqual(R.load_parent_metadata()['extension_publication'],R.FRESH);self.assertLess(len(R.P.encoded(R.protocol())),65536)
        for name,cap in R.CAPS.items():self.assertLessEqual((R.ROOT/name).stat().st_size,cap)
        self.assertEqual(R.ledger()['total_work_reserve'],450000000);self.assertEqual(sum(R.ledger()['allocations'].values()),450000000);self.assertEqual(R.protocol()['search']['power_steps'],8);self.assertEqual(R.protocol()['search']['armijo_trials'],12);self.assertEqual(R.protocol()['pivots'],782)
    def test_full_mocked_worker_writes_chart_center_and_cost(self):
        setup=({},dict(complete=True,counts={'operations':1}),dict(complete=True),dict(complete=True))
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate'),patch.object(R,'load_inputs',return_value=tuple(range(9))),patch.object(R.P,'setup',return_value=setup),patch.object(R.P,'propose',return_value=dict(complete=True,counts={'operations':2},stop_reason='budget_stop')),patch.object(R.P,'exact_endpoint',return_value=dict(complete=True,counts={'operations':3})):
            transport=R.worker(dict(directory=d,index=0,phase='search'));job=R.read(Path(d)/transport['file']);self.assertEqual(job['status'],'endpoint_complete');self.assertEqual(set(job['artifacts']),{'chart','center','map','proposal','endpoint'});self.assertIn('peak_rss_kib',job['cost']);self.assertEqual(R.read(Path(d)/'jobs/progress.json')['phase'],'terminal_endpoint_complete');self.assertFalse(job['exact_admission'])
    def test_setup_failure_no_fallback_or_reserve_refinement(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R.P,'setup',side_effect=OverflowError('whole scaling reservation')),patch.object(R.P,'propose',side_effect=AssertionError('no fallback')):
            out=R.process_search(tuple(range(9)),directory=d,deadline=time.monotonic()+30);self.assertEqual(out['status'],'UNKNOWN');self.assertFalse(out['endpoint_complete']);self.assertEqual(out['ledger'],R.ledger())
    def test_final_deadline_revokes_completion(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate'),patch.object(R,'load_inputs',return_value=()),patch.object(R,'process_search',return_value=dict(status='endpoint_complete',producer_complete=True,endpoint_complete=True)),patch.object(R.time,'monotonic',side_effect=[0.,3601.,3601.]):
            t=R.worker(dict(directory=d,index=0,phase='search'));job=R.read(Path(d)/t['file']);self.assertTrue(job['deadline_exceeded']);self.assertFalse(job['endpoint_complete']);self.assertEqual(job['status'],'UNKNOWN')

if __name__=='__main__':unittest.main()
