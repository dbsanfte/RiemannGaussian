import tempfile
import time
from pathlib import Path
import unittest
from unittest.mock import patch
import run_primitive_state_feedback_cone_search as R

def mocked_outputs():
    mapping={};mapreceipt=dict(complete=True,counts={'operations':1});proposal=dict(complete=True,counts={'operations':2},stop_reason='budget_stop');endpoint=dict(complete=True,counts={'operations':3})
    return mapping,mapreceipt,proposal,endpoint

class RunnerTests(unittest.TestCase):
    def test_actual_parent_metadata_protocol_and_byte_caps_without_scores(self):
        self.assertEqual(R.load_parent_metadata()['chart'],R.CHART);self.assertLess(len(R.P.encoded(R.protocol())),65536)
        for name,cap in R.CAPS.items():self.assertLessEqual((R.ROOT/name).stat().st_size,cap)
        self.assertEqual(R.ledger()['total_work_reserve'],450000000);self.assertEqual(R.protocol()['worker_independent_checks'],0)
    def test_complete_worker_lifecycle_stage_reserves_and_serialization(self):
        mapping,m,p,e=mocked_outputs()
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate'),patch.object(R,'load_inputs',return_value=(1,2,3,4,5)),patch.object(R.P,'setup',return_value=(mapping,m)),patch.object(R.P,'propose',return_value=p),patch.object(R.P,'exact_endpoint',return_value=e):
            t=R.worker(dict(directory=d,index=0,phase='search'));job=R.read(Path(d)/t['file']);self.assertEqual(job['status'],'endpoint_complete');self.assertTrue(job['endpoint_complete']);self.assertEqual(set(job['artifacts']),{'map','proposal','endpoint'});self.assertEqual(job['stage_counts'],dict(map_setup=m['counts'],proposal=p['counts'],exact_endpoint=e['counts']));self.assertIn('peak_rss_kib',job['cost']);self.assertEqual(R.read(Path(d)/'jobs/progress.json')['phase'],'terminal_endpoint_complete')
    def test_unknown_proposal_durable_terminal_and_no_endpoint(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R.P,'setup',return_value=({},dict(complete=True,counts={'operations':1}))),patch.object(R.P,'propose',return_value=dict(complete=False,counts={'operations':2},reason='model gap')),patch.object(R.P,'exact_endpoint',side_effect=AssertionError('no retry')):
            out=R.process_search((1,2,3,4,5),directory=d,deadline=time.monotonic()+30);self.assertFalse(out['producer_complete']);self.assertFalse(out['endpoint_complete']);self.assertEqual(out['ledger']['allocations']['final_independent'],150000000);self.assertEqual(R.read(Path(d)/'progress.json')['phase'],'terminal_UNKNOWN')
    def test_exception_and_final_deadline_do_not_promote(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate',side_effect=ValueError('bad literal')):
            t=R.worker(dict(directory=d,index=0,phase='search'));out=R.read(Path(d)/t['file']);self.assertFalse(out['endpoint_complete']);self.assertEqual(out['ledger'],R.ledger())
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate'),patch.object(R,'load_inputs',return_value=()),patch.object(R,'process_search',return_value=dict(status='endpoint_complete',producer_complete=True,endpoint_complete=True)),patch.object(R.time,'monotonic',side_effect=[0.,3601.,3601.]):
            t=R.worker(dict(directory=d,index=0,phase='search'));out=R.read(Path(d)/t['file']);self.assertTrue(out['deadline_exceeded']);self.assertFalse(out['endpoint_complete']);self.assertEqual(out['status'],'UNKNOWN')

if __name__=='__main__':unittest.main()
