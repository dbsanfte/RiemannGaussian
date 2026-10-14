import tempfile
import time
from pathlib import Path
import unittest
from unittest.mock import patch
import run_primitive_state_fresh_identity_probe as R

def tiny_case(index):return dict(index=index,X=1,H=3,assignment=[3,5,7]if index==0 else[-2,5,-10])

class RunnerTests(unittest.TestCase):
    def test_actual_recovered_metadata_vector_and_plan_envelopes_no_scores(self):
        parent,vector=R.load_parent();self.assertEqual(parent['candidate_source'],R.ENDPOINT);self.assertTrue(parent['original_producer_unknown_not_promoted']);self.assertEqual(len(vector),1957);self.assertLess(len(R.P.encoded(vector)),1048576);self.assertLess(len(R.P.encoded(R.protocol())),65536)
        for case in R.CASES:self.assertLess(len(R.P.encoded(R.P.preflight(vector,R.PROGRAM,X=case['X'],assignment=case['assignment'],case_index=case['index']))),262144)
        self.assertEqual(R.CASES[1]['assignment'][0],-2);self.assertEqual(R.CASES[1]['assignment'][-1],-1226);self.assertEqual(R.PARALLEL['workers'],2);self.assertEqual(R.PARALLEL['worker_memory_bytes'],3*1024**3);self.assertEqual(R.ledger()['total_work_reserve'],450000000)
    def test_tiny_two_case_directories_shared_joint_ledger(self):
        vector=['0']*1957
        with tempfile.TemporaryDirectory()as d:
            for index in range(2):
                sub=Path(d)/('case-%02d'%index);out=R.process_case(vector,tiny_case(index),directory=sub,deadline=time.monotonic()+30);self.assertTrue(out['producer_complete'],out.get('reason'));self.assertEqual(out['ledger'],R.ledger());self.assertEqual(out['producer_case_reserve'],100000000);self.assertEqual(R.read(sub/'progress.json')['phase'],'terminal_probe_complete');self.assertEqual(R.read(sub/'probe.json')['case_index'],index);self.assertFalse(out['nonconstant_formal_identity_refuted'])
    def test_mocked_worker_indexes_cost_and_terminal_serialization(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate',return_value=['0']*1957),patch.object(R,'CASES',[tiny_case(0),tiny_case(1)]):
            for i in range(2):
                transport=R.worker(dict(directory=d,index=i,phase='probe'));job=R.read(Path(d)/transport['file']);self.assertTrue(job['producer_complete']);self.assertEqual(job['case_index'],i);self.assertIn('peak_rss_kib',job['cost']);self.assertEqual(transport['file'],'jobs/case-%02d/probe-job.json'%i)
    def test_failure_and_final_deadline_reserve_both_cases_audit(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate',side_effect=ValueError('bad plan')):
            t=R.worker(dict(directory=d,index=1,phase='probe'));job=R.read(Path(d)/t['file']);self.assertFalse(job['producer_complete']);self.assertEqual(job['ledger']['allocations']['final_independent'],200000000);self.assertEqual(job['ledger']['allocations']['producer_cases'],{'case-00':100000000,'case-01':100000000})
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate',return_value=['0']*1957),patch.object(R,'process_case',return_value=dict(status='probe_complete',producer_complete=True,probe_complete=True)),patch.object(R.time,'monotonic',side_effect=[0.,3601.,3601.]):
            t=R.worker(dict(directory=d,index=0,phase='probe'));job=R.read(Path(d)/t['file']);self.assertTrue(job['deadline_exceeded']);self.assertFalse(job['producer_complete']);self.assertFalse(job['probe_complete']);self.assertEqual(job['status'],'UNKNOWN')

if __name__=='__main__':unittest.main()
