import tempfile
import time
from pathlib import Path
import unittest
from unittest.mock import patch
import run_primitive_state_direct_identity_probe as R

class RunnerTests(unittest.TestCase):
    def test_actual_parent_compact_math_plan_protocol(self):
        parent,vector=R.load_parent();self.assertEqual(len(vector),1957);self.assertEqual(parent['candidate_source'],R.PARENT+'/jobs/endpoint.json');plan=R.P.preflight(vector,R.PROGRAM,X=7);self.assertLess(len(R.P.encoded(plan)),R.LIMITS['max_plan_bytes']);self.assertLess(len(R.P.encoded(R.protocol(parent))),65536);self.assertEqual(R.overhead_reserve(),50000000)
    def test_complete_tiny_lifecycle_one_producer_no_worker_replay(self):
        vector=['0']*1957;plan=R.P.preflight(vector,R.PROGRAM,X=1)
        with tempfile.TemporaryDirectory()as d,patch.object(R.P,'preflight',return_value=plan):
            result=R.process_probe(vector,directory=d,deadline=time.monotonic()+30,overhead_work_reserve=50000000)
            self.assertTrue(result['producer_complete'],result.get('reason'));self.assertTrue(result['probe_complete']);self.assertEqual(result['ledger']['total_work_reserve'],450000000);self.assertEqual(set(result['artifacts']),{'plan','probe'});self.assertFalse(result['identity_refuted']);self.assertEqual(R.read(Path(d)/'progress.json')['phase'],'terminal_probe_complete')
    def test_exhaustion_retains_reserves_and_no_partial_row(self):
        vector=['0']*1957;plan=R.P.preflight(vector,R.PROGRAM,X=1);old=R.P.probe
        def limited(*args,**kwargs):kwargs['max_operations']=100;return old(*args,**kwargs)
        with tempfile.TemporaryDirectory()as d,patch.object(R.P,'preflight',return_value=plan),patch.object(R.P,'probe',side_effect=limited):
            result=R.process_probe(vector,directory=d,deadline=time.monotonic()+30,overhead_work_reserve=50000000);self.assertFalse(result['producer_complete']);self.assertEqual(result['ledger']['allocations']['final_independent_direct_evaluation'],200000000);receipt=R.read(Path(d)/'probe.json');self.assertIsNone(receipt['feedback_row'])
    def test_worker_terminal_exception_records_cost(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate',side_effect=ValueError('invalid math input')):
            transport=R.worker(dict(directory=d,phase='probe',index=0));job=R.read(Path(d)/transport['file']);self.assertEqual(job['status'],'UNKNOWN');self.assertFalse(job['producer_complete']);self.assertIn('peak_rss_kib',job['cost']);self.assertFalse(job['identity_refuted'])
    def test_final_deadline_revokes_producer_completion(self):
        result=dict(status='probe_complete',producer_complete=True,probe_complete=True,nonconstant_difference=1)
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate',return_value=({},['0']*1957)),patch.object(R,'process_probe',return_value=result),patch.object(R.time,'monotonic',side_effect=[0.,3601.,3601.]):
            transport=R.worker(dict(directory=d,phase='probe',index=0));job=R.read(Path(d)/transport['file']);self.assertTrue(job['deadline_exceeded']);self.assertFalse(job['producer_complete']);self.assertFalse(job['probe_complete']);self.assertEqual(job['status'],'UNKNOWN')
    def test_declaration_explicit_new_representation_and_whole_audit(self):
        p=R.protocol({});self.assertTrue(p['no_symbolic_polynomial_materialization']);self.assertTrue(p['no_python_source_tracing']);self.assertEqual(p['worker_independent_direct_evaluations'],0);self.assertEqual(p['predecessor_publication'],R.PREDECESSOR);self.assertIn('check_primitive_state_direct_identity_probe_run.py',R.sources())

if __name__=='__main__':unittest.main()
