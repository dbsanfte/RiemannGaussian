import tempfile
import time
from pathlib import Path
import unittest
from unittest.mock import patch
import run_primitive_state_uniform_identity_probe as R
import test_primitive_state_uniform_identity_probe as T

class RunnerTests(unittest.TestCase):
    def test_actual_parent_compact_protocol_overhead(self):
        parent,vector=R.load_parent();self.assertEqual(len(vector),1957);self.assertEqual(parent['candidate_source'],R.PARENT+'/jobs/endpoint.json');self.assertLess(len(R.P.encoded(R.protocol(parent))),65536);self.assertLessEqual(R.overhead_reserve(),50000000)
    def test_actual_parent_plan_size_without_source_evaluation(self):
        parent,vector=R.load_parent();plan=R.P.preflight(['0']*1957,R.PROGRAM,X=7,deadline=time.monotonic()+30)
        plan['candidate_vector']=vector
        self.assertLessEqual(len(R.P.encoded(plan)),R.LIMITS['max_plan_bytes'])
    def test_joint_synthetic_lifecycle_no_worker_checker(self):
        native,vector,plan=T.fixture();native.update(probe_source_meter=dict(line_events=1,cap=150000000),probe_construction_counts=dict(operations=1))
        with tempfile.TemporaryDirectory()as d,patch.object(R.P,'preflight',return_value=plan),patch.object(R.P,'build_native_metered',return_value=native):
            result=R.process_probe(vector,directory=d,deadline=time.monotonic()+30,overhead_work_reserve=100)
            self.assertTrue(result['probe_complete'],result.get('reason'));self.assertFalse(result['identity_refuted']);self.assertEqual(result['ledger']['total_work_reserve'],400000100);self.assertEqual(set(result['artifacts']),{'plan','probe'});self.assertEqual(R.read(Path(d)/'progress.json')['phase'],'terminal_probe_complete')
    def test_unknown_source_keeps_fixed_audit_reserves(self):
        native,vector,plan=T.fixture()
        with tempfile.TemporaryDirectory()as d,patch.object(R.P,'preflight',return_value=plan),patch.object(R.P,'build_native_metered',side_effect=OverflowError('line event cap')):
            result=R.process_probe(vector,directory=d,deadline=time.monotonic()+30,overhead_work_reserve=100)
            self.assertFalse(result['probe_complete']);self.assertEqual(result['ledger']['allocations']['final_independent_source'],150000000);self.assertIsNone(result['nonconstant_difference']);self.assertTrue((Path(d)/'plan.json').exists())
    def test_worker_terminal_exception_has_cost_and_unknown(self):
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate',side_effect=ValueError('bad seal')):
            transport=R.worker(dict(directory=d,phase='probe',index=0));job=R.read(Path(d)/transport['file']);self.assertFalse(job['probe_complete']);self.assertEqual(job['status'],'UNKNOWN');self.assertIn('peak_rss_kib',job['cost']);self.assertFalse(job['identity_refuted'])
    def test_final_deadline_revokes_available_result(self):
        result=dict(status='probe_complete',probe_complete=True,nonconstant_difference=1)
        with tempfile.TemporaryDirectory()as d,patch.object(R,'require_verified_runtime'),patch.object(R,'validate',return_value=({},['0']*1957)),patch.object(R,'overhead_reserve',return_value=100),patch.object(R,'process_probe',return_value=result),patch.object(R.time,'monotonic',side_effect=[0.,3601.,3601.]):
            transport=R.worker(dict(directory=d,phase='probe',index=0));job=R.read(Path(d)/transport['file']);self.assertTrue(job['deadline_exceeded']);self.assertFalse(job['probe_complete']);self.assertEqual(job['status'],'UNKNOWN')
    def test_source_closure_explicit_auditor_and_proof_flags(self):
        source=R.sources();self.assertIn('check_primitive_state_uniform_identity_probe_run.py',source);self.assertFalse(R.protocol({})['identity_refuted']);self.assertEqual(R.protocol({})['worker_independent_source_builds'],0)

if __name__=='__main__':unittest.main()
