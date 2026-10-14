import copy
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch
import run_primitive_state_triangular_restoration as R
from test_primitive_state_triangular_restoration import fixture

class RunnerTests(unittest.TestCase):
    def test_actual_parent_compact_protocol_construction(self):
        license=R.load_license();protocol=R.protocol(license)
        self.assertEqual(license['rank'],779);self.assertFalse(protocol['original_objective_preserved']);self.assertFalse(protocol['optimization_result']);self.assertLess(len(R.P.encoded(protocol)),65536)
        oversized=copy.deepcopy(license);oversized['padding']='x'*65536
        with self.assertRaises(OverflowError):R.protocol(oversized)
    def test_exact_pipeline_and_ledger(self):
        args=fixture()
        with tempfile.TemporaryDirectory() as d:
            result=R.process_restore(*args,directory=d,deadline=time.monotonic()+20,input_work_reserve=1)
            self.assertEqual(result['status'],'restoration_verified');self.assertTrue(result['finite_candidate_feasible']);self.assertFalse(result['certified']);self.assertLess(result['ledger']['total_work_reserve'],450000000)
            self.assertEqual(result['ledger']['entries'][1]['reserve'],125000000)
    def test_unknown_conservative_stage_no_admission(self):
        args=fixture()
        with tempfile.TemporaryDirectory() as d,patch.object(R.P,'restore',side_effect=TimeoutError('tiny timeout')):
            result=R.process_restore(*args,directory=d,deadline=time.monotonic()+20,input_work_reserve=1)
            self.assertEqual(result['status'],'missing_resource');self.assertFalse(result['restoration_verified']);self.assertIsNone(result['finite_candidate_feasible']);self.assertEqual(result['ledger']['entries'][1]['reserve'],125000000)
    def test_worker_terminal_exception_lifecycle(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d)/'jobs').mkdir()
            with patch.object(R,'require_verified_runtime'),patch.object(R,'validate',side_effect=ValueError('synthetic parent changed')):
                transport=R.worker(dict(directory=d,phase='restore',index=0))
            record=R.read(Path(d)/'jobs/restoration-job.json',65536);self.assertEqual(transport['status'],'rejected');self.assertFalse(record['restoration_verified']);self.assertGreater(record['cost']['pid'],0);self.assertIn('observed_threads_at_completion',record['cost'])
    def test_terminal_checkpoint_failure_revokes_verified_state(self):
        args=fixture();original=R.SOURCE.bounded_write
        def writer(path,value,cap):
            if Path(path).name=='progress.json' and value.get('phase')=='restoration_verified':raise OSError('synthetic checkpoint loss')
            return original(path,value,cap)
        with tempfile.TemporaryDirectory() as d,patch.object(R.SOURCE,'bounded_write',side_effect=writer):
            result=R.process_restore(*args,directory=d,deadline=time.monotonic()+20,input_work_reserve=1)
            self.assertEqual(result['status'],'rejected');self.assertFalse(result['restoration_verified']);self.assertIsNone(result['finite_candidate_feasible'])

    def test_final_validation_deadline_revokes_success_preserves_receipts(self):
        cache,trace,basis,projection=fixture();cache['original']['rhs']=['0']*5641;basis['augmented_rank']=779
        def reader(path,cap):
            return cache if str(path).endswith('source-cache.json') else trace if str(path).endswith('trace.json') else basis if str(path).endswith('basis.json') else projection
        result=dict(status='restoration_verified',restoration_verified=True,finite_candidate_feasible=True,artifacts={'restoration':{'file':'restoration.json','sha256':'a'}},ledger={'retained':'proof budget'})
        with tempfile.TemporaryDirectory() as d:
            (Path(d)/'jobs').mkdir()
            with patch.object(R,'require_verified_runtime'),patch.object(R,'validate',return_value={}),patch.object(R,'binding_work_reserve',return_value=1),patch.object(R,'read',side_effect=reader),patch.object(R,'process_restore',return_value=result),patch.object(R.time,'monotonic',side_effect=[0.,901.,901.]):
                transport=R.worker(dict(directory=d,phase='restore',index=0))
            import json
            record=json.loads((Path(d)/'jobs/restoration-job.json').read_text());self.assertEqual(transport['status'],'missing_resource');self.assertFalse(record['restoration_verified']);self.assertIsNone(record['finite_candidate_feasible']);self.assertTrue(record['deadline_exceeded']);self.assertEqual(record['ledger'],result['ledger']);self.assertEqual(record['artifacts'],result['artifacts'])
