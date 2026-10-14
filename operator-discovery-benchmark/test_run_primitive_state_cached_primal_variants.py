import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch
import run_primitive_state_cached_primal_variants as R
from test_primitive_state_cached_primal_variants import fixture

class RunnerTests(unittest.TestCase):
    def test_real_protocol_and_parent_license(self):
        license=R.load_license();protocol=R.protocol(license)
        self.assertEqual(len(license['selected_original_indices']),779);self.assertEqual(protocol['variants'],R.P.VARIANTS);self.assertEqual(set(protocol['solver_contracts']),{x['id'] for x in R.P.VARIANTS})
        self.assertFalse(protocol['exact_basis_replay_per_solver']);self.assertEqual(R.LIMITS['max_work'],450000000)
    def test_complete_tiny_cache_then_variant(self):
        args,cache=fixture()
        with tempfile.TemporaryDirectory() as d:
            prep=R.process_prepare(*args,directory=Path(d)/'prepare',deadline=time.monotonic()+20,compilation_work_reserve=1,parent_assembly=cache['assembly'],parent_bindings=cache['parent_bindings'])
            self.assertEqual(prep['status'],'cache_verified');read,_=R.P.read_cache(Path(d)/'prepare/source-cache.json',expected_sha256=prep['cache_binding']['cache_file_hash'])
            result=R.process_variant(read,prep['cache_binding'],'qdldl_default',directory=Path(d)/'variant',deadline=time.monotonic()+20)
            self.assertEqual(result['status'],'trace_verified');self.assertLessEqual(result['ledger']['total_work_reserve'],450000000)
    def test_unknown_preserves_conservative_allocation(self):
        args,cache=fixture()
        with tempfile.TemporaryDirectory() as d,patch.object(R.P,'decode_cache',side_effect=TimeoutError('tiny deadline')):
            result=R.process_variant(cache,{},'qdldl_default',directory=d,deadline=time.monotonic()+20)
            self.assertEqual(result['status'],'missing_resource');self.assertTrue(result['numerical_verification_pending']);self.assertEqual(result['ledger']['entries'][1]['reserve'],R.LIMITS['max_cache_bytes']+R.LIMITS['producer_operations'])

    def test_prepare_assembly_and_encoding_share_work_allowance(self):
        import copy
        args,cache=fixture();assembly=copy.deepcopy(cache['assembly']);assembly['counts']['operations']=R.LIMITS['producer_operations']
        with tempfile.TemporaryDirectory() as d,patch.object(R.P.P,'assemble',return_value=({},assembly)),patch.object(R.P,'encode_cache') as encode:
            result=R.process_prepare(*args,directory=d,deadline=time.monotonic()+20,compilation_work_reserve=1,parent_assembly=assembly,parent_bindings={})
            self.assertEqual(result['status'],'missing_resource');encode.assert_not_called()
            self.assertEqual(result['ledger']['entries'][1]['reserve'],R.LIMITS['max_cache_bytes']+R.LIMITS['producer_operations'])

    def test_failed_preparation_transport_cannot_start_variants(self):
        record=dict(status='cache_verified',cost={})
        self.assertFalse(R.preparation_ready(dict(results=[dict(status='error')]),record,Path('unused')))
        with patch.object(R.R,'sha',return_value='checked'):
            value=dict(file='jobs/prepare/job.json',sha256='checked',status='cache_verified',cost={},**R.FLAGS)
            self.assertTrue(R.preparation_ready(dict(results=[dict(status='available',value=value)]),record,Path('unused')))
            value['sha256']='changed'
            self.assertFalse(R.preparation_ready(dict(results=[dict(status='available',value=value)]),record,Path('unused')))
    def test_worker_lifecycle_terminal_cost_serialization(self):
        args,cache=fixture()
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'jobs/prepare').mkdir(parents=True);R.SOURCE.bounded_write(root/'jobs/prepare/source-cache.json',cache,R.LIMITS['max_cache_bytes']);b=R.binding(cache,root/'jobs/prepare/source-cache.json');R.SOURCE.bounded_write(root/'jobs/prepare/job.json',dict(status='cache_verified',cache_binding=b),65536)
            with patch.object(R,'validate',return_value={}),patch.object(R,'require_verified_runtime'),patch.object(R,'process_variant',return_value=dict(status='trace_verified',artifacts={},numerical_verification_pending=False)):
                result=R.worker(dict(directory=d,phase='variant',index=0))
            record=R.read(root/'jobs/qdldl_default/job.json',65536);self.assertEqual(result['status'],'trace_verified');self.assertGreater(record['cost']['pid'],0);self.assertIn('observed_threads_at_completion',record['cost'])
