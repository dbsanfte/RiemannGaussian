from fractions import Fraction as F
import copy
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import run_primitive_state_free_cone_search as R
from test_primitive_state_triangular_restoration import fixture as old_fixture


def synthetic_license():
    cache,trace,basis,projection=old_fixture();parent=R.P.EXACT.restore(cache,trace,basis,projection,deadline=time.monotonic()+10)
    budget=R.CHECK.EXACT.EXACT._Budget(None,10000000,10000000,4096);source=R.CHECK.CACHE_CHECK.decode_original(cache,budget);pivots=basis['pivot_columns'];free=[i for i in range(1224) if i not in pivots];vector=list(map(F,parent['restored_projected_vector']))
    summary=dict(normalized_basis_hash=parent['normalized_basis_hash'],rank=len(pivots),free_count=len(free),retained_indices=projection['retained_indices'])
    license=R.CHECK._EndpointLicense(R.CHECK._TOKEN,source,summary,vector,pivots,free,{})
    license.cache=cache;license.basis=basis;license.projection=projection;license.parent_restoration=parent
    return license

class RunnerTests(unittest.TestCase):
    def test_actual_parent_compact_protocol(self):
        license=R.load_license();protocol=R.protocol(license)
        self.assertEqual(license['free_count'],445);self.assertEqual(protocol['precision']['decimal_digits'],80);self.assertTrue(protocol['precision']['mixed_precision']);self.assertLess(len(R.P.encoded(protocol)),65536)
        oversized=copy.deepcopy(license);oversized['padding']='x'*65536
        with self.assertRaises(OverflowError):R.protocol(oversized)
    def test_synthetic_full_pipeline_and_conservative_stages(self):
        with tempfile.TemporaryDirectory() as d:
            result=R.process_search(synthetic_license(),directory=d,deadline=time.monotonic()+30,input_work_reserve=1)
            self.assertEqual(result['status'],'endpoint_verified',result.get('reason'));self.assertTrue(result['finite_candidate_feasible']);self.assertFalse(result['certified'])
            for entry,expected in zip(result['ledger']['entries'][1:4],[50000000,100000000,20000000]):self.assertEqual(entry['reserve'],expected);self.assertEqual(entry['precision'],'allocated_unverified')
    def test_unknown_proposal_preserves_finite_trace_no_endpoint(self):
        license=synthetic_license()
        with tempfile.TemporaryDirectory() as d,patch.object(R.P,'propose',side_effect=TimeoutError('synthetic deadline')):
            result=R.process_search(license,directory=d,deadline=time.monotonic()+30,input_work_reserve=1)
            self.assertEqual(result['status'],'missing_resource');self.assertFalse(result['endpoint_verified']);self.assertIsNone(result['finite_candidate_feasible']);self.assertEqual(result['ledger']['entries'][3]['reserve'],20000000)
    def test_worker_error_terminal_cost_metadata(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d)/'jobs').mkdir()
            with patch.object(R,'require_verified_runtime'),patch.object(R,'validate',side_effect=ValueError('synthetic immutable input changed')):
                result=R.worker(dict(directory=d,phase='search',index=0))
            record=json.loads((Path(d)/'jobs/search-job.json').read_text());self.assertEqual(result['status'],'rejected');self.assertFalse(record['endpoint_verified']);self.assertGreater(record['cost']['pid'],0)
    def test_worker_final_deadline_revokes_success(self):
        license=synthetic_license();license.summary.update(rank=779,free_count=445,original_variables=1957,original_rows=5641,audit_operations=1,audit_cells=1)
        output=dict(status='endpoint_verified',endpoint_verified=True,finite_candidate_feasible=True,artifacts={'endpoint':{'file':'endpoint.json','sha256':'a'}},ledger={'retained':'budget'})
        with tempfile.TemporaryDirectory() as d:
            (Path(d)/'jobs').mkdir()
            with patch.object(R,'require_verified_runtime'),patch.object(R,'validate',return_value=({},{})),patch.object(R,'binding_work_reserve',return_value=1),patch.object(R.CHECK,'load_verified_license',return_value=license),patch.object(R,'process_search',return_value=output),patch.object(R.time,'monotonic',side_effect=[0.,901.,901.]):
                result=R.worker(dict(directory=d,phase='search',index=0))
            record=json.loads((Path(d)/'jobs/search-job.json').read_text());self.assertEqual(result['status'],'missing_resource');self.assertFalse(record['endpoint_verified']);self.assertIsNone(record['finite_candidate_feasible']);self.assertEqual(record['ledger'],output['ledger']);self.assertEqual(record['artifacts'],output['artifacts'])
