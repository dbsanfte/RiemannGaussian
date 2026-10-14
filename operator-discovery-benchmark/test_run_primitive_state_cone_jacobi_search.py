"""Protocol and terminal lifecycle tests, without research execution."""
from fractions import Fraction as F
import copy
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import run_primitive_state_cone_jacobi_search as R
from test_primitive_state_cone_jacobi_search import fixture


def synthetic_license():
    mapping,receipt,cache,basis,projection,parent,seed=fixture()
    budget=R.CHECK.EXACT.EXACT._Budget(None,10000000,10000000,4096);source=R.CHECK.OLD.CACHE_CHECK.decode_original(cache,budget)
    summary=dict(normalized_basis_hash=parent['normalized_basis_hash'],rank=len(mapping['pivots']),free_count=len(mapping['free']),original_variables=1957,original_rows=len(source['monomials']),projected_variables=1224,retained_indices=mapping['retained'],pivot_columns=mapping['pivots'],free_indices=mapping['free'],parent_projected_hash=R.P.digest(seed['final_projected_vector']),parent_free_hash=R.P.digest(seed['final_free_vector']),sparse_map_entries=receipt['sparse_map_entries'])
    old=R.CHECK.OLD._EndpointLicense(R.CHECK.OLD._TOKEN,source,summary,list(map(F,parent['restored_projected_vector'])),mapping['pivots'],mapping['free'],{},cache=cache,basis=basis,projection=projection,parent_restoration=parent)
    return R.CHECK._EndpointLicense(R.CHECK._TOKEN,old,summary,list(map(F,seed['final_projected_vector'])),{},seed)

class RunnerTests(unittest.TestCase):
    def test_actual_parent_compact_protocol_and_resource_room(self):
        license=R.load_license();value=R.protocol(license)
        self.assertEqual(license['publication'],'publication-018');self.assertEqual(value['search']['gradient_iterations'],64);self.assertFalse(value['column_norms_independently_verified']);self.assertLess(len(R.P.encoded(value)),65536)
        over=copy.deepcopy(license);over['padding']='x'*65536
        with self.assertRaises(OverflowError):R.protocol(over)
        self.assertEqual(R.LIMITS['worker_max_work']+R.LIMITS['final_archive_audit_operations'],450000000)
        remaining=R.LIMITS['worker_max_work']-R.binding_work_reserve()-250000000-sum(R.ARTIFACT_CAPS.values())-1000000
        self.assertGreater(remaining,10000000)
    def test_actual_parent_map_receipt_envelope_without_replay(self):
        parent=R.read(R.ROOT/(R.SEED_PARENT+'/jobs/endpoint.json'))
        receipt=R.read(R.ROOT/(R.SEED_PARENT+'/jobs/map.json'))
        receipt.update(schema='primitive-state-cone-jacobi-map-v1',initial_free_vector=parent['final_free_vector'],precision=R.P.PRECISION,seed_rule=R.P.SEED,seed_endpoint_hash=R.P.digest(parent),initial_projected_hash=R.P.digest(parent['final_projected_vector']),**R.FLAGS)
        self.assertGreater(len(R.P.encoded(receipt)),65536)
        self.assertLess(len(R.P.encoded(receipt)),R.ARTIFACT_CAPS['map'])
    def test_synthetic_full_pipeline_joint_reserved_ledger(self):
        with tempfile.TemporaryDirectory() as d:
            out=R.process_search(synthetic_license(),directory=d,deadline=time.monotonic()+60,input_work_reserve=1)
            self.assertEqual(out['status'],'endpoint_verified',out.get('reason'));self.assertTrue(out['finite_candidate_feasible']);self.assertFalse(out['scaled_trace_bound_certified'])
            entries=out['ledger']['entries'];self.assertEqual([e['stage'] for e in entries[1:6]],['final_archive_audit','map_materialization','norm_scaling','proposal_generator','exact_endpoint'])
            self.assertEqual([e['reserve'] for e in entries[1:6]],[25000000,50000000,100000000,80000000,20000000]);self.assertTrue(all(e['precision']=='allocated_unverified' for e in entries[1:6]))
            self.assertTrue((Path(d)/'norms.json').is_file());self.assertTrue((Path(d)/'check.json').is_file())
    def test_unknown_norms_no_fallback_or_search(self):
        license=synthetic_license();unknown=dict(schema='primitive-state-cone-jacobi-norms-v1',complete=False,status='unknown',reason='bounded synthetic norm cap',normalized_basis_hash=license.summary['normalized_basis_hash'],seed_endpoint_hash=R.P.digest(license.parent_endpoint),scaling=R.P.SCALING,records=[],counts=dict(operations=1,peak_live_cells=1,fill_cells=0),**R.FLAGS)
        with tempfile.TemporaryDirectory() as d,patch.object(R.P,'cone_column_norms',return_value=unknown),patch.object(R.P,'propose') as propose:
            out=R.process_search(license,directory=d,deadline=time.monotonic()+30,input_work_reserve=1)
            self.assertEqual(out['status'],'unknown',out.get('reason'));self.assertFalse(out['endpoint_verified']);propose.assert_not_called();self.assertFalse((Path(d)/'proposal.json').exists())
    def test_worker_exception_serializes_terminal_cost(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d)/'jobs').mkdir()
            with patch.object(R,'require_verified_runtime'),patch.object(R,'validate',side_effect=ValueError('changed bound input')):result=R.worker(dict(directory=d,phase='search',index=0))
            record=json.loads((Path(d)/'jobs/search-job.json').read_text());self.assertEqual(result['status'],'rejected');self.assertGreater(record['cost']['pid'],0);self.assertFalse(record['endpoint_verified'])
    def test_final_deadline_revokes_endpoint_but_preserves_receipts(self):
        license=synthetic_license();license.summary.update(rank=779,free_count=445,original_variables=1957,original_rows=5641,audit_operations=1,audit_cells=1)
        output=dict(status='endpoint_verified',endpoint_verified=True,finite_candidate_feasible=True,artifacts={'endpoint':{'file':'endpoint.json','sha256':'a'}},ledger={'reserved':25})
        with tempfile.TemporaryDirectory() as d:
            (Path(d)/'jobs').mkdir()
            with patch.object(R,'require_verified_runtime'),patch.object(R,'validate',return_value=({},{})),patch.object(R,'binding_work_reserve',return_value=1),patch.object(R.CHECK,'load_verified_license',return_value=license),patch.object(R,'process_search',return_value=output),patch.object(R.time,'monotonic',side_effect=[0.,1801.,1801.]):result=R.worker(dict(directory=d,phase='search',index=0))
            record=json.loads((Path(d)/'jobs/search-job.json').read_text());self.assertEqual(result['status'],'missing_resource');self.assertFalse(record['endpoint_verified']);self.assertIsNone(record['finite_candidate_feasible']);self.assertEqual(record['ledger'],output['ledger']);self.assertEqual(record['artifacts'],output['artifacts'])
    def test_source_closure_explicit_wholechecker(self):
        self.assertIn('check_primitive_state_cone_jacobi_search_run.py',R.sources())

if __name__=='__main__':unittest.main()
