"""Synthetic lifecycle and bounded actual-parent metadata envelope checks."""
from fractions import Fraction as F
import copy
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import run_primitive_state_balanced_cone_search as R
from test_primitive_state_balanced_cone_search import fixture


def synthetic_license():
    mapping,mapreceipt,warmreceipt,cache,basis,projection,parent,base,warm,norms,proposal=fixture()
    budget=R.CHECK.EXACT.EXACT._Budget(None,10000000,10000000,4096);source=R.CHECK.J.OLD.CACHE_CHECK.decode_original(cache,budget)
    summary=dict(normalized_basis_hash=parent['normalized_basis_hash'],rank=len(mapping['pivots']),free_count=len(mapping['free']),original_variables=1957,original_rows=len(source['monomials']),projected_variables=1224,retained_indices=mapping['retained'],pivot_columns=mapping['pivots'],free_indices=mapping['free'],parent_projected_hash=R.P.digest(base['final_projected_vector']),parent_free_hash=R.P.digest(base['final_free_vector']),sparse_map_entries=mapreceipt['sparse_map_entries'])
    old=R.CHECK.J.OLD._EndpointLicense(R.CHECK.J.OLD._TOKEN,source,summary,list(map(F,parent['restored_projected_vector'])),mapping['pivots'],mapping['free'],{},cache=cache,basis=basis,projection=projection,parent_restoration=parent)
    jacobi=R.CHECK.J._EndpointLicense(R.CHECK.J._TOKEN,old,summary,list(map(F,base['final_projected_vector'])),{},base)
    summary=dict(summary,base_endpoint_hash=R.P.digest(base),warm_endpoint_hash=R.P.digest(warm),warm_proposal_hash=R.P.digest(proposal),warm_projected_hash=R.P.digest(warm['final_projected_vector']),norm_records_hash=norms['records_hash'])
    return R.CHECK._EndpointLicense(R.CHECK._TOKEN,jacobi,summary,list(map(F,warm['final_projected_vector'])),[F(0)]*len(mapping['free']),mapping['scales'],norms,warm,proposal,{})

class RunnerTests(unittest.TestCase):
    def test_actual_parent_protocol_and_joint_operation_room(self):
        license=R.load_license();protocol=R.protocol(license);self.assertEqual(license['publication'],'publication-020');self.assertEqual(protocol['search']['gradient_iterations'],96);self.assertEqual(protocol['model']['normalizer_floor'],'1/1099511627776');self.assertLess(len(R.P.encoded(protocol)),65536)
        bad=copy.deepcopy(license);bad['padding']='x'*65536
        with self.assertRaises(OverflowError):R.protocol(bad)
        self.assertEqual(R.LIMITS['worker_max_work']+R.LIMITS['final_archive_audit_operations'],450000000)
        room=425000000-R.binding_work_reserve()-205000000-sum(R.ARTIFACT_CAPS.values())-956589-1;self.assertGreater(room,5000000)
    def test_actual_parent_map_warm_size_without_replay(self):
        base=R.read(R.ROOT/(R.OLD.SEED_PARENT+'/jobs/endpoint.json'));warm=R.read(R.ROOT/(R.SEED_PARENT+'/jobs/endpoint.json'));proposal=R.read(R.ROOT/(R.SEED_PARENT+'/jobs/proposal.json'));norms=R.read(R.ROOT/(R.SEED_PARENT+'/jobs/norms.json'));receipt=R.read(R.ROOT/(R.SEED_PARENT+'/jobs/map.json'))
        receipt.update(schema='primitive-state-balanced-cone-map-v1',precision=R.P.PRECISION,seed_rule=R.P.SEED,base_endpoint_hash=R.P.digest(base),warm_endpoint_hash=R.P.digest(warm),warm_projected_hash=R.P.digest(warm['final_projected_vector']),**R.FLAGS)
        self.assertLess(len(R.P.encoded(receipt)),R.ARTIFACT_CAPS['map'])
        envelope=dict(schema='primitive-state-balanced-cone-warm-v1',complete=True,normalized_basis_hash=warm['normalized_basis_hash'],base_endpoint_hash=R.P.digest(base),warm_endpoint_hash=R.P.digest(warm),warm_proposal_hash=R.P.digest(proposal),norm_records_hash=norms['records_hash'],initial_free_vector=base['final_free_vector'],warm_free_vector=warm['final_free_vector'],initial_z_mp=proposal['final_z_mp'],scale_vector=[r['scale']for r in norms['records']],precision=R.P.PRECISION,scaling=R.P.SCALING,seed_rule=R.P.SEED,new_column_responses=0,counts=dict(operations=5000000,peak_live_cells=4000000,fill_cells=20000000),**R.FLAGS)
        self.assertLess(len(R.P.encoded(envelope)),R.ARTIFACT_CAPS['warm'])
    def test_synthetic_full_pipeline_and_unrefined_stages(self):
        with tempfile.TemporaryDirectory() as d:
            result=R.process_search(synthetic_license(),directory=d,deadline=time.monotonic()+30,input_work_reserve=1)
            self.assertEqual(result['status'],'endpoint_verified',result.get('reason'));self.assertTrue(result['finite_candidate_feasible']);self.assertFalse(result['model_optimality_certified'])
            entries=result['ledger']['entries'];self.assertEqual([e['stage']for e in entries[1:6]],['final_archive_audit','map_materialization','warm_setup','proposal_generator','exact_endpoint']);self.assertEqual([e['reserve']for e in entries[1:6]],[25000000,50000000,5000000,130000000,20000000]);self.assertTrue(all(e['precision']=='allocated_unverified'for e in entries[1:6]));self.assertFalse((Path(d)/'norms.json').exists())
    def test_warm_failure_no_fallback_search(self):
        license=synthetic_license()
        with tempfile.TemporaryDirectory() as d,patch.object(R.P,'warm_setup',side_effect=OverflowError('bounded synthetic setup')),patch.object(R.P,'propose')as propose:
            result=R.process_search(license,directory=d,deadline=time.monotonic()+30,input_work_reserve=1);self.assertEqual(result['status'],'missing_resource');self.assertFalse(result['endpoint_verified']);propose.assert_not_called()
    def test_terminal_worker_error_cost_serialization(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d)/'jobs').mkdir()
            with patch.object(R,'require_verified_runtime'),patch.object(R,'validate',side_effect=ValueError('bound input altered')):result=R.worker(dict(directory=d,phase='search',index=0))
            out=json.loads((Path(d)/'jobs/search-job.json').read_text());self.assertEqual(result['status'],'rejected');self.assertFalse(out['endpoint_verified']);self.assertGreater(out['cost']['pid'],0)
    def test_final_deadline_revokes_success_retains_ledger(self):
        license=synthetic_license();license.summary.update(rank=779,free_count=445,original_variables=1957,original_rows=5641,audit_operations=1,audit_cells=1)
        result=dict(status='endpoint_verified',endpoint_verified=True,finite_candidate_feasible=True,artifacts={'endpoint':{'file':'endpoint.json','sha256':'a'}},ledger={'reserved':'evidence'})
        with tempfile.TemporaryDirectory() as d:
            (Path(d)/'jobs').mkdir()
            with patch.object(R,'require_verified_runtime'),patch.object(R,'validate',return_value=({},{})),patch.object(R,'binding_work_reserve',return_value=1),patch.object(R.CHECK,'load_verified_license',return_value=license),patch.object(R,'process_search',return_value=result),patch.object(R.time,'monotonic',side_effect=[0.,1801.,1801.]):transport=R.worker(dict(directory=d,phase='search',index=0))
            out=json.loads((Path(d)/'jobs/search-job.json').read_text());self.assertEqual(transport['status'],'missing_resource');self.assertFalse(out['endpoint_verified']);self.assertIsNone(out['finite_candidate_feasible']);self.assertEqual(out['ledger'],result['ledger']);self.assertEqual(out['artifacts'],result['artifacts'])
    def test_source_closure_explicit_wholeauditor(self):
        self.assertIn('check_primitive_state_balanced_cone_search_run.py',R.sources())

if __name__=='__main__':unittest.main()
