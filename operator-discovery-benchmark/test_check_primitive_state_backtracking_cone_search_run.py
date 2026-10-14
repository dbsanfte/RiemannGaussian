import copy
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import check_primitive_state_backtracking_cone_search_run as C
import run_primitive_state_backtracking_cone_search as R
from test_check_primitive_state_backtracking_cone_search import warm_inputs

def write(path,value):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value))

def full_fixture(root,d):
    cache,chart,center,row,review,map025,proposal025,endpoint025,warmreview=warm_inputs();P=R.P
    mapping,mapreceipt=P.setup(chart,center,map025,proposal025,endpoint025,deadline=time.monotonic()+30)
    # Numerical exports are deliberately zero; no checker treats these as true PSD metrics.
    zero=[0,'0',0];proposal=dict(schema=P.SCHEMA,status='proposed',complete=True,precision=P.PRECISION,search=P.SEARCH,model=P.MODEL,scaling=P.SCALING,seed_rule=P.SEED,free_indices=mapping['free'],initial_free_vector=list(map(str,mapping['initial'])),scale_vector=list(map(str,mapping['scales'])),power_trace=[],iterations=[],calibration=mapping['calibration'],warm_free_vector=list(map(str,mapping['warm_free'])),initial_step=P.OLD.mp_record(mapping['initial_step']),initial_z_mp=[P.OLD.mp_record(v)for v in mapping['warm_z']],initial_block_penalties=[zero]*3,normalizers=list(map(str,mapping['fixed_normalizers'])),initial_normalized_blocks=[zero]*3,initial_objective=zero,initial_merit_details={},final_z_mp=[P.OLD.mp_record(v)for v in mapping['warm_z']],final_free_vector=list(map(str,mapping['warm_free'])),final_objective=zero,final_normalized_blocks=[zero]*3,stop_reason='zero_initial_numerical_defect',counts=dict(operations=648000,peak_live_cells=1,maximum_rational_bits=1),elapsed_seconds=0,**P.FLAGS)
    with patch.object(P,'setup',return_value=(mapping,mapreceipt)),patch.object(P,'propose',return_value=proposal):record=R.process_search((chart,center,map025,proposal025,endpoint025,cache,row),directory=d/'jobs',deadline=time.monotonic()+30)
    if not record['endpoint_complete']:raise AssertionError(record)
    record.update(cost=dict(elapsed_seconds=1,cpu_seconds=1,peak_rss_kib=1000,pid=1,observed_threads_at_completion=1),deadline_exceeded=False);write(d/'jobs/search-job.json',record)
    cost=dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',elapsed_seconds=1,result_bytes=100,payload_bytes=100,available=1,missing=0,errors=0)
    write(d/'execution.json',dict(results=[dict(index=0,status='available',value=dict(file='jobs/search-job.json',status=record['status'],cost=record['cost'],**P.FLAGS))],cost=cost))
    for name,value in [(C.CACHE,cache),(C.CHART,chart),(C.AFFINE,center),(C.CONSTRAINT,row),(C.REVIEW,review),(C.MAP,map025),(C.PROPOSAL,proposal025),(C.ENDPOINT,endpoint025),(C.WARM_REVIEW,warmreview)]:write(root/name,value)
    write(root/(C.PUBLICATION+'/report.json'),dict(schema=24,chart_verified=True,candidate_equations_verified=True,independent_audit_complete=True,classification='independent',coefficient_rank=780,augmented_rank=780,free_count=444,chosen_pivot=148,chart_path=C.CHART,affine_receipt_path=C.AFFINE))
    write(root/(C.WARM_PUBLICATION+'/report.json'),dict(schema=25,independent_audit_complete=True,endpoint_verified=True,candidate_equations_verified=True,stop_reason='line_search_failed'))
    write(d/'protocol.json',R.protocol());write(d/'parent.json',C.parent());write(d/'tests.json',dict(returncode=0,stderr='Ran 6 tests in 1s\n\nOK\n'));write(d/'run_started.json',dict(one_fixed_search=True))
    return record

class WholeTests(unittest.TestCase):
    def test_literals_match_actual_runner(self):
        C.verify_protocol(R.protocol());C.verify_ledger(R.ledger());self.assertEqual(C.LIMITS,R.LIMITS);self.assertEqual(C.CAPS,R.CAPS)
        value=R.protocol();value['worker_independent_checks']=1
        with self.assertRaises(ValueError):C.verify_protocol(value)
    def test_complete_archive_exact_endpoint_and_native_claims(self):
        with tempfile.TemporaryDirectory()as td:
            root=Path(td)/'root';d=Path(td)/'run';full_fixture(root,d)
            with patch.object(C,'ROOT',root),patch('hashlib.sha256',side_effect=AssertionError('no hashes')):r=C.audit(d)
            self.assertEqual(r['status'],'ENDPOINT_CHECKED');self.assertTrue(r['candidate_equations_verified']);self.assertFalse(r['finite_candidate_feasible']);self.assertEqual(r['independent_search_check']['full_original_rows_checked'],5641);self.assertEqual(r['joint_work']['total_work_reserve'],450000000)
    def test_failed_transport_saved_endpoint_is_not_promoted(self):
        with tempfile.TemporaryDirectory()as td:
            root=Path(td)/'root';d=Path(td)/'run';full_fixture(root,d);e=json.loads((d/'execution.json').read_text());e['results']=[dict(index=0,status='missing_resource')];e['cost'].update(available=0,missing=1);write(d/'execution.json',e)
            with patch.object(C,'ROOT',root):r=C.audit(d)
            self.assertEqual(r['status'],'UNKNOWN');self.assertFalse(r['endpoint_verified']);self.assertTrue(r['independent_search_check']['endpoint_verified'])
    def test_saved_before_terminal_commit_and_deadline_revocation(self):
        with tempfile.TemporaryDirectory()as td:
            root=Path(td)/'root';d=Path(td)/'run';record=full_fixture(root,d);record.update(status='UNKNOWN',producer_complete=False,endpoint_complete=False,deadline_exceeded=True);write(d/'jobs/search-job.json',record);e=json.loads((d/'execution.json').read_text());e['results'][0]['value'].update(status='UNKNOWN');write(d/'execution.json',e)
            with patch.object(C,'ROOT',root):r=C.audit(d)
            self.assertEqual(r['status'],'UNKNOWN');self.assertFalse(r['endpoint_verified'])
    def test_final_deadline_and_output_cap_cannot_claim_audit_complete(self):
        value=dict(schema='primitive-state-backtracking-cone-search-independent-review-v1',all_passed=True,status='ENDPOINT_CHECKED',endpoint_verified=True,candidate_equations_verified=True,finite_candidate_feasible=True)
        with tempfile.TemporaryDirectory()as td,patch.object(C,'_audit',return_value=copy.deepcopy(value)),patch.object(C.time,'monotonic',side_effect=[0.,3601.,3601.]):
            r=C.audit(td);self.assertFalse(r['all_passed']);self.assertEqual(r['status'],'UNKNOWN')
        value['oversized']='x'*70000
        with tempfile.TemporaryDirectory()as td,patch.object(C,'_audit',return_value=value):
            r=C.audit(td,write=True);self.assertFalse(r['all_passed']);self.assertEqual(r['status'],'UNKNOWN');self.assertLess((Path(td)/'independent_verification.json').stat().st_size,65536)
    def test_resource_caps_and_duplicate_write_before_work(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);write(d/'independent_verification.json',{})
            with self.assertRaises(FileExistsError):C.audit(d,write=True)
            for kwargs in [dict(time_limit=float('nan')),dict(time_limit=3601),dict(max_operations=150000001),dict(max_cells=True)]:
                with self.assertRaises(ValueError):C.audit(d,**kwargs)

if __name__=='__main__':unittest.main()
