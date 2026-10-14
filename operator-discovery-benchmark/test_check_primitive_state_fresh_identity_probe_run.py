import copy
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import check_primitive_state_fresh_identity_probe_run as C
import run_primitive_state_fresh_identity_probe as R
from test_check_primitive_state_fresh_identity_probe import chart_inputs

TINY_CASES=[dict(index=0,X=1,H=3,assignment_rule='tiny odd',assignment=[3,5,7]),dict(index=1,X=1,H=3,assignment_rule='tiny alternating',assignment=[-2,5,-10])]

def write(path,value):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value))


def fixture(root,d):
    vector=['0']*1957;chart,chartreview,chartreport=chart_inputs();chartreport['chart_path']=C.CHART
    report=dict(schema=26,independent_audit_complete=True,endpoint_verified=True,candidate_equations_verified=True,endpoint_path=C.ENDPOINT,independent_review_path=C.REVIEW)
    review=dict(schema='primitive-state-backtracking-recovery-independent-review-v1',all_passed=True,endpoint_verified=True,candidate_equations_verified=True,original_producer_status='UNKNOWN',independent_search_check=dict(verified=True,complete=True,endpoint_verified=True))
    endpoint=dict(schema='primitive-state-backtracking-recovered-endpoint-v1',complete=True,candidate_original_vector=vector)
    for name,value in [(C.PUBLICATION+'/report.json',report),(C.REVIEW,review),(C.ENDPOINT,endpoint),(C.CHART,chart),(C.CHART_REVIEW,chartreview),(C.CHART_PUBLICATION+'/report.json',chartreport)]:write(root/name,value)
    write(d/'protocol.json',R.protocol());write(d/'candidate.json',vector);write(d/'tests.json',dict(returncode=0,stderr='Ran 6 tests in 1s\n\nOK\n'));write(d/'run_started.json',dict(two_fixed_probes=True));results=[]
    for case in TINY_CASES:
        index=case['index'];sub=d/'jobs'/('case-%02d'%index);record=R.process_case(vector,case,directory=sub,deadline=time.monotonic()+30);record.update(cost=dict(elapsed_seconds=1,cpu_seconds=1,peak_rss_kib=1000,pid=index+1,observed_threads_at_completion=1),deadline_exceeded=False);write(sub/'probe-job.json',record)
        results.append(dict(index=index,status='available',value=dict(file='jobs/case-%02d/probe-job.json'%index,status=record['status'],case_index=index,cost=record['cost'],**R.FLAGS)))
    cost=dict(requested_workers=2,workers=2,max_in_flight=2,worker_memory_bytes=3*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',elapsed_seconds=1,result_bytes=100,payload_bytes=100,available=2,missing=0,errors=0)
    write(d/'execution.json',dict(results=results,cost=cost))

class WholeTests(unittest.TestCase):
    def test_protocol_and_ledger_literals_match_runner(self):
        C.verify_protocol(R.protocol());C.verify_ledger(R.ledger());self.assertEqual(C.LIMITS,R.LIMITS);self.assertEqual(C.CAPS,R.CAPS);self.assertEqual(C.CASES,R.CASES)
        value=R.protocol();value['independent_case_budget_shared']=False
        with self.assertRaises(ValueError):C.verify_protocol(value)
    def test_complete_two_tiny_cases_and_extension_no_hashes(self):
        with tempfile.TemporaryDirectory()as td,patch.object(C,'CASES',TINY_CASES),patch.object(R,'CASES',TINY_CASES):
            root=Path(td)/'root';d=Path(td)/'run';fixture(root,d)
            with patch.object(C,'ROOT',root),patch('hashlib.sha256',side_effect=AssertionError('no hashes')):r=C.audit(d,write=True)
            self.assertTrue(r['all_passed']);self.assertEqual(len(r['case_checks']),2);self.assertEqual(len(r['necessary_formal_identity_constraints']),2);self.assertTrue(r['affine_extension']['complete']);self.assertEqual(r['affine_extension']['old_rank'],780);self.assertEqual(r['joint_work']['total_work_reserve'],450000000);self.assertLess(r['joint_work']['independent_operations'],200000000)
            with self.assertRaises(FileExistsError):C.audit(d)
    def test_failed_transport_clears_constraints_and_extension(self):
        with tempfile.TemporaryDirectory()as td,patch.object(C,'CASES',TINY_CASES),patch.object(R,'CASES',TINY_CASES):
            root=Path(td)/'root';d=Path(td)/'run';fixture(root,d);e=json.loads((d/'execution.json').read_text());e['results'][1]=dict(index=1,status='missing_resource');e['cost'].update(available=1,missing=1);write(d/'execution.json',e)
            with patch.object(C,'ROOT',root):r=C.audit(d)
            self.assertFalse(r['all_passed']);self.assertEqual(r['status'],'UNKNOWN');self.assertEqual(r['necessary_formal_identity_constraints'],[]);self.assertIsNone(r['affine_extension'])
    def test_producer_false_proof_and_warm_candidate_bias_rejected(self):
        with tempfile.TemporaryDirectory()as td,patch.object(C,'CASES',TINY_CASES),patch.object(R,'CASES',TINY_CASES):
            root=Path(td)/'root';d=Path(td)/'run';fixture(root,d);record=json.loads((d/'jobs/case-00/probe-job.json').read_text());record['nonconstant_formal_identity_refuted']=True;write(d/'jobs/case-00/probe-job.json',record)
            with patch.object(C,'ROOT',root),self.assertRaises(ValueError):C.audit(d)
    def test_resource_failure_and_strict_caps_preserve_unknown(self):
        with tempfile.TemporaryDirectory()as td,patch.object(C,'_audit',side_effect=OverflowError('shared200m exhausted')):
            r=C.audit(td,write=True);self.assertFalse(r['all_passed']);self.assertEqual(r['necessary_formal_identity_constraints'],[]);self.assertIsNone(r['affine_extension'])
        for kwargs in (dict(time_limit=float('nan')),dict(max_operations=200000001),dict(max_cells=True)):
            with tempfile.TemporaryDirectory()as td,self.assertRaises(ValueError):C.audit(td,**kwargs)
    def test_late_IO_failure_is_durable_unknown(self):
        result=dict(schema='primitive-state-fresh-identity-probe-independent-review-v1',all_passed=True,status='REFUTED',nonconstant_formal_identity_refuted=True,necessary_formal_identity_constraints=[{}],affine_extension=dict(complete=True),case_checks=[],joint_work=dict(max_work=450000000,total_work_reserve=450000000,independent_operations=123),**C.FLAGS)
        with tempfile.TemporaryDirectory()as td,patch.object(C,'_audit',return_value=({},result)),patch.object(C,'account_bytes',side_effect=OverflowError('tailIO')):
            r=C.audit(td,write=True);self.assertFalse(r['all_passed']);self.assertEqual(r['necessary_formal_identity_constraints'],[]);self.assertIsNone(r['affine_extension']);self.assertEqual(r['joint_work']['independent_operations'],123);self.assertEqual(json.loads((Path(td)/'independent_verification.json').read_text())['status'],'UNKNOWN')
    def test_late_deadline_revokes_completed_math(self):
        result=dict(schema='primitive-state-fresh-identity-probe-independent-review-v1',all_passed=True,status='REFUTED',nonconstant_formal_identity_refuted=True,case_checks=[{}],necessary_formal_identity_constraints=[{}],affine_extension=dict(complete=True),resource_failure=None,joint_work=dict(max_work=450000000,total_work_reserve=450000000),**C.FLAGS)
        with tempfile.TemporaryDirectory()as td,patch.object(C,'_audit',return_value=({},result)),patch.object(C.time,'monotonic',side_effect=[0.,3601.,3601.,3601.,3601.]):
            r=C.audit(td);self.assertFalse(r['all_passed']);self.assertEqual(r['status'],'UNKNOWN');self.assertEqual(r['necessary_formal_identity_constraints'],[]);self.assertIsNone(r['affine_extension'])

if __name__=='__main__':unittest.main()
