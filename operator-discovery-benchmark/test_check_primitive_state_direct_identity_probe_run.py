"""Synthetic archive lifecycle and resource boundaries; no X7 evaluation."""
import copy
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import resource
import check_primitive_state_direct_identity_probe_run as C
import primitive_state_direct_identity_probe as P
import run_primitive_state_direct_identity_probe as R

def save(path,value):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value))

class DirectWholeTests(unittest.TestCase):
    def fixture(self,d):
        v=['0']*1957;plan=P.preflight(v,P.PROGRAM,X=7)
        # Explicit synthetic complete metadata; actual math replay is replaced
        # only in whole lifecycle fixtures, separately calibrated by core tests.
        probe=dict(complete=True,status='UNVERIFIED_COUNTEREXAMPLE',nonconstant_difference=1,counts=dict(operations=1),**C.FLAGS)
        ledger=dict(max_work=450000000,allocations=dict(preparation=50000000,producer_direct_evaluation=200000000,final_independent_direct_evaluation=200000000),total_work_reserve=450000000,remaining_work=0,precision='conservative fixed reserves; no producer count refinement',final_independent_stages_reserved=True)
        cost=dict(elapsed_seconds=1,cpu_seconds=1,peak_rss_kib=1,pid=1,observed_threads_at_completion=1)
        record=dict(status='probe_complete',probe_complete=True,producer_complete=True,producer_status=probe['status'],nonconstant_difference=1,evaluation_counts=probe['counts'],deadline_exceeded=False,artifacts=dict(plan='plan.json',probe='probe.json'),ledger=ledger,cost=cost,nonconstant_formal_identity_refuted=False,**C.FLAGS)
        execution=dict(results=[dict(index=0,status='available',value=dict(file='jobs/probe-job.json',status=record['status'],cost=cost,**C.FLAGS))],cost=dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',elapsed_seconds=1,result_bytes=100,payload_bytes=100,available=1,missing=0,errors=0))
        parent=dict(publication='cancellation-arithmetic-results/publication-021',candidate_source=C.PARENT+'/jobs/endpoint.json',n_variables=1957,one_fixed_candidate=True)
        for name,value in [('protocol.json',R.protocol(parent)),('candidate.json',v),('run_started.json',dict(one_fixed_probe=True)),('tests.json',dict(returncode=0,stderr='Ran 5 tests in 1s\n\nOK')),('execution.json',execution),('jobs/plan.json',plan),('jobs/probe.json',probe),('jobs/probe-job.json',record),('jobs/progress.json',dict(phase='terminal_probe_complete',ledger=ledger,artifacts=record['artifacts'],**C.FLAGS)),(C.PRIOR+'/candidate.json',v),(C.PARENT+'/jobs/endpoint.json',dict(complete=True,candidate_original_vector=v))]:save(d/name,value)
        check=dict(status='REFUTED',verified=True,complete=True,nonconstant_formal_identity_refuted=True,necessary_formal_identity_constraint=dict(width=1957,X=7,entries=[],rhs='1'),complete_grammar_independently_evaluated=True,complete_coefficient_row_verified=True,symbolic_source_constructed=False,audit_operations=1,audit_cells=1,**C.FLAGS)
        return check,record,execution
    def test_one_independent_replay_and_actual_protocol(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);check,_,_=self.fixture(d)
            with patch.object(C,'ROOT',d),patch.object(C.CORE,'verify_probe',return_value=check)as replay:result=C.audit(d)
            self.assertEqual(replay.call_count,1);self.assertEqual(result['status'],'REFUTED');self.assertEqual(result['joint_work']['total_work_reserve'],450000000);self.assertFalse(result['symbolic_source_constructed']);self.assertGreater(result['joint_work']['independent_io_operations'],0)
    def test_failed_transport_and_deadline_never_promote(self):
        for mode in ('transport','deadline'):
            with tempfile.TemporaryDirectory()as td:
                d=Path(td);check,record,execution=self.fixture(d)
                if mode=='transport':execution['results']=[dict(index=0,status='error')]
                else:record.update(status='UNKNOWN',producer_complete=False,probe_complete=False,deadline_exceeded=True);execution['results'][0]['value']['status']='UNKNOWN'
                save(d/'execution.json',execution);save(d/'jobs/probe-job.json',record)
                with patch.object(C,'ROOT',d),patch.object(C.CORE,'verify_probe',return_value=check):result=C.audit(d)
                self.assertEqual(result['status'],'UNKNOWN');self.assertIsNone(result['necessary_formal_identity_constraint'])
    def test_independent_resource_failure_publishable_unknown(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);self.fixture(d)
            with patch.object(C,'ROOT',d),patch.object(C.CORE,'verify_probe',side_effect=OverflowError('aggregate cap')):result=C.audit(d)
            self.assertEqual(result['status'],'UNKNOWN');self.assertIsNone(result['necessary_formal_identity_constraint']);self.assertEqual(result['joint_work']['independent_evaluation_operations'],None)
    def test_input_protocol_promotion_and_ledger_tampering(self):
        for mode in ('vector','protocol','flags','ledger'):
            with tempfile.TemporaryDirectory()as td:
                d=Path(td);self.fixture(d)
                if mode=='vector':v=C.read(d/'candidate.json');v[1]='1';save(d/'candidate.json',v)
                elif mode=='protocol':v=C.read(d/'protocol.json');v['limits']['producer_direct_operations']=200000001;save(d/'protocol.json',v)
                elif mode=='flags':v=C.read(d/'jobs/probe.json');v['global_bound_proved']=True;save(d/'jobs/probe.json',v)
                else:v=C.read(d/'jobs/probe-job.json');v['ledger']['allocations']['preparation']=1;save(d/'jobs/probe-job.json',v)
                with patch.object(C,'ROOT',d),patch.object(C.CORE,'verify_probe',side_effect=AssertionError('reject before math')):
                    with self.assertRaises(ValueError):C.audit(d)
    def test_strict_caps_upfront_duplicate_and_rlimit_restore(self):
        old=resource.getrlimit(resource.RLIMIT_AS)
        for kw in (dict(time_limit=float('nan')),dict(time_limit=3601),dict(max_operations=True),dict(max_cells=6000001)):
            with self.assertRaises(ValueError):C.audit('/missing',**kw)
        self.assertEqual(resource.getrlimit(resource.RLIMIT_AS),old)
        with tempfile.TemporaryDirectory()as td:
            save(Path(td)/'independent_verification.json',{})
            with patch.object(C,'_audit',side_effect=AssertionError('no replay')):
                with self.assertRaises(FileExistsError):C.audit(td,write=True)

if __name__=='__main__':unittest.main()
