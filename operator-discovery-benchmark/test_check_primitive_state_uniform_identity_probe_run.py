"""Lean mathematical archive tests; no fresh research source construction."""
import copy
import json
from pathlib import Path
import resource
import tempfile
import time
import unittest
from unittest.mock import patch
import check_primitive_state_uniform_identity_probe_run as C
import check_primitive_state_uniform_identity_probe as CORE
import primitive_state_uniform_identity_probe as P
import run_primitive_state_uniform_identity_probe as R


def save(path,value):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value))

class WholeProbeTests(unittest.TestCase):
    def archive(self,d):
        vector=['0']*1957;plan=P.preflight(vector,R.PROGRAM,X=7)
        one=[dict(m=[],c='1')];state=[one]+[[]for _ in range(14)]
        blocks=dict(full_child=[state for _ in range(14)],full_parent=[state for _ in range(7)])
        H=27;lhs={():CORE.F(32*49*2)}
        for b in range(1,H+1):
            j=sum(t>=b for t in range(14,28))-4*sum(t>=b for t in range(7,14))
            for a in range(1,b+1):
                if j:lhs[a,b]=CORE.F(-j*(1 if a==b else 2))
        native=dict(instance=dict(target='mu',horizon=27,lhs=CORE.LOCAL.P.canonical(lhs),square_groups=[[]for _ in range(366)],relation_groups=[[]for _ in range(613)]),gram_blocks=blocks,gram_specs=dict(full_child=15,full_parent=15,storage_K=15),storage_blocks=dict(kind='signed_storage_increment',child=blocks['full_child'],parent=blocks['full_parent'],child_multiplier='1',parent_multiplier='-4'))
        probe=P.probe_native(native,vector,plan,deadline=time.monotonic()+30)
        self.assertTrue(probe['complete'])
        ledger=dict(max_work=450000000,allocations=dict(preparation=50000000,producer_source=150000000,producer_evaluation=50000000,final_independent_source=150000000,final_independent_evaluation=50000000),total_work_reserve=450000000,remaining_work=0,precision='conservative fixed reserves; no producer count refinement',final_independent_stages_reserved=True)
        cost=dict(elapsed_seconds=1,cpu_seconds=1,peak_rss_kib=1,pid=1,observed_threads_at_completion=1)
        record=dict(status='probe_complete',probe_complete=True,nonconstant_formal_identity_refuted=False,artifacts=dict(plan='plan.json',probe='probe.json'),ledger=ledger,cost=cost,deadline_exceeded=False,producer_status=probe['status'],nonconstant_difference=probe['nonconstant_difference'],evaluation_counts=probe['counts'],source_meter=dict(metric='all Python LINE_EVENTS during complete native source call',line_events=1,cap=150000000,nested_resets_counted=True,one_affine_source_build=True,optional_expanded_hashes=False),**CORE.FLAGS)
        transport=dict(results=[dict(index=0,status='available',value=dict(file='jobs/probe-job.json',status=record['status'],cost=cost))],cost=dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',elapsed_seconds=1,result_bytes=100,payload_bytes=100,available=1,missing=0,errors=0))
        for name,value in [('protocol.json',R.protocol(C.fixed_parent())),('candidate.json',vector),('tests.json',dict(returncode=0,stderr='Ran 3 tests in 0.1s\n\nOK')),('run_started.json',dict(one_fixed_probe=True)),('execution.json',transport),('jobs/plan.json',plan),('jobs/probe.json',probe),('jobs/probe-job.json',record),('jobs/progress.json',dict(phase='terminal_probe_complete',ledger=ledger,artifacts=record['artifacts'],**CORE.FLAGS))]:save(d/name,value)
        save(d/C.PARENT/'jobs/endpoint.json',dict(complete=True,candidate_original_vector=vector))
        license=CORE._SourceLicense(CORE._TOKEN,native,plan,vector,dict(native_line_events=1,audit_operations=0,audit_cells=0))
        return license,record,transport
    def test_complete_archive_one_math_rebuild_and_row(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);license,_,_=self.archive(d)
            with patch.object(C,'ROOT',d),patch.object(CORE,'rebuild_source',return_value=license)as build:
                result=C.audit(d)
            self.assertEqual(build.call_count,1);self.assertEqual(result['status'],'REFUTED');self.assertTrue(result['necessary_formal_identity_constraint']);self.assertEqual(result['joint_work']['total_work_reserve'],450000000)
    def test_resource_exhaustion_is_unknown_without_row(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);self.archive(d)
            with patch.object(C,'ROOT',d),patch.object(CORE,'rebuild_source',side_effect=OverflowError('source cap')):
                result=C.audit(d)
            self.assertEqual(result['status'],'UNKNOWN');self.assertIsNone(result['necessary_formal_identity_constraint']);self.assertEqual(result['independent_resource_failure']['error_type'],'OverflowError')
    def test_failed_transport_retains_complete_evidence_without_promotion(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);license,record,transport=self.archive(d);transport['results']=[dict(index=0,status='error')];transport['cost'].update(available=0,errors=1);save(d/'execution.json',transport)
            with patch.object(C,'ROOT',d),patch.object(CORE,'rebuild_source',return_value=license):result=C.audit(d)
            self.assertEqual(result['status'],'UNKNOWN');self.assertFalse(result['nonconstant_formal_identity_refuted']);self.assertTrue(result['independent_nonzero_diagnostic_retained'])
    def test_deadline_revocation_retains_only_diagnostic(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);license,record,transport=self.archive(d);record.update(status='UNKNOWN',probe_complete=False,deadline_exceeded=True);save(d/'jobs/probe-job.json',record);transport['results'][0]['value']['status']='UNKNOWN';save(d/'execution.json',transport)
            with patch.object(C,'ROOT',d),patch.object(CORE,'rebuild_source',return_value=license):result=C.audit(d)
            self.assertEqual(result['status'],'UNKNOWN');self.assertFalse(result['nonconstant_formal_identity_refuted'])
    def test_forged_promotion_rejected_before_source(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);self.archive(d);probe=C.read(d/'jobs/probe.json');probe['global_bound_proved']=True;save(d/'jobs/probe.json',probe)
            with patch.object(C,'ROOT',d),patch.object(CORE,'rebuild_source',side_effect=AssertionError('no source')):
                with self.assertRaises(ValueError):C.audit(d)
    def test_caps_duplicate_write_and_memory_restored(self):
        old=resource.getrlimit(resource.RLIMIT_AS)
        for kwargs in [dict(time_limit=float('nan')),dict(time_limit=3601),dict(max_source_line_events=True),dict(max_evaluation_operations=50000001)]:
            with self.assertRaises(ValueError):C.audit('/missing',**kwargs)
        self.assertEqual(resource.getrlimit(resource.RLIMIT_AS),old)
        with tempfile.TemporaryDirectory()as td:
            (Path(td)/'independent_verification.json').write_text('{}')
            with patch.object(C,'_audit',side_effect=AssertionError('expensive replay')):
                with self.assertRaises(FileExistsError):C.audit(td,write=True)
    def test_protocol_and_math_candidate_tampering(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);self.archive(d);vector=C.read(d/'candidate.json');vector[0]='1';save(d/'candidate.json',vector)
            with patch.object(C,'ROOT',d),patch.object(CORE,'rebuild_source',side_effect=AssertionError('must reject before math')):
                with self.assertRaises(ValueError):C.audit(d)
        protocol=copy.deepcopy(R.protocol(C.fixed_parent()));protocol['spec']['prime']=3
        with self.assertRaises(ValueError):C.verify_protocol(protocol)

if __name__=='__main__':unittest.main()
