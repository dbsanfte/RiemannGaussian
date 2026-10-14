"""Synthetic complete feedback archive integration and failure windows."""
import copy
import json
from pathlib import Path
import resource
import tempfile
import time
import unittest
from unittest.mock import patch
import check_primitive_state_feedback_affine_run_v2 as C
import run_primitive_state_feedback_affine_v2 as R
import primitive_state_feedback_affine as P
from test_check_primitive_state_feedback_affine import fixture


def save(path,value):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value))

class AffineWholeTests(unittest.TestCase):
    def archive(self,d,kind='independent'):
        save(d/(C.CALIBRATION_PREDECESSOR+'/tests.json'),dict(returncode=1,stderr='FAILED (errors=1)'))
        inputs=fixture(kind);chart,affine=P.build(*inputs,deadline=time.monotonic()+30);self.assertTrue(affine['complete'],affine.get('reason'))
        for name,value in zip((C.CACHE,C.PROJECTION,C.BASIS,C.SEED,C.CONSTRAINT),inputs):save(d/name,value)
        save(d/(C.PUBLICATION+'/report.json'),dict(schema=23,independent_audit_complete=True,feedback_constraint_available=True,feedback_constraint_file='constraint.json',scale=7,horizon=27,RH_proved=False,global_bound_proved=False,universal_identity_proved=False,exact_admission=False))
        cost=dict(elapsed_seconds=1,cpu_seconds=1,peak_rss_kib=1,pid=1,observed_threads_at_completion=1)
        artifacts=dict(affine='affine.json',**(dict(chart='chart.json')if chart is not None else{}))
        record=dict(status='affine_complete',producer_complete=True,classification=affine['classification'],chart_available=affine['chart_available'],artifacts=artifacts,ledger=R.ledger(),producer_counts=affine['counts'],coefficient_rank=affine['coefficient_rank'],augmented_rank=affine['augmented_rank'],free_dimension=affine['free_dimension'],cost=cost,deadline_exceeded=False,**C.FLAGS)
        execution=dict(results=[dict(index=0,status='available',value=dict(file='jobs/affine-job.json',status=record['status'],cost=cost,**C.FLAGS))],cost=dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',elapsed_seconds=1,result_bytes=100,payload_bytes=100,available=1,missing=0,errors=0))
        for name,value in [('protocol.json',R.protocol()),('parent.json',C.parent()),('tests.json',dict(returncode=0,stderr='Ran 5 tests in 1s\n\nOK')),('run_started.json',dict(one_fixed_affine_job=True)),('execution.json',execution),('jobs/affine.json',affine),('jobs/affine-job.json',record),('jobs/progress.json',dict(phase='terminal_affine_complete',ledger=R.ledger(),artifacts=artifacts,**C.FLAGS))]:save(d/name,value)
        if chart is not None:save(d/'jobs/chart.json',chart)
        return record,execution
    def test_complete_all_three_classifications_one_final_replay(self):
        for kind,status in [('independent','AFFINE_UPDATED'),('redundant','REDUNDANT'),('inconsistent','FORMAL_SYSTEM_INCONSISTENT')]:
            with tempfile.TemporaryDirectory()as td:
                d=Path(td);self.archive(d,kind)
                with patch.object(C,'ROOT',d),patch.object(C.CORE,'verify_feedback',wraps=C.CORE.verify_feedback)as replay:result=C.audit(d)
                self.assertEqual(replay.call_count,1);self.assertEqual(result['status'],status);self.assertTrue(result['independent_affine_check']['all_original_rows_replayed']);self.assertEqual(result['joint_work']['total_work_reserve'],450000000)
                if kind=='inconsistent':self.assertFalse(result['chart_verified']);self.assertFalse(result['candidate_equations_verified']);self.assertIsNone(result['finite_candidate_feasible'])
                else:self.assertTrue(result['chart_verified']);self.assertTrue(result['candidate_equations_verified'])
    def test_failed_transport_retained_map_no_promotion(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);record,execution=self.archive(d);execution['results']=[dict(index=0,status='error')];execution['cost'].update(available=0,errors=1);save(d/'execution.json',execution)
            with patch.object(C,'ROOT',d):r=C.audit(d)
            self.assertEqual(r['status'],'UNKNOWN');self.assertFalse(r['chart_verified']);self.assertTrue(r['independent_affine_check']['verified'])
    def test_saved_artifact_before_terminal_commit_no_promotion(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);record,execution=self.archive(d);record.update(status='UNKNOWN',producer_complete=False,chart_available=False);execution['results'][0]['value']['status']='UNKNOWN';save(d/'jobs/affine-job.json',record);save(d/'execution.json',execution)
            progress=C.read(d/'jobs/progress.json');progress['phase']='complete';save(d/'jobs/progress.json',progress)
            with patch.object(C,'ROOT',d):r=C.audit(d)
            self.assertEqual(r['status'],'UNKNOWN');self.assertFalse(r['candidate_equations_verified']);self.assertIsNone(r['finite_candidate_feasible'])
    def test_resource_failure_and_deadline_false_claims(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);self.archive(d)
            with patch.object(C,'ROOT',d),patch.object(C.CORE,'verify_feedback',side_effect=OverflowError('old row replay cap')):r=C.audit(d)
            self.assertEqual(r['status'],'UNKNOWN');self.assertFalse(r['chart_verified']);self.assertEqual(r['resource_failure']['error_type'],'OverflowError')
            affine=C.read(d/'jobs/affine.json',8388608);affine['source_equations_independently_verified']=True;save(d/'jobs/affine.json',affine)
            with patch.object(C,'ROOT',d),patch.object(C.CORE,'verify_feedback',side_effect=AssertionError('no replay')):
                with self.assertRaises(ValueError):C.audit(d)
    def test_literal_caps_upfront_write_refusal_and_boundary_restore(self):
        C.verify_protocol(R.protocol());old=resource.getrlimit(resource.RLIMIT_AS)
        for kw in(dict(time_limit=float('nan')),dict(time_limit=3601),dict(max_operations=True),dict(max_live_cells=6000001)):
            with self.assertRaises(ValueError):C.audit('/missing',**kw)
        self.assertEqual(resource.getrlimit(resource.RLIMIT_AS),old)
        with tempfile.TemporaryDirectory()as td:
            save(Path(td)/'independent_verification.json',{})
            with patch.object(C,'_audit',side_effect=AssertionError('no replay')):
                with self.assertRaises(FileExistsError):C.audit(td,write=True)

if __name__=='__main__':unittest.main()
