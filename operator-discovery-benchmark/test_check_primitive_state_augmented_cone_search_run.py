import copy
from fractions import Fraction as F
import json
import tempfile
import time
from pathlib import Path
import unittest
from unittest.mock import patch
import check_primitive_state_augmented_cone_search_run as C
import run_primitive_state_augmented_cone_search as R
import primitive_state_augmented_cone_search as P
from test_check_primitive_state_augmented_cone_search import complete_inputs


def write(path,value):path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(P.encoded(value))

class Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.args=complete_inputs();a=cls.args
        cls.mapping,cls.map,cls.chart,cls.center=P.setup(a[1],a[2],a[5],a[9],a[11],deadline=time.monotonic()+30)
        # Numerical exports are proposal-only; this instrumented zero-defect
        # prefix exercises the terminal pipeline while exact checks remain real.
        def zero_metrics(mapping,x,budget,apply_adjoint=False):
            ctx=mapping['ctx'];budget.charge(2*96*15**3);return [ctx.zero]*3,[[ctx.zero]*mapping['width']for _ in range(3)],{}
        with patch.object(P,'block_metrics',side_effect=zero_metrics):cls.proposal=P.propose(cls.mapping,deadline=time.monotonic()+30)
        cls.endpoint=P.exact_endpoint(cls.mapping,cls.proposal,a[0],[a[3],*a[6]],deadline=time.monotonic()+30)
        assert cls.proposal['complete']and cls.endpoint['complete']
    def fixture(self,root):
        a=self.args;d=root/'run';d.mkdir()
        for path,value in {
            C.CACHE:a[0],C.CHART:a[1],C.AFFINE:a[2],C.CONSTRAINT:a[3],C.REVIEW:a[4],C.EXTENSION:a[5],C.NEW_CONSTRAINTS[0]:a[6][0],C.NEW_CONSTRAINTS[1]:a[6][1],C.FRESH_REVIEW:a[7],C.ENDPOINT:a[9],C.WARM_REVIEW:a[10],C.MAP:a[11],
            C.PUBLICATION+'/report.json':dict(schema=24,chart_verified=True,candidate_equations_verified=True,independent_audit_complete=True,coefficient_rank=780,free_count=444),
            C.FRESH+'/report.json':dict(a[8],coefficient_rank=782,augmented_rank=782,free_count=442),
            C.WARM_PUBLICATION+'/report.json':dict(schema=26,independent_audit_complete=True,endpoint_verified=True,candidate_equations_verified=True),
        }.items():write(root/path,value)
        write(d/'protocol.json',R.protocol());write(d/'parent.json',R.parent());write(d/'tests.json',dict(returncode=0,stdout='',stderr='Ran 1 test in 0.1s\n\nOK\n'));write(d/'run_started.json',dict(one_fixed_search=True))
        inputs=(a[1],a[2],a[5],a[9],a[11],a[0],a[3],*a[6])
        with patch.object(P,'setup',return_value=(self.mapping,self.map,self.chart,self.center)),patch.object(P,'propose',return_value=self.proposal),patch.object(P,'exact_endpoint',return_value=self.endpoint):record=R.process_search(inputs,directory=d/'jobs',deadline=time.monotonic()+30)
        record.update(cost=dict(elapsed_seconds=.1,cpu_seconds=.1,peak_rss_kib=1000,pid=123,observed_threads_at_completion=1),deadline_exceeded=False);write(d/'jobs/search-job.json',record)
        transport=dict(index=0,status='available',value=dict(file='jobs/search-job.json',status=record['status'],cost=record['cost'],**C.FLAGS))
        execution=dict(results=[transport],cost=dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',elapsed_seconds=.2,result_bytes=100,payload_bytes=100,available=1,missing=0,errors=0));write(d/'execution.json',execution)
        return d
    def test_literal_protocol_and_joint_ledger(self):
        C.verify_protocol(R.protocol());C.verify_ledger(R.ledger());self.assertEqual(R.LIMITS,C.LIMITS);self.assertEqual(R.CAPS,C.CAPS)
        bad=copy.deepcopy(R.protocol());bad['limits']['proposal_operations']=200000000
        with self.assertRaises(ValueError):C.verify_protocol(bad)
    def test_complete_synthetic_archive_and_exclusive_marker(self):
        with tempfile.TemporaryDirectory()as tmp,patch.object(C,'ROOT',Path(tmp)),patch('hashlib.sha256',side_effect=AssertionError('no hashes')):
            d=self.fixture(Path(tmp));result=C.audit(d,write=True,time_limit=30)
            self.assertTrue(result['all_passed']);self.assertEqual(result['status'],'SCALAR_REJECTED');self.assertTrue(result['chart_verified']);self.assertEqual(result['independent_search_check']['endpoint_check']['full_equations_checked'],5644);self.assertEqual(result['joint_work']['total_work_reserve'],450000000)
            with self.assertRaises(FileExistsError):C.audit(d,write=True,time_limit=30)
    def test_failed_transport_never_promotes_saved_complete_point(self):
        with tempfile.TemporaryDirectory()as tmp,patch.object(C,'ROOT',Path(tmp)):
            d=self.fixture(Path(tmp));execution=json.loads((d/'execution.json').read_text());execution['results']=[dict(index=0,status='error')];execution['cost'].update(available=0,errors=1);write(d/'execution.json',execution)
            result=C.audit(d,time_limit=30);self.assertEqual(result['status'],'UNKNOWN');self.assertFalse(result['all_passed']);self.assertFalse(result['endpoint_verified']);self.assertIsNone(result['finite_candidate_feasible'])
    def test_resource_cap_preserves_counters_and_no_admission(self):
        with tempfile.TemporaryDirectory()as tmp,patch.object(C,'ROOT',Path(tmp)):
            d=self.fixture(Path(tmp));r=C.audit(d,write=True,time_limit=30,max_operations=20);self.assertEqual(r['status'],'UNKNOWN');self.assertFalse(r['all_passed']);self.assertIsNotNone(r['resource_failure']['consumed_counts']);self.assertFalse(r['chart_verified'])
        with tempfile.TemporaryDirectory()as tmp:
            d=Path(tmp)
            with self.assertRaises(ValueError):C.audit(d,time_limit=float('nan'))
            self.assertFalse((d/'independent_started.json').exists())
    def test_forged_endpoint_or_missing_appended_row_rejected(self):
        with tempfile.TemporaryDirectory()as tmp,patch.object(C,'ROOT',Path(tmp)):
            d=self.fixture(Path(tmp));bad=copy.deepcopy(self.chart);bad['normalized_rows'].pop();write(d/'jobs/chart.json',bad)
            with self.assertRaises(ValueError):C.audit(d,time_limit=30)
    def test_late_tail_and_write_deadline_are_durable_unknown(self):
        result=dict(schema=C.SCHEMA,all_passed=True,status='SCALAR_REJECTED',chart_verified=True,center_verified=True,endpoint_verified=True,candidate_equations_verified=True,finite_candidate_feasible=False,independent_search_check=dict(audit_operations=5,audit_cells=3,peak_live_cells=4),joint_work=dict(max_work=450000000,total_work_reserve=450000000),**C.FLAGS)
        def finish(*args,**kwargs):C._IO.get()[0]=10000001;return copy.deepcopy(result)
        with tempfile.TemporaryDirectory()as tmp,patch.object(C,'_audit',side_effect=finish):
            r=C.audit(tmp,write=True,time_limit=30);self.assertFalse(r['all_passed']);self.assertFalse(r['endpoint_verified']);self.assertEqual(json.loads((Path(tmp)/'independent_verification.json').read_text())['status'],'UNKNOWN')
        with tempfile.TemporaryDirectory()as tmp,patch.object(C,'_audit',return_value=copy.deepcopy(result)),patch.object(C.time,'monotonic',side_effect=[0,0,0,31]):
            r=C.audit(tmp,write=True,time_limit=30);self.assertFalse(r['all_passed']);self.assertFalse(r['endpoint_verified']);self.assertEqual(json.loads((Path(tmp)/'independent_verification.json').read_text())['status'],'UNKNOWN')

if __name__=='__main__':unittest.main()
