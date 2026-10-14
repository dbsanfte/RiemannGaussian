import copy
from fractions import Fraction as F
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import check_primitive_state_backtracking_recovery as C
from test_check_primitive_state_backtracking_cone_search_run import full_fixture,write


def recovery_fixture(root,d):
    record=full_fixture(root,d)
    failed=json.loads((d/'jobs/endpoint.json').read_text());failed.update(complete=False,candidate_original_vector=None,final_projected_vector=None,final_free_vector=None,diagnostics=None,reason='rational result bit cap',error_type='OverflowError',counts=dict(operations=1000,peak_live_cells=1,maximum_rational_bits=4204))
    write(d/'jobs/endpoint.json',failed);record.update(status='UNKNOWN',producer_complete=True,endpoint_complete=False,reason='rational result bit cap');record['stage_counts']['exact_endpoint']=failed['counts'];write(d/'jobs/search-job.json',record)
    progress=json.loads((d/'jobs/progress.json').read_text());progress['phase']='terminal_UNKNOWN';progress['stage_counts']=record['stage_counts'];write(d/'jobs/progress.json',progress)
    execution=json.loads((d/'execution.json').read_text());execution['results'][0]['value']['status']='UNKNOWN';write(d/'execution.json',execution)
    write(d/'recovery_protocol.json',C.recovery_protocol());write(d/'recovery_tests.json',dict(returncode=0,stderr='Ran 8 tests in 1s\n\nOK\n'))
    return failed


class RecoveryTests(unittest.TestCase):
    def test_scalar_rejection_bypasses_PSD_but_checks_all_equations(self):
        x=[F(0)]*1957;x[0]=F(-1);full=[{0:F(1)}]*5641;rhs=[F(-1)]*5641
        with patch.object(C.CORE.AFFINE,'exact_psd',side_effect=AssertionError('unneeded PSD')):r=C.scalar_first_endpoint(full,rhs,[F(0)]*1957,F(0),x,C.CORE.Budget(time.monotonic()+30))
        self.assertEqual(r['negative_scalar_count'],1);self.assertEqual(r['PSD_blocks_checked'],0);self.assertIsNone(r['PSD_failures']);self.assertEqual(r['psd_status'],'NOT_CHECKED_AFTER_SCALAR_REJECTION');self.assertFalse(r['finite_candidate_feasible'])
        rhs[0]=F(0)
        with self.assertRaises(ValueError):C.scalar_first_endpoint(full,rhs,[F(0)]*1957,F(0),x,C.CORE.Budget(time.monotonic()+30))
    def test_positive_scalars_require_three_PSD_checks(self):
        with patch.object(C.CORE.AFFINE,'exact_psd',wraps=C.CORE.AFFINE.exact_psd)as check:r=C.scalar_first_endpoint([{}for _ in range(5641)],[F(0)]*5641,[F(0)]*1957,F(0),[F(0)]*1957,C.CORE.Budget(time.monotonic()+30))
        self.assertEqual(check.call_count,3);self.assertEqual(r['PSD_blocks_checked'],3);self.assertEqual(r['PSD_failures'],0);self.assertTrue(r['finite_candidate_feasible'])
    def test_full_synthetic_recovery_preserves_original_and_consumes_reserve_once(self):
        with tempfile.TemporaryDirectory()as td:
            root=Path(td)/'root';d=Path(td)/'run';recovery_fixture(root,d);original=(d/'jobs/endpoint.json').read_bytes()
            with patch.object(C,'ROOT',root),patch('hashlib.sha256',side_effect=AssertionError('no hashes')):r=C.audit(d,write=True)
            self.assertTrue(r['all_passed']);self.assertEqual(r['status'],'RECOVERED_SCALAR_REJECTED');self.assertEqual(r['original_producer_status'],'UNKNOWN');self.assertEqual(r['recovery_check']['full_original_rows_checked'],5641);self.assertEqual(r['recovery_check']['PSD_blocks_checked'],0);self.assertEqual(r['joint_work']['total_work_reserve'],450000000);self.assertGreater(r['joint_work']['independent_io_operations'],0)
            endpoint=json.loads((d/'recovered-endpoint.json').read_text());self.assertEqual(len(endpoint['candidate_original_vector']),1957);self.assertEqual(len(endpoint['final_projected_vector']),1224);self.assertEqual(len(endpoint['final_free_vector']),444);self.assertEqual((d/'jobs/endpoint.json').read_bytes(),original)
            with self.assertRaises(FileExistsError):C.audit(d,write=True)
    def test_failed_counts_are_diagnostic_not_relaxed_result_cap(self):
        proposal=dict(schema=C.CORE.SCHEMA,status='proposed',complete=True,free_indices=[])
        failed=dict(schema='primitive-state-backtracking-cone-endpoint-v1',complete=False,reason='rational result bit cap',error_type='OverflowError',candidate_original_vector=None,final_projected_vector=None,diagnostics=None,free_indices=[],limits=dict(max_operations=25000000,max_coefficient_bits=4096,max_endpoint_bytes=2097152),counts=dict(operations=1,peak_live_cells=1,maximum_rational_bits=4204),**C.FLAGS)
        C.validate_failed_endpoint(failed,proposal)
        for bits in (4096,8194,True):
            bad=copy.deepcopy(failed);bad['counts']['maximum_rational_bits']=bits
            with self.assertRaises(ValueError):C.validate_failed_endpoint(bad,proposal)
        with self.assertRaises(OverflowError):C.CORE.Budget(time.monotonic()+30).rational(F(1<<4096))
    def test_used_original_audit_and_bad_caps_are_rejected_upfront(self):
        with tempfile.TemporaryDirectory()as td:
            d=Path(td);write(d/'independent_verification.json',{})
            with self.assertRaises(ValueError):C.audit(d)
            self.assertFalse((d/'recovery_started.json').exists())
            for kwargs in (dict(time_limit=float('nan')),dict(time_limit=3601),dict(max_operations=150000001),dict(max_cells=True)):
                with self.assertRaises(ValueError):C.audit(d,**kwargs)
    def test_resource_failure_no_vector_or_promotion_and_no_retry(self):
        with tempfile.TemporaryDirectory()as td,patch.object(C,'_audit',side_effect=OverflowError('4096 result cap')):
            r=C.audit(td,write=True);self.assertFalse(r['all_passed']);self.assertEqual(r['status'],'UNKNOWN');self.assertFalse((Path(td)/'recovered-endpoint.json').exists())
            with self.assertRaises(FileExistsError):C.audit(td)

if __name__=='__main__':unittest.main()
