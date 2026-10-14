import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import primitive_state_chart_dual_reduction_protocol as C
import check_primitive_state_chart_dual_reduction_run as W
import publish_cancellation_primitive_state_chart_dual_reduction as PUB


def review(status='REDUCTION_VERIFIED'):
    reduction, proved = status != 'UNKNOWN', status == 'FINITE_CONE_INFEASIBLE'
    return dict(schema=W.SCHEMA, status=status, search_status='UNKNOWN',
                all_passed=reduction, workflow_verified=True, reduction_verified=reduction,
                certificate_verified=proved, finite_augmented_cone_infeasibility_certified=proved,
                resource_failure=None, joint_work=C.ledger(),
                independent_check=dict(schema='primitive-state-chart-dual-reduction-independent-check-v1',
                    verified=reduction, complete=reduction, reduction_verified=reduction,
                    status='FINITE_CONE_INFEASIBLE' if proved else 'UNKNOWN',
                    certificate_verified=proved, finite_augmented_cone_infeasibility_certified=proved,
                    certificate_check=dict(verified=True, complete=True, pairing='-1',
                        schema='primitive-state-chart-dual-independent-check-v1',
                        status='FINITE_CONE_INFEASIBLE',
                        finite_augmented_cone_infeasibility_certified=True) if proved else None), **C.FLAGS)


def job_pair():
    cost = dict(elapsed_seconds=1.0, cpu_seconds=1.0, peak_rss_kib=1024,
                observed_threads_at_completion=1, pid=123)
    counts = dict(reduction=dict(operations=100, peak_live_cells=20, maximum_rational_bits=5))
    job = dict(status='UNKNOWN', producer_complete=True, reduction_saved=True,
               deadline_exceeded=False, route='reduced_lp', stage_counts=counts,
               ledger=C.ledger(), cost=cost, **C.FLAGS)
    execution = dict(results=[dict(index=0, status='available', value=dict(
        file='jobs/search-job.json', status='UNKNOWN', cost=cost, **C.FLAGS))],
        cost=dict(requested_workers=1, workers=1, max_in_flight=1,
                  numerical_threads_per_worker=1, worker_memory_bytes=6*1024**3,
                  memory_budget_bytes=6*1024**3, worker_memory_limit_enforced=True,
                  serial_fallback=False, start_method='spawn'))
    outcome = dict(status='UNKNOWN', route='reduced_lp', stage_counts=copy.deepcopy(counts),
                   native=None, **C.FLAGS)
    return job, execution, outcome


class ReductionWorkflowTests(unittest.TestCase):
    def test_one_budget_with_shared_audit(self):
        self.assertEqual(sum(C.ALLOCATIONS.values()), 450000000)
        self.assertEqual(C.ALLOCATIONS['final_independent'], 80000000)

    def test_cumulative_synthetic_work_includes_development(self):
        stdout = '\n'.join('SYNTHETIC_WORK module='+name+' operations=100' for name in C.TESTS[:2])
        receipt = C.synthetic_receipt(stdout)
        self.assertEqual(receipt['total_charged'], sum(C.SYNTHETIC_WORK.values())+200)
        with self.assertRaises(ValueError):
            C.synthetic_receipt(stdout.replace('operations=100', 'operations=25000000'))
        with self.assertRaises(ValueError):
            C.synthetic_receipt(stdout.splitlines()[0])

    def test_reduction_can_be_verified_after_unknown_native(self):
        self.assertEqual(PUB.checked_review(review()), (True, False))
        self.assertEqual(PUB.checked_review(review('UNKNOWN')), (False, False))
        self.assertEqual(PUB.checked_review(review('FINITE_CONE_INFEASIBLE')), (True, True))

    def test_reduction_and_separator_cannot_be_confused(self):
        bad = review()
        bad['certificate_verified'] = True
        with self.assertRaises(ValueError):
            PUB.checked_review(bad)
        bad = review('FINITE_CONE_INFEASIBLE')
        bad['independent_check']['certificate_check']['pairing'] = '0'
        with self.assertRaises(ValueError):
            PUB.checked_review(bad)
        bad = review()
        bad['independent_check']['complete'] = False
        with self.assertRaises(ValueError):
            PUB.checked_review(bad)

    def test_counters_bind_to_saved_outcome(self):
        job, execution, outcome = job_pair()
        self.assertTrue(W.verify_job(job, execution, outcome, {'complete':True}))
        outcome['stage_counts']['reduction']['operations'] += 1
        with self.assertRaises(ValueError):
            W.verify_job(job, execution, outcome, {'complete':True})

    def test_dimension_only_native_cap_and_tampering(self):
        job, execution, outcome = job_pair()
        reserve = W.native_reservation(3, 2)
        counts = dict(operations=reserve['total'], peak_live_cells=100, maximum_rational_bits=10)
        outcome['stage_counts']['native'] = counts
        job['stage_counts'] = copy.deepcopy(outcome['stage_counts'])
        outcome['native'] = dict(counts=counts, attempted=True, success=False,
            iterations=reserve['max_iterations'], reservation=reserve,
            options=dict(presolve=False, threads=1, maxiter=reserve['max_iterations']))
        reduction = dict(final_rows=[1,2,3], active_columns=[4,5])
        self.assertTrue(W.verify_job(job, execution, outcome, reduction))
        outcome['native']['options']['maxiter'] -= 1
        with self.assertRaises(ValueError):
            W.verify_job(job, execution, outcome, reduction)

    def test_pre_native_resource_failure_keeps_explicit_unknown(self):
        job, execution, outcome = job_pair()
        counts = dict(operations=0, peak_live_cells=0, maximum_rational_bits=0)
        outcome['stage_counts']['native'] = counts
        job['stage_counts'] = copy.deepcopy(outcome['stage_counts'])
        outcome['native'] = dict(counts=counts, attempted=False, success=False,
            iterations=None, resource_failure='early native setup cap',
            options=dict(presolve=False, threads=1, maxiter=None))
        reduction = dict(final_rows=[1], active_columns=[2])
        self.assertTrue(W.verify_job(job, execution, outcome, reduction))

    def test_one_audit_and_resource_failure(self):
        with tempfile.TemporaryDirectory() as temporary:
            with patch.object(W, '_audit', side_effect=OverflowError('shared80m cap')):
                result = W.audit(temporary, write=True)
            self.assertFalse(result['reduction_verified'])
            self.assertEqual(result['status'], 'UNKNOWN')
            with self.assertRaises(FileExistsError):
                W.audit(temporary, write=True)

    def test_late_deadline_revokes_reduction(self):
        with tempfile.TemporaryDirectory() as temporary:
            with patch.object(W, '_audit', return_value=review()):
                with patch.object(W.time, 'monotonic', side_effect=[0,0,0,2]):
                    result = W.audit(temporary, write=True, time_limit=1)
            self.assertFalse(result['reduction_verified'])
            self.assertEqual(C.read(Path(temporary)/'independent_verification.json')['status'], 'UNKNOWN')

    def test_rejected_evidence_is_saved_without_promotion_or_second_audit(self):
        with tempfile.TemporaryDirectory() as temporary:
            with patch.object(W, '_audit', side_effect=ValueError('invalid exact reduction step')):
                result = W.audit(temporary, write=True)
            self.assertFalse(result['reduction_verified'])
            self.assertFalse(result['certificate_verified'])
            self.assertEqual(result['validation_failure']['type'], 'ValueError')
            self.assertEqual(C.read(Path(temporary)/'independent_verification.json')['status'], 'UNKNOWN')
            with self.assertRaises(FileExistsError):
                W.audit(temporary, write=True)


if __name__ == '__main__':
    unittest.main()
