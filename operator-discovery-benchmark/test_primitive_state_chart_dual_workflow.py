import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import primitive_state_chart_dual_protocol as C
import check_primitive_state_chart_dual_search_run as W
import publish_cancellation_primitive_state_chart_dual_search as PUB


def review(status='NONCERTIFIED'):
    proved = status == 'FINITE_CONE_INFEASIBLE'
    return dict(schema=W.SCHEMA, status=status, all_passed=status != 'UNKNOWN',
                workflow_verified=True, certificate_verified=proved,
                finite_augmented_cone_infeasibility_certified=proved,
                resource_failure=None, joint_work=C.ledger(),
                independent_check=dict(verified=proved, complete=proved,
                    schema='primitive-state-chart-dual-independent-check-v1',
                    status=status, pairing='-1' if proved else None,
                    rank=782, free_coordinates=442,
                    finite_augmented_cone_infeasibility_certified=proved), **C.FLAGS)


def job_pair():
    cost = dict(elapsed_seconds=1.0, cpu_seconds=1.0, peak_rss_kib=1024,
                observed_threads_at_completion=1, pid=123)
    job = dict(status='NONCERTIFIED', producer_complete=True,
               deadline_exceeded=False, artifact='proposal.json',
               stage_counts=dict(assembly=dict(operations=100, peak_live_cells=10,
                                                maximum_rational_bits=4)),
               ledger=C.ledger(), cost=cost, **C.FLAGS)
    execution = dict(results=[dict(index=0, status='available', value=dict(
        file='jobs/search-job.json', status=job['status'], cost=cost, **C.FLAGS))],
        cost=dict(requested_workers=1, workers=1, max_in_flight=1,
                  numerical_threads_per_worker=1, worker_memory_bytes=6*1024**3,
                  memory_budget_bytes=6*1024**3, worker_memory_limit_enforced=True,
                  serial_fallback=False, start_method='spawn'))
    return job, execution


class WorkflowTests(unittest.TestCase):
    def test_single_total_reservation(self):
        self.assertEqual(sum(C.ALLOCATIONS.values()), 450000000)
        self.assertEqual(C.ALLOCATIONS['final_independent'], 50000000)
        self.assertEqual(C.SEARCH['native_attempts'], 1)

    def test_saved_noncandidate_is_explicit(self):
        job, execution = job_pair()
        outcome = dict(status='NONCERTIFIED', stage_counts=copy.deepcopy(job['stage_counts']), **C.FLAGS)
        self.assertTrue(W.verify_job(job, execution, outcome))
        for field in ('producer_complete', 'deadline_exceeded'):
            damaged = copy.deepcopy(job)
            damaged[field] = not damaged[field]
            with self.assertRaises(ValueError):
                W.verify_job(damaged, execution, outcome)

    def test_stage_counter_binding_and_work_limits(self):
        job, execution = job_pair()
        outcome = dict(status='NONCERTIFIED', stage_counts=copy.deepcopy(job['stage_counts']), **C.FLAGS)
        outcome['stage_counts']['assembly']['operations'] += 1
        with self.assertRaises(ValueError):
            W.verify_job(job, execution, outcome)
        job['stage_counts'] = copy.deepcopy(outcome['stage_counts'])
        job['stage_counts']['assembly']['operations'] = 100000001
        outcome['stage_counts'] = copy.deepcopy(job['stage_counts'])
        with self.assertRaises(ValueError):
            W.verify_job(job, execution, outcome)

    def test_bad_memory_or_thread_contract_rejected(self):
        job, execution = job_pair()
        execution['cost']['worker_memory_limit_enforced'] = False
        with self.assertRaises(ValueError):
            W.verify_job(job, execution, dict(status='NONCERTIFIED'))

    def test_missing_transport_remains_explicit(self):
        _, execution = job_pair()
        execution['results'] = [dict(index=0, status='missing_resource', reason='external timeout')]
        self.assertEqual(W.verify_transport(execution)['status'], 'missing_resource')

    def test_observed_native_limit_failure_stays_unknown(self):
        job, execution = job_pair()
        counts = dict(operations=183764369, peak_live_cells=1024, maximum_rational_bits=100)
        job['status'] = 'UNKNOWN'
        job['stage_counts']['native'] = counts
        execution['results'][0]['value']['status'] = 'UNKNOWN'
        outcome = dict(status='UNKNOWN', stage_counts=copy.deepcopy(job['stage_counts']),
                       native=dict(counts=counts, iterations=101, success=False,
                         resource_failure='native count exceeded declared cap',
                         options=dict(presolve=False, maxiter=100, threads=1)), **C.FLAGS)
        self.assertTrue(W.verify_job(job, execution, outcome))
        del outcome['native']['resource_failure']
        with self.assertRaises(ValueError):
            W.verify_job(job, execution, outcome)

    def test_publisher_requires_completed_exact_proof(self):
        self.assertFalse(PUB.checked_review(review()))
        self.assertFalse(PUB.checked_review(review('UNKNOWN')))
        self.assertTrue(PUB.checked_review(review('FINITE_CONE_INFEASIBLE')))
        bad = review('FINITE_CONE_INFEASIBLE')
        bad['independent_check']['complete'] = False
        with self.assertRaises(ValueError):
            PUB.checked_review(bad)

    def test_no_scope_promotion(self):
        for key in C.FLAGS:
            damaged = review()
            damaged[key] = True
            with self.assertRaises(ValueError):
                PUB.checked_review(damaged)
        damaged = review()
        damaged['finite_augmented_cone_infeasibility_certified'] = True
        with self.assertRaises(ValueError):
            PUB.checked_review(damaged)

    def test_one_audit_and_resource_failure(self):
        with tempfile.TemporaryDirectory() as temporary:
            with patch.object(W, '_audit', side_effect=OverflowError('shared work cap')):
                result = W.audit(temporary, write=True)
            self.assertEqual(result['status'], 'UNKNOWN')
            self.assertFalse(result['certificate_verified'])
            self.assertTrue((Path(temporary)/'independent_verification.json').is_file())
            with self.assertRaises(FileExistsError):
                W.audit(temporary, write=True)

    def test_postwrite_deadline_revokes_success(self):
        with tempfile.TemporaryDirectory() as temporary:
            with patch.object(W, '_audit', return_value=review('FINITE_CONE_INFEASIBLE')):
                with patch.object(W.time, 'monotonic', side_effect=[0, 0, 0, 2]):
                    result = W.audit(temporary, write=True, time_limit=1)
            self.assertEqual(result['status'], 'UNKNOWN')
            self.assertFalse(result['finite_augmented_cone_infeasibility_certified'])
            self.assertEqual(C.read(Path(temporary)/'independent_verification.json')['status'],
                             'UNKNOWN')


if __name__ == '__main__':
    unittest.main()
