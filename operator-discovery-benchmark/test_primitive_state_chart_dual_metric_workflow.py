import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import primitive_state_chart_dual_metric_protocol as C
import check_primitive_state_chart_dual_metric_run as W
import publish_cancellation_primitive_state_chart_dual_metric as PUB


def review(status='NONCERTIFIED'):
    proved = status == 'FINITE_CONE_INFEASIBLE'
    return dict(schema=W.SCHEMA,status=status,search_status='CERTIFICATE_PROPOSED' if proved else status,
        all_passed=proved,workflow_verified=True,certificate_verified=proved,
        finite_augmented_cone_infeasibility_certified=proved,resource_failure=None,
        joint_work=C.ledger(),independent_check=dict(
            schema='primitive-state-chart-dual-metric-independent-check-v1',
            status=status,verified=True,complete=proved,certificate_verified=proved,
            finite_augmented_cone_infeasibility_certified=proved,
            numerical_trajectory_replayed=False,numerical_scores_verified=False,
            certificate_check=dict(schema='primitive-state-chart-dual-independent-check-v1',
                status='FINITE_CONE_INFEASIBLE',verified=True,complete=True,
                finite_augmented_cone_infeasibility_certified=True,pairing='-1') if proved else None),**C.FLAGS)


def job_pair():
    cost = dict(elapsed_seconds=1.,cpu_seconds=1.,peak_rss_kib=1024,
                observed_threads_at_completion=1,pid=123)
    counts = dict(model=dict(operations=100,peak_live_cells=20,maximum_rational_bits=5))
    job = dict(status='UNKNOWN',producer_complete=True,deadline_exceeded=False,
               route='metric_acceleration',stage_counts=counts,ledger=C.ledger(),cost=cost,**C.FLAGS)
    execution = dict(results=[dict(index=0,status='available',value=dict(
        file='jobs/search-job.json',status='UNKNOWN',cost=cost,**C.FLAGS))],
        cost=dict(requested_workers=1,workers=1,max_in_flight=1,numerical_threads_per_worker=1,
            worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,
            worker_memory_limit_enforced=True,serial_fallback=False,start_method='spawn'))
    outcome = dict(status='UNKNOWN',route='metric_acceleration',
                   stage_counts=copy.deepcopy(counts),numerical=None,**C.FLAGS)
    return job,execution,outcome


class AcceleratedWorkflowTests(unittest.TestCase):
    def test_one_combined_budget_and_cumulative_synthetic_work(self):
        self.assertEqual(sum(C.ALLOCATIONS.values()),450000000)
        self.assertEqual(C.ALLOCATIONS['final_independent'],90000000)
        stdout = '\n'.join('SYNTHETIC_WORK module='+name+' operations=100' for name in C.TESTS[:2])
        receipt = C.synthetic_receipt(stdout)
        self.assertEqual(receipt['total_charged'],sum(C.SYNTHETIC_WORK.values())+200)
        with self.assertRaises(ValueError):
            C.synthetic_receipt(stdout.replace('operations=100','operations=25000000'))

    def test_numerical_completion_never_promotes_an_exact_proof(self):
        self.assertFalse(PUB.checked_review(review()))
        self.assertFalse(PUB.checked_review(review('UNKNOWN')))
        self.assertTrue(PUB.checked_review(review('FINITE_CONE_INFEASIBLE')))
        bad = review(); bad['all_passed'] = True
        with self.assertRaises(ValueError):
            PUB.checked_review(bad)

    def test_exact_identity_fields_are_required(self):
        for field,value in (('pairing','0'),('complete',False),('verified',False)):
            bad = review('FINITE_CONE_INFEASIBLE')
            bad['independent_check']['certificate_check'][field] = value
            with self.assertRaises(ValueError):
                PUB.checked_review(bad)

    def test_unreplayed_scores_cannot_be_labeled_verified(self):
        bad = review(); bad['independent_check']['numerical_scores_verified'] = True
        with self.assertRaises(ValueError):
            PUB.checked_review(bad)

    def test_started_stage_counters_bind_to_terminal_record(self):
        job,execution,outcome = job_pair()
        self.assertTrue(W.verify_job(job,execution,outcome))
        outcome['stage_counts']['model']['operations'] += 1
        with self.assertRaises(ValueError):
            W.verify_job(job,execution,outcome)

    def test_only_complete_selected_trajectory_allows_restoration(self):
        job,execution,outcome = job_pair()
        count = dict(operations=10,peak_live_cells=10,maximum_rational_bits=0)
        outcome['stage_counts'].update(numerical=count,restoration=count)
        job['stage_counts'] = copy.deepcopy(outcome['stage_counts'])
        outcome['numerical'] = dict(counts=count,complete=True,selected={},
                                   max_operations=C.ALLOCATIONS['numerical'])
        self.assertTrue(W.verify_job(job,execution,outcome))
        outcome['numerical']['complete'] = False
        with self.assertRaises(ValueError):
            W.verify_job(job,execution,outcome)

    def test_numerical_consumed_counters_cannot_be_replaced(self):
        job,execution,outcome = job_pair()
        count = dict(operations=10,peak_live_cells=10,maximum_rational_bits=0)
        outcome['stage_counts']['numerical'] = count
        job['stage_counts'] = copy.deepcopy(outcome['stage_counts'])
        outcome['numerical'] = dict(counts=dict(count,operations=9),
                                   max_operations=C.ALLOCATIONS['numerical'])
        with self.assertRaises(ValueError):
            W.verify_job(job,execution,outcome)

    def test_actual_numerical_allocation_cannot_be_reduced(self):
        job,execution,outcome = job_pair()
        count = dict(operations=10,peak_live_cells=10,maximum_rational_bits=0)
        outcome['stage_counts']['numerical'] = count
        job['stage_counts'] = copy.deepcopy(outcome['stage_counts'])
        outcome['numerical'] = dict(counts=count,max_operations=C.ALLOCATIONS['numerical'])
        self.assertTrue(W.verify_job(job,execution,outcome))
        outcome['numerical']['max_operations'] -= 1
        with self.assertRaises(ValueError):
            W.verify_job(job,execution,outcome)

    def test_a_started_numerical_stage_requires_its_proposal(self):
        job,execution,outcome = job_pair()
        outcome['stage_counts']['numerical'] = dict(operations=10,peak_live_cells=10,maximum_rational_bits=0)
        job['stage_counts'] = copy.deepcopy(outcome['stage_counts'])
        with self.assertRaises(ValueError):
            W.verify_job(job,execution,outcome)

    def test_one_audit_records_resource_failure_and_blocks_repetition(self):
        with tempfile.TemporaryDirectory() as temporary:
            with patch.object(W,'_audit',side_effect=OverflowError('shared90m cap')):
                result = W.audit(temporary,write=True)
            self.assertEqual(result['status'],'UNKNOWN')
            self.assertFalse(result['certificate_verified'])
            with self.assertRaises(FileExistsError):
                W.audit(temporary,write=True)

    def test_rejected_evidence_is_saved_without_promotion(self):
        with tempfile.TemporaryDirectory() as temporary:
            with patch.object(W,'_audit',side_effect=ValueError('invalid full identity')):
                result = W.audit(temporary,write=True)
            self.assertFalse(result['certificate_verified'])
            self.assertEqual(result['validation_failure']['type'],'ValueError')
            self.assertEqual(C.read(Path(temporary)/'independent_verification.json')['status'],'UNKNOWN')

    def test_late_deadline_revokes_proof(self):
        with tempfile.TemporaryDirectory() as temporary:
            with patch.object(W,'_audit',return_value=review('FINITE_CONE_INFEASIBLE')):
                with patch.object(W.time,'monotonic',side_effect=[0,0,0,2]):
                    result = W.audit(temporary,write=True,time_limit=1)
            self.assertFalse(result['certificate_verified'])
            self.assertEqual(C.read(Path(temporary)/'independent_verification.json')['status'],'UNKNOWN')


if __name__ == '__main__':
    unittest.main()
