import ast
import copy
import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch
import publish_cancellation_primitive_state_exact_basis_v2 as P


class PublisherTests(unittest.TestCase):
    def fixture(self,verified=True,consistency='consistent'):
        indices=[0,3] if verified else None
        check=dict(complete=True,verified=True,**P.FLAGS)
        values=dict(projection=dict(complete=True,status='complete',counts={'operations':10}),basis=dict(complete=True,status='complete',retained_indices=[0,3],augmented_rank=2,coefficient_consistency=consistency),**{'projection-check':check,'basis-check':check})
        record=dict(status='basis_verified' if verified else 'missing_resource',equation_reduction_verified=verified,selected_original_row_indices=indices,ledger={'total_work_reserve':30},deadline_exceeded=not verified,cost={})
        worker=dict(transport_status='available' if verified else 'missing_resource',worker_status=record['status'],equation_reduction_verified=verified,selected_original_row_indices=indices,worker_state=dict(equation_reduction_verified=verified,ledger=dict(pending_stages=[],all_stages_committed=True)),**P.FLAGS)
        review=dict(schema='primitive-state-exact-row-basis-probe-independent-review-v2',all_passed=True,original_shape=P.CHECK.EXPECTED_SHAPE,solver_called=False,mathematical_feasibility='UNKNOWN',numerical_rank_cutoff_used=False,full_optimization_variables_and_cones_unchanged=True,worker=worker,equation_reduction_verified=verified,selected_original_row_indices=indices,artifact_replays=dict(projection=check,basis=check),**P.FLAGS)
        continuation=dict(changed_limits=dict(max_receipt_bytes=dict(prior=8388608,current=33554432)),algorithms_ordering_objective_cones_unchanged=True,comparison_location='independent whole-stage audit; worker pipeline unchanged')
        replay=dict(comparison_location=continuation['comparison_location'],projection_compared=True,basis_source_order_compared=True,
            all_completed_prior_records_covered=True,completed_prior_transcript_records_compared=2,audit_operations=10,audit_cells=100,
            encoded_bytes_processed=100,independent_audit_work_reserve=111,max_encoded_bytes=83886080)
        worker['continuation']=dict(original_source_compared=True)
        review.update(continuation=continuation,continuation_replay=replay,parent_bound_files=263,
            independent_replay_operations=1000,independent_replay_cells=2000,independent_replay_work_reserve=3000)
        execution=dict(results=[dict(status=worker['transport_status'])],cost={})
        return dict(stage=dict(protocol=dict(continuation=copy.deepcopy(continuation)),review=review,record=record,execution=execution,values=values,equivalent=verified),priors={})

    def validate(self,inputs):
        s=inputs['stage'];return P.validate_outcome(s['review'],s['record'],s['execution'],s['values'])

    def result(self,inputs):
        with patch.object(P,'sha',return_value='synthetic-sha'):return P.report(inputs)

    def continuation(self,inputs):
        stage=inputs['stage']
        with patch.object(P.CHECK,'read',return_value={'transcript':[{},{}]}):
            return P.validate_continuation(stage['review'],stage['protocol'],stage['equivalent'])

    def test_complete_continuation_preserves_recorded_path(self):
        data=self.fixture();self.assertTrue(self.continuation(data)['all_completed_prior_records_covered'])
        self.assertEqual(self.result(data)['continuation_replay']['independent_audit_work_reserve'],111)

    def test_admitted_basis_requires_all_earlier_records(self):
        data=self.fixture();data['stage']['review']['continuation_replay']['completed_prior_transcript_records_compared']=1
        with self.assertRaisesRegex(ValueError,'earlier records'):self.continuation(data)

    def test_unknown_can_have_partial_continuation(self):
        data=self.fixture(False);data['stage']['review']['continuation_replay'].update(all_completed_prior_records_covered=False,completed_prior_transcript_records_compared=1)
        self.assertFalse(self.continuation(data)['all_completed_prior_records_covered'])

    def test_continuation_cannot_change_another_limit(self):
        data=self.fixture()
        for obj in (data['stage']['protocol'],data['stage']['review']):obj['continuation']['changed_limits']['max_work']={'prior':450000000,'current':500000000}
        with self.assertRaisesRegex(ValueError,'cap-only'):self.continuation(data)

    def test_continuation_comparison_not_in_worker(self):
        data=self.fixture();data['stage']['review']['continuation_replay']['comparison_location']='worker'
        with self.assertRaisesRegex(ValueError,'audit-only'):self.continuation(data)

    def test_continuation_cost_and_source_checked(self):
        for key in ('independent_audit_work_reserve','source'):
            data=self.fixture()
            if key=='source':data['stage']['review']['worker']['continuation']['original_source_compared']=False
            else:data['stage']['review']['continuation_replay'][key]=110
            with self.assertRaises(ValueError):self.continuation(data)

    def test_verified_consistent_preserves_full_variable_domain(self):
        data=self.fixture();self.assertTrue(self.validate(data));r=self.result(data)
        self.assertEqual((r['original_variables'],r['original_finite_equations'],r['augmented_rank']),(1957,5641,2))
        self.assertIn('FULL 1957-coordinate',r['next_action']);self.assertFalse(r['certified']);self.assertFalse(r['solver_called'])
        self.assertEqual(len(r['selected_original_row_indices_sha256']),64)

    def test_inconsistency_requires_separate_witness(self):
        r=self.result(self.fixture(consistency='inconsistent'));self.assertIn('left-null',r['next_action']);self.assertFalse(r['infeasibility_proved'])

    def test_unknown_never_reports_partial_rank(self):
        data=self.fixture(False);data['stage']['values']['basis'].update(complete=False,status='unknown',reason='operation cap',augmented_rank=99)
        self.assertFalse(self.validate(data));r=self.result(data)
        self.assertIsNone(r['augmented_rank']);self.assertIsNone(r['selected_original_row_indices_sha256']);self.assertNotIn('augmented_rank',r['preprocessing']['basis'])
        self.assertIn('resource block',r['next_action'])

    def test_saved_complete_basis_needs_new_replay_after_transport_failure(self):
        data=self.fixture(False)
        data['stage']['execution']['results'][0]['status']='error'
        data['stage']['review']['artifact_replays']['basis']['augmented_rank']=2
        r=self.result(data)
        self.assertIsNone(r['augmented_rank']);self.assertIsNone(r['selected_original_row_indices'])
        self.assertEqual(r['saved_exact_basis_replay']['augmented_rank'],2)
        self.assertTrue(r['saved_exact_basis_replay']['new_complete_replay_required_before_solver'])
        self.assertIn('new trial protocol',r['next_action'])

    def test_failed_transport_cannot_promote_complete_progress(self):
        data=self.fixture();data['stage']['execution']['results'][0]['status']='missing_resource';data['stage']['review']['worker']['transport_status']='missing_resource'
        with self.assertRaisesRegex(ValueError,'equivalence'):self.validate(data)

    def test_wrong_original_index_domain(self):
        data=self.fixture()
        for obj in (data['stage']['review'],data['stage']['review']['worker'],data['stage']['record']):obj['selected_original_row_indices']=[5641]
        with self.assertRaisesRegex(ValueError,'index domain'):self.validate(data)

    def test_worker_check_tampering(self):
        data=self.fixture();data['stage']['values']['basis-check']=dict(complete=True,verified=False,**P.FLAGS)
        with self.assertRaisesRegex(ValueError,'worker check'):self.validate(data)

    def test_pending_ledger_cannot_authorize(self):
        data=self.fixture();data['stage']['review']['worker']['worker_state']['ledger']['pending_stages']=['basis_checker']
        with self.assertRaisesRegex(ValueError,'ledger'):self.validate(data)

    def test_proof_flag_tampering(self):
        data=self.fixture();data['stage']['review']['certified']=True
        with self.assertRaises(ValueError):self.validate(data)

    def test_missing_artifact_and_partial_basis(self):
        for change in ('missing','partial'):
            data=self.fixture()
            if change=='missing':del data['stage']['values']['basis']
            else:data['stage']['values']['basis']['complete']=False
            with self.assertRaisesRegex(ValueError,'independently checked'):self.validate(data)

    def test_existing_publication_is_immutable(self):
        with tempfile.TemporaryDirectory() as temporary:
            base=Path(temporary);out=base/'publication-014';out.mkdir();sentinel=out/'sentinel';sentinel.write_text('immutable')
            with patch.object(P,'BASE',base),patch.object(P,'load_inputs',return_value=self.fixture()):
                with self.assertRaisesRegex(ValueError,'exclusive'):P.publish()
            self.assertEqual(sentinel.read_text(),'immutable')
            self.assertFalse((base/'latest.json').exists())

    def test_bad_parent_pointer_cannot_create_publication(self):
        with tempfile.TemporaryDirectory() as temporary:
            base=Path(temporary);(base/'latest.json').write_text('{"publication":"publication-011"}')
            with patch.object(P,'BASE',base),patch.object(P,'load_inputs',return_value=self.fixture()):
                with self.assertRaisesRegex(ValueError,'latest'):P.publish()
            self.assertFalse((base/'publication-014').exists())
            self.assertEqual(P.read(base/'latest.json')['publication'],'publication-011')

    def test_publication_never_rebuilds_or_audits(self):
        tree=ast.parse(Path(P.__file__).read_text())
        calls=[node.func.attr for node in ast.walk(tree) if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute)]
        self.assertNotIn('audit',calls);self.assertNotIn('rebuild',calls);self.assertNotIn('verify_rows',calls);self.assertNotIn('verify_projection',calls)


if __name__=='__main__':unittest.main()
