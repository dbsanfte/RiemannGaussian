import ast
import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import publish_cancellation_primitive_state_triangular_restoration as P


class PublicationTests(unittest.TestCase):
    def fixture(self,feasible=True):
        exact=dict(equality_complete=True,scalar_signs_complete=True,equality_mismatch_count=0,negative_scalar_count=0 if feasible else 1,psd_blocks={n:dict(psd=True) for n in ('full_child','full_parent','storage_K')},finite_candidate_feasible=feasible)
        check=dict(verified=True,complete=True,restoration_verified=True,all_original_equations_checked=5641,original_variables=1957,candidate_hash='candidate',finite_candidate_feasible=feasible,exact_candidate_checks=exact,**P.FLAGS)
        producer=dict(status='restored',complete=True,candidate_hash='candidate',counts={},clipped_free_square_indices=[1],**P.FLAGS)
        record=dict(status='restoration_verified',deadline_exceeded=False,restoration_verified=True,finite_candidate_feasible=feasible,cost={},ledger={},**P.FLAGS)
        execution=dict(results=[dict(status='available')],cost={})
        job=dict(transport_status='available',worker_status='restoration_verified',restoration_verified=True,finite_candidate_feasible=feasible,lifecycle=dict(ledger=dict(all_stages_committed=True)),**P.FLAGS)
        review=dict(schema='primitive-state-triangular-restoration-independent-review-v1',all_passed=True,original_finite_equations=5641,original_variables=1957,projected_variables=1224,rank=779,parent_source_rebuilds=0,new_solver_calls=0,new_elimination_calls=0,uniform_or_RH_admission=False,objective_preserved=False,job=job,restoration_check=check,source_count=108,tests_passed=36,independent_replay_operations=1,independent_replay_cells=1,total_independent_audit_operations=2,total_independent_audit_cells=2,**P.FLAGS)
        return dict(priors={},stage=dict(review=review,execution=execution,record=record,producer=producer,check=check,available=True))

    def validate(self,data):
        s=data['stage'];return P.validate_outcome(s['review'],s['execution'],s['record'],s['producer'],s['check'])

    def report(self,data):
        with patch.object(P,'sha',return_value='synthetic'):return P.report(data)

    def test_exact_finite_success_remains_without_uniform_admission(self):
        data=self.fixture();self.assertTrue(self.validate(data));r=self.report(data)
        self.assertTrue(r['finite_candidate_feasible']);self.assertFalse(r['accepted_proposal']);self.assertFalse(r['RH_proved'])
        self.assertIn('typed finite-certificate',r['next_action'])

    def test_exact_failure_rejects_candidate_without_cone_exclusion(self):
        data=self.fixture(False);self.assertTrue(self.validate(data));r=self.report(data)
        self.assertFalse(r['finite_candidate_feasible']);self.assertFalse(r['infeasibility_proved'])
        self.assertEqual(r['mathematical_cone_feasibility'],'UNKNOWN');self.assertIn('free coordinates',r['next_action'])

    def test_all_constraints_determine_finite_verdict(self):
        for mode in ('sign','psd','equality','incomplete'):
            data=self.fixture();exact=data['stage']['check']['exact_candidate_checks']
            if mode=='sign':exact['negative_scalar_count']=1
            elif mode=='psd':exact['psd_blocks']['storage_K']['psd']=False
            elif mode=='equality':exact['equality_mismatch_count']=1
            else:exact['equality_complete']=False
            with self.subTest(mode=mode),self.assertRaises(ValueError):self.validate(data)

    def test_partial_transport_does_not_promote_retained_proof(self):
        data=self.fixture();s=data['stage'];s['execution']['results'][0]['status']='missing_resource'
        s['review']['job'].update(transport_status='missing_resource',restoration_verified=False,finite_candidate_feasible=None)
        s['available']=False;self.assertFalse(self.validate(data));self.assertIsNone(self.report(data)['finite_candidate_feasible'])
        s['review']['job']['finite_candidate_feasible']=True
        with self.assertRaises(ValueError):self.validate(data)

    def test_deadline_and_pending_ledger_cannot_report_available_success(self):
        for mode in ('deadline','ledger'):
            data=self.fixture()
            if mode=='deadline':data['stage']['record']['deadline_exceeded']=True
            else:data['stage']['review']['job']['lifecycle']['ledger']['all_stages_committed']=False
            with self.subTest(mode=mode),self.assertRaises(ValueError):self.validate(data)

    def test_reduced_equations_or_unbound_candidate_rejected(self):
        for key,value in [('all_original_equations_checked',779),('candidate_hash','changed'),('complete',False)]:
            data=self.fixture();data['stage']['check'][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):self.validate(data)

    def test_scope_and_theorem_promotion_rejected(self):
        for key,value in [('RH_proved',True),('objective_preserved',True),('new_solver_calls',1)]:
            data=self.fixture();data['stage']['review'][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):self.validate(data)

    def test_existing_publication_refuses_before_loading(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);(base/'publication-017').mkdir()
            with patch.object(P,'BASE',base),patch.object(P,'load_inputs') as load:
                with self.assertRaisesRegex(ValueError,'exclusive'):P.publish()
                load.assert_not_called()

    def test_publication_performs_no_research_or_exact_replay(self):
        tree=ast.parse(Path(P.__file__).read_text())
        names=[n.func.attr for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute)]
        for name in ('audit','restore','rebuild','verify_restoration','backsubstitute'):self.assertNotIn(name,names)

    def test_actual_completed_archive_and_review_filename_bindings(self):
        archive=P.completed_archive()
        self.assertTrue(archive['available'])
        self.assertFalse(archive['check']['finite_candidate_feasible'])
        self.assertEqual(archive['check']['all_original_equations_checked'],5641)
        self.assertEqual(archive['check']['exact_candidate_checks']['negative_scalar_count'],117)


if __name__=='__main__':unittest.main()
