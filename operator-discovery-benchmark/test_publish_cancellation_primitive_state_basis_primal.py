import ast
import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import publish_cancellation_primitive_state_basis_primal as P


class PublicationTests(unittest.TestCase):
    def fixture(self,status='NumericalError'):
        indices=list(range(779));exact=dict(verified=True,complete=True,**P.FLAGS)
        license=dict(indices=indices,prior_equation_admission=False,fresh_equation_authorization=True,replay_checks=dict(projection=exact,basis=exact))
        check=dict(verified=True,canonical_system_independently_rebuilt=True,diagnostics={'equality_max_abs':0.1},**P.FLAGS)
        trace=dict(termination_status=status,original_vector=[-1.]*1957,raw_solution=dict(x=[-1.]*1957,z=[0.]*2736,s=[0.]*2736),vector_role='raw_failed_last_iterate',raw_info={},solver={},**P.FLAGS)
        record=dict(status='trace_verified',fresh_exact_basis_authorized=True,numerical_verification_pending=False,selected_original_indices=indices,termination_status=status,raw_vector_available=True,cost={},ledger={},**P.FLAGS)
        trial=dict(accepted_proposal=False,mathematical_feasibility='UNKNOWN',transport_status='available',worker_status='trace_verified',terminal_numerical_diagnostics_available=True,trace_check=check,ledger=dict(all_stages_committed=True,pending_stages=[]),**P.FLAGS)
        review=dict(schema='primitive-state-basis-primal-independent-review-v1',all_passed=True,original_rows=5641,original_variables=1957,licensed_selected_rows=779,mathematical_feasibility='UNKNOWN',numerical_diagnostics_only=True,basis_license_replay=license,trial=trial,canonical_primal_matrix_independently_rebuilt=True,source_count=104,tests_passed=30,independent_replay_operations=100,independent_replay_cells=200,**P.FLAGS)
        return dict(priors={},stage=dict(review=review,record=record,trace=trace,check=check,execution=dict(results=[dict(status='available')],cost={}),available=True))

    def validate(self,data):
        s=data['stage'];return P.validate_outcome(s['review'],s['record'],s['execution'],s['trace'],s['check'])

    def report(self,data):
        with patch.object(P,'sha',return_value='synthetic'):return P.report(data)

    def test_available_error_is_checked_diagnostic_only(self):
        data=self.fixture();self.assertTrue(self.validate(data));r=self.report(data)
        self.assertEqual(r['original_finite_equations'],5641);self.assertEqual(r['raw_vector_lengths'],dict(x=1957,z=2736,s=2736))
        self.assertFalse(r['accepted_proposal']);self.assertFalse(r['RH_proved']);self.assertEqual(r['mathematical_feasibility'],'UNKNOWN')

    def test_native_status_only_selects_followup_not_proof(self):
        for status,text in [('Solved','rational restoration'),('PrimalInfeasible','dual ray')]:
            data=self.fixture(status);self.assertTrue(self.validate(data));r=self.report(data)
            self.assertIn(text,r['next_action']);self.assertFalse(r['certified']);self.assertFalse(r['infeasibility_proved'])

    def test_old_admission_cannot_replace_fresh_exact_replay(self):
        for key in ('prior_equation_admission','fresh_equation_authorization'):
            data=self.fixture();d=data['stage']['review']['basis_license_replay'];d[key]=not d[key]
            with self.assertRaises(ValueError):self.validate(data)
        data=self.fixture();data['stage']['review']['basis_license_replay']['replay_checks']['basis']['complete']=False
        with self.assertRaisesRegex(ValueError,'complete independent exact'):self.validate(data)

    def test_failed_transport_cannot_promote_finished_trace(self):
        data=self.fixture();data['stage']['execution']['results'][0]['status']='error';data['stage']['review']['trial']['transport_status']='error'
        with self.assertRaisesRegex(ValueError,'available diagnostic'):self.validate(data)
        data['stage']['review']['trial']['terminal_numerical_diagnostics_available']=False;data['stage']['available']=False
        self.assertFalse(self.validate(data));self.assertIn('diagnose',self.report(data)['next_action'])

    def test_missing_matrix_check_or_pending_ledger_rejected(self):
        for mode in ('matrix','check','ledger'):
            data=self.fixture()
            if mode=='matrix':data['stage']['review']['canonical_primal_matrix_independently_rebuilt']=False
            elif mode=='check':data['stage']['check']=None
            else:data['stage']['review']['trial']['ledger']['pending_stages']=['native_checker']
            with self.subTest(mode=mode),self.assertRaises(ValueError):self.validate(data)

    def test_row_domain_and_native_status_binding(self):
        data=self.fixture();data['stage']['review']['basis_license_replay']['indices']=[0]*779
        with self.assertRaisesRegex(ValueError,'row domain'):self.validate(data)
        data=self.fixture();data['stage']['record']['termination_status']='Solved'
        with self.assertRaisesRegex(ValueError,'native status'):self.validate(data)

    def test_proof_flag_rejected(self):
        data=self.fixture();data['stage']['review']['RH_proved']=True
        with self.assertRaises(ValueError):self.validate(data)

    def test_publication_exclusive_and_parent_checked(self):
        with tempfile.TemporaryDirectory() as temporary:
            base=Path(temporary);out=base/'publication-015';out.mkdir();(out/'sentinel').write_text('immutable')
            with patch.object(P,'BASE',base),patch.object(P,'load_inputs',return_value=self.fixture()):
                with self.assertRaisesRegex(ValueError,'exclusive'):P.publish()
            self.assertEqual((out/'sentinel').read_text(),'immutable')
        with tempfile.TemporaryDirectory() as temporary:
            base=Path(temporary);(base/'latest.json').write_text('{"publication":"publication-013"}')
            with patch.object(P,'BASE',base),patch.object(P,'load_inputs',return_value=self.fixture()):
                with self.assertRaisesRegex(ValueError,'latest'):P.publish()
            self.assertFalse((base/'publication-015').exists())

    def test_publisher_never_rebuilds_or_solves(self):
        tree=ast.parse(Path(P.__file__).read_text())
        names=[n.func.attr for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute)]
        for name in ('audit','rebuild','verify_trace','verify_rows','solve_trace'):self.assertNotIn(name,names)


if __name__=='__main__':unittest.main()
