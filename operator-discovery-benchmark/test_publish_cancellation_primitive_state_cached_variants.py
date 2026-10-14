import ast
import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import publish_cancellation_primitive_state_cached_variants as P


class PublisherTests(unittest.TestCase):
    def fixture(self):
        records={};traces={};checks={};jobs=[]
        for spec in P.CHECK.VARIANTS:
            name=spec['id'];check=dict(verified=True,canonical_system_independently_rebuilt=True,mathematical_feasibility='UNKNOWN',trace_check=dict(diagnostics={'equality_max_abs':1.}),**P.FLAGS)
            checks[name]=check;traces[name]=dict(variant=name,termination_status='NumericalError',raw_info={},vector_role='raw_failed_last_iterate')
            records[name]=dict(status='trace_verified',variant=name,numerical_verification_pending=False,termination_status='NumericalError',cost={},ledger={},**P.FLAGS)
            jobs.append(dict(variant=name,transport_status='available',worker_status='trace_verified',numerical_diagnostics_available=True,trace_check=check,lifecycle=dict(ledger=dict(all_stages_committed=True)),**P.FLAGS))
        review=dict(schema=P.CHECK.SCHEMA,all_passed=True,original_audit_contract_satisfied=False,protocol_envelope=dict(file='protocol.json',original_max_bytes=65536,supplemental_max_bytes=262144,actual_bytes=137531,original_audit_contract_satisfied=False),original_variables=1957,original_finite_equations=5641,selected_original_rows=779,mathematical_feasibility='UNKNOWN',numerical_diagnostics_only=True,
            preparation=dict(transport_status='available',worker_status='cache_verified',shared_cache_available=True,**P.FLAGS),cache_check=dict(verified=True,canonical_system_independently_rebuilt=True),jobs=jobs,
            source_count=109,tests_passed=20,independent_replay_operations=100,independent_replay_cells=200,**P.FLAGS)
        return dict(priors={},stage=dict(review=review,preparation_execution=dict(results=[dict(status='available')],cost={}),execution=dict(results=[dict(status='available'),dict(status='available')],cost={}),records=records,traces=traces,checks=checks,available=[True,True],preparation_record=dict(cost={},ledger={})))

    def validate(self,data):
        s=data['stage'];return P.validate_outcomes(s['review'],s['preparation_execution'],s['execution'],s['records'],s['traces'],s['checks'])

    def report(self,data):
        with patch.object(P,'sha',return_value='synthetic'):return P.report(data)

    def test_two_checked_variants_share_unchanged_problem(self):
        data=self.fixture();self.assertEqual(self.validate(data),[True,True]);r=self.report(data)
        self.assertEqual(r['shared_preparation_count'],1);self.assertFalse(r['exact_basis_replay_per_solver'])
        self.assertEqual(r['original_variables'],1957);self.assertFalse(r['RH_proved']);self.assertFalse(r['accepted_proposal'])

    def test_solver_status_selects_followup_without_admission(self):
        data=self.fixture()
        for spec,status in zip(P.CHECK.VARIANTS,('Solved','PrimalInfeasible')):
            name=spec['id'];data['stage']['traces'][name]['termination_status']=status;data['stage']['records'][name]['termination_status']=status
        self.validate(data);r=self.report(data)
        self.assertIn('rational restoration',r['variants'][0]['next_action']);self.assertIn('dual-ray',r['variants'][1]['next_action'])
        self.assertTrue(all(v['certified']is False and v['infeasibility_proved']is False for v in r['variants']))

    def test_failed_cache_gate_prevents_variant_launch(self):
        data=self.fixture();data['stage']['review']['preparation']['shared_cache_available']=False
        with self.assertRaisesRegex(ValueError,'cannot launch'):self.validate(data)

    def test_failed_transport_cannot_promote_available_trace(self):
        data=self.fixture();data['stage']['execution']['results'][0]['status']='error';data['stage']['review']['jobs'][0]['transport_status']='error'
        with self.assertRaisesRegex(ValueError,'transport admission'):self.validate(data)

    def test_variant_order_matrix_and_ledger_bindings(self):
        for mode in ('order','matrix','ledger'):
            data=self.fixture();job=data['stage']['review']['jobs'][0]
            if mode=='order':job['variant']='unexpected'
            elif mode=='matrix':job['trace_check']['canonical_system_independently_rebuilt']=False
            else:job['lifecycle']['ledger']['all_stages_committed']=False
            with self.subTest(mode=mode),self.assertRaises(ValueError):self.validate(data)

    def test_changed_original_domain_and_proof_claims_rejected(self):
        for key,value in [('original_variables',1224),('RH_proved',True),('mathematical_feasibility','feasible')]:
            data=self.fixture();data['stage']['review'][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):self.validate(data)

    def test_existing_publication_immutable(self):
        with tempfile.TemporaryDirectory() as temporary:
            base=Path(temporary);(base/'publication-016').mkdir()
            with patch.object(P,'BASE',base),patch.object(P,'load_inputs',return_value=self.fixture()):
                with self.assertRaisesRegex(ValueError,'exclusive'):P.publish()
            self.assertFalse((base/'latest.json').exists())

    def test_old_contract_failure_must_remain_explicit(self):
        for mode in ('claim','envelope','cap'):
            data=self.fixture();review=data['stage']['review']
            if mode=='claim':review['original_audit_contract_satisfied']=True
            elif mode=='envelope':review['protocol_envelope']['original_audit_contract_satisfied']=True
            else:review['protocol_envelope']['supplemental_max_bytes']=8388608
            with self.subTest(mode=mode),self.assertRaises(ValueError):self.validate(data)

    def test_no_search_or_heavy_audit_in_publication(self):
        tree=ast.parse(Path(P.__file__).read_text());calls=[n.func.attr for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute)]
        for name in ('audit','rebuild','verify_cache','verify_variant_trace','solve_cached'):self.assertNotIn(name,calls)


if __name__=='__main__':unittest.main()
