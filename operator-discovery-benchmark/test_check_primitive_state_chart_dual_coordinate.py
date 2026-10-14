"""Tiny proposal-metadata checks and one authentic synthetic exact witness."""
import copy
import time
import unittest
from unittest.mock import patch

import check_primitive_state_chart_dual_coordinate as C
import primitive_state_chart_dual_coordinate as P


class Checks(unittest.TestCase):
    budgets=[]
    producer_operations=0

    @classmethod
    def setUpClass(cls):
        model=dict(columns=[{0:1.0},{1:1.0}],rhs=[1.0,1.0],rows=2,columns_count=2,nonzeros=2)
        cls.numerical=P.coordinate_proposal(model,deadline=time.monotonic()+30,max_operations=1000000)
        cls.producer_operations+=cls.numerical['counts']['operations']
        if not cls.numerical['complete']:raise AssertionError(cls.numerical)

    @classmethod
    def tearDownClass(cls):
        operations=cls.producer_operations+sum(b.operations for b in cls.budgets)
        print('SYNTHETIC_WORK module=test_check_primitive_state_chart_dual_coordinate operations=%d'%operations)
        if operations>5000000:raise AssertionError('owned development invocation exceeds5m')

    def budget(self,**kwargs):
        b=C.Budget(time.monotonic()+30,**kwargs);self.budgets.append(b);return b

    def verify(self,numerical=None,**kwargs):
        with patch.object(P,'coordinate_proposal',side_effect=AssertionError('no numerical replay')):
            return C.verify_numerical(self.numerical if numerical is None else numerical,2,2,2,self.budget(**kwargs))

    def reject(self,numerical):
        with self.assertRaises(ValueError):self.verify(numerical)

    def test_authentic_tiny_trajectory_has17_accounted_checkpoints(self):
        result=self.verify();self.assertTrue(result['complete']);self.assertEqual(result['checkpoints'],17)
        self.assertFalse(result['numerical_trajectory_replayed']);self.assertFalse(result['numerical_scores_verified'])
        numeric=self.numerical;r=numeric['reservation']
        self.assertEqual(r['refresh'],8*2+16*(2+2)+256)
        self.assertEqual(numeric['refreshes_charged'],sum(cp['completed_sweeps']//16+1 for cp in numeric['checkpoints']))
        self.assertEqual(numeric['counts']['operations'],r['setup']+numeric['sweeps_charged']*r['sweep']+numeric['refreshes_charged']*r['refresh'])

    def test_reservation_is_dimension_only_and_largest_common_allowance(self):
        for mutate in (
            lambda n:n['reservation'].update(sweeps_per_phase=1),
            lambda n:n['reservation'].update(refresh=n['reservation']['refresh']-8),
            lambda n:n.update(nonzeros=3),
            lambda n:n.update(max_operations=190000001),
        ):
            bad=copy.deepcopy(self.numerical);mutate(bad);self.reject(bad)

    def test_block_counters_and_complete_visits_cannot_be_forged(self):
        for mutate in (
            lambda n:n['counts'].update(operations=n['counts']['operations']+1),
            lambda n:n.update(refreshes_charged=n['refreshes_charged']-1),
            lambda n:n.update(coordinate_visits=n['coordinate_visits']-1),
            lambda n:n.update(nonzero_updates=n['sweeps_charged']*3),
            lambda n:n.update(setup_charged=False),
        ):
            bad=copy.deepcopy(self.numerical);mutate(bad);self.reject(bad)

    def test_penalty_schedule_all_phases_finite_diagnostics_and_caps(self):
        for mutate in (
            lambda n:n['checkpoints'].pop(),
            lambda n:n['checkpoints'][1].update(phase=0),
            lambda n:n['checkpoints'][0].update(penalty=0.0),
            lambda n:n['checkpoints'][0].update(completed_sweeps=n['reservation']['sweeps_per_phase']+1),
            lambda n:n['checkpoints'][0].update(relative_residual=float('inf')),
            lambda n:n['checkpoints'][0].update(support_size=True),
        ):
            bad=copy.deepcopy(self.numerical);mutate(bad);self.reject(bad)

    def test_ranking_uses_reported_scores_support_size_then_phase(self):
        numeric=copy.deepcopy(self.numerical)
        for cp in numeric['checkpoints']:cp.update(relative_residual=1.0,support_size=2)
        numeric['selected'].update(phase=0,relative_residual=1.0)
        self.verify(numeric)
        bad=copy.deepcopy(numeric);bad['selected']['phase']=1;self.reject(bad)
        numeric['checkpoints'][1].update(relative_residual=0.5,support_size=1)
        numeric['checkpoints'][2].update(relative_residual=0.5,support_size=2)
        numeric['selected'].update(phase=1,relative_residual=0.5,scaled_vector=[1.0,0.0],support=[0])
        self.verify(numeric)
        bad=copy.deepcopy(numeric);bad['selected']['phase']=2;self.reject(bad)

    def test_full_vector_and_every_strictly_positive_support_position(self):
        numeric=copy.deepcopy(self.numerical);numeric['selected']['scaled_vector']=[1.0,1e-300]
        self.verify(numeric)
        for mutate in (
            lambda n:n['selected'].update(support=[0]),
            lambda n:n['selected']['scaled_vector'].pop(),
            lambda n:n['selected']['scaled_vector'].__setitem__(1,-1.0),
            lambda n:n['selected']['scaled_vector'].__setitem__(1,True),
            lambda n:n['selected'].update(relative_residual=1.0),
        ):
            bad=copy.deepcopy(numeric);mutate(bad);self.reject(bad)

    def test_incomplete_prefix_never_admits_a_selected_support(self):
        numeric=copy.deepcopy(self.numerical);numeric.update(complete=False,selected=None)
        self.verify(numeric)
        bad=copy.deepcopy(numeric);bad['selected']=self.numerical['selected'];self.reject(bad)
        bad=copy.deepcopy(numeric);bad['checkpoints']=bad['checkpoints'][:1]
        bad['sweeps_charged']=bad['reservation']['sweeps_per_phase']*3
        self.reject(bad)
        # A no-fit proposal retains explicit reservation but charges no setup.
        model=dict(columns=[{0:1.0},{1:1.0}],rhs=[1.0,1.0],rows=2,columns_count=2,nonzeros=2)
        nofit=P.coordinate_proposal(model,deadline=time.monotonic()+30,max_operations=1)
        self.__class__.producer_operations+=nofit['counts']['operations'];self.verify(nofit)

    def test_complete_no_eligible_checkpoint_and_resource_scope_guards(self):
        numeric=copy.deepcopy(self.numerical);numeric['selected']=None
        for cp in numeric['checkpoints']:cp['support_size']=0
        self.assertIsNone(self.verify(numeric)['selected_support'])
        bad=copy.deepcopy(numeric);bad['RH_proved']=True;self.reject(bad)
        with self.assertRaises(OverflowError):self.verify(max_operations=1)
        b=self.budget(max_cells=100);b.resident_cells=90
        with self.assertRaises(OverflowError):b.live(11)
        numeric.update(complete=False,resource_failure='numerical live cell cap')
        numeric['counts']['peak_live_cells']=6000001
        self.verify(numeric)
        bad=copy.deepcopy(numeric);bad['elapsed_seconds']=float('inf');self.reject(bad)

    def test_one_authentic_full_farkas_lift_and_licensed_reduction_reuse(self):
        from test_check_primitive_state_chart_dual_geometry_search import fixture
        chart,chart_review,rays,geometry,old=fixture()
        self.__class__.producer_operations+=sum(v.get('operations',0)for v in old['stage_counts'].values())
        b=P.Budget(time.monotonic()+30)
        source,n=P.REUSE.input_model(geometry,b);reduction=P.REUSE.reduce_system(source,n,b)
        model=P.build_model(reduction,b);self.__class__.producer_operations+=b.operations
        numerical=P.coordinate_proposal(model,deadline=time.monotonic()+30,max_operations=1000000)
        self.__class__.producer_operations+=numerical['counts']['operations']
        self.assertTrue(numerical['complete']);self.assertEqual(numerical['selected']['support'],[0])
        review=dict(schema='primitive-state-chart-dual-reduction-independent-review-v1',status='REDUCTION_VERIFIED',
                    all_passed=True,reduction_verified=True,resource_failure=None,validation_failure=None,
                    finite_augmented_cone_infeasibility_certified=False,independent_check=dict(
                        schema='primitive-state-chart-dual-reduction-independent-check-v1',verified=True,complete=True,
                        reduction_verified=True,restricted_system_inconsistent=False,reduced_rows=model['rows'],
                        reduced_columns=model['columns_count']),**C.FLAGS)
        outcome=dict(schema=C.OUTCOME_SCHEMA,status='CERTIFICATE_PROPOSED',route='coordinate_descent',numerical=numerical,
                     model_stats=dict(rows=model['rows'],columns=model['columns_count'],nonzeros=model['nonzeros'],
                         active_columns=model['active_columns'],row_ids=model['row_ids'],scaling=model['scaling']),
                     certificate=old['certificate'],restoration_stats=dict(support=[0],support_size=1,rank=1,
                         free_support_coordinates=[],free_rule='zero',complete=True),policy=P.POLICY,limits=P.LIMITS,**C.FLAGS)
        args=(chart,chart_review,rays,geometry,reduction,review,outcome);original=C.Budget
        def tracked(*a,**k):
            meter=original(*a,**k);self.budgets.append(meter);return meter
        def check(arguments,**kwargs):
            with patch.object(C,'Budget',side_effect=tracked), \
                 patch.object(P.REUSE,'reduce_system',side_effect=AssertionError('licensed reduction is not replayed')), \
                 patch.object(P,'coordinate_proposal',side_effect=AssertionError('no numerical replay')), \
                 patch.object(P.OLD,'certify',side_effect=AssertionError('independent exact identity')):
                return C.verify_outcome(*arguments,deadline=time.monotonic()+30,**kwargs)
        result=check(args);self.assertEqual(result['status'],'FINITE_CONE_INFEASIBLE')
        self.assertTrue(result['complete']);self.assertTrue(result['certificate_verified'])
        self.assertEqual(result['certificate_check']['pairing'],'-1');self.assertFalse(result['numerical_scores_verified'])
        self.assertFalse(result['original_unlearned_cone_infeasibility_certified'])
        # Two full-shape mutations bind the exact lift and original identity.
        bad=list(args);bad[6]=copy.deepcopy(outcome);bad[6]['restoration_stats']['support']=[1]
        with self.assertRaisesRegex(ValueError,'every positive'):check(bad)
        bad=list(args);bad[6]=copy.deepcopy(outcome);bad[6]['certificate']['lambda_vector'][0]='0'
        with self.assertRaisesRegex(ValueError,'every exact coordinate'):check(bad)
        absent=list(args);absent[6]=dict(outcome,status='NONCERTIFIED',certificate=None)
        no_certificate=check(absent)
        self.assertTrue(no_certificate['verified']);self.assertFalse(no_certificate['complete'])
        self.assertEqual(no_certificate['status'],'NONCERTIFIED');self.assertFalse(no_certificate['certificate_verified'])
        with self.assertRaises(OverflowError)as caught:check(args,max_operations=no_certificate['audit_operations'])
        self.assertLessEqual(caught.exception.independent_audit_counts['operations'],no_certificate['audit_operations'])
        # Tiny changes to model/cost metadata fail before expensive ray parsing.
        for mutate in (
            lambda o:o['model_stats'].update(nonzeros=0),
            lambda o:o['policy'].update(penalty_weights='original L1'),
            lambda o:o.update(finite_augmented_cone_infeasibility_certified=True),
        ):
            bad=list(args);bad[6]=copy.deepcopy(outcome);mutate(bad[6])
            with self.assertRaises(ValueError):check(bad)
        with self.assertRaises(OverflowError)as caught:check(args,max_certificate_bytes=1)
        self.assertIn('operations',caught.exception.independent_audit_counts)


if __name__=='__main__':unittest.main()
