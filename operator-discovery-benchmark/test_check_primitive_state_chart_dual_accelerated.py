"""Tiny accelerated metadata counterexamples and one full exact witness."""
import copy
import time
import unittest
from unittest.mock import patch

import check_primitive_state_chart_dual_accelerated as C
import primitive_state_chart_dual_accelerated as P


def record(k=1,*,trials=1,zero=False,cap=None):
    """Synthetic reported diagnostics, without any numerical iterates."""
    work=P.numerical_work_model(2,2,2);checkpoints=[];cumulative=work['setup'];L=1.0
    for index in range(1,k+1):
        L*=2**(trials-1);cumulative+=work['gradient']+trials*work['trial']+work['commit']
        norm=0.0 if zero and index==k else float(k-index+1)
        checkpoints.append(dict(iteration=index,backtracking_trials=trials,lipschitz=L,
            residual_norm=norm,relative_residual=norm,support_size=2,momentum_restarted=index%64==0,
            cumulative_operations=cumulative))
    operations=cumulative+work['final'];last=checkpoints[-1]
    if cap is None:cap=190000000 if k==10000 else operations+work['iteration_reserve']-1
    return dict(schema=C.NUMERICAL_SCHEMA,complete=True,attempted=True,max_operations=cap,
        rows=2,columns=2,nonzeros=2,work_model=work,initial_lipschitz=1.0,checkpoints=checkpoints,
        selected=dict(iteration=k,scaled_vector=[1.0,1.0],support=[0,1],relative_residual=last['relative_residual']),
        setup_charged=True,final_charged=True,gradient_blocks=k,trial_blocks=k*trials,commit_blocks=k,
        stop_reason='zero_reported_residual'if zero else'iteration_limit'if k==10000 else'work_boundary',
        final_diagnostic=dict(iteration=k,lipschitz=L,residual_norm=last['residual_norm'],
            relative_residual=last['relative_residual'],projected_gradient_norm=0.1),
        counts=dict(operations=operations,peak_live_cells=1000,maximum_rational_bits=0),elapsed_seconds=0.1,**C.FLAGS)


class Checks(unittest.TestCase):
    budgets=[]
    producer_operations=0

    @classmethod
    def setUpClass(cls):
        model=dict(columns=[{0:1.0},{1:1.0}],rhs=[1.0,1.0],rows=2,columns_count=2,nonzeros=2)
        cls.numerical=P.accelerated_proposal(model,deadline=time.monotonic()+30,max_operations=1000000)
        cls.producer_operations+=cls.numerical['counts']['operations']
        if not cls.numerical['complete']:raise AssertionError(cls.numerical)

    @classmethod
    def tearDownClass(cls):
        operations=cls.producer_operations+sum(b.operations for b in cls.budgets)
        print('SYNTHETIC_WORK module=test_check_primitive_state_chart_dual_accelerated operations=%d'%operations)
        if operations>5000000:raise AssertionError('owned development invocation exceeds5m')

    def budget(self,**kwargs):
        b=C.Budget(time.monotonic()+30,**kwargs);self.budgets.append(b);return b

    def verify(self,numerical=None,**kwargs):
        with patch.object(P,'accelerated_proposal',side_effect=AssertionError('no numerical replay')), \
             patch.object(P,'numerical_work_model',side_effect=AssertionError('independent work model')):
            return C.verify_numerical(self.numerical if numerical is None else numerical,2,2,2,self.budget(**kwargs))

    def reject(self,numerical):
        with self.assertRaises(ValueError):self.verify(numerical)

    def test_authentic_tiny_zero_stop_and_exact_block_accounting(self):
        result=self.verify();self.assertTrue(result['complete']);self.assertEqual(result['selected_support'],[0,1])
        self.assertFalse(result['numerical_scores_verified']);self.assertFalse(result['numerical_trajectory_replayed'])
        self.assertEqual(self.numerical['stop_reason'],'zero_reported_residual')
        work=self.numerical['work_model'];self.assertEqual(work['trial'],16*2+64*4+1024)
        self.assertEqual(work['iteration_reserve'],work['gradient']+32*work['trial']+work['commit'])

    def test_work_model_block_counters_and_cumulative_charges(self):
        for mutate in (
            lambda n:n['work_model'].update(trial=1),
            lambda n:n.update(gradient_blocks=2),
            lambda n:n['counts'].update(operations=n['counts']['operations']+1),
            lambda n:n['checkpoints'][0].update(cumulative_operations=1),
            lambda n:n.update(final_charged=False),
        ):
            bad=copy.deepcopy(self.numerical);mutate(bad);self.reject(bad)

    def test_accepted_start_reserves_worst32_trials_and_final(self):
        numeric=record();self.verify(numeric)
        bad=copy.deepcopy(numeric);bad['max_operations']=bad['work_model']['minimum_attempt']-1;self.reject(bad)
        bad=copy.deepcopy(numeric);bad['max_operations']=190000000;self.reject(bad)
        numeric=record(k=2)
        numeric['max_operations']=numeric['work_model']['minimum_attempt']
        self.reject(numeric) # The first step fits; the second worst-case start does not.

    def test_backtracking_l_doubling_and64_step_restart(self):
        numeric=record(k=64,trials=2);self.verify(numeric)
        bad=copy.deepcopy(numeric);bad['checkpoints'][1]['lipschitz']/=2;self.reject(bad)
        bad=copy.deepcopy(numeric);bad['checkpoints'][63]['momentum_restarted']=False;self.reject(bad)
        bad=copy.deepcopy(numeric);bad['checkpoints'][0]['backtracking_trials']=33;self.reject(bad)

    def test_zero_reported_residual_and10000_iteration_priority(self):
        numeric=record(k=2,zero=True);self.verify(numeric)
        bad=copy.deepcopy(numeric);bad['stop_reason']='work_boundary';self.reject(bad)
        bad=copy.deepcopy(numeric);bad['checkpoints'][0]['residual_norm']=0.0;self.reject(bad)
        self.verify(record(k=10000))
        numeric=record();numeric['stop_reason']='iteration_limit';self.reject(numeric)

    def test_final_diagnostic_describes_last_iterate_and_is_finite(self):
        numeric=record(k=2);self.verify(numeric)
        for mutate in (
            lambda n:n['final_diagnostic'].update(iteration=1),
            lambda n:n['final_diagnostic'].update(lipschitz=2.0),
            lambda n:n['final_diagnostic'].update(projected_gradient_norm=float('inf')),
            lambda n:n.update(elapsed_seconds=float('nan')),
        ):
            bad=copy.deepcopy(numeric);mutate(bad);self.reject(bad)

    def test_reported_ranking_and_untrimmed_full_support(self):
        numeric=record(k=2)
        for cp in numeric['checkpoints']:cp['relative_residual']=1.0
        numeric['selected'].update(iteration=1,relative_residual=1.0,scaled_vector=[1.0,1e-300])
        self.verify(numeric)
        bad=copy.deepcopy(numeric);bad['selected']['iteration']=2;self.reject(bad)
        bad=copy.deepcopy(numeric);bad['selected']['support']=[0];self.reject(bad)
        bad=copy.deepcopy(numeric);bad['selected']['scaled_vector'].pop();self.reject(bad)
        bad=copy.deepcopy(numeric);bad['selected']['scaled_vector'][1]=-1.0;self.reject(bad)

    def test_only_one_interrupted_step_or_final_and_no_selection(self):
        numeric=record(k=1,cap=1000000);work=numeric['work_model']
        numeric.update(complete=False,selected=None,final_diagnostic=None,stop_reason=None,final_charged=False,
            gradient_blocks=2,trial_blocks=3)
        numeric['counts']['operations']=work['setup']+2*work['gradient']+3*work['trial']+work['commit']
        self.verify(numeric)
        bad=copy.deepcopy(numeric);bad['gradient_blocks']=3;self.reject(bad)
        bad=copy.deepcopy(numeric);bad['initial_lipschitz']=None;self.reject(bad)
        bad=copy.deepcopy(numeric);bad['selected']=self.numerical['selected'];self.reject(bad)
        interrupted=copy.deepcopy(self.numerical)
        interrupted.update(complete=False,selected=None,final_diagnostic=None,
            resource_failure='final live cell cap')
        interrupted['counts']['peak_live_cells']=6000001;self.verify(interrupted)
        bad=copy.deepcopy(interrupted);bad['stop_reason']=None;self.reject(bad)

    def test_real_unattempted_and_deadline_failure_counters(self):
        model=dict(columns=[{0:1.0},{1:1.0}],rhs=[1.0,1.0],rows=2,columns_count=2,nonzeros=2)
        for kwargs in (dict(max_operations=1,deadline=time.monotonic()+30),
                       dict(max_operations=1000000,deadline=time.monotonic()-1)):
            numeric=P.accelerated_proposal(model,**kwargs)
            self.__class__.producer_operations+=numeric['counts']['operations']
            self.assertFalse(numeric['complete']);self.assertIsNone(numeric['selected']);self.verify(numeric)
        with self.assertRaises(OverflowError):self.verify(max_operations=1)
        b=self.budget(max_cells=100);b.resident_cells=90
        with self.assertRaises(OverflowError):b.live(11)

    def test_one_authentic_full_exact_certificate_and_shared90m_lift(self):
        from test_check_primitive_state_chart_dual_geometry_search import fixture
        chart,chart_review,rays,geometry,old=fixture()
        self.__class__.producer_operations+=sum(v.get('operations',0)for v in old['stage_counts'].values())
        producer=P.Budget(time.monotonic()+30)
        source,n=P.REUSE.input_model(geometry,producer);reduction=P.REUSE.reduce_system(source,n,producer)
        model=P.build_model(reduction,producer);self.__class__.producer_operations+=producer.operations
        numerical=P.accelerated_proposal(model,deadline=time.monotonic()+30,max_operations=1000000)
        self.__class__.producer_operations+=numerical['counts']['operations']
        self.assertTrue(numerical['complete']);self.assertEqual(numerical['selected']['support'],[0])
        review=dict(schema='primitive-state-chart-dual-reduction-independent-review-v1',status='REDUCTION_VERIFIED',
            all_passed=True,reduction_verified=True,resource_failure=None,validation_failure=None,
            finite_augmented_cone_infeasibility_certified=False,independent_check=dict(
                schema='primitive-state-chart-dual-reduction-independent-check-v1',verified=True,complete=True,
                reduction_verified=True,restricted_system_inconsistent=False,reduced_rows=model['rows'],
                reduced_columns=model['columns_count']),**C.FLAGS)
        outcome=dict(schema=C.OUTCOME_SCHEMA,status='CERTIFICATE_PROPOSED',route='accelerated_gradient',numerical=numerical,
            model_stats=dict(rows=model['rows'],columns=model['columns_count'],nonzeros=model['nonzeros'],
                active_columns=model['active_columns'],row_ids=model['row_ids'],scaling=model['scaling']),
            certificate=old['certificate'],restoration_stats=dict(support=[0],support_size=1,rank=1,
                free_support_coordinates=[],free_rule='zero',complete=True),policy=P.POLICY,limits=P.LIMITS,**C.FLAGS)
        args=(chart,chart_review,rays,geometry,reduction,review,outcome);original=C.Budget
        def tracked(*a,**k):
            b=original(*a,**k);self.budgets.append(b);return b
        def check(arguments,**kwargs):
            with patch.object(C,'Budget',side_effect=tracked), \
                 patch.object(P,'accelerated_proposal',side_effect=AssertionError('no trajectory replay')), \
                 patch.object(P.REUSE,'reduce_system',side_effect=AssertionError('licensed reduction reused')), \
                 patch.object(P.OLD,'certify',side_effect=AssertionError('independent full identity')):
                return C.verify_outcome(*arguments,deadline=time.monotonic()+30,**kwargs)
        result=check(args);self.assertTrue(result['complete']);self.assertTrue(result['certificate_verified'])
        self.assertEqual(result['status'],'FINITE_CONE_INFEASIBLE');self.assertEqual(result['certificate_check']['pairing'],'-1')
        self.assertFalse(result['numerical_scores_verified']);self.assertFalse(result['original_unlearned_cone_infeasibility_certified'])
        bad=list(args);bad[6]=copy.deepcopy(outcome);bad[6]['restoration_stats']['support']=[1]
        with self.assertRaisesRegex(ValueError,'every positive'):check(bad)
        bad=list(args);bad[6]=copy.deepcopy(outcome);bad[6]['certificate']['lambda_vector'][0]='0'
        with self.assertRaisesRegex(ValueError,'every exact coordinate'):check(bad)
        absent=list(args);absent[6]=dict(outcome,status='NONCERTIFIED',certificate=None)
        diagnostic=check(absent);self.assertTrue(diagnostic['verified']);self.assertFalse(diagnostic['complete'])
        self.assertEqual(diagnostic['status'],'NONCERTIFIED');self.assertFalse(diagnostic['certificate_verified'])
        with self.assertRaises(OverflowError)as caught:check(args,max_operations=diagnostic['audit_operations'])
        self.assertLessEqual(caught.exception.independent_audit_counts['operations'],diagnostic['audit_operations'])
        bad=list(args);bad[6]=dict(outcome,RH_proved=True)
        with self.assertRaises(ValueError):check(bad)
        with self.assertRaises(OverflowError)as caught:check(args,max_certificate_bytes=1)
        self.assertIn('operations',caught.exception.independent_audit_counts)


if __name__=='__main__':unittest.main()
