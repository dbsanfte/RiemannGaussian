"""Tiny active-face metadata checks and one synthetic original exact witness."""
import copy
import time
import unittest
from unittest.mock import patch

import check_primitive_state_chart_dual_active as C
import primitive_state_chart_dual_active as P


def reconcile(numeric):
    """Populate synthetic counter receipts without running any numerical step."""
    work=numeric['work_model'];cumulative=work['setup']if numeric['setup_charged']else 0
    if numeric['checkpoints']:numeric['checkpoints'][0]['cumulative_operations']=cumulative
    for face in numeric['faces']:
        fw=P.face_work_model(numeric['rows'],len(face['active']),face['nonzeros'])
        cumulative+=work['gradient']+int(face['setup_charged'])*fw['setup']+face['cg_blocks']*fw['cg_step']+int(face['commit_charged'])*work['commit']
        face['cumulative_operations']=cumulative if face['complete']else None
        if face['complete']:numeric['checkpoints'][face['iteration']]['cumulative_operations']=cumulative
    cumulative+=(numeric['gradient_blocks']-len(numeric['faces']))*work['gradient']
    operations=cumulative+int(numeric['final_charged'])*work['final']
    numeric['counts']=dict(operations=operations,peak_live_cells=1000,maximum_rational_bits=0)
    numeric['max_operations']=operations+work['iteration_reserve']-1 if numeric['stop_reason']=='work_boundary'else 1000000
    return numeric


def script():
    """Reported damped initial face, surviving refinement, then one entry."""
    faces=[]
    for index,(active,mode,entry,damped,hits,survivors) in enumerate((
        ([0,1],'initial_face',None,True,[0],[1]),
        ([1],'refine_face',None,False,[],[1]),
        ([1,2],'enter_column',2,False,[],[1,2]),
    ),1):
        z=sum([1,2,1][j]for j in active)
        faces.append(dict(iteration=index,mode=mode,entered=entry,entry_score=1.0 if entry is not None else None,
            active=active,nonzeros=z,cg_limit=min(128,2*len(active)),setup_charged=True,cg_blocks=1,
            cg_steps_completed=1,cg_stop='zero_normal_residual',commit_charged=True,complete=True,
            damped=damped,step_fraction=0.5 if damped else 1.0,boundary_hits=hits,
            surviving_support=survivors,cumulative_operations=None))
    numeric=dict(schema=C.NUMERICAL_SCHEMA,complete=True,attempted=True,rows=2,columns=3,nonzeros=4,
        work_model=P.numerical_work_model(2,3,4),initial_vector=[1.0,1.0,0.0],metric_diagonal=[1.0,2.0,1.0],
        setup_charged=True,final_charged=True,gradient_blocks=3,faces=faces,
        checkpoints=[dict(iteration=i,residual_norm=1.0-i*0.2,relative_residual=1.0-i*0.2,
            support_size=size,cumulative_operations=None)for i,size in enumerate((2,1,1,2))],
        selected=dict(iteration=3,scaled_vector=[0.0,1.0,1e-300],support=[1,2],relative_residual=0.4),
        stop_reason='work_boundary',final_diagnostic=dict(iteration=3,residual_norm=0.4,
            relative_residual=0.4,projected_gradient_norm=0.1,mapping_metric=C.METRIC),elapsed_seconds=0.1,**C.FLAGS)
    numeric['selected']['relative_residual']=numeric['checkpoints'][3]['relative_residual']
    return reconcile(numeric)


class Checks(unittest.TestCase):
    budgets=[]
    producer_operations=0

    @classmethod
    def setUpClass(cls):
        cls.model=dict(columns=[{0:1.0},{1:1.0}],rhs=[1.0,1.0],rows=2,columns_count=2,nonzeros=2)
        cls.numeric=P.active_set_proposal(cls.model,deadline=time.monotonic()+30,max_operations=1000000)
        cls.producer_operations+=cls.numeric['counts']['operations']
        if not cls.numeric['complete']:raise AssertionError(cls.numeric)

    @classmethod
    def tearDownClass(cls):
        operations=cls.producer_operations+sum(b.operations for b in cls.budgets)
        print('SYNTHETIC_WORK module=test_check_primitive_state_chart_dual_active operations=%d'%operations)
        if operations>5000000:raise AssertionError('owned invocation exceeds5m synthetic work')

    def budget(self,**kwargs):
        b=C.Budget(time.monotonic()+30,**kwargs);self.budgets.append(b);return b

    def verify(self,numeric=None,*,scripted=False,initial=None,**kwargs):
        data=self.numeric if numeric is None else numeric
        dimensions=(2,3,4)if scripted else(2,2,2);column_nnz=[1,2,1]if scripted else[1,1]
        if scripted and initial is None:initial=[1.0,1.0,0.0]
        with patch.object(P,'active_set_proposal',side_effect=AssertionError('no numerical replay')), \
             patch.object(P,'face_work_model',side_effect=AssertionError('independent face work')), \
             patch.object(P,'numerical_work_model',side_effect=AssertionError('independent full work')):
            return C.verify_numerical(data,*dimensions,self.budget(**kwargs),column_nonzeros=column_nnz,initial_vector=initial)

    def reject(self,data,**kwargs):
        with self.assertRaises(ValueError):self.verify(data,**kwargs)

    def test_authentic_cold_face_blocks_and_actual_column_sparsity(self):
        result=self.verify();self.assertTrue(result['complete']);self.assertEqual(result['selected_support'],[0,1])
        self.assertFalse(result['numerical_scores_verified']);self.assertFalse(result['numerical_trajectory_replayed'])
        self.assertEqual(self.numeric['checkpoints'][0]['iteration'],0)
        self.assertEqual(self.numeric['stop_reason'],'zero_reported_residual')
        for face in self.numeric['faces']:
            self.assertEqual(face['nonzeros'],len(face['active']))
        bad=copy.deepcopy(self.numeric);bad['faces'][0]['nonzeros']+=1;self.reject(bad)
        bad=copy.deepcopy(self.numeric);bad['work_model']['cg_step_full']-=1;self.reject(bad)

    def test_damped_initial_refine_then_entry_support_carry(self):
        numeric=script();self.verify(numeric,scripted=True)
        for mutate in (
            lambda n:n['faces'][1].update(mode='enter_column'),
            lambda n:n['faces'][2].update(entered=1),
            lambda n:n['faces'][0].update(surviving_support=[0,1]),
            lambda n:n['faces'][1].update(boundary_hits=[1]),
        ):
            bad=copy.deepcopy(numeric);mutate(bad);self.reject(bad,scripted=True)

    def test_initial_vector_is_seed_bound_and_initial_checkpoint_can_win(self):
        numeric=P.active_set_proposal(self.model,[1.0,1.0],deadline=time.monotonic()+30,max_operations=1000000)
        self.__class__.producer_operations+=numeric['counts']['operations']
        self.verify(numeric,initial=[1.0,1.0]);self.assertEqual(numeric['selected']['iteration'],0)
        self.reject(numeric,initial=[2.0,1.0])
        bad=copy.deepcopy(numeric);bad['selected']['scaled_vector'][0]=2.0;self.reject(bad,initial=[1.0,1.0])
        bad=copy.deepcopy(numeric);bad['metric_diagonal'][0]=0.0;self.reject(bad,initial=[1.0,1.0])

    def test_full_start_guard_cumulative_counts_and_work_boundary(self):
        numeric=script()
        for mutate in (
            lambda n:n.update(max_operations=n['work_model']['minimum_attempt']),
            lambda n:n.update(max_operations=190000000),
            lambda n:n['faces'][0].update(cumulative_operations=1),
            lambda n:n['counts'].update(operations=n['counts']['operations']+1),
        ):
            bad=copy.deepcopy(numeric);mutate(bad);self.reject(bad,scripted=True)

    def test_cg_stop_completed_counts_and_breakdown_priority(self):
        numeric=script();numeric['faces']=numeric['faces'][:1];numeric['checkpoints']=numeric['checkpoints'][:2]
        numeric.update(gradient_blocks=1,stop_reason='krylov_breakdown')
        numeric['faces'][0].update(cg_stop='zero_curvature',cg_steps_completed=0)
        numeric['selected'].update(iteration=1,scaled_vector=[0.0,1.0,0.0],support=[1],
            relative_residual=numeric['checkpoints'][1]['relative_residual'])
        numeric['final_diagnostic']['iteration']=1;reconcile(numeric);self.verify(numeric,scripted=True)
        bad=copy.deepcopy(numeric);bad['faces'][0]['cg_steps_completed']=1;self.reject(bad,scripted=True)
        bad=copy.deepcopy(numeric);bad['stop_reason']='work_boundary';self.reject(bad,scripted=True)
        bad=copy.deepcopy(self.numeric);bad['faces'][0]['cg_stop']='iteration_limit';self.reject(bad)

    def test_terminal_no_positive_correlation_has_one_extra_guarded_gradient(self):
        model=dict(self.model,rhs=[-1.0,-1.0])
        numeric=P.active_set_proposal(model,deadline=time.monotonic()+30,max_operations=1000000)
        self.__class__.producer_operations+=numeric['counts']['operations']
        self.verify(numeric);self.assertEqual(numeric['stop_reason'],'no_positive_inactive_correlation')
        self.assertEqual(numeric['gradient_blocks'],len(numeric['faces'])+1)
        self.assertIsNone(numeric['selected'])
        bad=copy.deepcopy(numeric);bad['gradient_blocks']=0;reconcile(bad);self.reject(bad)

    def test_ranked_selected_vector_keeps_every_strictly_positive_entry(self):
        numeric=script();self.verify(numeric,scripted=True)
        for mutate in (
            lambda n:n['selected'].update(support=[1]),
            lambda n:n['selected']['scaled_vector'].__setitem__(2,0.0),
            lambda n:n['selected'].update(iteration=1),
            lambda n:n['selected']['scaled_vector'].pop(),
        ):
            bad=copy.deepcopy(numeric);mutate(bad);self.reject(bad,scripted=True)

    def test_one_partial_face_or_final_retains_charges_without_selection(self):
        numeric=script();numeric['faces']=numeric['faces'][:1];numeric['checkpoints']=numeric['checkpoints'][:1]
        numeric.update(complete=False,selected=None,gradient_blocks=1,final_charged=False,
            final_diagnostic=None,stop_reason=None)
        numeric['faces'][0].update(complete=False,commit_charged=False,cg_steps_completed=0,cg_stop=None,
            damped=None,step_fraction=None,boundary_hits=None,surviving_support=None)
        reconcile(numeric);self.verify(numeric,scripted=True)
        bad=copy.deepcopy(numeric);bad['gradient_blocks']=2;reconcile(bad);self.reject(bad,scripted=True)
        bad=copy.deepcopy(numeric);bad['selected']=script()['selected'];self.reject(bad,scripted=True)
        interrupted=copy.deepcopy(self.numeric);interrupted.update(complete=False,selected=None,final_diagnostic=None,
            resource_failure='active live cells')
        interrupted['counts']['peak_live_cells']=6000001;self.verify(interrupted)

    def test_real_no_fit_deadline_and_final_diagnostic_label(self):
        for kwargs in (dict(max_operations=1,deadline=time.monotonic()+30),
                       dict(max_operations=1000000,deadline=time.monotonic()-1)):
            numeric=P.active_set_proposal(self.model,**kwargs)
            self.__class__.producer_operations+=numeric['counts']['operations'];self.verify(numeric)
            self.assertFalse(numeric['complete']);self.assertIsNone(numeric['selected'])
        bad=copy.deepcopy(self.numeric);bad['final_diagnostic']['mapping_metric']='unscaled KKT proof';self.reject(bad)
        bad=copy.deepcopy(self.numeric);bad['final_diagnostic']['iteration']=0;self.reject(bad)
        with self.assertRaises(OverflowError):self.verify(max_operations=1)
        b=self.budget(max_cells=100);b.resident_cells=90
        with self.assertRaises(OverflowError):b.live(11)

    def test_one_authentic_full_original_farkas_witness_and_optional_seed(self):
        from test_check_primitive_state_chart_dual_geometry_search import fixture
        chart,chart_review,rays,geometry,old=fixture()
        self.__class__.producer_operations+=sum(v.get('operations',0)for v in old['stage_counts'].values())
        producer=P.Budget(time.monotonic()+30)
        source,n=P.REUSE.input_model(geometry,producer);reduction=P.REUSE.reduce_system(source,n,producer)
        model=P.build_model(reduction,producer);self.__class__.producer_operations+=producer.operations
        numerical=P.active_set_proposal(model,[0.5],deadline=time.monotonic()+30,max_operations=1000000)
        self.__class__.producer_operations+=numerical['counts']['operations']
        self.assertTrue(numerical['complete']);self.assertEqual(numerical['selected']['support'],[0])
        seed=dict(schema='primitive-state-chart-dual-coordinate-search-v1',numerical=dict(
            schema='primitive-state-chart-dual-coordinate-proposal-v1',complete=True,selected=dict(scaled_vector=[0.5])))
        review=dict(schema='primitive-state-chart-dual-reduction-independent-review-v1',status='REDUCTION_VERIFIED',
            all_passed=True,reduction_verified=True,resource_failure=None,validation_failure=None,
            finite_augmented_cone_infeasibility_certified=False,independent_check=dict(
                schema='primitive-state-chart-dual-reduction-independent-check-v1',verified=True,complete=True,
                reduction_verified=True,restricted_system_inconsistent=False,reduced_rows=model['rows'],
                reduced_columns=model['columns_count']),**C.FLAGS)
        outcome=dict(schema=C.OUTCOME_SCHEMA,status='CERTIFICATE_PROPOSED',route='active_set',numerical=numerical,
            model_stats=dict(rows=model['rows'],columns=model['columns_count'],nonzeros=model['nonzeros'],
                active_columns=model['active_columns'],row_ids=model['row_ids'],scaling=model['scaling']),
            certificate=old['certificate'],restoration_stats=dict(support=[0],support_size=1,rank=1,
                free_support_coordinates=[],free_rule='zero',complete=True),policy=P.POLICY,limits=P.LIMITS,**C.FLAGS)
        args=(chart,chart_review,rays,geometry,reduction,review,outcome);original=C.Budget
        def tracked(*a,**k):
            b=original(*a,**k);self.budgets.append(b);return b
        def check(arguments,**kwargs):
            with patch.object(C,'Budget',side_effect=tracked), \
                 patch.object(P,'active_set_proposal',side_effect=AssertionError('no trajectory replay')), \
                 patch.object(P.REUSE,'reduce_system',side_effect=AssertionError('licensed prior reduction')), \
                 patch.object(P.OLD,'certify',side_effect=AssertionError('independent exact witness')):
                return C.verify_outcome(*arguments,seed=seed,deadline=time.monotonic()+30,**kwargs)
        result=check(args);self.assertTrue(result['complete']);self.assertEqual(result['status'],'FINITE_CONE_INFEASIBLE')
        self.assertEqual(result['certificate_check']['pairing'],'-1');self.assertFalse(result['numerical_scores_verified'])
        self.assertFalse(result['original_unlearned_cone_infeasibility_certified'])
        bad=list(args);bad[6]=copy.deepcopy(outcome);bad[6]['restoration_stats']['support']=[1]
        with self.assertRaisesRegex(ValueError,'every selected positive'):check(bad)
        bad=list(args);bad[6]=copy.deepcopy(outcome);bad[6]['certificate']['lambda_vector'][0]='0'
        with self.assertRaisesRegex(ValueError,'every exact coordinate'):check(bad)
        absent=list(args);absent[6]=dict(outcome,status='NONCERTIFIED',certificate=None)
        diagnostic=check(absent);self.assertTrue(diagnostic['verified']);self.assertFalse(diagnostic['complete'])
        self.assertEqual(diagnostic['status'],'NONCERTIFIED')
        with self.assertRaises(OverflowError)as caught:check(args,max_operations=diagnostic['audit_operations'])
        self.assertLessEqual(caught.exception.independent_audit_counts['operations'],diagnostic['audit_operations'])
        bad=list(args);bad[6]=dict(outcome,RH_proved=True)
        with self.assertRaises(ValueError):check(bad)
        with self.assertRaises(OverflowError)as caught:check(args,max_certificate_bytes=1)
        self.assertIn('operations',caught.exception.independent_audit_counts)


if __name__=='__main__':unittest.main()
