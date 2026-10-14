"""Tiny exact proof-rule counterexamples and one synthetic full Farkas lift."""
import copy
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch

import check_primitive_state_chart_dual_reduction as C
import primitive_state_chart_dual_reduction as P


def artifact(rows,n,steps,final,*,forced=(),discarded=(),active=None):
    if active is None:active=sorted(set(range(n))-set(forced)-set(discarded))
    contradictory=next((i for i,row in sorted(final.items())if set(row)=={n}),None)
    return dict(schema=C.REDUCTION_SCHEMA,complete=True,input_rows=len(rows),input_columns=n,
                steps=steps,final_rows=[dict(row_id=i,terms=[[j,str(q)]for j,q in sorted(row.items())if j!=n],
                rhs=str(row.get(n,F(0))))for i,row in sorted(final.items())],
                active_columns=list(active),forced_zero_columns=list(forced),
                discarded_zero_target_columns=list(discarded),rounds=1,fixed_point=False,
                status='RESTRICTED_SYSTEM_INCONSISTENT'if contradictory is not None else'REDUCED',
                contradiction_row=contradictory,policy=C.PROTOCOL.POLICY,**C.FLAGS)


class Checks(unittest.TestCase):
    budgets=[]
    producer_budgets=[]
    extra_producer_operations=0

    @classmethod
    def tearDownClass(cls):
        operations=sum(b.operations for b in cls.budgets+cls.producer_budgets)+cls.extra_producer_operations
        print('SYNTHETIC_WORK module=test_check_primitive_state_chart_dual_reduction operations=%d'%operations)
        if operations>5000000:raise AssertionError('owned synthetic invocation exceeds5m')

    def budget(self,**kwargs):
        b=C.Budget(time.monotonic()+30,**kwargs);self.budgets.append(b);return b

    def producer_budget(self):
        b=P.Budget(time.monotonic()+30);self.producer_budgets.append(b);return b

    def replay(self,rows,n,record,**kwargs):
        with patch.object(P,'reduce_system',side_effect=AssertionError('independent reducer')):
            return C.verify_reduction(rows,n,record,self.budget(**kwargs))

    def reject(self,rows,n,record,**kwargs):
        with self.assertRaises(ValueError):self.replay(rows,n,record,**kwargs)

    def test_full_sign_support_forces_zero_in_every_row(self):
        rows={0:{0:F(-1),1:F(-2)},1:{0:F(3),1:F(-4),2:F(1),3:F(2)}}
        steps=[dict(kind='force_zero',row_id=0,columns=[0,1]),dict(kind='drop_zero_rows',rows=[0])]
        proof=artifact(rows,3,steps,{1:{2:F(1),3:F(2)}},forced=[0,1])
        result=self.replay(rows,3,proof)
        self.assertEqual(result['forced_zero_columns'],[0,1]);self.assertEqual(result['active_columns'],[2])
        bad=copy.deepcopy(proof);bad['steps'][0]['columns']=[0];self.reject(rows,3,bad)
        # Positive support with nonzero RHS admits x0=1; it cannot force zero.
        rows={0:{0:F(1),1:F(1)}}
        self.reject(rows,1,artifact(rows,1,[dict(kind='force_zero',row_id=0,columns=[0])],
                                  {0:{1:F(1)}},forced=[0]))

    def test_mixed_sign_homogeneous_equation_does_not_force_zero(self):
        rows={0:{0:F(1),1:F(-1)}}
        self.reject(rows,2,artifact(rows,2,[dict(kind='force_zero',row_id=0,columns=[0,1])],
                                  {0:{}},forced=[0,1]))

    def test_closed_zero_target_component_is_discarded_not_forced(self):
        # x0=x1 admits positive values. Choosing their zero extension suffices.
        rows={0:{0:F(1),1:F(-1)},1:{2:F(1),4:F(2)}}
        proof=artifact(rows,4,[dict(kind='discard_homogeneous_components',columns=[0,1,3],rows=[0])],
                       {1:rows[1]},discarded=[0,1,3])
        result=self.replay(rows,4,proof)
        self.assertEqual(result['discarded_zero_target_columns'],[0,1,3])
        self.assertEqual(result['forced_zero_columns'],[])
        bad=copy.deepcopy(proof);bad['forced_zero_columns']=[0,1,3];bad['discarded_zero_target_columns']=[]
        self.reject(rows,4,bad)

    def test_component_closure_and_target_are_both_essential(self):
        step=dict(kind='discard_homogeneous_components',columns=[0],rows=[0])
        for rows in ({0:{0:F(1),2:F(1)}},             # nonzero component RHS
                     {0:{0:F(1),1:F(-1)}},           # crosses removed row boundary
                     {0:{0:F(1)},1:{0:F(2),1:F(1)}}): # retained row uses removed column
            proof=artifact(rows,2,[step],{i:row for i,row in rows.items()if i!=0},discarded=[0])
            self.reject(rows,2,proof)

    def test_augmented_pivot_replays_exact_invertible_row_operations(self):
        rows={0:{0:F(2),1:F(4),2:F(6)},1:{0:F(-1),1:F(1),2:F(2)}}
        proof=artifact(rows,2,[dict(kind='pivot',row_id=0,column=0,eliminate=[1])],
                       {0:{0:F(1),1:F(2),2:F(3)},1:{1:F(3),2:F(5)}})
        result=self.replay(rows,2,proof);self.assertEqual(result['reduced_rows'],2)
        bad=copy.deepcopy(proof);bad['final_rows'][1]['rhs']='2';self.reject(rows,2,bad)
        bad=copy.deepcopy(proof);bad['steps'][0]['eliminate']=[0];self.reject(rows,2,bad)
        # Partial elimination is explicitly allowed; all unlisted rows persist.
        proof=artifact(rows,2,[dict(kind='pivot',row_id=0,column=0,eliminate=[])],
                       {0:{0:F(1),1:F(2),2:F(3)},1:rows[1]})
        self.replay(rows,2,proof)

    def test_only_zero_augmented_rows_can_be_dropped(self):
        for row in ({0:F(1)},{1:F(1)}):
            rows={0:row};self.reject(rows,1,artifact(rows,1,[dict(kind='drop_zero_rows',rows=[0])],{}))
        rows={0:{}};self.replay(rows,1,artifact(rows,1,[dict(kind='drop_zero_rows',rows=[0])],{}))

    def test_every_original_row_and_column_has_explicit_disposition(self):
        rows={0:{0:F(1),2:F(2)},1:{1:F(-1)}}
        proof=artifact(rows,2,[],rows)
        for mutate in (
            lambda p:p['final_rows'].pop(),
            lambda p:p.update(active_columns=[0]),
            lambda p:p.update(forced_zero_columns=[1]),
            lambda p:p['final_rows'][1].update(row_id=0),
        ):
            bad=copy.deepcopy(proof);mutate(bad);self.reject(rows,2,bad)
        bad=copy.deepcopy(proof);bad['steps']=[dict(kind='unknown')];self.reject(rows,2,bad)

    def test_restricted_search_contradiction_is_not_primal_infeasibility(self):
        rows={0:{1:F(-1)}};proof=artifact(rows,1,[],rows)
        result=self.replay(rows,1,proof)
        self.assertTrue(result['restricted_system_inconsistent'])
        self.assertFalse(result['primal_feasibility_certified'])
        self.assertFalse(result['RH_proved'])
        bad=copy.deepcopy(proof);bad['status']='REDUCED';self.reject(rows,1,bad)

    def test_tiny_authentic_producer_trace_is_checked_independently(self):
        rows={0:{0:F(1),1:F(1)},1:{0:F(1),2:F(-1),3:F(1)},2:{1:F(-1),2:F(1),3:F(2)}}
        proof=P.reduce_system(rows,3,self.producer_budget())
        result=self.replay(rows,3,proof)
        self.assertTrue(result['reduction_verified'])
        self.assertEqual(result['forced_zero_columns'],proof['forced_zero_columns'])

    def test_resource_and_canonical_encoding_guards(self):
        rows={0:{0:F(1),1:F(-1)}};proof=artifact(rows,2,[],rows)
        for kwargs in (dict(max_operations=1),dict(max_cells=1)):
            with self.assertRaises(OverflowError):self.replay(rows,2,proof,**kwargs)
        bad=copy.deepcopy(proof);bad['final_rows'][0]['rhs']='00';self.reject(rows,2,bad)
        bad=copy.deepcopy(proof);bad['RH_proved']=True;self.reject(rows,2,bad)
        with self.assertRaises(ValueError):C.Budget(time.monotonic()+30,max_operations=80000001)
        # Old direct-helper live calls must include the shared resident base.
        b=self.budget(max_cells=200);b.resident_cells=190
        with self.assertRaises(OverflowError):b.live(11)

    def test_one_authentic_full_farkas_certificate_support_and_shared_meter(self):
        # Existing synthetic fixture contains no actual source charts or LP.
        from test_check_primitive_state_chart_dual_geometry_search import fixture
        chart,chart_review,rays,geometry,old_outcome=fixture()
        self.__class__.extra_producer_operations+=sum(v.get('operations',0)for v in old_outcome['stage_counts'].values())
        producer=self.producer_budget();rows,n=P.input_model(geometry,producer)
        reduction=P.reduce_system(rows,n,producer)
        self.assertEqual(len(reduction['active_columns']),1)
        retained=reduction['active_columns'][0]
        ray=geometry['compression']['column_representatives'][retained]
        self.assertEqual(ray,0)
        review=dict(schema='primitive-state-chart-dual-geometry-independent-review-v1',
                    status='GEOMETRY_VERIFIED',all_passed=True,geometry_verified=True,
                    resource_failure=None,finite_augmented_cone_infeasibility_certified=False,
                    independent_check=dict(schema=C.GEOMETRY.SCHEMA,verified=True,complete=True,
                        exact_compression_verified=True,compressed_rows=len(rows),compressed_columns=n),**C.FLAGS)
        outcome=dict(schema=C.OUTCOME_SCHEMA,status='CERTIFICATE_PROPOSED',reduction_complete=True,
                     route='reduced_lp',certificate=old_outcome['certificate'],
                     native=dict(attempted=True,success=True,scaled_vector=[0.5]),
                     restoration_stats=dict(support=[0],support_size=1,rank=1,
                         free_support_coordinates=[],free_rule='zero',complete=True),**C.FLAGS)
        args=(chart,chart_review,rays,geometry,review,reduction,outcome)
        original=C.Budget
        def tracked(*a,**k):
            b=original(*a,**k);self.budgets.append(b);return b
        def check(arguments,**kwargs):
            with patch.object(C,'Budget',side_effect=tracked), \
                 patch.object(P,'reduce_system',side_effect=AssertionError('no reducer replay')), \
                 patch.object(C.GEOMETRY,'verify_geometry',side_effect=AssertionError('licensed geometry reuse')), \
                 patch.object(P.NATIVE,'native_proposal',side_effect=AssertionError('no actual LP')):
                return C.verify_outcome(*arguments,deadline=time.monotonic()+30,**kwargs)
        result=check(args)
        self.assertEqual(result['status'],'FINITE_CONE_INFEASIBLE')
        self.assertTrue(result['certificate_verified']);self.assertTrue(result['reduction_verified'])
        self.assertEqual(result['certificate_check']['pairing'],'-1')
        self.assertFalse(result['original_unlearned_cone_infeasibility_certified'])
        self.assertFalse(result['native_LP_replayed'])
        self.assertEqual(result['audit_operations'],result['independent_audit_work_reserve'])
        # Two targeted full-shape mutations: lift support and exact identity.
        bad=list(args);bad[6]=copy.deepcopy(outcome);bad[6]['restoration_stats']['support']=[1]
        with self.assertRaisesRegex(ValueError,'strictly positive'):check(bad)
        bad=list(args);bad[6]=copy.deepcopy(outcome);bad[6]['certificate']['lambda_vector'][0]='0'
        with self.assertRaisesRegex(ValueError,'every exact coordinate'):check(bad)
        absent=list(args);absent[6]=dict(outcome,status='UNKNOWN',certificate=None)
        geometry_only=check(absent)
        self.assertTrue(geometry_only['reduction_verified'])
        self.assertFalse(geometry_only['certificate_verified'])
        # Geometry reuse/reduction and certificate cannot consume fresh meters.
        with self.assertRaises(OverflowError)as caught:check(args,max_operations=geometry_only['audit_operations'])
        self.assertLessEqual(caught.exception.independent_audit_counts['operations'],geometry_only['audit_operations'])
        for kwargs in (dict(max_reduction_bytes=1),dict(max_certificate_bytes=1)):
            with self.assertRaises(OverflowError)as caught:check(args,**kwargs)
            self.assertIn('operations',caught.exception.independent_audit_counts)


if __name__=='__main__':unittest.main()
