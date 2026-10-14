import copy
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import check_primitive_state_fresh_identity_probe as C
import primitive_state_fresh_identity_probe as P


def tiny_cases():
    vector=['0']*1957;plans=[];receipts=[]
    for index,assignment in enumerate(([3,5,7],[-2,5,-10])):
        plan=P.preflight(vector,P.PROGRAM,X=1,assignment=assignment,case_index=index);receipt=P.probe(vector,plan,deadline=time.monotonic()+30);plans.append(plan);receipts.append(receipt)
    return vector,plans,receipts


def chart_inputs():
    retained,_=C.projection_layout();old=[j for j in range(780)if j!=148];pivots=list(range(780));free=list(range(780,1224))
    chart=dict(schema='primitive-state-feedback-affine-chart-v1',width=1224,original_width=1957,old_rank=779,new_rank=780,classification='independent',retained_indices=retained,old_pivots=old,pivot_columns=pivots,free_indices=free,old_free_indices=sorted([148,*free]),normalized_rows=[dict(pivot=p,source_row=i,terms=[[p,'1']])for i,p in enumerate(old)],appended_row=dict(pivot=148,source_row='feedback',terms=[[148,'1']]))
    report=dict(schema=24,chart_verified=True,candidate_equations_verified=True,independent_audit_complete=True,classification='independent',coefficient_rank=780,augmented_rank=780,free_count=444)
    review=dict(schema='primitive-state-feedback-affine-independent-review-v1',all_passed=True,status='AFFINE_UPDATED',chart_verified=True,independent_affine_check=dict(verified=True,complete=True,all_original_rows_replayed=True,normalized_chart_verified=True,new_rank=780,new_free_count=444))
    return chart,review,report

class CoreTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.vector,cls.plans,cls.receipts=tiny_cases()
    def test_two_full_assignments_shared_budget_and_no_hashes(self):
        chart,review,report=chart_inputs()
        with patch('hashlib.sha256',side_effect=AssertionError('no hashes')):result=C.verify_cases(self.vector,self.plans,self.receipts,chart,review,report,deadline=time.monotonic()+30,chart_path='designated024')
        self.assertEqual(result['scalar_passes'],4);self.assertTrue(result['shared_budget']);self.assertEqual(len(result['necessary_formal_identity_constraints']),2);self.assertEqual(result['necessary_formal_identity_constraints'][1]['assignment'],[-2,5,-10]);self.assertEqual(result['affine_extension']['prior_chart_path'],'designated024');self.assertTrue(result['affine_extension']['complete'])
        self.assertGreater(result['audit_operations'],4*(1000*3**3+10000));self.assertLess(result['audit_operations'],200000000)
    def test_domain_bounds_baseline_and_full_rows_tampering(self):
        for values in ([1,2], [1,2,4097], [True,2,3]):
            with self.assertRaises(ValueError):C.validate_assignment(1,values)
        for field,value in [('assignment',[3,5,7]),('baseline',[1,0,0]),('column_values',['0']*1957),('target_exact_values',['0','0'])]:
            receipt=copy.deepcopy(self.receipts[1]);receipt[field]=value
            with self.assertRaises(ValueError):C.verify_probe(self.vector,self.plans[1],receipt,C.Budget(time.monotonic()+30))
    def test_sequential_all_pivots_leading_free_and_contradiction(self):
        b=C.Budget(time.monotonic()+30);basis={0:{0:F(1),2:F(1)},2:{2:F(1),5:F(2)}}
        record=C.reduce_row({1:F(1),2:F(3)},F(7),basis,0,b);self.assertEqual(record['chosen_pivot'],1);self.assertEqual(record['residual_terms'],[[1,'1'],[5,'-6'],[1224,'7']]);self.assertNotIn(2,basis[1])
        basis={0:{0:F(1)}};a=C.reduce_row({0:F(2)},F(3),basis,0,b);z=C.reduce_row({0:F(4)},F(6),basis,1,b)
        self.assertEqual(a['classification'],'inconsistent');self.assertEqual(z['classification'],'redundant');self.assertEqual(z['coefficient_rank'],1);self.assertEqual(z['augmented_rank'],2);self.assertIsNone(z['free_count'])
    def test_signed_storage_slacks_and_missing_appended_row(self):
        b=C.Budget(time.monotonic()+30);constraint=copy.deepcopy(self.receipts[0]['feedback_row']);C.project_constraint(constraint,b)
        constraint['entries'].append(dict(index=1957,coefficient='1'))
        with self.assertRaises(ValueError):C.project_constraint(constraint,b)
        chart,review,report=chart_inputs();chart['appended_row']=None
        with self.assertRaises(ValueError):C.parse_chart(chart,review,report,b)
    def test_shared_resource_failure_retains_consumed_counter_and_phase(self):
        chart,review,report=chart_inputs()
        with self.assertRaises(OverflowError)as caught:C.verify_cases(self.vector,self.plans,self.receipts,chart,review,report,deadline=time.monotonic()+30,max_operations=1000)
        self.assertTrue(hasattr(caught.exception,'independent_audit_counts'));self.assertLessEqual(caught.exception.independent_audit_counts['operations'],1000);self.assertIn('case',caught.exception.independent_phase)
    def test_one_cap_not_renewed_between_cases_and_bit_guard(self):
        b=C.Budget(time.monotonic()+30,600000);C.verify_probe(self.vector,self.plans[0],self.receipts[0],b)
        with self.assertRaises(OverflowError):C.verify_probe(self.vector,self.plans[1],self.receipts[1],b)
        with self.assertRaises(OverflowError):C.Budget(time.monotonic()+30).parse(str(1<<4096))

if __name__=='__main__':unittest.main()
