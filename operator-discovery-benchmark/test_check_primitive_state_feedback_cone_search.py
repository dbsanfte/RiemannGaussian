import copy
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import check_primitive_state_feedback_cone_search as C
import primitive_state_feedback_cone_search as P
from test_primitive_state_feedback_cone_search import synthetic_inputs,nonzero_tiny_mapping

def licensed_inputs():
    chart,center,norms,cache,row=synthetic_inputs()
    row.update(X=7,assignment=[2*n+1 for n in range(1,28)],layout=dict(n_variables=1957),zero_coordinates=[j for j in range(1957)if j not in {r['index']for r in row['entries']}])
    b=C.Budget(time.monotonic()+30);retained,recipes=C.AFFINE.projection_layout(cache['original']);_,pr,rhs=C.AFFINE.decode_feedback(row,retained,recipes,b)
    old={r['pivot']:{j:F(q)for j,q in r['terms']}for r in chart['normalized_rows']};_,_,reduction=C.AFFINE.reduce_feedback(pr,rhs,old,b)
    center.update(schema='primitive-state-feedback-affine-v1',status='complete',reduction=reduction,preserved_free_indices=chart['free_indices'])
    # Cover all5641 synthetic source rows, instead of leaving zero rows outside domain.
    columns=[dict((i,F(q))for i,q in col)for col in cache['original']['columns']]
    for i in range(779,5641):
        r=chart['normalized_rows'][i%779]
        for j,q in r['terms']:columns[retained[j]][i]=F(q)
    for omitted,recipe in recipes.items():
        columns[omitted]={}
        for j,q in recipe.items():
            for i,v in columns[j].items():columns[omitted][i]=columns[omitted].get(i,F(0))+q*v
    cache['original']['columns']=[[[i,str(q)]for i,q in sorted(col.items())if q]for col in columns]
    check=dict(verified=True,complete=True,all_original_rows_replayed=True,projection_dependencies_verified=True,feedback_reduction_verified=True,normalized_chart_verified=True,candidate_equations_verified=True,new_rank=780,new_free_count=444)
    review=dict(schema='primitive-state-feedback-affine-independent-review-v1',all_passed=True,status='AFFINE_UPDATED',chart_verified=True,candidate_equations_verified=True,independent_affine_check=check)
    return cache,chart,center,row,norms,review

class CheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inputs=licensed_inputs();cache,chart,center,row,norms,_=cls.inputs
        cls.mapping,cls.map=P.setup(chart,center,norms,deadline=time.monotonic()+30)
    def check(self,mapreceipt=None,proposal=None,endpoint=None):
        return C.verify_search(*self.inputs,mapreceipt or self.map,proposal,endpoint,deadline=time.monotonic()+30)
    def test_setup_exact_center_selective_support_and_no_hashes(self):
        with patch('hashlib.sha256',side_effect=AssertionError('no hashes')):r=self.check()
        self.assertTrue(r['setup_check']['verified']);self.assertFalse(r['column_norms_independently_verified']);self.assertTrue(r['chart_used_without_old_tape_replay'])
    def test_missing_appended_row_wrong_center_and_scale_rejected(self):
        for field in ('appended_row','pivot_columns'):
            inputs=copy.deepcopy(self.inputs);inputs[1][field]=None
            with self.assertRaises((ValueError,TypeError)):C.verify_search(*inputs,self.map,deadline=time.monotonic()+30)
        m=copy.deepcopy(self.map);m['scale_vector'][0]='2'
        with self.assertRaises(ValueError):self.check(m)
    def test_homogeneous_rhs_and_false_norm_claim_rejected(self):
        for key in ('column_norms_independently_verified','new_map_preconditioner_certified'):
            m=copy.deepcopy(self.map);m[key]=True
            with self.assertRaises(ValueError):self.check(m)
        m=copy.deepcopy(self.map);m['calibration']['homogeneous_exact_reference'][148]='1'
        with self.assertRaises(ValueError):self.check(m)
    def test_exact_endpoint_preserves_long_center_and_checks_all_rows(self):
        m=self.mapping;ctx=m['ctx'];z=[ctx.zero]*444;i=m['free'].index(800);z[i]=ctx.power(2,-700)
        free=[q+D*P.OLD.record_fraction(P.OLD.mp_record(v))for q,D,v in zip(m['initial'],m['scales'],z)]
        proposal=dict(schema=P.SCHEMA,complete=True,final_z_mp=[P.OLD.mp_record(v)for v in z],final_free_vector=list(map(str,free)))
        endpoint=P.exact_endpoint(m,proposal,self.inputs[0],self.inputs[3],deadline=time.monotonic()+30)
        b=C.Budget(time.monotonic()+30);license=C.validate_chart(self.inputs[0],self.inputs[1],self.inputs[2],self.inputs[3],self.inputs[5],b);C.verify_setup(license,self.inputs[4],self.map,b)
        r=C.verify_endpoint(license,proposal,endpoint,b);self.assertTrue(r['endpoint_verified']);self.assertEqual(r['full_original_rows_checked'],5641);self.assertGreater(F(endpoint['final_free_vector'][i]).numerator.bit_length(),269)
        bad=copy.deepcopy(endpoint);bad['candidate_original_vector'][0]='1'
        with self.assertRaises(ValueError):C.verify_endpoint(license,proposal,bad,b)
    def test_bounded_nonzero_history_and_step_carry_tamper(self):
        mapping=nonzero_tiny_mapping();mapping['calibration']['center_exact_reference_relative_error']='0';proposal=P.propose(mapping,deadline=time.monotonic()+30,max_trace_bytes=100000)
        license=C._License();license.free=mapping['free'];license.parent_vector=mapping['parent_projected'];license.scales=mapping['scales'];license.pivots=mapping['pivots'];license.source=dict(shape=[0,0],offset=1);license.summary=dict(sparse_map_entries=sum(map(len,mapping['normalized'].values())));license.initial_z=[F(0)]*2;license.setup=dict(calibration=mapping['calibration'])
        proposal['calibration']['center_exact_reference_relative_error']='0';license.setup['calibration']=proposal['calibration']
        r=C.verify_proposal_trace(license,proposal,C.Budget(time.monotonic()+30),max_trace_bytes=100000);self.assertGreater(r['accepted_iterations'],0)
        bad=copy.deepcopy(proposal);bad['iterations'][0]['next_start_step']=P.OLD.mp_record(mapping['ctx'].one)
        with self.assertRaises(ValueError):C.verify_proposal_trace(license,bad,C.Budget(time.monotonic()+30),max_trace_bytes=100000)

if __name__=='__main__':unittest.main()
