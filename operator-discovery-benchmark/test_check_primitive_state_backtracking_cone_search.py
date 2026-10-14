import copy
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import check_primitive_state_backtracking_cone_search as C
import primitive_state_feedback_cone_search as OLD
import primitive_state_backtracking_cone_search as P
from test_primitive_state_feedback_cone_search import nonzero_tiny_mapping
from test_check_primitive_state_feedback_cone_search import licensed_inputs

def warm_inputs():
    cache,chart,center,row,norms,review024=licensed_inputs();mapping,map025=OLD.setup(chart,center,norms,deadline=time.monotonic()+30);ctx=mapping['ctx'];z=[ctx.zero]*444;z[mapping['free'].index(800)]=ctx.power(2,-700)
    finalfree=[q+D*OLD.OLD.record_fraction(OLD.OLD.mp_record(v))for q,D,v in zip(mapping['initial'],mapping['scales'],z)]
    steps=[ctx.mpf(1),ctx.one/2,ctx.one/4]
    proposal025=dict(schema=OLD.SCHEMA,status='proposed',complete=True,stop_reason='line_search_failed',free_indices=mapping['free'],initial_free_vector=list(map(str,mapping['initial'])),scale_vector=list(map(str,mapping['scales'])),final_z_mp=[OLD.OLD.mp_record(v)for v in z],final_free_vector=list(map(str,finalfree)),initial_block_penalties=[OLD.OLD.mp_record(ctx.mpf(i))for i in (1,2,3)],normalizers=['1','2','3'],iterations=[dict(accepted=False,trials=[dict(index=i,finite=True,armijo_passed=False,step=OLD.OLD.mp_record(a))for i,a in enumerate(steps)])],**OLD.FLAGS)
    endpoint025=OLD.exact_endpoint(mapping,proposal025,cache,row,deadline=time.monotonic()+30)
    check=dict(verified=True,complete=True,endpoint_verified=True,candidate_equations_verified=True,full_original_rows_checked=5641,feedback_row_verified=True)
    review025=dict(schema='primitive-state-feedback-cone-search-independent-review-v1',all_passed=True,status='ENDPOINT_CHECKED',endpoint_verified=True,candidate_equations_verified=True,independent_search_check=check)
    return cache,chart,center,row,review024,map025,proposal025,endpoint025,review025

class WarmLicenseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.inputs=warm_inputs()
    def test_new_setup_exact_endpoint_and_long_center_without_hashes(self):
        cache,chart,center,row,review024,map025,proposal025,endpoint025,review025=self.inputs
        with patch('hashlib.sha256',side_effect=AssertionError('no hashes')):
            mapping,mapreceipt=P.setup(chart,center,map025,proposal025,endpoint025,deadline=time.monotonic()+30)
            b=C.Budget(time.monotonic()+30);license=C.warm_license(*self.inputs,b);result=C.verify_setup(license,mapreceipt,b)
            z=mapping['warm_z'];free=[q+D*OLD.OLD.record_fraction(OLD.OLD.mp_record(v))for q,D,v in zip(mapping['initial'],mapping['scales'],z)]
            proposal=dict(schema=P.SCHEMA,complete=True,final_z_mp=[OLD.OLD.mp_record(v)for v in z],final_free_vector=list(map(str,free)))
            endpoint=P.exact_endpoint(mapping,proposal,cache,row,deadline=time.monotonic()+30);checked=C.verify_endpoint(license,proposal,endpoint,b)
        self.assertTrue(result['normalizers_unchanged']);self.assertEqual(result['new_norm_responses'],0);self.assertTrue(checked['endpoint_verified']);self.assertEqual(checked['full_original_rows_checked'],5641)
        bad=copy.deepcopy(mapreceipt);bad['warm_z_mp']=[[0,'0',0]]*444
        with self.assertRaises(ValueError):C.verify_setup(license,bad,b)
    def test_nonzero_history_no_power_fixed_normalizers_and_twelve_trial_budget(self):
        mapping=nonzero_tiny_mapping();ctx=mapping['ctx'];mapping['warm_z']=[ctx.one/16,-ctx.one/16];mapping['warm_projected']=[q for q in mapping['parent_projected']];mapping['warm_free']=[q+OLD.OLD.record_fraction(OLD.OLD.mp_record(v))for q,v in zip(mapping['initial'],mapping['warm_z'])];mapping['warm_forward_mp']=P.centered_forward(mapping,mapping['warm_z'],P.Budget(time.monotonic()+30))[0];mapping['fixed_normalizers']=[F(1),F(2),F(3)];mapping['initial_step']=ctx.one/8;mapping['calibration']=dict(passed=True,tolerance='1e-40',warm_exact_reference_relative_error='0',reference='exact publication025 projected endpoint')
        proposal=P.propose(mapping,deadline=time.monotonic()+30,max_trace_bytes=150000)
        self.assertTrue(proposal['complete'],proposal.get('reason'));self.assertEqual(proposal['power_trace'],[]);self.assertEqual(proposal['normalizers'],['1','2','3']);self.assertEqual(proposal['stop_reason'],'budget_stop')
        license=C.CACHED._License();license.free=mapping['free'];license.parent_vector=mapping['parent_projected'];license.scales=mapping['scales'];license.pivots=mapping['pivots'];license.source=dict(shape=[0,0],offset=1);license.summary=dict(sparse_map_entries=sum(map(len,mapping['normalized'].values())));license.initial_z=[OLD.OLD.record_fraction(OLD.OLD.mp_record(v))for v in mapping['warm_z']];license.initial_step=F(1,8);license.normalizers=mapping['fixed_normalizers'];license.warm_free=mapping['warm_free'];license.setup=dict(calibration=mapping['calibration'])
        checked=C.verify_proposal_trace(license,proposal,C.Budget(time.monotonic()+30),max_trace_bytes=150000);self.assertGreater(checked['accepted_iterations'],0)
        for field,value in [('initial_z_mp',[[0,'0',0]]*2),('normalizers',['1','1','1']),('power_trace',[{}])]:
            bad=copy.deepcopy(proposal);bad[field]=value
            with self.assertRaises(ValueError):C.verify_proposal_trace(license,bad,C.Budget(time.monotonic()+30),max_trace_bytes=150000)
    def test_exact_warm_seed_and_fixed_initial_step_without_hashes(self):
        with patch('hashlib.sha256',side_effect=AssertionError('no hashes')):license=C.warm_license(*self.inputs,C.Budget(time.monotonic()+30))
        self.assertEqual(license.initial_step,F(1,8));self.assertEqual(license.normalizers,[F(1),F(2),F(3)]);self.assertNotEqual(license.initial_z,[F(0)]*444);self.assertGreater(license.warm_free[20].denominator.bit_length(),269)
    def test_warm_zero_reset_endpoint_bias_and_renormalization_rejected(self):
        for index,key,value in [(6,'final_z_mp',[[0,'0',0]]*444),(7,'candidate_original_vector',['0']*1957),(6,'normalizers',['1','1','1'])]:
            inputs=copy.deepcopy(self.inputs);inputs[index][key]=value
            with self.assertRaises(ValueError):C.warm_license(*inputs,C.Budget(time.monotonic()+30))
    def test_inherited_scale_and_failed_step_provenance(self):
        inputs=copy.deepcopy(self.inputs);inputs[5]['scale_vector'][0]='3'
        with self.assertRaises(ValueError):C.warm_license(*inputs,C.Budget(time.monotonic()+30))
        inputs=copy.deepcopy(self.inputs);inputs[6]['iterations'][-1]['trials'][-1]['armijo_passed']=True
        with self.assertRaises(ValueError):C.warm_license(*inputs,C.Budget(time.monotonic()+30))

if __name__=='__main__':unittest.main()
