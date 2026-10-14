from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import primitive_state_backtracking_cone_search as P
from test_primitive_state_feedback_cone_search import synthetic_inputs,nonzero_tiny_mapping

def warm_inputs():
    """Synthetic prior values only; no publication source/point access."""
    chart,center,norms,cache,row=synthetic_inputs();oldmap,oldreceipt=P.PREVIOUS.setup(chart,center,norms,deadline=time.monotonic()+30)
    ctx=oldmap['ctx'];z=[ctx.zero]*444;z[oldmap['free'].index(800)]=ctx.power(2,-700)
    free=[c+D*P.OLD.record_fraction(P.OLD.mp_record(v))for c,D,v in zip(oldmap['initial'],oldmap['scales'],z)]
    proposal=dict(schema=P.PREVIOUS.SCHEMA,status='proposed',complete=True,stop_reason='line_search_failed',free_indices=oldmap['free'],scale_vector=list(map(str,oldmap['scales'])),final_z_mp=[P.OLD.mp_record(v)for v in z],final_free_vector=list(map(str,free)),normalizers=['17','19','23'],iterations=[dict(index=0,accepted=False,trials=[dict(index=i,step=P.OLD.mp_record(ctx.mpf(8)/2**i),finite=True,armijo_passed=False)for i in range(3)])])
    endpoint=P.PREVIOUS.exact_endpoint(oldmap,proposal,cache,row,deadline=time.monotonic()+30)
    if not endpoint['complete']:raise AssertionError(endpoint)
    return chart,center,oldreceipt,proposal,endpoint,cache,row

def tiny_warm_mapping(*,step=1,normalizers=(17,19,23)):
    m=nonzero_tiny_mapping();ctx=m['ctx'];z=[ctx.zero]*2;x,_,_=P.centered_forward(m,z,P.Budget(time.monotonic()+30))
    m.update(warm_z=z,warm_forward_mp=x,warm_free=list(m['initial']),fixed_normalizers=list(map(F,normalizers)),initial_step=ctx.mpf(step),calibration=dict(passed=True,tolerance='1e-40'))
    return m

class CoreTests(unittest.TestCase):
    def test_warm_setup_exact_absolute_z_center_and_fixed_data_without_responses(self):
        args=warm_inputs()
        with patch('hashlib.sha256',side_effect=AssertionError('no hashing')),patch.object(P.PREVIOUS,'setup',side_effect=AssertionError('no norm setup')),patch.object(P.PREVIOUS,'selective_scales',side_effect=AssertionError('no norm responses')):
            mapping,receipt=P.setup(*args[:5],deadline=time.monotonic()+30)
        self.assertTrue(receipt['calibration']['passed']);self.assertEqual(receipt['warm_z_mp'],args[3]['final_z_mp']);self.assertEqual(receipt['normalizers'],['17','19','23']);self.assertEqual(receipt['scale_vector'],args[2]['scale_vector']);self.assertEqual(receipt['initial_step'],[0,'1',0]);self.assertEqual(receipt['source_failed_trial_step'],'2');self.assertEqual(mapping['parent_projected'],list(map(F,args[1]['candidate_projected_vector'])));self.assertEqual(receipt['warm_free_vector'],args[4]['final_free_vector']);self.assertFalse(receipt['candidate_admitted'])
    def test_warm_export_and_original_endpoint_mismatch_rejected(self):
        args=warm_inputs();args[4]['candidate_original_vector'][4]='1'
        with self.assertRaises(ValueError):P.setup(*args[:5],deadline=time.monotonic()+30)
        args=warm_inputs();args[3]['complete']=False
        with self.assertRaises(ValueError):P.setup(*args[:5],deadline=time.monotonic()+30)
    def test_twelve_trials_naturally_accept_beyond_three_no_power(self):
        proposal=P.propose(tiny_warm_mapping(step=128,normalizers=(1,1,1)),deadline=time.monotonic()+30,max_trace_bytes=500000)
        self.assertTrue(proposal['complete'],proposal.get('reason'));self.assertEqual(proposal['power_trace'],[]);self.assertEqual(proposal['search']['armijo_trials'],12)
        first=proposal['iterations'][0];self.assertTrue(first['accepted']);accepted=next(t for t in first['trials']if t.get('armijo_passed'));self.assertGreater(accepted['index'],2);self.assertEqual(P.OLD.record_fraction(first['next_start_step']),2*P.OLD.record_fraction(accepted['step']));self.assertTrue(all(P.OLD.record_fraction(t['step'])==F(128,1<<t['index'])for t in first['trials']))
    def test_proposal_preserves_prior_normalizers_and_budget_stop(self):
        mapping=tiny_warm_mapping();proposal=P.propose(mapping,deadline=time.monotonic()+30,max_trace_bytes=100000)
        self.assertTrue(proposal['complete'],proposal.get('reason'));self.assertEqual(proposal['normalizers'],['17','19','23']);self.assertEqual(proposal['initial_step'],[0,'1',0]);self.assertEqual(proposal['initial_z_mp'],[[0,'0',0],[0,'0',0]]);self.assertEqual(proposal['power_trace'],[]);self.assertEqual(proposal['stop_reason'],'budget_stop');self.assertEqual(proposal['budget_stop']['worst_iteration_work_reserve'],P.iteration_work_reserve(mapping));self.assertEqual(proposal['budget_stop']['worst_iteration_trace_bytes'],65536+48*96*2)
    def test_exact_endpoint_no_recenter_or_269bit_rounding(self):
        args=warm_inputs();mapping,_=P.setup(*args[:5],deadline=time.monotonic()+30);ctx=mapping['ctx'];z=list(mapping['warm_z']);i=mapping['free'].index(800);z[i]+=ctx.power(2,-600)
        free=[c+D*P.OLD.record_fraction(P.OLD.mp_record(v))for c,D,v in zip(mapping['initial'],mapping['scales'],z)];proposal=dict(schema=P.SCHEMA,complete=True,final_z_mp=[P.OLD.mp_record(v)for v in z],final_free_vector=list(map(str,free)))
        endpoint=P.exact_endpoint(mapping,proposal,args[5],args[6],deadline=time.monotonic()+30)
        self.assertTrue(endpoint['complete'],endpoint.get('reason'));self.assertEqual(F(endpoint['final_free_vector'][i]),F(1)+F(1,1<<500)+mapping['scales'][i]*(F(1,1<<700)+F(1,1<<600)));self.assertGreater(F(endpoint['final_free_vector'][i]).numerator.bit_length(),269);self.assertTrue(endpoint['diagnostics']['affine_equalities_satisfied']);self.assertFalse(endpoint['candidate_admitted'])
    def test_failed_step_cap_and_no_schema_shortcuts(self):
        b=P.Budget(time.monotonic()+30)
        with self.assertRaises(ValueError):P.failed_trial_step(dict(complete=True,schema=P.SCHEMA),b)
        with self.assertRaises(ValueError):P.positive_dyadic('3/2',b)
        with self.assertRaises(ValueError):P.Budget(float('nan'))
        with self.assertRaises(OverflowError):P.setup(*warm_inputs()[:5],deadline=time.monotonic()+30,max_operations=10)

if __name__=='__main__':unittest.main()
