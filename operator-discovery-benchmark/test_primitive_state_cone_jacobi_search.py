"""Synthetic Jacobi calibrations only; no published research map replay."""
from fractions import Fraction as F
import copy
import time
import unittest
from unittest.mock import patch
import primitive_state_cone_jacobi_search as P
from test_primitive_state_triangular_restoration import fixture as old_fixture


def fixture():
    cache,trace,basis,projection=old_fixture();parent=P.EXACT.restore(cache,trace,basis,projection,deadline=time.monotonic()+30)
    oldmap,_=P.OLD.materialize(cache,basis,projection,parent,deadline=time.monotonic()+30)
    vector=parent['restored_projected_vector'];free=oldmap['free']
    seed=dict(schema='primitive-state-free-cone-endpoint-v1',complete=True,normalized_basis_hash=parent['normalized_basis_hash'],free_indices=free,final_free_vector=[vector[j] for j in free],final_projected_vector=vector,candidate_original_vector=parent['candidate_original_vector'],candidate_hash=parent['candidate_hash'])
    mapping,receipt=P.materialize(cache,basis,projection,parent,seed,deadline=time.monotonic()+30)
    return mapping,receipt,cache,basis,projection,parent,seed


def scaled_fixture():
    mapping,receipt,*rest=fixture();norms=P.cone_column_norms(mapping,deadline=time.monotonic()+30);P.install_scales(mapping,norms)
    return mapping,receipt,norms,rest

class JacobiTests(unittest.TestCase):
    def budget(self,**kwargs):return P.EXACT.Budget(time.monotonic()+30,**kwargs)
    def test_exact_exponent_boundary_and_zero(self):
        for g,k,d in [(F(0),0,F(1)),(F(1),0,F(1)),(F(1,4),-1,F(2)),(F(1,4)+F(1,2**20),0,F(1)),(F(4),1,F(1,2)),(F(5),2,F(1,4))]:
            self.assertEqual(P.dyadic_scale(g),(k,d))
            if g:self.assertLess(F(1,4),g*d*d);self.assertLessEqual(g*d*d,1)
        for cap in [0,-1,10**12,True,1.5]:
            with self.assertRaises(ValueError):P.dyadic_scale(F(1),exponent_abs_cap=cap)
        with self.assertRaises(OverflowError):P.dyadic_scale(F(1<<1801))
        with self.assertRaises(OverflowError):P.dyadic_scale(F(1,1<<1802))
    def test_homogeneous_rhs_ignored_and_operand_caps(self):
        mapping=dict(width=3,free=[1,2],pivots=[0],normalized={0:{0:F(1),1:F(2),3:F(999)}},scalar_indices=[0,1],gram_pairs=[],C_indices=[],P_indices=[])
        self.assertEqual(P.homogeneous_response(mapping,1,self.budget()),[F(-2),F(1),F(0)])
        mapping['normalized'][0][1]=F(1<<5000)
        with self.assertRaises(OverflowError):P.homogeneous_response(mapping,1,self.budget())
    def test_cone_norm_full_frobenius_and_response_temporary_caps(self):
        mapping=dict(scalar_indices=[0],gram_pairs=[(0,0),(0,1)],C_indices=[1,2],P_indices=[3,4])
        response=list(map(F,[3,2,5,7,11]));g,_=P.cone_norm(mapping,response,self.budget())
        self.assertEqual(g,F(9+4+225+2*25+2*961))
        response[0]=F(1<<5000)
        with self.assertRaises(OverflowError):P.cone_norm(mapping,response,self.budget())
    def test_scaled_forward_adjoint_identity(self):
        ctx=P.OLD.context();mapping=dict(ctx=ctx,width=4,free=[1,3],pivots=[0,2],converted={0:{0:ctx.one,1:ctx.mpf(2),4:ctx.mpf(3)},2:{2:ctx.one,3:ctx.mpf(-1),4:ctx.one}},center_mp=[ctx.mpf(5),ctx.mpf(7)],scale_mp=[ctx.mpf('0.5'),ctx.mpf(4)])
        d=list(map(ctx.mpf,[2,3]));g=list(map(ctx.mpf,[5,7,11,13]));Nd,_,_=P.scaled_forward(mapping,d,self.budget(),linear=True);Ng=P.scaled_adjoint(mapping,g,self.budget())
        self.assertEqual(Nd,list(map(ctx.mpf,[-2,1,12,12])));self.assertEqual(Ng,[ctx.mpf('-1.5'),ctx.mpf(96)]);self.assertEqual(P.OLD.dot(ctx,Nd,g,self.budget()),P.OLD.dot(ctx,d,Ng,self.budget()))
    def test_complete_norms_zero_columns_retained_and_seed_calibrated(self):
        mapping,_,norms,_=scaled_fixture();self.assertTrue(norms['complete']);self.assertEqual(len(norms['records']),len(mapping['free']));self.assertFalse(norms['column_norms_independently_verified']);self.assertFalse(norms['scaled_trace_bound_certified'])
        zeros=[r for r in norms['records'] if r['norm']=='0'];self.assertTrue(zeros);self.assertTrue(all(r['scale']=='1' for r in zeros));self.assertEqual(len(mapping['scales']),len(mapping['free']))
        z,x,calibration=P.calibrate(mapping,self.budget());self.assertTrue(calibration['passed']);self.assertTrue(all(v==0 for v in z));self.assertEqual([P.OLD.record_fraction(P.OLD.mp_record(v)) for v in x],mapping['parent_projected'])
    def test_norm_resource_unknown_has_complete_prefix_only(self):
        mapping,*_=fixture();receipt=P.cone_column_norms(mapping,deadline=time.monotonic()+30,max_operations=1)
        self.assertFalse(receipt['complete']);self.assertEqual(receipt['records'],[])
        with self.assertRaises(ValueError):P.install_scales(mapping,receipt)
    def test_exact_endpoint_sum_more_than269bits(self):
        mapping,_,_,_=scaled_fixture();j=mapping['free'][0];mapping['initial'][0]=F(1);mapping['scales'][0]=F(1,1<<300);ctx=mapping['ctx'];z=[ctx.zero]*len(mapping['free']);z[0]=ctx.one
        free=list(mapping['initial']);free[0]+=F(1,1<<300)
        proposal=dict(complete=True,status='proposed',seed_endpoint_hash=mapping['seed_endpoint_hash'],norm_records_hash=mapping['norm_records_hash'],final_z_mp=[P.OLD.mp_record(v) for v in z],final_free_vector=list(map(str,free)))
        endpoint=P.exact_endpoint(mapping,proposal,deadline=time.monotonic()+30);self.assertEqual(F(endpoint['final_free_vector'][0]),F(1)+F(1,1<<300));self.assertGreater(F(endpoint['final_free_vector'][0]).numerator.bit_length(),269)
        proposal['final_free_vector'][0]='1'
        with self.assertRaises(ValueError):P.exact_endpoint(mapping,proposal,deadline=time.monotonic()+30)
    def test_zero_gradient_proposal_and_endpoint(self):
        mapping,_,_,_=scaled_fixture();proposal=P.propose(mapping,deadline=time.monotonic()+30);self.assertTrue(proposal['complete'],proposal.get('reason'));self.assertEqual(proposal['stop_reason'],'zero_gradient');self.assertTrue(all(P.OLD.record_fraction(r)==0 for r in proposal['final_z_mp']))
        endpoint=P.exact_endpoint(mapping,proposal,deadline=time.monotonic()+30);self.assertEqual(endpoint['diagnostics']['equality_mismatch_count'],0);self.assertTrue(endpoint['diagnostics']['candidate_cone_checks_pass'])
    def test_pre_iteration_budget_stop_has_no_partial_trial(self):
        mapping,_,_,_=scaled_fixture();proposal=P.propose(mapping,deadline=time.monotonic()+30,max_operations=30000000)
        self.assertTrue(proposal['complete'],proposal.get('reason'));self.assertEqual(proposal['stop_reason'],'budget_stop');self.assertEqual(proposal['iterations'],[]);stop=proposal['budget_stop'];self.assertLess(stop['remaining_operations'],stop['worst_iteration_work_reserve']+stop['finalization_work_reserve'])
    def test_pre_iteration_trace_stop_has_bounded_complete_endpoint(self):
        mapping,_,_,_=scaled_fixture();proposal=P.propose(mapping,deadline=time.monotonic()+30,max_trace_bytes=1500000)
        self.assertTrue(proposal['complete'],proposal.get('reason'));self.assertEqual(proposal['stop_reason'],'budget_stop');self.assertEqual(proposal['budget_stop']['resource'],'trace_bytes');self.assertLessEqual(len(P.encoded(proposal)),1500000)
    def test_wrong_seed_no_fallback(self):
        _,_,cache,basis,projection,parent,seed=fixture();seed=copy.deepcopy(seed);seed['normalized_basis_hash']='wrong'
        with self.assertRaises(ValueError):P.materialize(cache,basis,projection,parent,seed,deadline=time.monotonic()+30)

if __name__=='__main__':unittest.main()
