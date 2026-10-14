"""Synthetic balanced max-model and exact-centered endpoint calibrations."""
from fractions import Fraction as F
import copy
import time
import unittest
import primitive_state_balanced_cone_search as P
from test_primitive_state_triangular_restoration import fixture as old_fixture


def fixture():
    cache,trace,basis,projection=old_fixture();parent=P.EXACT.restore(cache,trace,basis,projection,deadline=time.monotonic()+30)
    oldmap,_=P.OLD.materialize(cache,basis,projection,parent,deadline=time.monotonic()+30);vector=parent['restored_projected_vector'];free=oldmap['free']
    base=dict(schema='primitive-state-free-cone-endpoint-v1',complete=True,normalized_basis_hash=parent['normalized_basis_hash'],free_indices=free,final_free_vector=[vector[j] for j in free],final_projected_vector=vector,candidate_original_vector=parent['candidate_original_vector'],candidate_hash=parent['candidate_hash'])
    records=[dict(index=k,free_index=j,norm='1',exponent=0,scale='1',response_max_bits=1,norm_max_bits=1) for k,j in enumerate(free)]
    norms=dict(schema='primitive-state-cone-jacobi-norms-v1',complete=True,status='scaled',normalized_basis_hash=parent['normalized_basis_hash'],seed_endpoint_hash=P.digest(base),scaling=P.J.SCALING,records=records,records_hash=P.digest(records),counts=dict(operations=1,peak_live_cells=1,fill_cells=0),**P.J.FLAGS)
    warm=dict(base,schema='primitive-state-cone-jacobi-endpoint-v1',seed_endpoint_hash=P.digest(base),norm_records_hash=norms['records_hash'])
    ctx=P.OLD.context();z=[[0,'0',0] for _ in free];proposal=dict(schema=P.J.SCHEMA,complete=True,status='proposed',normalized_basis_hash=parent['normalized_basis_hash'],seed_endpoint_hash=P.digest(base),norm_records_hash=norms['records_hash'],final_z_mp=z,final_free_vector=base['final_free_vector'])
    mapping,mapreceipt=P.materialize(cache,basis,projection,parent,base,warm,deadline=time.monotonic()+30)
    warmreceipt=P.warm_setup(mapping,norms,proposal,warm,deadline=time.monotonic()+30)
    return mapping,mapreceipt,warmreceipt,cache,basis,projection,parent,base,warm,norms,proposal

class BalancedTests(unittest.TestCase):
    def budget(self):return P.EXACT.Budget(time.monotonic()+30)
    def model(self,r,g,alpha=1):
        ctx=P.OLD.context();return P.simplex_model(ctx,list(map(ctx.mpf,r)),[list(map(ctx.mpf,v)) for v in g],ctx.mpf(F(alpha).numerator)/ctx.mpf(F(alpha).denominator),self.budget())
    def test_interior_model_exact_simplex_and_gap(self):
        d,n,m=self.model([1,1,1],[[1,0],[0,1],[-1,-1]])
        self.assertEqual(m['candidates'][m['selected_candidate']]['face'],[0,1,2]);weights=list(map(F,m['lambda_vector']));self.assertEqual(sum(weights),1);self.assertTrue(all(v>=0 for v in weights));self.assertTrue(m['model_consistent']);self.assertLessEqual(abs(P.OLD.record_fraction(m['model_gap'])),P.OLD.record_fraction(m['model_gap_tolerance']));self.assertFalse(P.FLAGS['model_optimality_certified'])
    def test_edge_vertex_and_singular_boundary_models(self):
        d,n,m=self.model([2,1,0],[[1],[-1],[0]])
        self.assertEqual(list(map(F,m['lambda_vector'])),[F(3,4),F(1,4),F(0)]);self.assertEqual(m['interior']['disposition'],'near_singular_numerical_boundary_only')
        d,n,m=self.model([1,-5,-10],[[1,0],[0,1],[0,0]],F(1,4));self.assertEqual(m['lambda_vector'],['1','0','0']);self.assertEqual(list(d),[P.OLD.context().mpf('-0.25'),0])
        d,n,m=self.model([1,1,1],[[0],[0],[0]]);self.assertEqual(n,0);self.assertEqual(m['selected_candidate'],0)
    def test_model_recomputed_for_halved_step(self):
        a=self.model([2,1,0],[[1],[-1],[0]],1)[2];b=self.model([2,1,0],[[1],[-1],[0]],F(1,2))[2]
        self.assertNotEqual(a['lambda_vector'],b['lambda_vector']);self.assertEqual(a['direction'],b['direction'])
    def test_bad_step_nonfinite_inputs_stop(self):
        ctx=P.OLD.context()
        with self.assertRaises(ValueError):P.simplex_model(ctx,[ctx.one]*3,[[ctx.one]]*3,ctx.zero,self.budget())
        with self.assertRaises(OverflowError):P.simplex_model(ctx,[ctx.inf]*3,[[ctx.one]]*3,ctx.one,self.budget())
    def test_warm_setup_no_new_columns_and_zero_increment(self):
        mapping,_,warm,*_=fixture();self.assertEqual(warm['new_column_responses'],0);self.assertTrue(warm['complete']);self.assertTrue(all(v==0 for v in mapping['warm_z']));self.assertFalse(warm['column_norms_independently_verified'])
        z,x,cal=P.calibrate(mapping,self.budget());self.assertTrue(cal['passed']);self.assertEqual(cal['reference'],'exact publication020 projected endpoint')
    def test_mismatched_warm_exact_sum_rejected(self):
        mapping,_,_,_,_,_,_,_,warm,norms,proposal=fixture();bad=copy.deepcopy(warm);bad['final_free_vector'][0]='17'
        with self.assertRaises(ValueError):P.warm_setup(mapping,norms,proposal,bad,deadline=time.monotonic()+30)
    def test_block_half_penalties_and_scaled_gradient(self):
        mapping,*_=fixture();ctx=mapping['ctx'];x=[ctx.zero]*mapping['width'];ci=mapping['C_indices'][0];pi=mapping['P_indices'][0];x[ci]=-ctx.one;x[pi]=ctx.mpf(5)
        penalties,grad,detail=P.block_metrics(mapping,x,self.budget(),[ctx.one,ctx.mpf(2),ctx.mpf(3)])
        self.assertEqual(penalties,[0,ctx.mpf('0.5'),0]);index=mapping['free'].index(ci);self.assertEqual(grad[1][index],ctx.mpf('-0.5'));self.assertEqual(grad[0][index],0);self.assertEqual(grad[2][index],0)
        h=ctx.mpf('1e-6');lo=list(x);hi=list(x);lo[ci]-=h;hi[ci]+=h
        p0=P.block_metrics(mapping,lo,self.budget(),apply_adjoint=False)[0][1]/2;p1=P.block_metrics(mapping,hi,self.budget(),apply_adjoint=False)[0][1]/2
        self.assertLess(abs((p1-p0)/(2*h)-grad[1][index]),ctx.mpf('1e-6'))
    def test_zero_initial_defect_exports_exact_endpoint(self):
        mapping,*_=fixture();proposal=P.propose(mapping,deadline=time.monotonic()+30);self.assertTrue(proposal['complete'],proposal.get('reason'));self.assertEqual(proposal['stop_reason'],'zero_initial_numerical_defect');self.assertEqual(proposal['power_trace'],[]);self.assertEqual(proposal['iterations'],[]);self.assertTrue(all(F(v)>0 for v in proposal['normalizers']))
        endpoint=P.exact_endpoint(mapping,proposal,deadline=time.monotonic()+30);self.assertEqual(endpoint['diagnostics']['equality_mismatch_count'],0);self.assertTrue(endpoint['diagnostics']['candidate_cone_checks_pass']);self.assertFalse(endpoint['model_optimality_certified'])
    def test_exact_endpoint_sum_not269bit_rerounded(self):
        mapping,*_=fixture();ctx=mapping['ctx'];mapping['initial'][0]=F(1);mapping['scales'][0]=F(1,1<<300);z=[ctx.zero]*len(mapping['free']);z[0]=ctx.one;free=list(mapping['initial']);free[0]+=F(1,1<<300)
        proposal=dict(complete=True,status='proposed',base_endpoint_hash=mapping['base_endpoint_hash'],warm_endpoint_hash=mapping['warm_endpoint_hash'],warm_proposal_hash=mapping['warm_proposal_hash'],norm_records_hash=mapping['norm_records_hash'],final_z_mp=[P.OLD.mp_record(v) for v in z],final_free_vector=list(map(str,free)))
        endpoint=P.exact_endpoint(mapping,proposal,deadline=time.monotonic()+30);self.assertGreater(F(endpoint['final_free_vector'][0]).numerator.bit_length(),269);self.assertEqual(F(endpoint['final_free_vector'][0]),F(1)+F(1,1<<300))
    def test_fixed_protocol_and_conservative_iteration_reserve(self):
        mapping,*_=fixture();self.assertEqual(P.SEARCH['gradient_iterations'],96);self.assertEqual(P.SEARCH['armijo_trials'],3);self.assertTrue(P.SEARCH['model_recomputed_each_trial']);self.assertGreater(P.iteration_work_reserve(mapping),3*2*96*15**3)
        self.assertEqual(F(P.MODEL['normalizer_floor']),F(1,1<<40));self.assertEqual(F(P.MODEL['interior_relative_determinant_tolerance']),F(1,1<<160))

if __name__=='__main__':unittest.main()
