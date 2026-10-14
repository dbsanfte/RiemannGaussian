from fractions import Fraction as F
import time
import unittest
import primitive_state_free_cone_search as P
from test_primitive_state_triangular_restoration import fixture as old_fixture


def fixture():
    cache,trace,basis,projection=old_fixture();parent=P.EXACT.restore(cache,trace,basis,projection,deadline=time.monotonic()+10)
    mapping,receipt=P.materialize(cache,basis,projection,parent,deadline=time.monotonic()+10)
    return mapping,receipt

class FreeSearchTests(unittest.TestCase):
    def budget(self,**kw):return P.EXACT.Budget(time.monotonic()+30,**kw)
    def test_fixed_precision_and_dyadic_bits_before_shifts(self):
        ctx=P.context();self.assertEqual(ctx.prec,269);self.assertEqual(P.record_fraction(P.mp_record(ctx.mpf(3)/2)),F(3,2))
        for record in ([0,'1',10**12],[0,'1',-10**12],[0,'2',-1],[0,'00',0],[1,'0',0]):
            with self.assertRaises((ValueError,OverflowError)):P.record_fraction(record)
        with self.assertRaises(ValueError):P.mp_record(ctx.inf)
        with self.assertRaises(OverflowError):P.mp_record(ctx.power(2,5000))
    def test_exact_tiny_forward_adjoint_dot_identity(self):
        ctx=P.context();mapping=dict(ctx=ctx,width=4,free=[1,3],pivots=[0,2],converted={0:{0:ctx.one,1:ctx.mpf(2),4:ctx.mpf(3)},2:{2:ctx.one,3:ctx.mpf(-1),4:ctx.one}})
        d=[ctx.mpf(2),ctx.mpf(3)];g=list(map(ctx.mpf,[5,7,11,13]));Nd,_=P.forward(mapping,d,self.budget(),linear=True);Ng=P.adjoint(mapping,g,self.budget())
        self.assertEqual(Nd,list(map(ctx.mpf,[-4,2,3,3])));self.assertEqual(Ng,list(map(ctx.mpf,[-3,24])));self.assertEqual(P.dot(ctx,Nd,g,self.budget()),P.dot(ctx,d,Ng,self.budget()))
    def test_initial_exact_conversion_and_actual_calibration(self):
        mapping,_=fixture();initial,x,check=P.calibrate(mapping,self.budget());self.assertTrue(check['passed']);self.assertEqual(F(check['initial_exact_reference_relative_error']),0)
        mapping['initial'][0]=F(1,3)
        with self.assertRaises(ValueError):P.calibrate(mapping,self.budget())
    def test_projection_orthogonality_and_finite_difference_gradient(self):
        mapping,_=fixture();ctx=mapping['ctx'];free=[P.to_mp(q,ctx,self.budget()) for q in mapping['initial']];x,_=P.forward(mapping,free,self.budget())
        c0=mapping['C_indices'][0];coff=mapping['C_indices'][1];p0=mapping['P_indices'][0];x[c0]=ctx.mpf(-1);x[coff]=ctx.mpf('0.2');x[p0]=ctx.mpf(1)
        merit,gradient,details=P.merit_gradient(mapping,x,self.budget());index=mapping['free'].index(coff);h=ctx.mpf('1e-6');before=list(x);after=list(x);before[coff]-=h;after[coff]+=h
        lo=P.merit_gradient(mapping,before,self.budget())[0];hi=P.merit_gradient(mapping,after,self.budget())[0];approx=(hi-lo)/(2*h)
        self.assertLess(abs(approx-gradient[index])/max(ctx.one,abs(gradient[index])),ctx.mpf('1e-6'))
        for record in details['native_negative_parts']:
            self.assertLess(abs(record['scaled_negative_positive_pairing']),1e-12);self.assertLess(record['scaled_eigen_backward_error'],1e-12);self.assertLess(record['eigenvector_orthogonality_error'],1e-12)
    def test_zero_merit_proposal_and_exact_endpoint(self):
        mapping,receipt=fixture();proposal=P.propose(mapping,deadline=time.monotonic()+30);self.assertTrue(proposal['complete']);self.assertEqual(proposal['stop_reason'],'zero_gradient');self.assertEqual(proposal['precision']['decimal_digits'],80)
        endpoint=P.exact_endpoint(mapping,proposal,deadline=time.monotonic()+30);self.assertEqual(endpoint['candidate_original_vector'][0],'2');self.assertTrue(endpoint['diagnostics']['candidate_cone_checks_pass']);self.assertEqual(endpoint['normalized_basis_hash'],receipt['normalized_basis_hash'])
    def test_fixed24_iteration_descent_order_and_finite_endpoint(self):
        cache,trace,_,_=old_fixture();cache['original']['columns'][1]=[[0,'2']];cache['original']['rhs']=['3'];trace['original_vector'][1]=2.
        import primitive_state_equation_projection as Q
        import primitive_state_exact_row_basis as B
        retained,recipes=Q.full15_recipes([366,613],1597,dict(cache['original']['specs']),1957)
        cols=[{(0,):F(1)},{(0,):F(2)}]+[{} for _ in range(1955)];rows,rhs,projection=Q.project_equations(cols,{(0,):F(3)},[(0,)],retained,recipes,deadline=time.monotonic()+10)
        _,_,basis=B.reduce_rows(rows,rhs,1224,deadline=time.monotonic()+10);parent=P.EXACT.restore(cache,trace,basis,projection,deadline=time.monotonic()+10)
        mapping,_=P.materialize(cache,basis,projection,parent,deadline=time.monotonic()+10);proposal=P.propose(mapping,deadline=time.monotonic()+30)
        self.assertTrue(proposal['complete']);self.assertEqual(len(proposal['power_trace']),8);self.assertEqual(proposal['stop_reason'],'iteration_limit');self.assertEqual(len(proposal['iterations']),24)
        merit=proposal['initial_merit']
        for iteration in proposal['iterations']:
            self.assertTrue(iteration['accepted']);self.assertLessEqual(len(iteration['trials']),3);trial=iteration['trials'][-1];self.assertTrue(trial['armijo_passed']);self.assertLess(P.record_fraction(trial['merit']),P.record_fraction(merit));merit=trial['merit']
        endpoint=P.exact_endpoint(mapping,proposal,deadline=time.monotonic()+30);self.assertEqual(endpoint['diagnostics']['equality_mismatch_count'],0);self.assertEqual(endpoint['diagnostics']['negative_scalar_count'],1)
    def test_nonfinite_native_conversion_no_retry(self):
        mapping,_=fixture();ctx=mapping['ctx'];x=[ctx.zero]*mapping['width'];x[mapping['C_indices'][0]]=ctx.mpf('1e500')
        with self.assertRaises(OverflowError):P.merit_gradient(mapping,x,self.budget())
    def test_budget_unknown_and_map_binding_failure(self):
        mapping,_=fixture();proposal=P.propose(mapping,deadline=time.monotonic()+30,max_operations=1);self.assertFalse(proposal['complete']);self.assertEqual(proposal['status'],'unknown')
        cache,trace,basis,projection=old_fixture();parent=P.EXACT.restore(cache,trace,basis,projection,deadline=time.monotonic()+10);parent['normalized_basis_hash']='bad'
        with self.assertRaises(ValueError):P.materialize(cache,basis,projection,parent,deadline=time.monotonic()+10)
