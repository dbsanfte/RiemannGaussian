from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
from types import SimpleNamespace
import primitive_state_chart_dual_search as P

def budget():return P.Budget(time.monotonic()+30)
def retained():return P.EXACT.full15_recipes([366,613],1597,{'full_child':15,'full_parent':15,'storage_K':15},1957)[0]

class DualTests(unittest.TestCase):
    def test_ascending_functional_sign_and_all_pivots(self):
        rows={2:{2:F(1),3:F(4),4:F(7)},0:{0:F(1),1:F(3),2:F(2),4:F(5)}}
        r,t,l=P.reduce_functional(rows,4,{0:F(1),1:F(9)},budget());self.assertEqual(r,{1:F(6),3:F(8)});self.assertEqual(t,F(-9));self.assertEqual(l,{0:F(1),2:F(-2)})
        x=P.EXACT.back_substitute(rows,[F(0),F(2),F(0),F(3)],4,budget());self.assertEqual(x[0]+9*x[1],t+sum(q*x[j]for j,q in r.items()))
    def test_shared_reverse_responses_match_ascending_elimination(self):
        rows={2:{2:F(1),3:F(4),4:F(7)},0:{0:F(1),1:F(3),2:F(2),4:F(5)}}
        cache,count=P.coordinate_responses(rows,4,[0,1,2,3],budget());self.assertEqual(count,4)
        for j in cache:
            r,t,_=P.reduce_functional(rows,4,{j:F(1)},budget());self.assertEqual(cache[j],(r,t))
    def test_native_resource_failure_and_observed_iteration_guard(self):
        model=dict(width=2,free=[0],columns=[{0:F(1),2:F(-1)},{0:F(-1),2:F(-1)}],target={2:F(-1)})
        failure=P.native_proposal(model,deadline=time.monotonic()+30,max_operations=1)
        self.assertFalse(failure['success']);self.assertFalse(failure['attempted']);self.assertIsNone(failure['scaled_vector']);self.assertEqual(failure['options']['maxiter'],100);self.assertEqual(failure['counts']['operations'],1)
        fake=SimpleNamespace(x=[.5,.5],success=True,status=0,message='synthetic',nit=101)
        with patch('scipy.optimize.linprog',return_value=fake):failure=P.native_proposal(model,deadline=time.monotonic()+30)
        self.assertFalse(failure['success']);self.assertEqual(failure['scaled_vector'],[.5,.5]);self.assertEqual(failure['iterations'],101);self.assertIn('iteration',failure['resource_failure']);self.assertTrue(failure['attempted'])
    def test_psd_ray_offdiagonal_and_H_transport(self):
        scalar,C,Q=P.geometry(retained());v=['0']*15;v[0]='2';v[1]='-3';ray=dict(kind='rank_one',block='H',vector=v);w=P.ray_functional(ray,scalar,C,Q,budget());self.assertEqual(w[C[0]],16);self.assertEqual(w[C[1]],-48);self.assertEqual(w[Q[1]],-12);self.assertEqual(w[Q[15]],9);self.assertFalse(set(w)&set(range(366,979)))
        with self.assertRaises(ValueError):P.ray_functional(dict(kind='scalar',coordinate=366),scalar,C,Q,budget())
    def test_exact_support_consistency_nonnegative_and_zero_free_rule(self):
        alpha,stats=P.exact_support_solve([{0:F(1),2:F(-1)},{0:F(-1),2:F(-1)}],{2:F(-1)},2,[0,1],budget());self.assertEqual(alpha,[F(1,2),F(1,2)]);self.assertEqual(stats['rank'],2)
        alpha,stats=P.exact_support_solve([{2:F(-1)},{2:F(-1)}],{2:F(-1)},2,[0,1],budget());self.assertEqual(alpha,[F(1),F(0)]);self.assertEqual(stats['free_support_coordinates'],[1])
        with self.assertRaises(ValueError):P.exact_support_solve([{2:F(1)}],{2:F(-1)},2,[0],budget())
        with self.assertRaises(ValueError):P.exact_support_solve([{0:F(1)}],{2:F(-1)},2,[0],budget())
    def test_exact_farkas_certificate_and_negative_weight_rejection(self):
        r=retained();rays=dict(schema=P.RAY_SCHEMA,records=[dict(index=0,kind='scalar',coordinate=0)]);rows={0:{0:F(1),1224:F(-1)}}
        with patch('hashlib.sha256',side_effect=AssertionError('no hashes')):cert=P.certify(rows,1224,list(range(1,1224)),r,rays,[F(1)],budget())
        self.assertEqual(cert['lambda_vector'],['1']);self.assertEqual(cert['pairing'],'-1');self.assertEqual(cert['combined_functional'][0],'1');self.assertFalse(cert['infeasibility_proved'])
        with self.assertRaises(ValueError):P.certify(rows,1224,list(range(1,1224)),r,rays,[F(-1)],budget())
    def test_exact_scaling_float_gates_and_native_proxy(self):
        model=dict(width=2,free=[0],columns=[{0:F(2),2:F(-4)},{0:F(-6),2:F(-2)}],target={2:F(-1)})
        keys,cols,b,R,D=P.scaled_model(model,budget());self.assertEqual(keys,[0,2]);self.assertEqual(R,{0:F(6),2:F(4)});self.assertEqual(D,[F(1),F(1)]);self.assertEqual(b,[F(0),F(-1,4)])
        self.assertLess(P.native_work_reserve(443,851)['total'],190000000)
        with self.assertRaises(OverflowError):P.finite_float(F(1,1<<2000))
        with self.assertRaises(OverflowError):P.finite_float(F(1<<2000))
    def test_tiny_native_calibration_single_call_and_support(self):
        model=dict(width=2,free=[0],columns=[{0:F(1),2:F(-1)},{0:F(-1),2:F(-1)}],target={2:F(-1)})
        with patch('hashlib.sha256',side_effect=AssertionError('no hashes')):native=P.native_proposal(model,deadline=time.monotonic()+30)
        self.assertTrue(native['success'],native['message']);self.assertEqual(native['options']['maxiter'],100);self.assertFalse(native['options']['presolve']);self.assertEqual(native['policy']['method'],'highs-ds');self.assertTrue(all(q>0 for q in native['scaled_vector']))
    def test_complete_rays_tiny_zero_endpoint_and_zero_beta(self):
        b=budget();r=retained();point=dict(complete=True,final_projected_vector=['0']*1224)
        with patch('hashlib.sha256',side_effect=AssertionError('no hashes')):rays=P.make_rays(r,point,b)
        self.assertEqual(len(rays['records']),851);self.assertEqual(sum(v.get('origin')=='endpoint_eigenvector'for v in rays['records']),30);self.assertEqual(rays['records'][0]['coordinate'],0);self.assertEqual(rays['records'][370]['coordinate'],983)
        self.assertTrue(all(not(set(P.ray_functional(v,*P.geometry(r),b))&set(range(366,979)))for v in rays['records']))
    def test_bounded_operations_bits_and_unknown(self):
        with self.assertRaises(ValueError):P.Budget(float('nan'))
        with self.assertRaises(OverflowError):P.reduce_functional({0:{0:F(1),1:F(3)}},2,{0:F(1)},P.Budget(time.monotonic()+30,1))
        out=P.search({}, {},deadline=time.monotonic()+30);self.assertEqual(out['status'],'UNKNOWN');self.assertIsNone(out['certificate'])
        with self.assertRaises(ValueError):P.exact_support_solve([],{},2,[0],budget())
        with self.assertRaises(OverflowError):budget().q(F(1<<4096))

if __name__=='__main__':unittest.main()
