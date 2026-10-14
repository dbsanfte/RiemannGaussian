"""Synthetic dual identities only; no licensed chart, endpoint or solver runs."""
from fractions import Fraction as F
import time
import unittest
import primitive_state_chart_dual_search as P
import check_primitive_state_chart_dual_search as C

def pb(**kw):return P.Budget(time.monotonic()+30,**kw)
def cb(**kw):return C.Budget(time.monotonic()+30,**kw)
class Soundness(unittest.TestCase):
    def test_reduction_eliminates_pivot_after_leading_free_and_rhs_sign(self):
        r,t,m=P.reduce_functional({2:{2:F(1),3:F(4),4:F(5)}},4,{0:F(2),2:F(3)},pb())
        self.assertEqual(r,{0:F(2),3:F(-12)});self.assertEqual(t,15);self.assertEqual(m,{2:F(3)})
    def test_generator_offdiagonal_and_storage_exact(self):
        v=['1','-1']+['0']*13
        ray=dict(index=0,kind='rank_one',block='C',vector=v,origin='toy')
        s=C.generator(ray,cb());self.assertEqual(s,{984:F(1),985:F(-2),999:F(1)})
        ray['block']='H';h=C.generator(ray,cb())
        self.assertEqual(h[984],4);self.assertEqual(h[985],-8)
        self.assertEqual(h[1104],1);self.assertEqual(h[1105],-2)
    def test_relation_coordinate_not_a_scalar_generator(self):
        with self.assertRaises(ValueError):C.generator(dict(index=0,kind='scalar',coordinate=366),cb())
    def test_full_identity_rejects_unannihilated_relation(self):
        with self.assertRaises(ValueError):C.check_identity([{0:F(1),1:F(1),2:F(-1)}],[{0:F(1)}],['1'],['1'],2,cb())
    def test_negative_alpha_and_wrong_pairing_rejected(self):
        for alpha,rhs in [('-1',F(-1)),('1',F(1))]:
            with self.assertRaises(ValueError):C.check_identity([{0:F(1),1:rhs}],[{0:F(1)}],[alpha],['1'],1,cb())
    def test_exact_support_solves_original_not_scaled_coordinates(self):
        alpha,stats=P.exact_support_solve([{0:F(1),2:F(-1)},{0:F(-1),2:F(-1)}],{2:F(-1)},2,[0,1],pb())
        self.assertEqual(alpha,[F(1,2),F(1,2)]);self.assertEqual(stats['rank'],2)
    def test_free_support_zero_can_reject_without_retry(self):
        # Feasible nonnegative a=0,b=1 exists, but the declared zero-free repair
        # deterministically returns a=-1 and must reject this one support.
        with self.assertRaises(ValueError):P.exact_support_solve([{2:F(1)},{2:F(-1)}],{2:F(-1)},2,[0,1],pb())
    def test_empty_support_does_not_erase_target(self):
        with self.assertRaises(ValueError):P.exact_support_solve([{2:F(1)}],{2:F(-1)},2,[],pb())
    def test_positive_row_and_column_scaling_identity(self):
        model=dict(free=[0],width=2,columns=[{0:F(2),2:F(-4)},{0:F(-1),2:F(-2)}],target={2:F(-1)})
        keys,cols,rhs,R,D=P.scaled_model(model,pb())
        alpha=[F(1,8),F(1,4)];native=[a/d for a,d in zip(alpha,D)]
        for i in keys:self.assertEqual(sum((col.get(i,F(0))*x for col,x in zip(cols,native)),F(0)),model['target'].get(i,F(0))/R[i])
    def test_native_reserve_is_explicit_proxy(self):
        r=P.native_work_reserve(443,851)
        self.assertEqual(r['total'],183764369);self.assertLess(r['total'],190000000)
        with self.assertRaises(ValueError):P.native_work_reserve(443,851,101)
    def test_native_preflight_failure_retains_consumed_counters(self):
        model=dict(free=[0],width=2,columns=[{0:F(2),2:F(-4)}],target={2:F(-1)})
        out=P.native_proposal(model,deadline=time.monotonic()+30,max_operations=1)
        self.assertFalse(out['success']);self.assertIsNone(out['scaled_vector'])
        self.assertIn('resource_failure',out);self.assertEqual(out['counts']['operations'],1)
    def test_exact_bit_cap_and_work_cap(self):
        with self.assertRaises(OverflowError):pb().q(F(1<<4096))
        with self.assertRaises(OverflowError):P.reduce_functional({0:{0:F(1),1:F(2),2:F(1)}},2,{0:F(1)},pb(max_operations=1))

if __name__=='__main__':unittest.main()
