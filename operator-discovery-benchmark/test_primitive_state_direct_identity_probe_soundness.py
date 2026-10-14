"""Tiny direct grammar calibrations, never a saved candidate or X7 evaluation."""
from fractions import Fraction as F
import time
import unittest
import check_primitive_state_direct_identity_probe as C
import primitive_state_direct_identity_probe as P

def budget(**kw):return C.Budget(time.monotonic()+30,**kw)
class Soundness(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.a=C.evaluate_pass(1,[3,0,0],budget())
        cls.z=C.evaluate_pass(1,[0,0,0],budget())
    def test_full_group_coverage(self):
        self.assertEqual((len(self.a['squares']),len(self.a['relations'])),(366,613))
        self.assertEqual(list(map(len,self.a['grams'])),[120]*3)
    def test_formal_unit_norm_and_coprime_are_distinct(self):
        # Norm sum is (u1²-1)+(u2²-1)+(u3²-1), unit is u1-1.
        self.assertEqual(self.a['relations'][0],6)
        self.assertEqual(self.z['relations'][0],-3)
        self.assertEqual(self.a['relations'][192],2)
        self.assertEqual(self.z['relations'][192],-1)
        # First factor cell includes coprime(1,1): u1²-u1=6.
        self.assertEqual(self.a['relations'][231],72)
        self.assertEqual(self.a['relations'][232],36)
    def test_whole_product_baseline_and_cell_plus(self):
        self.assertEqual(self.a['squares'][312],16)
        self.assertEqual(self.z['squares'][312],F(1,4))
        self.assertEqual(self.a['relations'][331],8)
        self.assertEqual(self.z['relations'][331],-1)
        self.assertEqual(self.a['relations'][333],32)
        self.assertEqual(self.z['relations'][333],F(1,2))
        self.assertEqual(self.a['relations'][333]-self.z['relations'][333],F(63,2))
    def test_factor_closure_has_complete_scalar_cross_terms(self):
        self.assertEqual(self.a['squares'][106:108],[81,9])
        # R*(B+C)=(B-C)*(B+C), rather than separate squared defects.
        self.assertEqual(self.a['relations'][231],self.a['squares'][106]-self.a['squares'][107])
    def test_signed_storage_before_offdiagonal_export(self):
        self.assertEqual(self.a['grams'][0][1],6)
        self.assertEqual(self.a['grams'][1][1],3)
        self.assertEqual(self.a['grams'][2][1],-6)
    def test_exact_root_boundary(self):
        self.assertEqual(C.floor_root(8,'2/3',budget()),4)
        self.assertEqual(C.floor_root(7,'2/3',budget()),3)
        self.assertEqual(C.ceil_root(8,3,budget()),2)
        self.assertEqual(C.ceil_root(9,3,budget()),3)
    def test_primitive_norm_is_not_actual_sign_substitution(self):
        self.assertGreater(self.a['relations'][0],0)
        # Family unit, parent, atom unit: one parent row times (u1-1).
        self.assertEqual(self.a['relations'][403],2)
        self.assertEqual(self.z['relations'][403],-1)
    def test_paired_ring_preserves_constant_cross_terms(self):
        b=P.Budget(time.monotonic()+30);a=P.Algebra(b)
        unit=(F(2),F(-1));plus=(F(4),F(1));contrast=(F(4),F(-1,2))
        whole=a.mul(a.mul(unit,plus),contrast)
        self.assertEqual(whole,(F(32),F(1,2)))
        self.assertEqual(whole[0]-whole[1],F(63,2))
        self.assertNotEqual(whole[0]-whole[1],F(9)*F(9,2))
    def test_paired_product_operand_cap(self):
        b=P.Budget(time.monotonic()+30,max_bits=3);a=P.Algebra(b)
        with self.assertRaises(OverflowError):a.mul((F(8),F(0)),a.one)
    def test_work_deadline_and_bits_caps(self):
        with self.assertRaises(OverflowError):C.evaluate_pass(1,[3,0,0],budget(max_operations=1))
        with self.assertRaises(ValueError):C.Budget(float('nan'))
        with self.assertRaises(OverflowError):C.evaluate_pass(1,[3,0,0],budget(max_bits=1))
if __name__=='__main__':unittest.main()
