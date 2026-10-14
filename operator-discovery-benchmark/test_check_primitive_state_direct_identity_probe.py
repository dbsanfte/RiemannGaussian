"""Tiny independent native equivalence and direct arithmetic boundaries."""
import time
import copy
import primitive_state_direct_identity_probe as P
import unittest
from unittest.mock import patch
from fractions import Fraction as F
import check_primitive_state_direct_identity_probe as C
import check_primitive_state_uniform_identity_probe as N
import primitive_state_uniform_identity_probe as OLD

class DirectCheckerTests(unittest.TestCase):
    def test_tiny_complete_native_exact_row_equivalence_no_hash(self):
        import hashlib
        with patch.object(hashlib,'sha256',side_effect=AssertionError('no hash')):
            b=C.Budget(time.monotonic()+30);row,rhs,a,z=C.exact_row(1,b)
            native=N._construct_source(C.PROGRAM,1);v=['0']*1957;plan=OLD.preflight(v,C.PROGRAM,X=1)
            expected=N.exact_row(native,plan,N.verify_plan(plan,v,N.Budget()),N.Budget())
        self.assertEqual(row,expected['row']);self.assertEqual(rhs,expected['rhs']);self.assertEqual(len(a['squares']),366);self.assertEqual(len(a['relations']),613);self.assertEqual(len(a['grams']),3)
        self.assertEqual(row[1592:1597],[0]*5);self.assertEqual(row[366],-row[367]);self.assertEqual(rhs,-253)
    def test_inclusive_root_cuts_and_coefficient_caps(self):
        b=C.Budget(time.monotonic()+10)
        self.assertEqual(C.floor_root(8,'2/3',b),4);self.assertEqual(C.floor_root(7,'2/3',b),3);self.assertEqual(C.ceil_root(1,6,b),1);self.assertEqual(C.ceil_root(2,6,b),2)
        self.assertEqual(C.factor(12,b),{2:2,3:1})
        with self.assertRaises(OverflowError):b.parse(str(1<<4096))
        with self.assertRaises(ValueError):b.parse('2/4')
        with self.assertRaises(ValueError):C.Budget(float('nan'))
        with self.assertRaises(ValueError):C.Budget(time.monotonic()+1,True)
    def test_direct_complete_receipt_and_adversarial_mutations(self):
        v=['0']*1957;plan=P.preflight(v,C.PROGRAM,X=1);r=P.probe(v,plan,deadline=time.monotonic()+30)
        checked=C.verify_probe(v,plan,r);self.assertTrue(checked['complete_coefficient_row_verified']);self.assertFalse(checked['global_bound_proved'])
        for field in ('columns','row','states','target','counts','proof'):
            bad=copy.deepcopy(r)
            if field=='columns':bad['column_values'][1843]='1'
            elif field=='row':bad['feedback_row']['rhs']='0'
            elif field=='states':bad['regional_states']['full_parent'][0][0][1]='0'
            elif field=='target':bad['target_exact_values'][0]='0'
            elif field=='counts':bad['counts']['operations']=200000001
            else:bad['universal_identity_proved']=True
            with self.assertRaises(ValueError):C.verify_probe(v,plan,bad)
        with self.assertRaises(OverflowError):C.verify_probe(v,plan,r,max_operations=1)
        bad=list(v);bad[0]='1/65537';plan=P.preflight(bad,C.PROGRAM,X=1)
        with self.assertRaises(ValueError):C.verify_probe(bad,plan,r)
    def test_complete_allzero_pass_keeps_formal_constants(self):
        b=C.Budget(time.monotonic()+30);r=C.evaluate_pass(1,[0]*3,b)
        self.assertEqual(r['squares'][0],1);self.assertEqual(r['delta'],0)
        self.assertNotEqual(r['grams'][0][0],0)
        # unit state + negative half cell constants remain, u1 remains zero.
        self.assertEqual(r['relations'][0],-3)
    def test_shared_budget_deadline_and_domain_precharge(self):
        with self.assertRaises(OverflowError):C.exact_row(1,C.Budget(time.monotonic()+5,max_operations=1))
        with self.assertRaises(TimeoutError):C.exact_row(1,C.Budget(time.monotonic()-1))
        b=C.Budget(time.monotonic()+10);C.evaluate_pass(1,[0]*3,b);self.assertGreaterEqual(b.operations,37000)

if __name__=='__main__':unittest.main()
