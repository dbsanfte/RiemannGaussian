from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import primitive_state_fresh_identity_probe as P
import primitive_state_direct_identity_probe as OLD

def deadline():return time.monotonic()+30

class CoreTests(unittest.TestCase):
    def test_tiny_legacy_formula_compatibility_complete_layout(self):
        a=OLD.column_pairs(OLD.PROGRAM,1,OLD.Budget(deadline()));b=P.column_pairs(P.PROGRAM,1,[3,5,7],P.Budget(deadline()))
        for key in('columns','target','states','raw_relations','factor_witnesses'):self.assertEqual(a[key],b[key])
        self.assertEqual(len(b['columns']),1957);self.assertEqual(len(b['raw_relations']),613)
    def test_alternate_assignment_preserved_products_before_baseline(self):
        d=P.column_pairs(P.PROGRAM,1,[-2,5,-10],P.Budget(deadline()));self.assertEqual(d['columns'][1],(F(129),F(0)));self.assertEqual(d['target'],(F(-10),F(32)))
        for j in range(613):self.assertEqual(d['columns'][367+2*j],tuple(-q for q in d['columns'][366+2*j]))
        for j in range(120):self.assertEqual(d['columns'][1837+j],tuple(a-4*b for a,b in zip(d['columns'][1597+j],d['columns'][1717+j])))
        # A nonzero constant baseline multiplied before subtracting differs
        # from multiplying differences; the evaluator always uses Q x Q.
        A=P.Algebra(P.Budget(deadline()));self.assertEqual(A.mul((F(-3),F(-1)),(F(4),F(2))),(F(-12),F(-2)))
        self.assertNotEqual(F(-12)-F(-2),(F(-3)+1)*(F(4)-2))
    def test_full_tiny_receipt_and_no_hashes(self):
        vector=['0']*1957;plan=P.preflight(vector,P.PROGRAM,X=1,assignment=[-2,5,-10],case_index=1)
        with patch('hashlib.sha256',side_effect=AssertionError('no hashes')):
            receipt=P.probe(vector,plan,deadline=deadline())
        self.assertTrue(receipt['complete'],receipt.get('reason'));self.assertEqual(receipt['case_index'],1);self.assertEqual(receipt['assignment'],[-2,5,-10]);self.assertEqual(receipt['baseline'],[0,0,0]);self.assertEqual(receipt['feedback_row']['assignment'],[-2,5,-10]);self.assertEqual(receipt['feedback_row']['rhs'],'-42');self.assertEqual(receipt['nonconstant_difference'],65537-42);self.assertFalse(receipt['identity_refuted'])
    def test_allzero_is_only_not_refuted_and_constant_baseline_kept(self):
        vector=['0']*1957;plan=P.preflight(vector,P.PROGRAM,X=1,assignment=[0,0,0]);receipt=P.probe(vector,plan,deadline=deadline())
        self.assertTrue(receipt['complete']);self.assertEqual(receipt['status'],'NOT_REFUTED_BY_THIS_PROBE');self.assertEqual(receipt['feedback_row']['entries'],[]);self.assertEqual(receipt['feedback_row']['rhs'],'0');self.assertFalse(receipt['universal_identity_proved']);self.assertEqual(receipt['column_values'],receipt['column_baselines'])
    def test_assignment_boundaries_roots_and_before_allocation_caps(self):
        self.assertEqual(P.validate_assignment(1,[-4096,0,4096]),[-4096,0,4096])
        for a in([True,0,1],[4097,0,1],[1,2]):
            with self.assertRaises(ValueError):P.preflight(['0']*1957,P.PROGRAM,X=1,assignment=a)
        b=P.Budget(deadline());self.assertEqual(P.factor_witness(35,b),((5,1),(7,1)));self.assertEqual(P.floor_power(32,'2/3',b),10);self.assertEqual(P.ceil_root(9,6,b),2)
        with self.assertRaises(ValueError):P.Budget(float('nan'))
        with self.assertRaises(ValueError):P.Budget(deadline(),max_operations=100000001)
        with self.assertRaises((OverflowError,ValueError)):P.Budget(deadline(),max_bits=8).rational('1/'+str(1<<100))
    def test_plan_mutation_or_resource_limit_discards_all_rows(self):
        vector=['0']*1957;plan=P.preflight(vector,P.PROGRAM,X=1,assignment=[3,5,7]);plan['H']=4;receipt=P.probe(vector,plan,deadline=deadline());self.assertFalse(receipt['complete']);self.assertIsNone(receipt['feedback_row'])
        plan=P.preflight(vector,P.PROGRAM,X=1,assignment=[3,5,7]);receipt=P.probe(vector,plan,deadline=deadline(),max_operations=100);self.assertFalse(receipt['complete']);self.assertIsNone(receipt['feedback_row']);self.assertLessEqual(receipt['counts']['operations'],100)

if __name__=='__main__':unittest.main()
