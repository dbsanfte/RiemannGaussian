from fractions import Fraction as F
import copy
import hashlib
import sys
import time
import unittest
from unittest.mock import patch
import primitive_state_direct_identity_probe as P

class DirectTests(unittest.TestCase):
    def budget(self,**kw):return P.Budget(time.monotonic()+120,**kw)
    def test_actual_tiny_full1957_columns_match_native_functional_oracle(self):
        import primitive_state_uniform_identity_probe as OLD
        vector=['0']*1957;deadline=time.monotonic()+120
        source=OLD.build_native_metered(P.PROGRAM,1,deadline=deadline,max_line_events=10000000)
        oracle=OLD.probe_native(source,vector,OLD.preflight(vector,P.PROGRAM,X=1,deadline=deadline),deadline=deadline)
        self.assertTrue(oracle['complete'],oracle.get('reason'));columns=[]
        columns.extend((F(s['exact_value']),F(s['exact_baseline']))for s in oracle['square_values'])
        for r in oracle['relation_values']:
            a,b=F(r['exact_value']),F(r['exact_baseline']);columns.extend([(a,b),(-a,-b)])
        columns.extend([(F(0),F(0))]*5)
        columns.extend((F(c['value']),F(c['baseline']))for g in oracle['gram_values']for c in g['exact_columns'])
        with patch.object(hashlib,'sha256',side_effect=AssertionError('no hashes')),patch.object(sys,'settrace',side_effect=AssertionError('no tracing')):direct=P.column_pairs(P.PROGRAM,1,self.budget())
        self.assertEqual(direct['columns'],columns);self.assertEqual(list(map(str,direct['target'])),oracle['target_exact_values'])
    def test_complete_probe_exact_row_and_modular_unverified_status(self):
        v=['0']*1957;p=P.preflight(v,P.PROGRAM,X=1)
        with patch.object(hashlib,'sha256',side_effect=AssertionError('no hashes')),patch.object(sys,'settrace',side_effect=AssertionError('no tracing')):r=P.probe(v,p,deadline=time.monotonic()+30)
        self.assertTrue(r['complete'],r.get('reason'));self.assertEqual(r['nonconstant_difference'],65284);self.assertEqual(r['feedback_row']['rhs'],'-253');self.assertEqual(len(r['column_values']),1957);self.assertEqual(len(r['column_baselines']),1957);self.assertFalse(r['identity_refuted']);self.assertEqual(r['status'],'UNVERIFIED_COUNTEREXAMPLE');self.assertEqual(r['counts']['operations'],218076)
    def test_zero_probe_never_universal_proof(self):
        v=['0']*1957;pairs=[(i,j)for i in range(15)for j in range(i,15)];v[1597+240+pairs.index((1,1))]='-1';p=P.preflight(v,P.PROGRAM,X=1);r=P.probe(v,p,deadline=time.monotonic()+30);self.assertTrue(r['complete']);self.assertEqual(r['status'],'NOT_REFUTED_BY_THIS_PROBE');self.assertEqual(r['nonconstant_difference'],0);self.assertFalse(r['universal_identity_proved'])
    def test_split_slack_and_original_storage_signs(self):
        d=P.column_pairs(P.PROGRAM,1,self.budget());columns=d['columns']
        for i in range(613):self.assertEqual(columns[367+2*i],tuple(-x for x in columns[366+2*i]))
        self.assertEqual(columns[1592:1597],[(F(0),F(0))]*5)
        for i in range(120):self.assertEqual(columns[1837+i],tuple(a-4*b for a,b in zip(columns[1597+i],columns[1717+i])))
        self.assertEqual(d['states']['full_child'][0][0],(F(1),F(1)));self.assertTrue(all(p[1]==-F(1,2)for p in d['states']['full_child'][0][6:]))
    def test_pair_homomorphism_and_exact_integer_cuts(self):
        b=self.budget();A=P.Algebra(b);x=(F(2,3),F(-5,7));y=(F(3,2),F(9,4));z=(F(4),F(0));self.assertEqual(A.mul(A.add(x,y),z),A.add(A.mul(x,z),A.mul(y,z)))
        self.assertEqual(P.floor_power(8,'2/3',b),4);self.assertEqual(P.floor_power(7,'2/3',b),3);self.assertEqual(P.ceil_root(3,2,b),2);self.assertEqual(P.factor_witness(4,b),((2,2),));self.assertEqual(P.factor_witness(6,b),((2,1),(3,1)))
    def test_resource_stop_no_partial_row_or_admission(self):
        v=['0']*1957;p=P.preflight(v,P.PROGRAM,X=1)
        for kwargs in [dict(max_operations=100),dict(max_cells=1),dict(max_receipt_bytes=4096)]:
            r=P.probe(v,p,deadline=time.monotonic()+30,**kwargs);self.assertFalse(r['complete']);self.assertIsNone(r['feedback_row']);self.assertIsNone(r['nonconstant_difference']);self.assertFalse(r['identity_refuted'])
    def test_denominator_preallocation_and_deadline(self):
        b=self.budget()
        for text in ['1/0','1/-2','01']:
            with self.assertRaises(ValueError):b.rational(text)
        with self.assertRaises(OverflowError):b.rational('9'*2000)
        with self.assertRaises(ValueError):P.Budget(float('nan'))
        v=['0']*1957;v[0]='1/65537';r=P.probe(v,P.preflight(v,P.PROGRAM,X=1),deadline=time.monotonic()+30);self.assertFalse(r['complete']);self.assertIn('denominator',r['reason'])
    def test_mathematical_input_mutation_rejected(self):
        v=['0']*1957;p=P.preflight(v,P.PROGRAM,X=1);p['candidate_vector'][1]='1';r=P.probe(v,p,deadline=time.monotonic()+30);self.assertFalse(r['complete']);self.assertIsNone(r['feedback_row'])

if __name__=='__main__':unittest.main()
