"""Tiny formal assignments only; no recovered candidate or fresh-scale run."""
from fractions import Fraction as F
import time
import unittest
import primitive_state_fresh_identity_probe as P
import check_primitive_state_feedback_affine as A
import check_primitive_state_fresh_identity_probe as C

def b():return P.Budget(time.monotonic()+30)
class Soundness(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source=P.column_pairs(P.PROGRAM,1,[-2,5,-10],b())
    def test_explicit_alternate_assignment_and_constant_target(self):
        d=self.source
        self.assertEqual(d['columns'][1],(F(129),F(0)))
        self.assertEqual(d['target'],(F(-10),F(32)))
        self.assertEqual(d['target'][0]-d['target'][1],F(-42))
    def test_multiply_before_baseline_and_formal_u1(self):
        d=self.source
        self.assertEqual(d['raw_relations'][0],(F(126),F(-3)))
        self.assertEqual(d['raw_relations'][192],(F(-3),F(-1)))
        a=P.Algebra(b());v=(F(3),F(2));w=(F(5),F(4))
        p=a.mul(v,w);self.assertEqual(p[0]-p[1],7)
        self.assertNotEqual(p[0]-p[1],(v[0]-v[1])*(w[0]-w[1]))
    def test_complete_signed_storage_dependencies(self):
        c=self.source['columns'];self.assertEqual(len(c),1957)
        for j in range(613):self.assertEqual(c[367+2*j],tuple(-q for q in c[366+2*j]))
        for j in range(120):self.assertEqual(c[1837+j],tuple(a-4*d for a,d in zip(c[1597+j],c[1717+j])))
        self.assertEqual(c[1592:1597],[(F(0),F(0))]*5)
    def test_gram_offdiagonal_factor_two(self):
        d=self.source
        # Pair(0,1) follows(0,0); sum rows before multiplying by two.
        for k,name in enumerate(('full_child','full_parent')):
            expected=tuple(2*sum((s[0][a]*s[1][a]for s in d['states'][name]),F(0))for a in range(2))
            self.assertEqual(d['columns'][1598+120*k],expected)
    def test_assignment_validation_rejects_bool_and_missing_coordinate(self):
        for v in ([True,2,3],[1,2],[1,2,4097]):
            with self.assertRaises(ValueError):P.validate_assignment(1,v)
    def test_all_pivots_eliminated_past_leading_free(self):
        row={0:F(2),2:F(3)};chart={2:{2:F(1),3:F(4)}}
        kind,reduced,receipt=A.reduce_feedback([row.get(j,F(0))for j in range(4)],F(9),chart,A.Budget(time.monotonic()+30))
        self.assertEqual(kind,'independent');self.assertNotIn(2,reduced)
        self.assertEqual(reduced[0],1);self.assertEqual(reduced[3],-6)
    def test_independent_alternate_row_matches_all_coordinates(self):
        row,rhs,_,_=C.exact_row(1,[-2,5,-10],C.Budget(time.monotonic()+30))
        self.assertEqual(row,[a-z for a,z in self.source['columns']])
        self.assertEqual(rhs,-42)
    def test_noninvertible_denominator_is_not_retried(self):
        with self.assertRaises(ValueError):C.modular(F(1,65537),C.Budget(time.monotonic()+30))
    def test_sequential_new_row_detects_contradiction_not_new_coefficient(self):
        b=A.Budget(time.monotonic()+30);basis={0:{0:F(1),2:F(1)}}
        kind,row,_=A.reduce_feedback([F(0),F(1),F(1)],F(3),basis,b)
        self.assertEqual(kind,'independent');basis[1]=row
        kind,row,receipt=A.reduce_feedback([F(0),F(2),F(2)],F(7),basis,b)
        self.assertEqual(kind,'inconsistent');self.assertIsNone(row)
        self.assertEqual(receipt['residual_terms'],[[3,'1']])
        # Coefficient rank2, augmented rank3; a usable chart is impossible.
        kind,row,_=A.reduce_feedback([F(0),F(2),F(2)],F(6),basis,b)
        self.assertEqual(kind,'redundant');self.assertIsNone(row)
    def test_complete_receipt_keeps_alternate_assignment(self):
        vector=['0']*1957;values=[-2,5,-10]
        plan=P.preflight(vector,P.PROGRAM,X=1,assignment=values,case_index=1)
        receipt=P.probe(vector,plan,deadline=time.monotonic()+30)
        result=C.verify_probe(vector,plan,receipt,C.Budget(time.monotonic()+30))
        self.assertEqual(result['necessary_formal_identity_constraint']['assignment'],values)
        self.assertTrue(result['nonconstant_formal_identity_refuted'])
        self.assertFalse(result['universal_identity_proved'])
    def test_actual_rank_helper_preserves_inconsistency(self):
        b=C.Budget(time.monotonic()+30);basis={0:{0:F(1),1224:F(1)}}
        a=C.reduce_row({0:F(1)},F(2),basis,0,b)
        self.assertEqual(a['classification'],'inconsistent')
        self.assertEqual((a['coefficient_rank'],a['augmented_rank']),(1,2))
        self.assertIsNone(a['free_count'])
        a=C.reduce_row({1:F(2)},F(7),basis,1,b)
        self.assertEqual(a['classification'],'independent')
        self.assertEqual((a['coefficient_rank'],a['augmented_rank']),(2,3))
        self.assertIsNone(a['free_count'])
    def test_actual_projector_rejects_tampered_signed_and_storage(self):
        row=[a-z for a,z in self.source['columns']]
        for j in (367,1837):
            bad=list(row);bad[j]+=1
            constraint=C.feedback_row(bad,F(-42),1,[-2,5,-10])
            with self.assertRaises(ValueError):C.project_constraint(constraint,C.Budget(time.monotonic()+30))
    def test_no_shared_budget_reset(self):
        q=P.Budget(time.monotonic()+30,max_operations=20)
        q.charge(15)
        with self.assertRaises(OverflowError):q.charge(6)

if __name__=='__main__':unittest.main()
