import unittest
from fractions import Fraction as F
import grouped_arithmetic_language as L
import cancellation_linear_span as S
class Tests(unittest.TestCase):
 def test_negative_square_membership_not_positivity(self):
  p=L.variable(2);i=dict(target='mu',horizon=2,lhs=L.dump_poly(L.scale(L.mul(p,p),-3)),square_groups=[[dict(weight='1',poly=L.dump_poly(p))]],relation_groups=[])
  r=S.analyze([i]);self.assertEqual(r['status'],'exact_span_member');self.assertEqual(r['exact_weights'],['-3','0']);self.assertFalse(r['positivity_certificate']);self.assertEqual(r['reconstructed_polynomials'],[i['lhs']])
 def test_exact_annihilator(self):
  i=dict(target='mu',horizon=2,lhs=L.dump_poly(L.variable(2)),square_groups=[[dict(weight='1',poly=L.dump_poly(L.variable(1)))]],relation_groups=[])
  r=S.analyze([i]);self.assertEqual(r['status'],'exact_span_obstruction');d=r['annihilator'];self.assertTrue(d['certified']);self.assertEqual(d['lhs_dot_y'],'-1');self.assertTrue(all(F(v)==0 for v in d['columns_dot_y']))
 def test_constants_signed_and_limits(self):
  i=dict(target='mu',horizon=1,lhs=L.dump_poly(L.constant(-7)),square_groups=[],relation_groups=[])
  self.assertEqual(S.analyze([i])['exact_weights'],['-7'])
  self.assertEqual(S.analyze([i],max_columns=0)['status'],'uncertified')
  self.assertEqual(S.analyze([i],max_horizon=1,max_monomials=1)['status'],'exact_span_member')
if __name__=='__main__':unittest.main()
