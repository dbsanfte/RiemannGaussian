import unittest
from fractions import Fraction as F
import grouped_arithmetic_language as L
import cancellation_arithmetic_synthesis as S
from check_grouped_arithmetic import verify_joint_result
class Tests(unittest.TestCase):
 def test_padding_cannot_improve(self):
  # Anonymous x1^2=1 relation, plus constant padding. The scalar target needs no structure.
  i=dict(target='mu',horizon=1,lhs=L.dump_poly(L.constant(7)),square_groups=[[dict(weight='1',poly=L.dump_poly(L.constant(1)))],[dict(weight='1',poly=L.dump_poly(L.variable(1)))]],relation_groups=[[dict(spec={'kind':'unit'},multiplier=L.dump_poly(L.add(L.variable(1),L.constant(1))))]])
  result=S.synthesize([i]);self.assertEqual(result['status'],'finite_certificate');self.assertEqual(result['weights'],dict(square_weights=['0','0'],relation_weights=['0']));self.assertEqual(result['constant_slacks'],['7']);self.assertEqual(result['diagnostics']['exact_structural_objective'],'0');self.assertTrue(verify_joint_result([i],result,allow_constant_slack=True)['verified'])
  # Adding alpha constant or coordinate/norm padding raises structural L1 by alpha or2alpha.
  costs=S.objective_costs(2,1,1);self.assertEqual(costs,[1,1,1,1,0]);self.assertGreater(F(costs[0]),0);self.assertGreater(F(costs[1]+costs[3]),0)
 def test_nonconstant_target_exact(self):
  p=L.add(L.variable(2),L.constant(1));i=dict(target='mu',horizon=2,lhs=L.dump_poly(L.add(L.scale(L.mul(p,p),F(3,7)),L.constant(4))),square_groups=[[dict(weight='1',poly=L.dump_poly(p))]],relation_groups=[])
  r=S.synthesize([i]);self.assertEqual(r['status'],'finite_certificate');self.assertEqual(r['weights']['square_weights'],['3/7']);self.assertEqual(r['constant_slacks'],['4']);self.assertTrue(verify_joint_result([i],r,allow_constant_slack=True)['verified'])
 def test_negative_control(self):
  i=dict(target='mu',horizon=1,lhs=L.dump_poly(L.constant(-1)),square_groups=[],relation_groups=[])
  self.assertEqual(S.synthesize([i])['status'],'no_certificate_found')
if __name__=='__main__':unittest.main()
