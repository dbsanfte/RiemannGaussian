import unittest
from fractions import Fraction as F
import exact_dual_support_reconstruction as D
import check_grouped_arithmetic as G
class TestDual(unittest.TestCase):
 def test_simple_separation(self):
  r=D.reconstruct_dual([{():F(1)}],{():F(-1)},[()],[0],[])
  self.assertTrue(r['certified']);self.assertEqual(r['weights'],['1']);self.assertEqual(r['lhs_dot_y'],'-1')
 def test_relation_and_slack_joint(self):
  inst=dict(target='mu',horizon=1,lhs=[dict(m=[1],c='-1')],square_groups=[],relation_groups=[[dict(spec=dict(kind='unit'),multiplier=[dict(m=[],c='1')])]])
  r=D.reconstruct_joint_separator([inst],allow_constant_slack=True)
  self.assertTrue(r['certified']);self.assertTrue(G.verify_joint_dual([inst],r,allow_constant_slack=True)['verified'])
 def test_feasible_no_separator(self):
  r=D.reconstruct_dual([{():F(1)}],{():F(1)},[()],[0],[])
  self.assertFalse(r['certified'])
 def test_missing_and_hostile(self):
  r=D.reconstruct_dual([{():F(1)}],{():F(-1)},[()],[0],[],max_work=1)
  self.assertEqual(r['status'],'missing_resource')
  r=D.reconstruct_dual([{():F(1)}],{():F(-1)},[],[0],[])
  self.assertFalse(r['certified'])
if __name__=='__main__':unittest.main()
