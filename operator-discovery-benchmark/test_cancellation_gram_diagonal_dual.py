import unittest
import cancellation_gram_diagonal_dual as D
class TestGramDual(unittest.TestCase):
 def test_toy_zero_atoms(self):
  inst=dict(target='mu',horizon=3,lhs=[dict(m=[],c='-1')],square_groups=[],relation_groups=[])
  # No ordinary blocks; full Gram is zero, constant slack gives yconst>=0.
  r=D.propose([inst],[1],allow_constant_slack=True)
  self.assertTrue(r['certified']);self.assertEqual(r['lhs_dot_y'],'-1')
  self.assertEqual(r['extra_cross_dots'],['0']*20)
  self.assertTrue(all(v['PSD_certificate']['rank']==0 for v in r['gram_duals'].values()))
 def test_feasible_zero(self):
  inst=dict(target='mu',horizon=1,lhs=[],square_groups=[],relation_groups=[])
  r=D.propose([inst],[],allow_constant_slack=True)
  self.assertFalse(r['certified'])
 def test_horizon_and_limits(self):
  inst=dict(target='mu',horizon=1,lhs=[],square_groups=[],relation_groups=[])
  r=D.propose([inst],[1]);self.assertFalse(r['certified'])
  r=D.propose([inst],[],max_work=1);self.assertFalse(r['certified'])
if __name__=='__main__':unittest.main()
