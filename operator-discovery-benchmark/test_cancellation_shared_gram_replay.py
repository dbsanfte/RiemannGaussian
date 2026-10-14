import unittest
from unittest.mock import patch
import cancellation_shared_gram_replay as R

class ReplayTests(unittest.TestCase):
 def test_default_budget_modest_increase(self):
  self.assertEqual(R.budget_check(1262,584)['work_proxy'],430412672)
  with self.assertRaises(OverflowError):R.budget_check(1262,598)
  with self.assertRaises(OverflowError):R.budget_check(1262,584,max_work=400000000)
 def test_budget_pure_no_native(self):
  with patch.object(R.N,'reconstruct_dual_fixed_support',side_effect=AssertionError('native must not run')):
   with self.assertRaises(OverflowError):R.budget_check(1262,598)
 def test_exact_constant_separator(self):
  i=[dict(target='mu',horizon=1,lhs=[dict(m=[1],c='-1')],square_groups=[],relation_groups=[])]
  b=[{'g':[[[dict(m=[],c='1')]]]}]
  # Rows: perinstance slack and Gram diagonal, both constant; y(mu_1)=1.
  result=R.replay(i,b,gram_specs={'g':1},saved_support=[1],time_limit=5)
  self.assertEqual(result['status'],'exact_separator',result)
  self.assertTrue(result['independent_full_Gram_check_passed'])
  self.assertFalse(result['refitted'])
  self.assertEqual(result['gram_duals']['g']['matrix'],[['0']])
 def test_bad_support_explicit(self):
  i=[dict(target='mu',horizon=1,lhs=[],square_groups=[],relation_groups=[])]
  r=R.replay(i,[{'g':[]}],gram_specs={'g':1},saved_support=[True])
  self.assertEqual(r['status'],'uncertified')
if __name__=='__main__':unittest.main()
