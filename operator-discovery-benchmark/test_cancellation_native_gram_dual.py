import unittest,time
from fractions import Fraction as F
import cancellation_native_gram_dual as D
import native_exact_support as N
class Tests(unittest.TestCase):
 def test_generic_separator(self):
  # Anonymous cone requires y(a)>=0 and y(b)=0, with y(lhs)=-1.
  cols=[{'a':F(1)},{'b':F(1)}];lhs={'a':F(-2),'b':F(3)};ms=['a','b']
  support,diag=D.support_proposal(cols,lhs,ms,[0],[1],deadline=time.monotonic()+10,max_rows=10,max_variables=20,max_work=1000)
  out=N.reconstruct_dual_fixed_support(cols,lhs,ms,[0],[1],support,time_limit=10)
  self.assertTrue(out['certified']);self.assertEqual(out['lhs_dot_y'],'-1');self.assertEqual(out['columns_dot_y'][1],'0')
  self.assertEqual(diag['threads'],1);self.assertFalse(diag['parallel'])
 def test_float_failure_is_not_refutation(self):
  support,diag=D.support_proposal([{'a':F(1)}],{'a':F(1)},['a'],[0],[],deadline=time.monotonic()+10,max_rows=10,max_variables=20,max_work=1000)
  self.assertIsNone(support)
 def test_limits(self):
  self.assertEqual(D.propose([],[],time_limit=float('nan'))['status'],'uncertified')
  with self.assertRaises(OverflowError):D.support_proposal([{'a':F(1)}],{'a':F(-1)},['a'],[0],[],deadline=time.monotonic()+10,max_rows=1,max_variables=20,max_work=100)
if __name__=='__main__':unittest.main()
