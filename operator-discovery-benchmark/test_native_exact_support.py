import unittest,time
from fractions import Fraction as F
import native_exact_support as N
class Tests(unittest.TestCase):
 def test_exact_signed_free_and_inconsistent(self):
  cols=[{0:F(2),1:F(1)},{0:F(1),1:F(3)},{0:F(3),1:F(4)}]
  self.assertEqual(N.exact_support_solution(cols,{0:F(1),1:F(-2)},[0,1]),[F(1),F(-1)])
  self.assertEqual(N.exact_support_solution(cols,{0:F(1),1:F(-2)},[0,1,2]),[F(1),F(-1),F(0)])
  self.assertIsNone(N.exact_support_solution([{0:F(1)}],{1:F(1)},[0]))
 def test_fixed_dual_order_and_dots(self):
  # y0=0,y1=-1; support yminus1 index3. Column0 annihilated.
  r=N.reconstruct_dual_fixed_support([{0:F(1)}],{1:F(1)},[0,1],[],[0],[3])
  self.assertEqual(r['status'],'exact_separator');self.assertEqual(r['weights'],['0','-1']);self.assertEqual(r['columns_dot_y'],['0'])
  # Positive square pairing: y0=1; nonnegative slack variable2=1.
  r=N.reconstruct_dual_fixed_support([{0:F(1)}],{0:F(-1)},[0],[0],[],[0,2])
  self.assertEqual(r['status'],'exact_separator');self.assertEqual(r['weights'],['1']);self.assertEqual(r['columns_dot_y'],['1'])
 def test_caps_and_no_float(self):
  with self.assertRaises(ValueError):N.exact_support_solution([{0:1.0}],{},[0])
  with self.assertRaises(TimeoutError):N.exact_support_solution([],{},[],deadline=time.monotonic()-1)
  with self.assertRaises(OverflowError):N.exact_support_solution([{0:F(1)}],{0:F(1,3)},[0],max_denominator=2)
  with self.assertRaises(OverflowError):N.exact_support_solution([{0:F(1)}],{0:F(1)},[0],max_cells=1)
if __name__=='__main__':unittest.main()
