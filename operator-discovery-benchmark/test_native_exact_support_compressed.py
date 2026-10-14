import unittest,time
from fractions import Fraction as F
from unittest.mock import patch
import native_exact_support_compressed as C

class CompressionTests(unittest.TestCase):
 def test_scalar_multiples_zero_rows_full_equality(self):
  columns=[{0:F(1),1:F(2),2:F(-3),3:F(0)}]
  lhs={0:F(4),1:F(8),2:F(-12),3:F(0)};d={}
  self.assertEqual(C.exact_support_solution(columns,lhs,[0],diagnostics=d),[F(4)])
  info=d['row_compression'];self.assertEqual(info['reduced_rows'],1)
  self.assertEqual(info['mapping'][2]['ratio'],'-3')
  self.assertEqual(info['mapping'][3]['representative'],None)
 def test_contradictory_rhs_never_merged(self):
  d={};self.assertIsNone(C.exact_support_solution([{0:F(1),1:F(2)}],{0:F(1),1:F(3)},[0],diagnostics=d))
  self.assertEqual(d['row_compression']['reduced_rows'],2)
 def test_zero_coefficient_nonzero_rhs(self):
  self.assertIsNone(C.exact_support_solution([{}],{0:F(1)},[0]))
 def test_full_original_mismatch_detected(self):
  with patch.object(C.N,'exact_support_solution',return_value=[F(5)]):
   with self.assertRaisesRegex(ValueError,'full original equality'):C.exact_support_solution([{0:F(1),1:F(2)}],{0:F(1),1:F(2)},[0])
 def test_bounds_before_native(self):
  with patch.object(C.N,'exact_support_solution',side_effect=AssertionError('native forbidden')):
   for kw in ({'max_work':1},{'max_preprocessing_operations':1},{'max_preprocessing_cells':1},{'max_coefficient_bits':1},{'deadline':time.monotonic()-1}):
    with self.assertRaises((OverflowError,TimeoutError)):C.exact_support_solution([{0:F(2)}],{0:F(2)},[0],**kw)
 def test_augmented_normalization_bits(self):
  with self.assertRaises(OverflowError):C.exact_support_solution([{0:F(1,7)}],{0:F(7)},[0],max_coefficient_bits=3)
 def test_saved_dual_support_exact(self):
  columns=[{0:F(1)},{0:F(-1)}];lhs={1:F(-1)}
  r=C.reconstruct_dual_fixed_support(columns,lhs,[0,1],[],[0,1],[1],time_limit=5)
  self.assertEqual(r['status'],'exact_separator',r)
  self.assertEqual(r['saved_support'],[1]);self.assertEqual(r['lhs_dot_y'],'-1')
  self.assertLessEqual(r['diagnostics']['row_compression']['total_work_proxy'],450000000)
 def test_budget_charge_beyond_native_proxy(self):
  d={}
  with self.assertRaises(OverflowError):C.exact_support_solution([{0:F(1),1:F(2)}],{0:F(1),1:F(2)},[0],max_work=20,diagnostics=d)
if __name__=='__main__':unittest.main()
