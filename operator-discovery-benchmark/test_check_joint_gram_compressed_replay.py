import copy
import unittest
from fractions import Fraction as F
import check_joint_gram_compressed_replay as I
class Compression(unittest.TestCase):
 def test_signed_proportional_augmented_rows(self):
  columns=[{0:F(2),1:F(-4),2:F(3),3:F(0)}];lhs={0:F(6),1:F(-12),2:F(9),3:F(0)}
  c=I.canonical_compression(columns,lhs,[0]);self.assertEqual(c['compressed_rows'],1)
  self.assertEqual(c['row_mapping'][1]['ratio'],'-2');self.assertIsNone(c['row_mapping'][3]['representative'])
  self.assertTrue(I.verify_mapping(columns,lhs,[0],c)['verified']);self.assertTrue(I.verify_original_solution(columns,lhs,[0],['3'])['verified'])
 def test_rhs_breaks_proportionality(self):
  columns=[{0:F(1),1:F(2)}];lhs={0:F(3),1:F(7)}
  c=I.canonical_compression(columns,lhs,[0]);self.assertEqual(c['compressed_rows'],2)
  with self.assertRaises(ValueError):I.verify_original_solution(columns,lhs,[0],['3'])
 def test_inconsistent_zero_coefficient_row_retained(self):
  c=I.canonical_compression([{}],{1:F(1)},[0]);self.assertEqual(c['compressed_rows'],1)
  with self.assertRaises(ValueError):I.verify_original_solution([{}],{1:F(1)},[0],['0'])
 def test_producer_report_independently_rebuilt(self):
  import native_exact_support_compressed as B
  cols=[{0:F(2),1:F(-4),2:F(3),3:F(0)}];lhs={0:F(6),1:F(-12),2:F(9),3:F(0)};d={}
  answer=B.exact_support_solution(cols,lhs,[0],diagnostics=d)
  self.assertTrue(I.verify_producer_compression(cols,lhs,[0],d['row_compression'])['verified'])
  self.assertTrue(I.verify_original_solution(cols,lhs,[0],answer)['verified'])
  for key in ['preprocessing_work','verification_work_reserve','native_work_proxy','total_work_proxy']:
   bad=copy.deepcopy(d['row_compression']);bad[key]+=1
   with self.assertRaises(ValueError):I.verify_producer_compression(cols,lhs,[0],bad)
 def test_hash_mapping_support_tampering(self):
  cols=[{0:F(1),1:F(-1)}];lhs={0:F(2),1:F(-2)};c=I.canonical_compression(cols,lhs,[0])
  for key,value in [('support',[]),('augmented_rows_sha256','bad'),('compressed_rows',2)]:
   bad=copy.deepcopy(c);bad[key]=value
   with self.assertRaises(ValueError):I.verify_mapping(cols,lhs,[0],bad)
  bad=copy.deepcopy(c);bad['row_mapping'][1]['ratio']='1'
  with self.assertRaises(ValueError):I.verify_mapping(cols,lhs,[0],bad)
if __name__=='__main__':unittest.main()
