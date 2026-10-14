import unittest
from fractions import Fraction as F
import cancellation_gcd_inverse_projection as G
import grouped_arithmetic_language as L
from check_arithmetic_cycle_certificate import verify_certificate
class Tests(unittest.TestCase):
 def test_complete_asymmetric_kernel_and_complement(self):
  for H in (1,2,4):
   K=[[str(F(2*a-b,3))for b in range(1,H+1)]for a in range(1,H+1)]
   out=G.build_projection(H,K);self.assertEqual(out['source']['full_pair_count'],H*H);self.assertEqual(out['source']['full_pair_count'],out['source']['coprime_pair_count']+out['source']['noncoprime_pair_count']);self.assertEqual(L.load_poly(out['full_pair_polynomial']),L.add(L.load_poly(out['coprime_projection']),L.load_poly(out['noncoprime_complement'])));self.assertTrue(verify_certificate(out['certificate'])['finite_identity_verified'])
   self.assertFalse(out['source']['product_indices_used'])
 def test_signed_squares_not_PSD_proof(self):
  H=4;K=[['1']*H for _ in range(H)];out=G.build_projection(H,K,psd_kernel=True)
  self.assertTrue(out['kernel_PSD_decomposition']['PSD_verified']);self.assertFalse(out['signed_expression_is_PSD_certificate']);self.assertEqual(len(out['signed_square_expression']),H)
  # d=2 term has unknown signed coefficient x2, not a nonnegative rational weight.
  self.assertEqual(out['signed_square_expression'][1]['signed_weight_variable'],2)
 def test_reject_incomplete_and_wrong_arithmetic(self):
  with self.assertRaises(ValueError):G.build_projection(2,[['1']])
  with self.assertRaises(ValueError):G.build_projection(1,[['1']],target='c')
  with self.assertRaises(ValueError):G.build_projection(1,[['-1']],psd_kernel=True)
  with self.assertRaises(OverflowError):G.build_projection(3,[['1']*3 for _ in range(3)],max_operations=1)
if __name__=='__main__':unittest.main()
