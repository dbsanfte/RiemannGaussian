import unittest,copy
import cancellation_gcd_inverse_projection as P
import check_cancellation_gcd_inverse_projection as C
class Tests(unittest.TestCase):
 def test_dense_zero_and_ab_outside(self):
  K=[['1','-2','0'],['3','0','1/2'],['0','-1','2']];r=P.build_projection(3,K);C.check_projection(3,K,r);self.assertEqual(r['source']['full_pair_count'],9)
  bad=copy.deepcopy(r);bad['certificate']['relations'].pop()
  with self.assertRaises(ValueError):C.check_projection(3,K,bad)
 def test_signed_PSD_inner(self):
  K=[['1','1'],['1','1']];r=P.build_projection(2,K,psd_kernel=True);C.check_projection(2,K,r)
  r['signed_expression_is_PSD_certificate']=True
  with self.assertRaises(ValueError):C.check_projection(2,K,r)
 def test_complement_and_cubic_tampering(self):
  K=[['1','0'],['0','1']];r=P.build_projection(2,K);r['signed_divisor_polynomial'].pop()
  with self.assertRaises(ValueError):C.check_projection(2,K,r)
if __name__=='__main__':unittest.main()
