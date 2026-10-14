import unittest,copy
from fractions import Fraction as F
import cancellation_divisor_coupling as C
import grouped_arithmetic_language as L
class Tests(unittest.TestCase):
 def verify(self,out):
  for name in ('normalization_certificate','square_closure_certificate'):
   self.assertTrue(L.compile_certificate(out[name])['finite_identity_verified'])
 def test_mixed_complete(self):
  out=C.build_coupling(5,['2/3','-1/2','0','5/4','-2']);self.verify(out)
  self.assertIn([3,3],out['source']['pairs']);self.assertEqual(out['c'],'2/3')
  B=L.load_poly(out['B']);sq=L.load_poly(out['square_polynomial'])
  self.assertEqual(sq,L.mul(B,B));self.assertFalse(out['arithmetic_values_substituted'])
  # Two distinct divisor-source monomials produce their complete cross coefficient.
  self.assertEqual(sq[(1,1,1,2)],F(-2,3))
 def test_unit_endpoint(self):
  out=C.build_coupling(1,['-3/2']);self.verify(out)
  self.assertEqual(L.load_poly(out['B']),{(1,1):F(-3,2)})
  self.assertEqual(L.load_poly(out['normalization_certificate']['relations'][0]['multiplier']),{():F(-3,2),(1,):F(-3,2)})
 def test_zero_complete_and_tamper(self):
  out=C.build_coupling(4,['0']*4);self.verify(out)
  self.assertEqual(out['B'],[]);self.assertEqual(len(out['normalization_certificate']['relations']),4)
  bad=copy.deepcopy(C.build_coupling(2,['1','1'])['square_closure_certificate']);bad['relations'][0]['multiplier']=[]
  with self.assertRaises(ValueError):L.compile_certificate(bad)
 def test_resource_and_domain(self):
  with self.assertRaises(ValueError):C.build_coupling(2,['1'])
  with self.assertRaises(ValueError):C.build_coupling(1,['2/2'])
  with self.assertRaises(ValueError):C.build_coupling(1,['1'],target='c')
  with self.assertRaises(OverflowError):C.build_coupling(4,['1']*4,max_operations=10)
if __name__=='__main__':unittest.main()
