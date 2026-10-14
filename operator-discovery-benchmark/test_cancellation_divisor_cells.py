import unittest,copy
from fractions import Fraction as F
import grouped_arithmetic_language as L
import cancellation_divisor_cells as C
class Tests(unittest.TestCase):
 def test_mixed_complete_closures(self):
  out=C.build_cells(6,['1','-1/2','0','2','-3','1/3'],{'kind':'divisor_le','coefficient':'1','power':'1/2'})
  self.assertEqual(out['cutoff'],2)
  full=out['source']['full']['pairs'];self.assertEqual(sorted(out['source']['inside_pairs']+out['source']['complement_pairs']),sorted(full))
  self.assertIn([3,3],out['source']['complement_pairs'])
  self.assertEqual(L.add(L.load_poly(out['inside']),L.load_poly(out['complement'])),L.load_poly(out['B']))
  certs=[out['normalization_certificate']]+[x['certificate']for x in out['closures']+out['square_transports']]
  for cert in certs:self.assertTrue(L.compile_certificate(cert)['finite_identity_verified'])
  self.assertTrue(all(x['formal_scalar']=='1/4'for x in out['coupled_squares']))
 def test_fractional_cut_inside_comparison(self):
  out=C.build_cells(8,['1']*8,{'kind':'divisor_le','coefficient':'1/2','power':'1/2'})
  self.assertEqual(out['cutoff'],1)
  for a,d in out['source']['inside_pairs']:self.assertLessEqual(d,1)
 def test_unit_and_tamper(self):
  out=C.build_cells(1,['-2'],{'kind':'divisor_le','coefficient':'0','power':'1'})
  self.assertEqual(out['inside'],[])
  bad=copy.deepcopy(out['square_transports'][0]['certificate']);bad['relations'][0]['multiplier']=[]
  with self.assertRaises(ValueError):L.compile_certificate(bad)
 def test_caps(self):
  with self.assertRaises(ValueError):C.build_cells(1,['1'],{'kind':'sign_oracle','coefficient':'1','power':'1'})
  with self.assertRaises(OverflowError):C.build_cells(8,['1']*8,{'kind':'divisor_le','coefficient':'1','power':'1'},max_operations=100)
if __name__=='__main__':unittest.main()
