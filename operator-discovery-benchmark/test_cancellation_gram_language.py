import unittest
import cancellation_gram_language as G
import arithmetic_cycle_language as L
class TestGram(unittest.TestCase):
 def test_singular_zero_pivots(self):
  d=G.ldlt_psd([[0,0,0],[0,1,1],[0,1,1]]);self.assertEqual(d['rank'],1);self.assertEqual(d['positive_pivots'],['1'])
  self.assertEqual(G.ldlt_psd([[0,0],[0,0]])['rank'],0)
 def test_negative_and_zero_remainder(self):
  for M in [[[0,1],[1,1]],[[1,2],[2,1]],[[-1,0],[0,1]]]:
   with self.assertRaises(ValueError):G.ldlt_psd(M)
 def test_complete_long_sos(self):
  M=[[1,'-2'],['-2',4]];atoms=[L.dump_poly(L.variable(2)),L.dump_poly(L.variable(3))]
  r=G.instantiate_sos(M,[atoms,atoms]);cert=dict(target='mu',horizon=3,lhs=r['polynomial'],squares=r['squares'],relations=[])
  self.assertTrue(L.compile_certificate(cert)['finite_identity_verified']);self.assertEqual(r['decomposition']['covectors'],[['1','-2']])
 def test_signed_pair_mapping(self):
  r=G.pair_square_coordinates([[1,-2],[-2,4]]);self.assertEqual(r['diagonal'],['3','6']);self.assertEqual(r['plus_pairs'][0]['coefficient'],'-2')
 def test_congruence(self):
  M=[[1,1],[1,1]];a=[L.dump_poly(L.variable(2)),L.dump_poly(L.variable(3))];b=[L.dump_poly(L.scale(L.variable(2),2)),L.dump_poly(L.scale(L.variable(3),-3))]
  N=G.diagonal_congruence(M,[2,-3]);self.assertEqual(G.gram_polynomial(M,a),G.gram_polynomial(N,b));self.assertTrue(G.ldlt_psd(N)['PSD_verified'])
 def test_hostile(self):
  with self.assertRaises(ValueError):G.ldlt_psd([[True]])
  with self.assertRaises(ValueError):G.ldlt_psd([['1e1000000000']])
  with self.assertRaises(OverflowError):G.ldlt_psd([['1'*10000]])
  with self.assertRaises(ValueError):G.ldlt_psd([[1,0],[1,1]])
  with self.assertRaises(ValueError):G.instantiate_sos([[1]],[[L.dump_poly(L.constant(1))]])
  with self.assertRaises(OverflowError):G.ldlt_psd([[1,1],[1,1]],max_operations=1)
if __name__=='__main__':unittest.main()
