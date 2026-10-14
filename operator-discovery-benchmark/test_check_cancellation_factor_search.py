import unittest
from fractions import Fraction as F
import check_cancellation_factor_search as I
import check_grouped_arithmetic as G
class Tests(unittest.TestCase):
 def program(self):return dict(target='mu',q=6,C=32,claim='critical',constraint='zero_cubic',dictionary_mode='extended',allow_constant_slack=True)
 def test_full_dictionary_and_aux(self):
  d=I.descriptors();self.assertEqual(len(d['square']),282);self.assertEqual(len(d['relation']),319);a=I.auxiliary()['instance'];self.assertTrue(all(not s for s in a['square_groups']));self.assertTrue(all(not r for r in a['relation_groups'][231:]))
 def test_full_ordered_complement(self):
  b=I.build(self.program(),2)
  for a in b['factor_archive']:
   self.assertEqual(a['full_pair_count'],a['cells']['inside']['pair_count']+a['cells']['complement']['pair_count'])
  self.assertEqual(b['instance']['lhs'],I.I.build(self.program(),2)['instance']['lhs'])
 def test_closure_complete_mixed_terms(self):
  b=I.build(self.program(),2);lhs,sq,rel=G.columns(b['instance'])
  for j in range(44):
   difference=I.P.add(sq[106+4*j],sq[107+4*j],F(-1));self.assertEqual(difference,rel[231+2*j])
if __name__=='__main__':unittest.main()
