import unittest
from fractions import Fraction as F
import check_cancellation_gram_run as R
import check_cancellation_gram as G
class Tests(unittest.TestCase):
 def test_atom_complete_domains(self):
  blocks=G.atom_blocks(2)
  self.assertEqual(len(blocks['parent']),2);self.assertEqual(len(blocks['child']),4)
  self.assertEqual(blocks['child'][-1][0],[dict(m=[n],c='1') for n in range(1,8)])
  self.assertEqual(blocks['child'][-1][4],[dict(m=[n],c='1') for n in [2,3,5,7]])
 def test_full_cross_coefficient(self):
  a=[['0']*5 for _ in range(5)];a[0][1]=a[1][0]='1'
  p=G.gram_polynomial(a,[[[dict(m=[1],c='1')],[dict(m=[2],c='1')],[],[],[]]],3)
  self.assertEqual(p,{(1,2):F(2)})
 def test_frozen_checker_dependencies(self):
  self.assertEqual(len(R.EXTRA),len(set(R.EXTRA)))
  self.assertIn('test_check_cancellation_gram',R.TESTS)
  self.assertIn('test_check_cancellation_gram_run.py',R.EXTRA)
if __name__=='__main__':unittest.main()
