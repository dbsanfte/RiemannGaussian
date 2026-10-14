import unittest
from fractions import Fraction as F
import cancellation_cell_joint_gram_probe as J
class Probe(unittest.TestCase):
 def test_complete_blocks(self):
  for X in (1,2):
   b=J.blocks(X)
   for r in ['parent','child']:
    self.assertEqual(len(b[r]),X*(1 if r=='parent' else 2))
    self.assertTrue(all(len(a)==10 for a in b[r]))
    self.assertTrue(all(J.I.P.parse(p,4*X-1).get((),F(0))==-F(1,2) for a in b[r] for p in a[1:]))
 def test_exact_directions(self):
  for matrix in [[[0,1],[1,0]],[[1,2],[2,1]],[[1,1,0],[1,1,1],[0,1,2]]]:
   v=J.negative_direction(matrix)
   self.assertLess(sum(v[i]*matrix[i][j]*v[j] for i in range(len(v)) for j in range(len(v))),0)
  self.assertIsNone(J.negative_direction([[1,1],[1,1]]))
 def test_missing_domain_unknown(self):
  r=J.audit([1],[dict(horizon=3)],dict(monomials=[],weights=[]))
  self.assertTrue(all(v['status']=='unknown_missing_coordinates' for v in r['regions'].values()))
if __name__=='__main__':unittest.main()
