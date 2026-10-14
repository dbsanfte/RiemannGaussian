import unittest
from fractions import Fraction as F
import grouped_arithmetic_budget_reduction as R
import grouped_arithmetic_templates as T
import grouped_arithmetic_budget as B
import grouped_arithmetic_language as L
class Tests(unittest.TestCase):
 def test_universal_scalar_removal(self):
  d=T.descriptors();sw=['0']*52;rw=['0']*195;sw[0]='3/7'
  for i,s in enumerate(d['square']):
   if s['family']=='coordinate' and s['weight'] in ('one','X'):
    sw[i]='2/3'
    for j,r in enumerate(d['relation']):
     if r['family']=='norm' and r['multiplier']=='one' and r['region']==s['region'] and r['weight']==s['weight']:rw[j]='-1/3'
  original=dict(square_weights=sw,relation_weights=rw);reduced=R.reduce_weights(original)['weights']
  for target in ('mu','c'):
   for X in (1,2):
    b=T.build_instance(target,X,2,1);diff={}
    for a,c,group in zip(sw,reduced['square_weights'],b['instance']['square_groups']):
     for t in group:diff=L.add(diff,L.scale(L.mul(L.load_poly(t['poly']),L.load_poly(t['poly'])),(F(a)-F(c))*F(t['weight'])))
    for a,c,group in zip(rw,reduced['relation_weights'],b['instance']['relation_groups']):
     for t in group:diff=L.add(diff,L.scale(L.mul(L.load_poly(t['multiplier']),L.relation(t['spec'],target,4*X-1)),F(a)-F(c)))
    self.assertFalse(any(m for m in diff));self.assertGreaterEqual(diff.get((),0),0)
    self.assertEqual(F(B.extract_budget(b,original)['B'])-F(B.extract_budget(b,reduced)['B']),diff.get((),0))
 def test_shape(self):
  with self.assertRaises(ValueError):R.reduce_weights(dict(square_weights=[],relation_weights=[]))
if __name__=='__main__':unittest.main()
