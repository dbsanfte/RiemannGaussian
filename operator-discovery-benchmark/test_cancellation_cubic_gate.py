import unittest
from fractions import Fraction as F
import cancellation_cubic_gate as C
import grouped_arithmetic_templates as T
import check_grouped_arithmetic as G
class TestGate(unittest.TestCase):
 def test_exact_basis_positions(self):
  ds=T.descriptors();b=C.build_constraint(ds);c=list(map(F,b['gamma_coefficients']))
  self.assertEqual(len(c),195);self.assertEqual(len(b['instance']['square_groups']),52)
  for d,q in zip(ds['relation'],c):
   expected=F({'all':'-56/3','head':'-12','tail':'-20/3'}[d['region']]) if d['family']=='norm' and d['weight']=='child_rowmass' and d['multiplier']=='one' else 0
   self.assertEqual(q,expected)
 def test_reject_both_signs_even_slack(self):
  ds=T.descriptors();i=next(i for i,d in enumerate(ds['relation']) if d['family']=='norm' and d['region']=='all' and d['weight']=='child_rowmass' and d['multiplier']=='one');inst=C.build_constraint(ds)['instance']
  for sign in [-1,1]:
   rw=['0']*195;rw[i]=str(sign)
   self.assertNotEqual(C.gamma(rw,ds),0)
   with self.assertRaises(ValueError):G.verify_joint([inst],['0']*52,rw,allow_constant_slack=True)
 def test_zero_gamma_permitted(self):
  ds=T.descriptors();rw=['0']*195
  for i,d in enumerate(ds['relation']):
   if d['family']=='norm' and d['weight']=='child_rowmass' and d['multiplier']=='one':rw[i]={'all':'9','head':'-14','tail':'0'}[d['region']]
  self.assertEqual(C.gamma(rw,ds),0)
  r=G.verify_joint([C.build_constraint(ds)['instance']],['0']*52,rw,allow_constant_slack=True)
  self.assertEqual(r['instances'][0]['constant_slack'],'0')
 def test_hostile_binding(self):
  ds=T.descriptors();ds['relation'][0]['id']='wrong'
  with self.assertRaises(ValueError):C.build_constraint(ds)
  with self.assertRaises(ValueError):C.gamma([True]*195,T.descriptors())
if __name__=='__main__':unittest.main()
