import unittest,math
from fractions import Fraction as F
import cancellation_arithmetic_templates as T
import grouped_arithmetic_templates as B
import grouped_arithmetic_language as L
class Tests(unittest.TestCase):
 def test_full_original_preserved_and_stable(self):
  ids=None
  for target in ('mu','c'):
   for X in (1,2,3):
    base=B.build_instance(target,X,2,2);new=T.build_instance(target,X,2,2)
    self.assertEqual(new['instance']['lhs'],base['instance']['lhs']);self.assertEqual(new['instance']['square_groups'][:52],base['instance']['square_groups']);self.assertEqual(new['instance']['relation_groups'][:195],base['instance']['relation_groups'])
    self.assertEqual(len(new['square_ids']),106);self.assertEqual(len(new['relation_ids']),231)
    pair=(new['square_ids'],new['relation_ids'])
    if ids is None:ids=pair
    self.assertEqual(ids,pair)
 def test_atoms_and_complete_growing_prime_domain(self):
  b=T.build_instance('mu',2,3,8);d=T.descriptors()
  for desc,group in zip(d['square'][52:],b['instance']['square_groups'][52:]):
   if desc['contrast']!='growing_prime':continue
   ts=range(2,4) if desc['region']=='parent' else range(4,8)
   for t,term in zip(ts,group):
    expected={}
    for p in range(2,B._ceilroot(2,desc['root_order'])+1):
     if all(p%i for i in range(2,math.isqrt(p)+1)):
      for j in range(1,t//p+1):
       if math.gcd(j,p)==1:expected=L.add(expected,L.variable(j))
    self.assertEqual(L.load_poly(term['poly']),expected)
 def test_gcd_norm_closure_degree_and_coverage(self):
  b=T.build_instance('c',2,2,2);d=T.descriptors()
  for desc,group in zip(d['relation'][195:],b['instance']['relation_groups'][195:]):
   if desc['family']=='norm_core' and desc['region']=='all' and desc['weight']=='one':self.assertEqual(len(group),28)
   for term in group:self.assertTrue(all(len(v['m'])<=2 for v in term['multiplier']));L.relation(term['spec'],'c',7)
 def test_resource_caps(self):
  with self.assertRaises(OverflowError):T.build_instance('mu',21,2,2)
  with self.assertRaises(OverflowError):T.build_instance('mu',2,2,2,max_columns=10)
if __name__=='__main__':unittest.main()
