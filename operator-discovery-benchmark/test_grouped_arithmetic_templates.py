import unittest
from fractions import Fraction as F
import grouped_arithmetic_templates as T
import grouped_arithmetic_language as L
class Tests(unittest.TestCase):
 def test_fixed_dictionary_and_empty_groups(self):
  d=T.descriptors();self.assertEqual(len(d['square']),52);self.assertEqual(len(d['relation']),195);self.assertEqual(len({r['id'] for r in d['square']}),52)
  a=T.build_instance('mu',1,2,1);b=T.build_instance('c',2,6,4)
  self.assertEqual(a['square_ids'],b['square_ids']);self.assertEqual(a['relation_ids'],b['relation_ids']);self.assertEqual(len(a['instance']['relation_groups']),195)
  for desc,group in zip(d['relation'],b['instance']['relation_groups']):
   if desc['family'] in ('squarefree_zero','inverse_row'):self.assertEqual(group,[])
 def test_full_critical_lhs(self):
  from arithmetic_cycle_language import complete_defect
  for X in [1,2,4]:
   t=T.build_instance('mu',X,2,1);expected=L.add(L.constant(F(t['D'])),L.scale(complete_defect(X),-1));self.assertEqual(L.load_poly(t['instance']['lhs']),expected)
 def test_uniform_unsigned_identity_in_dictionary(self):
  d=T.descriptors()
  for target in ['mu','c']:
   for X in [1,2,4]:
    t=T.build_instance(target,X,2,1,'unsigned_calibration');self.assertEqual(t['D'],t['unsigned_bound']);self.assertEqual(F(t['critical_budget']),X*X*T._ceilroot(X,2));instance=t['instance'];s=[];r=[]
    for desc,group in zip(d['square'],instance['square_groups']):
     weight=4 if desc==dict(family='prefix',region='parent',weight='one',id=desc['id']) else 1 if desc['family']=='pair' and desc['domain']=='all' and desc['sign']==-1 and desc['weight']=='child_kernel' else 0
     if weight:
      for term in group:s.append(dict(weight=str(F(term['weight'])*weight),poly=term['poly']))
    for desc,group in zip(d['relation'],instance['relation_groups']):
     if desc['family']=='norm' and desc['region']=='all' and desc['weight']=='child_rowmass' and desc['multiplier']=='one':
      for term in group:r.append(dict(spec=term['spec'],multiplier=L.dump_poly(L.scale(L.load_poly(term['multiplier']),-1))))
    cert=dict(target=target,horizon=instance['horizon'],lhs=instance['lhs'],squares=s,relations=r);self.assertTrue(L.compile_certificate(cert,max_operations=200000000)['finite_identity_verified'])
 def test_resources_and_domain(self):
  with self.assertRaises(OverflowError):T.build_instance('mu',33,2,1)
  with self.assertRaises(OverflowError):T.build_instance('mu',2,2,1,max_operations=1)
  with self.assertRaises(ValueError):T.build_instance('mu',True,2,1)
  with self.assertRaises(ValueError):T.build_instance('mu',1,2,1,'bad')
if __name__=='__main__':unittest.main()
