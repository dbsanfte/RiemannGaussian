import unittest
from copy import deepcopy
import check_arithmetic_cycle_certificate as c
class Tests(unittest.TestCase):
 def test_real_relation_certificate(self):
  p=[{'m':[1],'c':'1'}];cert=dict(target='mu',horizon=6,lhs=p,squares=[dict(weight='1',poly=[dict(m=[],c='1')])],relations=[dict(spec=dict(kind='unit'),multiplier=[dict(m=[],c='1')])])
  self.assertTrue(c.verify_certificate(cert)['verified'])
  bad=deepcopy(cert);bad['squares'][0]['weight']='-1'
  with self.assertRaises(ValueError):c.verify_certificate(bad)
 def test_strict_schema_actual_relations(self):
  for target,spec in [('c',dict(kind='inverse_row',n=2)),('mu',dict(kind='prime_power',p=4,e=1)),('mu',dict(kind='squarefree_zero',n=3)),('mu',dict(kind='coprime_product',a=2,b=4)),('mu',dict(kind='unit',extra=1))]:
   with self.assertRaises(ValueError):c.relation(spec,target,16)
  self.assertEqual(c.relation(dict(kind='prime_power',p=2,e=2),'c',4),{(4,):c.F(1),():c.F(-2)})
 def test_complete_defect_independent_evaluation(self):
  X=2;N=7;values=[0,1,-1,-1,0,-1,1,-1]
  poly=c.parse(c.complete_defect(X),N);v=sum(a*__import__('functools').reduce(lambda x,i:x*values[i],m,1) for m,a in poly.items())
  prefix=[sum(values[:n+1]) for n in range(N+1)];self.assertEqual(v,sum(prefix[n]**2 for n in range(4,8))-4*sum(prefix[n]**2 for n in range(2,4)))
 def test_canonical_rejection(self):
  for p in [[dict(m=[True],c='1')],[dict(m=[2,1],c='1')],[dict(m=[],c='2/2')],[dict(m=[],c='0')],[dict(m=[],c='1'),dict(m=[],c='2')]]:
   with self.assertRaises(ValueError):c.parse(p,4)
 def test_nontrivial_cycle_and_invalid_zero_multiplier(self):
  for target in ('mu','c'):
   cert=dict(target=target,horizon=6,lhs=[dict(m=[2,3,6],c='1')],squares=[dict(weight='1',poly=[dict(m=[6],c='1')])],relations=[dict(spec=dict(kind='coprime_product',a=2,b=3),multiplier=[dict(m=[6],c='1')])])
   self.assertTrue(c.verify_certificate(cert)['verified'])
   cert['relations'].append(dict(spec=dict(kind='prime_power',p=4,e=1),multiplier=[]))
   with self.assertRaises(ValueError):c.verify_certificate(cert)
   cert['relations'].pop();cert['horizon']=5
   with self.assertRaises(ValueError):c.verify_certificate(cert)
 def test_resource_distinct_and_public_target(self):
  with self.assertRaises(c.ResourceLimit):c.parse([dict(m=[1]*13,c='1')],4)
  with self.assertRaises(c.ResourceLimit):c.verify_certificate(dict(target='mu',horizon=10**100,lhs=[],squares=[],relations=[]))
  with self.assertRaises(ValueError):c.relation(dict(kind='unit'),'fake',2)
  with self.assertRaises(ValueError):c.relation(dict(kind='prime_power',p=10**100,e=10**100),'mu',4)
 def test_defect_omission_boundary_and_extra_horizon(self):
  # Empty certificate is rejected against independently complete target;
  # tests distinguish missing offdiagonal and last contributing boundary.
  expected=c.parse(c.complete_defect(1),3)
  for omitted in ((1,2),(3,3)):
   modified=dict(expected);modified.pop(omitted)
   lhs=c.canonical(c.add({},modified,c.F(-1)))
   cert=dict(target='mu',horizon=9,lhs=lhs,squares=[],relations=[])
   with self.assertRaises(ValueError):c.verify_defect_certificate(cert,1,'0')
  cert=dict(target='mu',horizon=2,lhs=[],squares=[],relations=[])
  with self.assertRaises(ValueError):c.verify_defect_certificate(cert,1,'0')
if __name__=='__main__':unittest.main()
