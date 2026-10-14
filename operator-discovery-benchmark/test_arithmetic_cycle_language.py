import unittest
from fractions import Fraction as F
import arithmetic_cycle_language as a
class TestCycle(unittest.TestCase):
 def test_polynomial_semantics(self):
  p=a.mul(a.add(a.variable(2),a.constant(1)),a.add(a.variable(3),a.constant(-1)))
  self.assertEqual(a.evaluate(p,{2:3,3:5}),16)
  self.assertEqual(a.load_poly(a.dump_poly(p)),p)
  self.assertEqual(a.add(p,a.scale(p,-1)),{})
 def test_cycle_certificate(self):
  x,y,z=a.variable(2),a.variable(3),a.variable(6)
  # xyz = z²+z*(xy-z).
  lhs=a.mul(a.mul(x,y),z)
  c=dict(target='mu',horizon=6,lhs=a.dump_poly(lhs),squares=[dict(weight='1',poly=a.dump_poly(z))],relations=[dict(spec=dict(kind='coprime_product',a=2,b=3),multiplier=a.dump_poly(z))])
  r=a.compile_certificate(c);self.assertTrue(r['finite_identity_verified']);self.assertFalse(r['RH_proved'])
  c['relations']=[]
  with self.assertRaises(ValueError):a.compile_certificate(c)
 def test_complete_defect(self):
  for X in [1,2,4]:
   N=4*X-1;values={n:F((-1)**n) for n in range(1,N+1)};prefix={n:sum(values[i] for i in range(1,n+1)) for n in range(1,N+1)}
   expected=sum(prefix[n]**2 for n in range(2*X,4*X))-4*sum(prefix[n]**2 for n in range(X,2*X))
   self.assertEqual(a.evaluate(a.complete_defect(X),values),expected)
 def test_relation_whitelist(self):
  self.assertEqual(a.relation(dict(kind='prime_power',p=2,e=3),'c',8),a.add(a.variable(8),a.constant(2)))
  self.assertEqual(a.relation(dict(kind='squarefree_zero',n=12),'mu',12),a.variable(12))
  cases=[(dict(kind='coprime_product',a=2,b=4),'mu',8),(dict(kind='coprime_product',a=2,b=3),'mu',5),(dict(kind='prime_power',p=4,e=1),'mu',8),(dict(kind='squarefree_zero',n=6),'mu',8),(dict(kind='inverse_row',n=4),'c',8),(dict(kind='unit',extra=1),'mu',8),(dict(kind='coefficient',n=3,value=-1),'mu',8)]
  for spec,t,H in cases:
   with self.subTest(spec=spec),self.assertRaises(ValueError):a.relation(spec,t,H)
 def test_hostile_serialization_and_signs(self):
  for data in [[dict(m=[True],c='1')],[dict(m=[3,2],c='1')],[dict(m=[2],c='2/2')],[dict(m=[],c='0')],[dict(m=[2],c='1'),dict(m=[2],c='1')]]:
   with self.assertRaises(ValueError):a.load_poly(data)
  with self.assertRaises(ValueError):a.variable(True)
  with self.assertRaises(ValueError):a.constant(0.5)
  cert=dict(target='mu',horizon=2,lhs=[],squares=[dict(weight='-1',poly=[])],relations=[])
  with self.assertRaises(ValueError):a.compile_certificate(cert)
 def test_domain_and_resources(self):
  d=a.cycle_domain(3,max_horizon=9);self.assertEqual(d['horizon'],9);self.assertEqual(len(d['specs']),7)
  self.assertEqual(len(a.cycle_domain(3,max_horizon=9,include_diagonal=False)['specs']),6)
  with self.assertRaises(OverflowError):a.cycle_domain(3,max_horizon=8)
  with self.assertRaises(OverflowError):a.complete_defect(8,max_operations=1)
  with self.assertRaises(OverflowError):a.mul(a.add(a.variable(1),a.variable(2)),a.add(a.variable(1),a.variable(2)),max_operations=1)
  with self.assertRaises(ValueError):a.relation(dict(kind='prime_power',p=2,e=10**100),'mu',128)
if __name__=='__main__':unittest.main()
