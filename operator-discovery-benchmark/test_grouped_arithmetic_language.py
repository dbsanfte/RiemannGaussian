import unittest
import grouped_arithmetic_language as g
from arithmetic_cycle_controls import coefficients
class TestGrouped(unittest.TestCase):
 def test_complete_actual_relations(self):
  for target in ['mu','c']:
   vals=coefficients(64,target)['coefficients'];v={i:vals[i] for i in range(1,65)}
   for n in range(1,65):self.assertEqual(g.evaluate(g.relation(dict(kind='norm',n=n,factors=g.factor_witness(n)),target,64),v),0)
   for a in range(1,17):
    for b in range(1,17):
     s=dict(kind='gcd_product',a=a,b=b,factors_a=g.factor_witness(a),factors_b=g.factor_witness(b))
     self.assertEqual(g.evaluate(g.relation(s,target,64),v),0)
 def test_factor_hostility(self):
  for n,f in [(6,[[2,1]]),(6,[[3,1],[2,1]]),(4,[[4,1]]),(4,[[2,True]]),(4,[[2,1],[2,1]]),(1,[[2,1]])]:
   with self.subTest(n=n,f=f),self.assertRaises(ValueError):g.relation(dict(kind='norm',n=n,factors=f),'mu',16)
  with self.assertRaises(ValueError):g.relation(dict(kind='norm',n=4,factors=[[2,10**100]]),'mu',16)
 def test_certificate(self):
  spec=dict(kind='norm',n=4,factors=[[2,2]]);p=g.relation(spec,'mu',4)
  cert=dict(target='mu',horizon=4,lhs=g.dump_poly(p),squares=[],relations=[dict(spec=spec,multiplier=g.dump_poly(g.constant(1)))])
  self.assertTrue(g.compile_certificate(cert)['finite_identity_verified'])
  cert['lhs']=g.dump_poly(g.add(p,g.constant(1)))
  with self.assertRaises(ValueError):g.compile_certificate(cert)
 def test_whitelist_and_limits(self):
  self.assertEqual(g.relation(dict(kind='unit'),'mu',1),g.add(g.variable(1),g.constant(-1)))
  with self.assertRaises(ValueError):g.relation(dict(kind='norm',n=17,factors=[[17,1]]),'mu',16)
  with self.assertRaises(ValueError):g.relation(dict(kind='actual_value',n=3,value=-1),'mu',16)
  with self.assertRaises(OverflowError):g.factor_witness(65,max_n=64)
  with self.assertRaises(OverflowError):g.relation(dict(kind='norm',n=61,factors=[[61,1]]),'mu',64,max_operations=1)
if __name__=='__main__':unittest.main()
