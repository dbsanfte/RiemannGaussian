import unittest
import check_grouped_arithmetic as c
class Tests(unittest.TestCase):
 def test_norm_and_gcd_actual(self):
  for target in ('mu','c'):
   for a in range(1,13):
    for b in range(1,13):
     H=12;fa=[[p,e] for p,e in c.P.factor(a).items()];fb=[[p,e] for p,e in c.P.factor(b).items()];r=c.relation(dict(kind='gcd_product',a=a,b=b,factors_a=fa,factors_b=fb),target,H)
     def f(n):
      fac=c.P.factor(n)
      return (0 if any(e>1 for e in fac.values()) else (-1)**len(fac)) if target=='mu' else 2**len(fac)*(-1)**sum(fac.values())
     v=sum(q*__import__('functools').reduce(lambda z,n:z*f(n),m,1) for m,q in r.items());self.assertEqual(v,0)
  with self.assertRaises(ValueError):c.witness(6,[[2,1]],12)
 def test_joint_fixed_weight_transfer(self):
  p=[dict(m=[2],c='1')];i=dict(target='mu',horizon=2,lhs=[dict(m=[2,2],c='1')],square_groups=[[dict(weight='1',poly=p)]],relation_groups=[[]])
  self.assertTrue(c.verify_joint([i,i],['1'],['0'])['verified'])
  with self.assertRaises(ValueError):c.verify_joint([i],['2'],['0'])
 def test_joint_dual_domain(self):
  i=dict(target='mu',horizon=1,lhs=[dict(m=[],c='-1')],square_groups=[[dict(weight='1',poly=[dict(m=[],c='1')])]],relation_groups=[])
  d=dict(status='exact_separator',certified=True,monomials=[dict(instance=0,m=[])],weights=['1'],columns_dot_y=['1'],lhs_dot_y='-1');self.assertTrue(c.verify_joint_dual([i],d)['verified']);d['monomials']=[]
  with self.assertRaises(ValueError):c.verify_joint_dual([i],d)
 def test_constant_slack_certificate_and_dual_constraints(self):
  i=dict(target='mu',horizon=1,lhs=[dict(m=[],c='2'),dict(m=[1,1],c='1')],square_groups=[[dict(weight='1',poly=[dict(m=[1],c='1')])]],relation_groups=[[]])
  cert=dict(target='mu',horizon=1,lhs=i['lhs'],squares=[dict(weight='1',poly=[dict(m=[1],c='1')]),dict(weight='2',poly=[dict(m=[],c='1')])],relations=[])
  r=dict(status='finite_certificate',weights=dict(square_weights=['1'],relation_weights=['0']),constant_slacks=['2'],certificates=[cert]);self.assertTrue(c.verify_joint_result([i],r,allow_constant_slack=True)['verified']);r['constant_slacks']=['3']
  with self.assertRaises(ValueError):c.verify_joint_result([i],r,allow_constant_slack=True)
  a=dict(target='mu',horizon=1,lhs=[dict(m=[],c='-1')],square_groups=[],relation_groups=[]);d=dict(status='exact_separator',certified=True,monomials=[dict(instance=0,m=[])],weights=['1'],columns_dot_y=['1'],lhs_dot_y='-1');self.assertTrue(c.verify_joint_dual([a],d,allow_constant_slack=True)['verified']);d['weights']=['-1']
  with self.assertRaises(ValueError):c.verify_joint_dual([a],d,allow_constant_slack=True)
if __name__=='__main__':unittest.main()
