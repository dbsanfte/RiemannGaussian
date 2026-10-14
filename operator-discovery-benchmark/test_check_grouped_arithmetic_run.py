import unittest
import check_grouped_arithmetic_run as c
class Tests(unittest.TestCase):
 def test_descriptor_and_generator(self):
  import grouped_arithmetic_templates as producer
  self.assertEqual(c.descriptors(),producer.descriptors())
  for target in ('mu','c'):
   for claim in ('critical','unsigned_calibration'):
    program=dict(target=target,q=2,C=8,claim=claim,allow_constant_slack=claim=='critical');a=c.build(program,2);b=producer.build_instance(target,2,2,8,claim)
    c.check_built(b,a)
    b['instance']['lhs']=[]
    with self.assertRaises(ValueError):c.check_built(b,a)
 def test_scalar_and_nonconstant_mismatch(self):
  G=c.G;p=[dict(m=[1],c='1')];i=dict(target='mu',horizon=1,lhs=[dict(m=[],c='2'),dict(m=[1,1],c='1')],square_groups=[[dict(weight='1',poly=p)]],relation_groups=[[]])
  r=G.verify_joint([i],['1'],['0'],allow_constant_slack=True);self.assertEqual(r['instances'][0]['constant_slack'],'2')
  with self.assertRaises(ValueError):G.verify_joint([i],['1'],['0'])
  with self.assertRaises(ValueError):G.verify_joint([i],['2'],['0'],allow_constant_slack=True)
 def test_truth_uses_unsigned_bound(self):
  p=dict(target='c',q=2,C=1,claim='unsigned_calibration',allow_constant_slack=False);b=c.build(p,1);t=c.truth(b);self.assertEqual(t['D'],b['unsigned_bound']);self.assertTrue(t['bound_true'])
if __name__=='__main__':unittest.main()
