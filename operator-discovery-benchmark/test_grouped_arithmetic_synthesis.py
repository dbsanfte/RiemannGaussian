import unittest,copy
from fractions import Fraction as F
import grouped_arithmetic_language as L
import grouped_arithmetic_synthesis as S

def instance(index,factor=1):
 p=L.add(L.variable(index),L.constant(1));return dict(target='mu',horizon=index,lhs=L.dump_poly(L.scale(L.mul(p,p),F(3,7)*factor)),square_groups=[[dict(weight=str(factor),poly=L.dump_poly(p))],[]],relation_groups=[[]])
class Tests(unittest.TestCase):
 def test_shared_recovery_and_transfer(self):
  result=S.synthesize([instance(2),instance(3,2)]);self.assertEqual(result['status'],'finite_certificate');self.assertEqual(result['weights']['square_weights'],['3/7','0']);self.assertEqual(result['weights']['relation_weights'],['0'])
  c=S.instantiate_certificate(instance(5,4),result['weights']);self.assertTrue(L.compile_certificate(c)['finite_identity_verified'])
  bad=instance(5,4);bad['lhs'][0]['c']=str(F(bad['lhs'][0]['c'])+1)
  with self.assertRaises(ValueError):S.instantiate_certificate(bad,result['weights'])
 def test_shared_not_individual_fit(self):
  a=instance(2);b=instance(3);b['lhs']=L.dump_poly(L.scale(L.load_poly(b['lhs']),2));result=S.synthesize([a,b]);self.assertEqual(result['status'],'no_certificate_found');d=S.find_separator([a,b]);self.assertTrue(d['certified']);self.assertLess(F(d['lhs_dot_y']),0)
 def test_shared_relation_group_and_cycle(self):
  spec=dict(kind='coprime_product',a=2,b=3);p=L.variable(6);lhs=L.dump_poly(L.mul(L.mul(L.variable(2),L.variable(3)),p));instance=dict(target='mu',horizon=6,lhs=lhs,square_groups=[[dict(weight='1',poly=L.dump_poly(p))]],relation_groups=[[dict(spec=spec,multiplier=L.dump_poly(p))]])
  result=S.synthesize([instance,copy.deepcopy(instance)]);self.assertEqual(result['status'],'finite_certificate');self.assertEqual(result['weights'],dict(square_weights=['1'],relation_weights=['1']))
 def test_shapes_and_resources(self):
  a=instance(2);b=instance(3);b['square_groups'].pop();self.assertEqual(S.synthesize([a,b])['status'],'no_certificate_found')
  self.assertEqual(S.synthesize([a],max_columns=1)['status'],'missing_resource')
  bad=instance(2);bad['square_groups'][0][0]['weight']='-1';self.assertEqual(S.synthesize([bad])['status'],'no_certificate_found')
 def test_constant_slack_and_transfer(self):
  a=instance(2);b=instance(3)
  a['lhs']=L.dump_poly(L.add(L.load_poly(a['lhs']),L.constant(2)))
  b['lhs']=L.dump_poly(L.add(L.load_poly(b['lhs']),L.constant(5)))
  result=S.synthesize([a,b],allow_constant_slack=True)
  self.assertEqual(result['status'],'finite_certificate');self.assertEqual(result['constant_slacks'],['2','5'])
  new=instance(4);new['lhs']=L.dump_poly(L.add(L.load_poly(new['lhs']),L.constant(7)))
  cert=S.instantiate_certificate(new,result['weights'],allow_constant_slack=True)
  self.assertEqual(cert['squares'][-1]['weight'],'7')
  new['lhs']=L.dump_poly(L.add(L.load_poly(instance(4)['lhs']),L.constant(-1)))
  with self.assertRaises(ValueError):S.instantiate_certificate(new,result['weights'],allow_constant_slack=True)
  negative=dict(target='mu',horizon=1,lhs=L.dump_poly(L.constant(-1)),square_groups=[],relation_groups=[])
  dual=S.find_separator([negative],allow_constant_slack=True)
  self.assertTrue(dual['certified']);self.assertGreaterEqual(F(dual['weights'][0]),0)
 def test_negative_square_separator(self):
  a=instance(2);a['lhs']=L.dump_poly(L.scale(L.load_poly(a['lhs']),-1));self.assertEqual(S.synthesize([a])['status'],'no_certificate_found');self.assertTrue(S.find_separator([a])['certified'])
if __name__=='__main__':unittest.main()
