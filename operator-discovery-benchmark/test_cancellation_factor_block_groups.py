import unittest
import cancellation_factor_blocks as P
import cancellation_factor_block_groups as A
import grouped_arithmetic_synthesis as S
import check_grouped_arithmetic as G
class TestAdapter(unittest.TestCase):
 def block(self):
  cut=dict(lower=dict(coefficient='1',power='0'),upper=dict(coefficient='1',power='1'))
  spec=dict(kind='factor_bilinear',product_scale='2',coprime=False,cuts=dict(left=cut,right=cut),kernel=[dict(coefficient='1',a_power=0,b_power=0,x_power=0)])
  return P.build_block(spec,2,7)
 def desc(self):return A.descriptors([dict(part='inside',component='bilinear'),dict(part='complement',component='coprime_projection')],['full','inside'])
 def test_shared_columns(self):
  b=self.block();ds=self.desc();base=dict(target='mu',horizon=7,lhs=[],square_groups=[],relation_groups=[]);r=A.append_groups(base,b,ds)
  self.assertEqual(r['instance']['lhs'],[]);self.assertEqual(r['added_gamma_coefficients'],['0','0'])
  self.assertTrue(r['all_added_formal_scalars_zero']);self.assertTrue(G.verify_joint([r['instance']],['0','0'],['0','0'])['verified'])
  # Existing column compiler accepts the quadratic factor atoms (quartic squares).
  cols,lhs,ms,shape=S._limits([r['instance']],max_columns=20,max_monomials=100,max_operations=100000,max_coefficient_bits=4096,max_horizon=16,max_degree=6,deadline=__import__('time').monotonic()+5)
  self.assertEqual(shape,(2,2));self.assertEqual(len(cols),6)
 def test_auxiliary_empty(self):
  aux=dict(target='mu',horizon=1,lhs=[],square_groups=[[]],relation_groups=[[]]);r=A.append_groups(aux,None,self.desc(),auxiliary=True)
  self.assertEqual(r['instance']['square_groups'],[[],[],[]]);self.assertEqual(r['instance']['relation_groups'],[[],[],[]])
 def test_multiplier_binding(self):
  b=self.block();changed=P.build_block(b['spec'],2,7,multiplier=[dict(m=[1],c='1')])
  base=dict(target='mu',horizon=7,lhs=[],square_groups=[],relation_groups=[])
  with self.assertRaises(ValueError):A.append_to_instances([base,base],[b,changed],self.desc())
  r=A.append_to_instances([base],[b],self.desc())
  self.assertIn('semantic_binding_sha256',r);self.assertNotEqual(r['namespaced_square_ids'][0],self.desc()['square'][0]['id'])
 def test_binding_and_no_selection(self):
  ds=self.desc();ds['square'][0]['id']='tamper'
  with self.assertRaises(ValueError):A.groups(self.block(),ds)
  with self.assertRaises(ValueError):A.descriptors([dict(part='full',component='actual_response')],[])
if __name__=='__main__':unittest.main()
