import unittest,copy
import cancellation_factor_blocks as P
import check_cancellation_factor_blocks as C
class TestCheckFactor(unittest.TestCase):
 def spec(self,coprime=False):
  return dict(kind='factor_bilinear',product_scale='2',coprime=coprime,cuts={a:dict(lower=dict(coefficient='1',power='0'),upper=dict(coefficient='1',power='1/2')) for a in ['left','right']},kernel=[dict(coefficient='1/2',a_power=1,b_power=0,x_power=0),dict(coefficient='-1',a_power=0,b_power=1,x_power=0)])
 def test_complete_projection(self):
  for t in ['mu','c']:
   for cop in [False,True]:
    r=P.build_block(self.spec(cop),4,8,target=t,multiplier=[dict(m=[1],c='2')]);self.assertTrue(C.check_block(r)['verified'])
 def test_mutations(self):
  r=P.build_block(self.spec(),4,8)
  for field in ['pairs','relations']:
   a=copy.deepcopy(r);a['parts']['full'][field].pop()
   with self.assertRaises(ValueError):C.check_block(a)
  a=copy.deepcopy(r);a['parts']['complement']['bilinear']=[]
  with self.assertRaises(ValueError):C.check_block(a)
  a=copy.deepcopy(r);next(iter(a['parts']['full']['projection_multiplicities'].values()))['count']+=1
  with self.assertRaises(ValueError):C.check_block(a)
 def test_exact_fractional_bounds(self):
  self.assertEqual(C.floor_scaled_power(8,'3/2','1/3'),3)
  self.assertEqual(C.floor_scaled_power(9,'3/2','1/3'),3)
  self.assertEqual(C.floor_scaled_power(8,'0','100'),0)
if __name__=='__main__':unittest.main()
