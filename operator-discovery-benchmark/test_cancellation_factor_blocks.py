import unittest,copy
from fractions import Fraction as F
import cancellation_factor_blocks as B
import grouped_arithmetic_language as L

def cut(c,p='1'):return dict(coefficient=c,power=p)
def spec(coprime=False):return dict(kind='factor_bilinear',product_scale='4',coprime=coprime,cuts=dict(left=dict(lower=cut('1','0'),upper=cut('1','1/2')),right=dict(lower=cut('1','0'),upper=cut('3/2'))),kernel=[dict(coefficient='1',a_power=0,b_power=0,x_power=0),dict(coefficient='-1/3',a_power=1,b_power=0,x_power=0)])
class Tests(unittest.TestCase):
 def test_exact_rational_cut_inside_power(self):
  for X in range(1,33):
   for c in ('1/2','3/2','2/3'):
    for power in ('1/2','2/3','3/2','0'):
     r=B.floor_scaled_power(X,cut(c,power));q=F(c);p=F(power);num=q.numerator**p.denominator*X**p.numerator;den=q.denominator**p.denominator
     self.assertLessEqual(r**p.denominator*den,num);self.assertGreater((r+1)**p.denominator*den,num)
 def test_partition_projection_and_complete_residual(self):
  for target in ('mu','c'):
   for coprime in (False,True):
    out=B.build_block(spec(coprime),3,12,target,multiplier=L.dump_poly(L.add(L.variable(1),L.variable(3))))
    parts=out['parts'];self.assertEqual(parts['full']['pair_count'],parts['inside']['pair_count']+parts['complement']['pair_count']);self.assertEqual(L.load_poly(parts['full']['bilinear']),L.add(L.load_poly(parts['inside']['bilinear']),L.load_poly(parts['complement']['bilinear'])))
    for part in parts.values():
     if coprime:self.assertEqual(part['noncoprime_residual'],[])
     rhs={}
     for term in part['relations']:rhs=L.add(rhs,L.mul(L.load_poly(term['multiplier']),L.relation(term['spec'],target,12)))
     self.assertEqual(rhs,L.load_poly(part['rewrite_difference']))
    self.assertEqual(parts['full']['projection_multiplicities']['6']['count'],4)
 def test_horizon_and_resources_and_empty(self):
  with self.assertRaises(ValueError):B.build_block(spec(),3,11)
  with self.assertRaises(OverflowError):B.build_block(spec(),3,12,max_pairs=1)
  with self.assertRaises(OverflowError):B.floor_scaled_power(2,cut('1','1000'))
  s=spec();s['product_scale']='0';out=B.build_block(s,1,1);self.assertEqual(out['parts']['full']['pair_count'],0)
if __name__=='__main__':unittest.main()
