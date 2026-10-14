import copy
import unittest
import check_complete_gram_moment_probe_v2 as I
class Moments(unittest.TestCase):
 def fixture(self):
  x=[dict(m=[1],c='1')];y=[dict(m=[2],c='1')];atoms=[x,y]+[[]]*12
  blocks=[{k:[copy.deepcopy(atoms)] for k in I.B.gram_specs()}];instances=[dict(horizon=2)]
  dual=dict(monomials=[dict(instance=0,m=m) for m in [[],[1,1],[1,2],[2,2]]],weights=['1','1','1','0'])
  return instances,blocks,dual
 def test_negative_direction_full_polynomial(self):
  out=I.moment_probe(*self.fixture())
  for r in out['regions'].values():
   self.assertEqual(r['status'],'witness_invalid_for_complete_cone');self.assertTrue(r['full_polynomial_matching_verified']);self.assertEqual(r['quadratic_value'],r['full_square_polynomial_dot'])
 def test_missing_no_implicit_zero(self):
  args=self.fixture();args[2]['monomials'].pop(2);args[2]['weights'].pop(2)
  self.assertTrue(all(r['status']=='unknown_missing_coordinates' for r in I.moment_probe(*args)['regions'].values()))
 def test_PSD_and_aggregated_cross_cancellation(self):
  inst,blocks,dual=self.fixture();dual['weights']=['1','1','0','1']
  self.assertTrue(all(r['status']=='PSD_extension' for r in I.moment_probe(inst,blocks,dual)['regions'].values()))
  for k in blocks[0]:
   other=copy.deepcopy(blocks[0][k][0]);other[1]=[dict(m=[2],c='-1')];blocks[0][k].append(other)
  dual['monomials'].pop(2);dual['weights'].pop(2)
  self.assertTrue(all(r['status']=='PSD_extension' for r in I.moment_probe(inst,blocks,dual)['regions'].values()))
 def test_large_moment_denominator_short_polynomial_witness(self):
  inst,blocks,dual=self.fixture();denominator=2**3000+1
  dual['weights']=['1','0',str(I.F(1,denominator)),'0']
  out=I.moment_probe(inst,blocks,dual)
  for row in out['regions'].values():
   self.assertEqual(row['status'],'witness_invalid_for_complete_cone')
   self.assertTrue(all(I.F(v).denominator==1 for v in row['negative_direction']))
   self.assertEqual(row['quadratic_value'],str(I.F(-2,denominator)))
 def test_dyadic_pair_witness_and_invalid_budget(self):
  matrix=[['0','1/1000'],['1/1000','1']]
  v=I.negative_direction(matrix)
  self.assertLess(sum(I.F(matrix[i][j])*v[i]*v[j] for i in range(2) for j in range(2)),0)
  self.assertLessEqual(max(q.denominator.bit_length() for q in v),257)
  with self.assertRaises(ValueError):I.negative_direction(matrix,max_exponent=2048)
 def test_indefinite_matrix_with_positive_pair_minors(self):
  matrix=[[I.F(1),I.F(2,3),I.F(2,3)],
          [I.F(2,3),I.F(1),I.F(-2,3)],
          [I.F(2,3),I.F(-2,3),I.F(1)]]
  self.assertTrue(all(matrix[i][i]*matrix[j][j]>matrix[i][j]**2 for i in range(3) for j in range(i+1,3)))
  v=I.negative_direction(matrix)
  self.assertLess(sum(matrix[i][j]*v[i]*v[j] for i in range(3) for j in range(3)),0)
if __name__=='__main__':unittest.main()
