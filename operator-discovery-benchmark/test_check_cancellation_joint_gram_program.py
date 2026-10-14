import copy
import unittest
from fractions import Fraction as F
import check_cancellation_joint_gram_program as I

def zeros(n):return [['0']*n for _ in range(n)]
def joint_zero():return {k:zeros(n) for k,n in I.gram_specs().items()}
def pair_zero():return {k:zeros(n) for k,n in I.B.gram_specs().items()}
class Joint(unittest.TestCase):
 def test_complete_builder_and_permutation(self):
  import cancellation_joint_gram_program as B
  self.assertEqual(I.SPEC,B.SPEC);self.assertEqual(I.group_descriptors(),B.group_descriptors())
  program=dict(target='mu',q=6,C='32',claim='critical')
  for X in (1,2):
   a=I.build_blocks(X);b=B.build_blocks(X);b.pop('construction_operations');self.assertEqual(a,b)
   out=B.build(program,X);self.assertTrue(I.check_builder(program,X,out)['verified'])
   old=I.B.build(program,X)
   for k in ['instance','square_ids','relation_ids','dictionary_sha256','cell_archive']:
    self.assertEqual(out[k],old[k])
   row=out['gram_blocks']['joint_child'][0];row[1],row[2]=row[2],row[1]
   with self.assertRaises(ValueError):I.check_builder(program,X,out)
  self.assertEqual(I.auxiliary(),B.auxiliary())

 def test_pair_embedding_exact_polynomials(self):
  pair=pair_zero()
  for k,d in I.B.group_descriptors().items():
   if d['kind']=='divisor_cell':pair[k]=[['1','-1'],['-1','1']]
  joint=I.embed_pair_grams(pair)
  for X in (1,2):
   old=I.B.build_blocks(X)['blocks'];new=I.build_blocks(X)['blocks']
   for region in ['parent','child']:
    expected={}
    for k,d in I.B.group_descriptors().items():
     if d['kind']=='divisor_cell' and d['region']==region:expected=I.P.add(expected,I.I.gram_polynomial(pair[k],old[k],4*X-1))
    self.assertEqual(expected,I.I.gram_polynomial(joint['joint_'+region],new['joint_'+region],4*X-1))
 def test_scalar_offdiagonal_charge(self):
  g=joint_zero();a=g['joint_parent'];a[1][1]=a[2][2]=a[1][2]=a[2][1]='1'
  self.assertEqual(I.scalar_budget(g,3)['total'],'3')
  blocks=I.build_blocks(3)['blocks']
  self.assertEqual(I.I.gram_polynomial(a,blocks['joint_parent'],11).get((),F(0)),F(3))
  a[1][2]=a[2][1]='-1'
  self.assertEqual(I.scalar_budget(g,3)['total'],'0')
  self.assertEqual(I.I.gram_polynomial(a,blocks['joint_parent'],11).get((),F(0)),F(0))
  g['joint_child']=copy.deepcopy(a);g['joint_child'][1][2]=g['joint_child'][2][1]='1'
  self.assertEqual(I.scalar_budget(g,3)['total'],'6')
 def test_permutation_scalar_invariance(self):
  g=joint_zero();a=g['joint_parent'];a[1][1]='1';a[4][4]='4';a[1][4]=a[4][1]='2'
  expected=I.scalar_budget(g,2)['total'];order=[0,4,2,3,1,5,6,7,8,9]
  g['joint_parent']=[[a[i][j] for j in order] for i in order]
  self.assertEqual(I.scalar_budget(g,2)['total'],expected)
 def test_dimension_and_PSD(self):
  g=joint_zero();g['joint_parent'][1][2]=g['joint_parent'][2][1]='1'
  with self.assertRaises(ValueError):I.scalar_budget(g,1)
  with self.assertRaises(ValueError):I.embed_pair_grams({})
if __name__=='__main__':unittest.main()
