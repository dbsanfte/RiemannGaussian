import copy
import unittest
from fractions import Fraction as F
import check_cancellation_complete_gram_program as I
import cancellation_complete_gram_program as B
class Complete(unittest.TestCase):
 def test_full_semantics_and_order(self):
  self.assertEqual(I.SPEC,B.SPEC);self.assertEqual(I.group_descriptors(),B.group_descriptors())
  program=dict(target='mu',q=6,C='32',claim='critical')
  for X in (1,2):
   out=B.build(program,X);self.assertTrue(I.check_builder(program,X,out)['verified'])
   prior=I.B.build(program,X)
   for key in ['instance','dictionary_sha256','square_ids','relation_ids','cell_archive']:self.assertEqual(out[key],prior[key])
   row=out['gram_blocks']['full_child'][0];row[5],row[6]=row[6],row[5]
   with self.assertRaises(ValueError):I.check_builder(program,X,out)
  self.assertEqual(I.auxiliary(),B.auxiliary())
 def test_exact_embedding(self):
  grams={k:[['0']*n for _ in range(n)] for k,n in I.B.gram_specs().items()}
  for region in ['child','parent']:
   grams['old_'+region][0][0]='2';g=grams['joint_'+region];g[0][0]=g[1][1]='1';g[0][1]=g[1][0]='-1'
  embedded=I.embed_joint_grams(grams)
  for X in (1,2):
   old=I.B.build_blocks(X)['blocks'];new=I.build_blocks(X)['blocks']
   for region in ['child','parent']:
    expected=I.P.add(I.I.gram_polynomial(grams['old_'+region],old['old_'+region],4*X-1),I.I.gram_polynomial(grams['joint_'+region],old['joint_'+region],4*X-1))
    self.assertEqual(expected,I.I.gram_polynomial(embedded['full_'+region],new['full_'+region],4*X-1))
   self.assertEqual(I.scalar_budget(embedded,X)['total'],I.B.scalar_budget(grams,X)['total'])
 def test_crosscharge_and_difference(self):
  grams={k:[['0']*14 for _ in range(14)] for k in I.gram_specs()};g=grams['full_parent']
  g[5][5]=g[6][6]=g[5][6]=g[6][5]='1';self.assertEqual(I.scalar_budget(grams,3)['total'],'3')
  blocks=I.build_blocks(3)['blocks'];self.assertEqual(I.I.gram_polynomial(g,blocks['full_parent'],11).get((),F(0)),F(3))
  g[5][6]=g[6][5]='-1';self.assertEqual(I.scalar_budget(grams,3)['total'],'0');self.assertEqual(I.I.gram_polynomial(g,blocks['full_parent'],11).get((),F(0)),F(0))
 def test_sharedprefix_and_dimension(self):
  old=I.B.build_blocks(1)['blocks'];old['joint_child'][0][0]=[]
  with self.assertRaises(ValueError):I.assemble_blocks(1,old)
  with self.assertRaises(ValueError):I.embed_joint_grams({})
if __name__=='__main__':unittest.main()
