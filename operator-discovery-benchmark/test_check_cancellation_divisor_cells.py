import copy
import unittest
import cancellation_divisor_cells as C
import cancellation_divisor_cell_language as L
import check_cancellation_divisor_cells as I
class Tests(unittest.TestCase):
 def test_generic(self):
  for w in [['1','-1/2','0','2'],['0','0','0','0']]:
   for coeff in ['0','1','3/2']:
    p=dict(kind='divisor_le',coefficient=coeff,power='1/2');o=C.build_cells(4,w,p);self.assertTrue(I.check_cells(4,w,p,o)['verified'])
 def test_mutations(self):
  w=['1','-1'];p=dict(kind='divisor_le',coefficient='1',power='1/2');o=C.build_cells(2,w,p)
  for key in ['D','source','closures','coupled_squares']:
   z=copy.deepcopy(o);z[key]=[]
   with self.assertRaises(ValueError):I.check_cells(2,w,p,z)
 def test_grouped(self):
  p=dict(target='mu',q=6,C='32',claim='critical')
  for X in [1,2]:
   o=L.build_instance('mu',X,6,'32');self.assertTrue(I.check_builder(p,X,o)['verified']);z=copy.deepcopy(o);z['cell_archive'][0]['rows'][0]['inside_count']+=1
   with self.assertRaises(ValueError):I.check_builder(p,X,z)
  self.assertEqual(len(I.descriptors()['square']),366);self.assertEqual(len(I.descriptors()['relation']),403)
 def test_hostile(self):
  with self.assertRaises(OverflowError):I.build_additions(2,max_horizon=3)
  with self.assertRaises(OverflowError):I.floor_cut(3,dict(kind='divisor_le',coefficient='1',power='1/100000000000000000000'))
  with self.assertRaises(ValueError):I.core(1,[True],dict(kind='divisor_le',coefficient='1',power='1'))
if __name__=='__main__':unittest.main()
