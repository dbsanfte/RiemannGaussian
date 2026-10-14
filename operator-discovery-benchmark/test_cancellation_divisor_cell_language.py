import unittest
from fractions import Fraction as F
import grouped_arithmetic_language as L
import cancellation_divisor_cells as C
import cancellation_divisor_cell_language as A
import cancellation_divisor_localizer_language as BASE
class Tests(unittest.TestCase):
 def test_all_contexts_compiler_match(self):
  for X in (1,2):
   out=A.build_additions(X);sg=[];rg=[]
   for archive in out['archive']:
    forms=[[]for _ in range(3)];closures=[{}for _ in range(4)]
    for row in archive['rows']:
     t=row['t'];weights=[str(F(a)**archive['power'])for a in range(1,t+1)]
     built=C.build_cells(t,weights,dict(kind='divisor_le',coefficient='1',power=archive['theta']))
     self.assertEqual(row['cut'],built['cutoff'])
     self.assertEqual(row['source_pairs_sha256'],built['source']['full']['pairs_sha256'])
     self.assertEqual(row['inside_pairs_sha256'],built['source']['inside_pairs_sha256'])
     self.assertEqual(row['complement_pairs_sha256'],built['source']['complement_pairs_sha256'])
     self.assertEqual(row['source_count'],row['inside_count']+row['complement_count'])
     D=built['D'];P=built['prefix']
     for i,p in enumerate([D,L.dump_poly(L.add(L.load_poly(P),L.load_poly(D))),L.dump_poly(L.add(L.load_poly(P),L.scale(L.load_poly(D),-1))) ]):forms[i].append(dict(weight='1',poly=p))
     for i,cl in enumerate(built['closures']):
      for term in cl['certificate']['relations']:
       n=1 if term['spec']['kind']=='unit'else term['spec']['n']
       closures[i][n]=L.add(closures[i].get(n,{}),L.load_poly(term['multiplier']))
    sg.extend(forms)
    rg.extend([[dict(spec=dict(kind='unit')if n==1 else dict(kind='inverse_row',n=n),multiplier=L.dump_poly(p))for n,p in sorted(g.items())]for g in closures])
    count=len(archive['scales'])
    self.assertEqual(archive['formal_square_scalars'],[str(F(count,4))]*3)
    self.assertEqual(archive['formal_relation_scalars'],list(map(str,[-F(count),F(0),F(count,2),F(count)])))
   self.assertEqual(out['square_groups'],sg);self.assertEqual(out['relation_groups'],rg)
 def test_dictionary_and_full_target(self):
  ds=A.descriptors();self.assertEqual(len(ds['square']),366);self.assertEqual(len(ds['relation']),403)
  self.assertEqual(len({d['id']for k in ds for d in ds[k]}),769)
  for X in (1,2):
   old=BASE.build_instance('mu',X,2,8);new=A.build_instance('mu',X,2,8)
   self.assertEqual(old['instance']['lhs'],new['instance']['lhs'])
   ns=len(old['instance']['square_groups']);nr=len(old['instance']['relation_groups'])
   self.assertEqual(new['instance']['square_groups'][:ns],old['instance']['square_groups'])
   self.assertEqual(new['instance']['relation_groups'][:nr],old['instance']['relation_groups'])
 def test_resources(self):
  with self.assertRaises(OverflowError):A.build_additions(2,max_horizon=6)
  with self.assertRaises(OverflowError):A.build_additions(2,max_operations=10)
  with self.assertRaises(OverflowError):A.build_additions(2,max_terms=1)
  with self.assertRaises(ValueError):A.build_additions(True)
  with self.assertRaises(ValueError):A.build_instance('c',1,2,8)
if __name__=='__main__':unittest.main()
