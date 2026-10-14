import unittest
from fractions import Fraction as F
import cancellation_factor_blocks as FACTOR
import cancellation_factor_search_language as T
import cancellation_arithmetic_templates as OLD
import grouped_arithmetic_language as L
class Tests(unittest.TestCase):
 def test_cost_dictionary_stable_and_bounded(self):
  c=T.template_catalog();self.assertEqual(len(c['selected']),44);self.assertEqual(len(c['unselected']),0);d=T.descriptors();self.assertEqual(len(d['square']),282);self.assertEqual(len(d['relation']),319);self.assertLess(len(d['square'])+2*len(d['relation']),1024)
  self.assertEqual(len({v['theta']for v in c['selected']+c['unselected']}),11)
 def test_full_lhs_groups_complete_cells(self):
  for target in ('mu','c'):
   spec=dict(T.DEFAULT_SPEC,max_blocks=2)
   for X in (1,2):
    old=OLD.build_instance(target,X,2,2);new=T.build_instance(target,X,2,2,spec=spec)
    self.assertEqual(old['instance']['lhs'],new['instance']['lhs']);self.assertEqual(old['instance']['square_groups'],new['instance']['square_groups'][:106]);self.assertEqual(old['instance']['relation_groups'],new['instance']['relation_groups'][:231])
    for r in new['factor_archive']:self.assertEqual(r['full_pair_count'],sum(c['pair_count']for c in r['cells'].values()));self.assertTrue(r['difference_square_closure_verified'])
 def test_exact_closure_can_compile(self):
  b=T.build_instance('mu',1,2,2,spec=dict(T.DEFAULT_SPEC,max_blocks=1));groups=b['instance'];B=groups['square_groups'][106];C=groups['square_groups'][107];relations=groups['relation_groups'][231]
  lhs={}
  for sign,group in ((1,B),(-1,C)):
   for t in group:p=L.load_poly(t['poly']);lhs=L.add(lhs,L.scale(L.mul(p,p),sign))
  rhs={}
  for t in relations:rhs=L.add(rhs,L.mul(L.load_poly(t['multiplier']),L.relation(t['spec'],'mu',3)))
  self.assertEqual(lhs,rhs)
 def test_signed_prefix_interactions(self):
  b=T.build_instance('mu',2,2,2,spec=dict(T.DEFAULT_SPEC,max_blocks=1));groups=b['instance']['square_groups'];plus=L.load_poly(groups[108][0]['poly']);minus=L.load_poly(groups[109][0]['poly']);prefix=L.add(*(L.variable(n)for n in range(1,8)));self.assertEqual(L.add(plus,minus),L.scale(prefix,2));self.assertNotEqual(plus,minus)
  self.assertTrue(T.block_spec(T.template_catalog()['selected'][0])['coprime'])
 def test_exact_kernel_normalization(self):
  b=T.build_instance('mu',1,2,2);catalog=T.template_catalog()['selected']
  for k,(desc,archive)in enumerate(zip(catalog,b['factor_archive'])):
   factor=F(1,3**desc['kernel_degree']);self.assertEqual(F(archive['normalization']),factor)
   raw=FACTOR.build_block(T.block_spec(desc),3,3)
   for i,cell in enumerate(('inside','complement')):
    self.assertEqual(L.load_poly(b['instance']['square_groups'][106+4*k][i]['poly']),L.scale(L.load_poly(raw['parts'][cell]['bilinear']),factor))
   lhs={}
   for sign,group in ((1,b['instance']['square_groups'][106+4*k]),(-1,b['instance']['square_groups'][107+4*k])):
    for term in group:p=L.load_poly(term['poly']);lhs=L.add(lhs,L.scale(L.mul(p,p),sign))
   rhs={}
   for term in b['instance']['relation_groups'][231+2*k]:rhs=L.add(rhs,L.mul(L.load_poly(term['multiplier']),L.relation(term['spec'],'mu',3)))
   self.assertEqual(lhs,rhs)
 def test_caps(self):
  with self.assertRaises(OverflowError):T.template_catalog(dict(T.DEFAULT_SPEC,max_blocks=100))
  with self.assertRaises(OverflowError):T.build_instance('mu',2,2,2,max_columns=100)
if __name__=='__main__':unittest.main()
