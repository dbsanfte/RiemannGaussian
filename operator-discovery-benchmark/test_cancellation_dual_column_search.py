import unittest
from fractions import Fraction as F
import cancellation_dual_column_search as C
class TestColumns(unittest.TestCase):
 def fixture(self):
  inst=dict(target='mu',horizon=3,lhs=[],square_groups=[],relation_groups=[])
  # Synthetic complete quadratic functional: offdiagonal -1, diagonal0.
  ms=[dict(instance=0,m=[i,j]) for i in range(1,4) for j in range(i,4)]
  dual=dict(status='exact_separator',certified=True,monomials=ms,weights=['0' if m['m'][0]==m['m'][1] else '-1' for m in ms])
  return [inst],dual
 def test_generic_archive(self):
  inst,d=self.fixture();r=C.propose(inst,d,[1]);self.assertEqual(len(r['candidates']),120);self.assertLessEqual(len(r['selected']),8)
  self.assertTrue(all(F(c['dot'])<0 for c in r['selected']));self.assertEqual(len({c['descriptor']['id'] for c in r['candidates']}),120)
  self.assertEqual(r['candidate_archive_sha256'],C.digest(r['candidates']))
 def test_group_semantics(self):
  d=next(d for d in C.enumerate_descriptors() if d['region']=='child' and d['left']=='prefix' and d['right']=='half' and d['coefficient']=='2')
  g=C.build_group(d,1,3);self.assertEqual(g[0]['poly'],[dict(m=[1],c='3'),dict(m=[2],c='1')])
 def test_missing_rejected(self):
  inst,d=self.fixture();d['monomials'].pop();d['weights'].pop()
  with self.assertRaises(ValueError):C.propose(inst,d,[1])
 def test_auxiliary_empty_and_resource(self):
  inst,d=self.fixture();inst.append(dict(target='mu',horizon=1,lhs=[],square_groups=[[]],relation_groups=[]))
  r=C.propose(inst,d,[1]);self.assertTrue(r['auxiliary_groups_empty'])
  with self.assertRaises(OverflowError):C.propose(inst,d,[1],max_operations=1)
if __name__=='__main__':unittest.main()
