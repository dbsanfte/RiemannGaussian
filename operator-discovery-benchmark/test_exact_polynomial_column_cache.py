import unittest,time
from fractions import Fraction as F
import exact_polynomial_column_cache as C
import grouped_arithmetic_synthesis as G
import grouped_arithmetic_language as L
class Tests(unittest.TestCase):
 def instance(self,budget):
  return dict(target='mu',horizon=2,lhs=L.dump_poly(L.add(L.constant(budget),L.variable(2))),square_groups=[[dict(weight='1',poly=L.dump_poly(L.add(L.variable(1),L.variable(2))))]],relation_groups=[[dict(spec={'kind':'unit'},multiplier=L.dump_poly(L.variable(2)))]])
 def test_exact_match_target_reuse_and_mutation(self):
  cache=C.ColumnCache();a=self.instance(1);r=cache.prepare([a]);self.assertFalse(r['metadata']['cache_hit']);r['columns'][0].clear()
  b=self.instance(3);s=cache.prepare([b]);self.assertTrue(s['metadata']['cache_hit']);cols,lhs,ms,shape=G._limits([b],**C.DEFAULTS,deadline=time.monotonic()+5)
  self.assertEqual((s['columns'],s['lhs'],s['monomials'],s['shape']),(cols,lhs,ms,shape))
  b['square_groups'][0][0]['weight']='2';self.assertFalse(cache.prepare([b])['metadata']['cache_hit'])
 def test_revalidate_lhs_and_caps(self):
  cache=C.ColumnCache();a=self.instance(1);cache.prepare([a]);a['lhs']=[dict(m=[3],c='1')]
  with self.assertRaises(ValueError):cache.prepare([a])
  with self.assertRaises(OverflowError):cache.prepare([self.instance(1)],max_columns=1)
 def test_bounded_eviction(self):
  c=C.ColumnCache(max_entries=1);a=self.instance(1);c.prepare([a]);a['square_groups'][0][0]['weight']='2';c.prepare([a]);self.assertEqual(len(c._cache),1)
if __name__=='__main__':unittest.main()
