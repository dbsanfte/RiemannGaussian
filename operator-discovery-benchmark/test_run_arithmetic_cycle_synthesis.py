import unittest,tempfile,json
from pathlib import Path
from unittest.mock import patch
import run_arithmetic_cycle_synthesis as r
import arithmetic_cycle_language as L
class Tests(unittest.TestCase):
 def test_order_and_complete_template(self):
  cases=r.cases([1,2]);self.assertEqual(len(cases),32)
  for mode in ('atomic_local','grouped_cycles'):
   t=r.template(dict(target='mu',X=1,q=2,C=1,mode=mode));self.assertEqual(t['horizon'],3);self.assertEqual(t['D'],'1');self.assertEqual(L.load_poly(t['lhs']),L.add(L.constant(1),L.scale(L.complete_defect(1),-1)))
   self.assertTrue(all(set(term)=={'spec','multiplier'} for group in t['relation_columns'] for term in group))
   self.assertEqual(t,r.template(dict(target='mu',X=1,q=2,C=1,mode=mode)))
 def test_freeze_no_overwrite_and_hashes(self):
  with tempfile.TemporaryDirectory() as d:
   root=Path(d)/'src';root.mkdir();(root/'fixture').write_text('frozen source')
   dest=Path(d)/'run'
   with patch.object(r,'ROOT',root),patch.object(r,'CODE',['fixture']):r.freeze(dest)
   seal=json.loads((dest/'seal.json').read_text());self.assertEqual(seal['protocol_sha256'],r.filehash(dest/'protocol.json'));self.assertEqual((dest/'frozen_source'/'fixture').read_text(),'frozen source')
   with self.assertRaises(ValueError):r.freeze(dest)
 def test_cutoff_bounds_and_modes(self):
  for X in range(1,33):
   for q in (2,6):
    c=r.rootceil(X,q);self.assertGreaterEqual(c**q,X);self.assertLess((c-1)**q,X)
  t=r.template(dict(target='c',X=2,q=6,C=4,mode='grouped_cycles'))
  self.assertTrue(all(s['kind'] not in ('inverse_row','squarefree_zero') for s in t['relations']));self.assertTrue(t['column_generation_archive'])
if __name__=='__main__':unittest.main()
