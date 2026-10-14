import unittest
import arithmetic_cycle_controls as c
class TestControls(unittest.TestCase):
 def test_actual_coefficients(self):
  self.assertEqual(c.coefficients(8,'mu')['coefficients'],[0,1,-1,-1,0,-1,1,-1,0])
  self.assertEqual(c.coefficients(8,'c')['coefficients'],[0,1,-2,-2,2,-2,4,-2,-2])
 def test_full_counterfeit_audit(self):
  a=c.audit_counterfeit([2],8,24,[2,4],horizon_cap=128)
  self.assertTrue(a['all_finite_premise_checks_passed']);self.assertEqual(a['horizon'],64)
  self.assertGreater(a['zero_cycle_pairs_checked'],0);self.assertEqual(a['inverse_rows_checked'],list(range(2,25,2)))
  self.assertTrue(any(r['prime']==3 for r in a['normalization_mismatches']))
  self.assertEqual(a['ordered_coprime_pairs_checked'],43)
 def test_counterexample_and_tamper(self):
  a=c.audit_counterfeit([],4,8,[2],horizon_cap=32)
  r=c.certify_stored_counterexample(a,2,'0');self.assertTrue(r['certified_finite_counterexample']);self.assertFalse(r['actual_RH_refuted'])
  with self.assertRaises(OverflowError):c.certify_stored_counterexample(a,2,'0',horizon_cap=8)
  a['energies'][0]['Delta']+=1
  with self.assertRaises(ValueError):c.certify_stored_counterexample(a,2,'0')
 def test_resource_and_domain(self):
  for args in [(8,'mu',[4]),(8,'mu',[True])]:
   with self.assertRaises(ValueError):c.coefficients(*args)
  with self.assertRaises(OverflowError):c.coefficients(129,horizon_cap=128)
  with self.assertRaises(OverflowError):c.audit_counterfeit([2],20,4,pair_work_cap=100)
  with self.assertRaises(ValueError):c.block_energy([0,1],1)
if __name__=='__main__':unittest.main()
