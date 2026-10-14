import unittest
import run_cancellation_divisor_coupling_calibration as R
class Tests(unittest.TestCase):
 def test_frozen_dictionary_signed_zero_and_endpoint(self):
  fs=R.fixtures();self.assertEqual(len(fs),6);self.assertTrue(any(f['H']==1 and f['weights']==['0']for f in fs));self.assertTrue(any('-1'in f['weights']and '0'in f['weights']for f in fs))
  for f in fs:self.assertTrue(R.C.check_coupling(f['H'],f['weights'],R.P.build_coupling(f['H'],f['weights']))['verified'])
 def test_complete_dependency_closure(self):
  names=R.sources();self.assertIn('check_cancellation_divisor_coupling.py',names);self.assertIn('check_arithmetic_cycle_certificate.py',names);self.assertIn('grouped_arithmetic_language.py',names);self.assertEqual(names,sorted(set(names)))
if __name__=='__main__':unittest.main()
