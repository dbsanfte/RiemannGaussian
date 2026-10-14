import unittest
from unittest.mock import patch
import check_cancellation_factor_lp_retry as C
class Tests(unittest.TestCase):
 def fixture(self):
  program=dict(constraint='none');i=dict(target='mu',horizon=1,lhs=[],square_groups=[],relation_groups=[]);cert=dict(target='mu',horizon=1,lhs=[],squares=[],relations=[]);r=dict(status='finite_certificate',weights=dict(square_weights=[],relation_weights=['0']*319),certificates=[cert],constant_slacks=['0'])
  # A finite fixture must retain the actual empty groups corresponding to shared weights.
  i['relation_groups']=[[]for _ in range(319)]
  a=dict(program=program,dictionary_sha256=C.I.digest(C.Z.descriptors()),grams_fixed_zero=True,case_hashes=[C.I.digest(i)],factor_archive_hashes=[C.I.digest([])],synthesis=r,proposed_synthesis=r,gamma='0')
  return program,i,a
 def test_exact_weight_transfer_and_tamper(self):
  p,i,a=self.fixture()
  with patch.object(C.Z,'build',return_value=dict(instance=i,factor_archive=[])):
   C.verify_attempt(a,p,[1]);a['synthesis']['constant_slacks']=['1']
   with self.assertRaises(ValueError):C.verify_attempt(a,p,[1])
 def test_dictionary_and_missing(self):
  p,i,a=self.fixture();a.update(synthesis=dict(status='missing_resource',reason='cap'),gamma=None);a.pop('proposed_synthesis')
  with patch.object(C.Z,'build',return_value=dict(instance=i,factor_archive=[])):
   C.verify_attempt(a,p,[1]);a['grams_fixed_zero']=False
   with self.assertRaises(ValueError):C.verify_attempt(a,p,[1])
if __name__=='__main__':unittest.main()
