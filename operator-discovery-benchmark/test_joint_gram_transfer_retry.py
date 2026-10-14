import unittest,copy
from unittest.mock import patch
import run_joint_gram_transfer_retry as R
import cancellation_shared_gram_synthesis_v2 as S

class TransferRetryTests(unittest.TestCase):
 def fixture(self):
  instance=dict(target='mu',horizon=1,lhs=[dict(m=[1,1],c='1')],square_groups=[[dict(weight='1',poly=[dict(m=[1],c='1')])]],relation_groups=[])
  specs={'joint_child':10,'joint_parent':10,'old_child':5,'old_parent':5}
  blocks={name:[]for name in specs};grams={name:[['0']*n for _ in range(n)]for name,n in specs.items()}
  candidate=dict(weights=dict(square_weights=['1'],relation_weights=[]),grams=grams)
  limits=dict(time_limit=180,max_operations=100000,max_horizon=80,max_columns=2048,max_monomials=100000)
  return instance,blocks,specs,candidate,limits
 def test_memory_only_resource_policy(self):
  self.assertEqual(R.PARALLEL['workers'],1)
  self.assertEqual(R.PARALLEL['worker_memory_bytes'],6*1024**3)
  self.assertEqual(R.PARALLEL['memory_budget_bytes'],6*1024**3)
  self.assertEqual(R.PARALLEL['timeout_seconds'],600)
 def test_unchanged_certificate_without_search(self):
  i,b,s,c,l=self.fixture();before=copy.deepcopy((i,b,c))
  with patch.object(S,'synthesize',side_effect=AssertionError('no SDP')):
   result=R.transfer(i,b,s,c,l)
  self.assertTrue(result['independent_check']['verified'])
  self.assertEqual(result['weights'],c['weights']);self.assertEqual(result['grams'],c['grams'])
  self.assertEqual(result['constant_slacks'],['0'])
  self.assertEqual((i,b,c),before)
 def test_wrong_fixed_weight_rejected(self):
  i,b,s,c,l=self.fixture();c['weights']['square_weights']=['2']
  with self.assertRaises(ValueError):R.transfer(i,b,s,c,l)
 def test_full_source_zero_atom_tamper_rejected(self):
  i,b,s,c,l=self.fixture();b['old_parent']=[[[dict(m=[2],c='1')]]+[[]]*4]
  # Generic checker checks horizon even though the Gram is zero.
  with self.assertRaises(ValueError):R.transfer(i,b,s,c,l)
 def test_closure_contains_frozen_instantiator_and_checker(self):
  names=R.sources()
  for name in ('run_joint_gram_transfer_retry.py','test_joint_gram_transfer_retry.py','cancellation_shared_gram_synthesis_v2.py','cancellation_shared_gram_synthesis.py','grouped_arithmetic_sparse.py','check_cancellation_shared_gram.py','check_joint_gram_transfer_retry.py'):
   self.assertIn(name,names)
if __name__=='__main__':unittest.main()
