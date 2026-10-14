import copy
import unittest
import cancellation_shared_gram_dual_v2 as D
import check_complete_gram_search as I
class Search(unittest.TestCase):
 def fixture(self):
  inst=dict(target='mu',horizon=1,lhs=[dict(m=[1,1],c='-1')],square_groups=[],relation_groups=[])
  atoms=[[dict(m=[1],c='1')]]+[[]]*13;blocks=[{k:[copy.deepcopy(atoms)] for k in I.B.gram_specs()}]
  return [inst],blocks,I.B.gram_specs()
 def test_dual_checkpoint_and_exact_admission(self):
  instances,blocks,specs=self.fixture();result=D.propose(instances,blocks,gram_specs=specs,max_rows=2500,time_limit=180)
  self.assertEqual(result['status'],'exact_separator')
  self.assertTrue(I.verify_dual_checkpoint(result['proposal_checkpoint'],instances,blocks,specs)['verified'])
  self.assertTrue(I.verify_compressed_dual(instances,blocks,specs,result)['verified'])
  for key,value in [('row_order_hash','bad'),('support',[999999]),('exact_target_hash','bad')]:
   bad=copy.deepcopy(result['proposal_checkpoint']);bad[key]=value
   with self.assertRaises(ValueError):I.verify_dual_checkpoint(bad,instances,blocks,specs)
 def test_stage_decisions(self):
  self.assertEqual(I.expected_plan('exact_separator'),[])
  self.assertEqual(I.expected_plan('uncertified'),[dict(phase='primal',program=I.PROGRAM)])
  self.assertEqual([r['X'] for r in I.expected_plan('missing_resource','finite_PSD_certificate')],[8,13])
  self.assertEqual(I.expected_plan('uncertified','missing_resource'),[])
 def test_resource_tamper(self):
  e=dict(cost=dict(workers=1,requested_workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False),results=[dict(index=0,status='available')])
  self.assertTrue(I.verify_runtime(e,1));e['cost']['worker_memory_limit_enforced']=False
  with self.assertRaises(ValueError):I.verify_runtime(e,1)
 def test_frozen_contract_matches_runner(self):
  import run_complete_gram_search as R
  for key in ['PROGRAM','LIMITS','SOLVER_LIMITS','DUAL_LIMITS','PARALLEL','TESTS']:self.assertEqual(getattr(I,key),getattr(R,key))
 def test_fixed_candidate_tamper(self):
  t=dict(status='finite_PSD_certificate',synthesis=dict(weights={'x':'1'},grams={'g':[['1']]}));r=dict(status='finite_PSD_certificate',program=I.PROGRAM,scales=[8],refitted=False,synthesis=copy.deepcopy(t['synthesis']))
  self.assertTrue(I.verify_fixed_transfer(t,r));r['synthesis']['grams']['g'][0][0]='2'
  with self.assertRaises(ValueError):I.verify_fixed_transfer(t,r)
if __name__=='__main__':unittest.main()
