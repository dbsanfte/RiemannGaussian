import copy
import unittest
from unittest.mock import patch
import check_joint_gram_transfer_retry as I
class Retry(unittest.TestCase):
 def test_resources_only_memory(self):
  p=dict(parallel=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=600),limits=dict(time_limit=180),no_new_float_search=True,same_candidate=True,refitted=False,scales=[13])
  self.assertTrue(I.verify_resources(p)['verified'])
  for key,value in [('workers',2),('worker_memory_bytes',2*1024**3),('timeout_seconds',601)]:
   q=copy.deepcopy(p);q['parallel'][key]=value
   with self.assertRaises(ValueError):I.verify_resources(q)
 def test_actual_execution_tamper(self):
  result=dict(status='finite_PSD_certificate',cost=dict(pid=1))
  execution=dict(cost=dict(worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,workers=1,requested_workers=1,available=1,missing=0,errors=0,worker_memory_limit_enforced=True,serial_fallback=False,numerical_threads_per_worker=1),results=[dict(index=0,status='available',value=dict(file='result.json',sha256='hash',status=result['status'],cost=result['cost'],**I.FLAGS))])
  self.assertTrue(I.verify_execution(execution,result,'hash')['verified'])
  for key,value in [('worker_memory_bytes',2*1024**3),('memory_budget_bytes',2*1024**3),('workers',2),('worker_memory_limit_enforced',False)]:
   bad=copy.deepcopy(execution);bad['cost'][key]=value
   with self.assertRaises(ValueError):I.verify_execution(bad,result,'hash')
  for key,value in [('sha256','bad'),('status','missing_resource'),('cost',{})]:
   bad=copy.deepcopy(execution);bad['results'][0]['value'][key]=value
   with self.assertRaises(ValueError):I.verify_execution(bad,result,'hash')
 def fixture(self):
  program=dict(target='mu',q=6,C=1,claim='unsigned_calibration');inst=dict(target='mu',horizon=1,lhs=[],square_groups=[],relation_groups=[])
  grams={k:[['0']*n for _ in range(n)] for k,n in I.B.gram_specs().items()};blocks={k:[] for k in grams};built=dict(instance=inst,gram_blocks=blocks,gram_archive={},factor_archive={},divisor_archive={},cell_archive={},dictionary_sha256='test')
  gp={k:dict(polynomial=[],squares=[],decomposition=dict(matrix=g)) for k,g in grams.items()}
  cert=dict(target='mu',horizon=1,lhs=[],squares=[],relations=[])
  fitted=dict(status='finite_PSD_certificate',weights=dict(square_weights=[],relation_weights=[]),grams=grams,gram_specs=I.B.gram_specs(),source_hashes=[I.digest(inst)],gram_block_hashes=[I.digest(blocks)],constant_slacks=['0'],certificates=[dict(certificate=cert,Gram_proofs=gp)],**I.FLAGS)
  original=dict(reason='MemoryError',phase='final',index=2,status='missing_resource',scales=[13],program=program,case_hashes=[I.digest(inst)],gram_block_hashes=[I.digest(blocks)],gram_archive_hashes=[I.digest({})])
  for key in ['ordinary_case_hashes','factor_archive_hashes','divisor_archive_hashes','cell_archive_hashes']:original[key]=[I.digest(inst if key=='ordinary_case_hashes' else {})]
  original.update(dictionary_sha256='test',gram_specs=I.B.gram_specs())
  train=dict(status='finite_PSD_certificate',program=program,synthesis=copy.deepcopy(fitted));result=dict(program=program,scales=[13],refitted=False,synthesis=fitted,case_hashes=original['case_hashes'],gram_block_hashes=original['gram_block_hashes'],gram_archive_hashes=original['gram_archive_hashes'])
  for key in ['ordinary_case_hashes','factor_archive_hashes','divisor_archive_hashes','cell_archive_hashes','dictionary_sha256','gram_specs']:result[key]=original[key]
  return built,original,train,result
 def test_fixed_identity_and_candidate_tampering(self):
  b,o,t,r=self.fixture()
  with patch.object(I.B,'build',return_value=b):self.assertTrue(I.verify_fixed_transfer(o,t,r)['verified'])
  for field,value in [('scales',[8]),('refitted',True),('case_hashes',['bad'])]:
   q=copy.deepcopy(r);q[field]=value
   with patch.object(I.B,'build',return_value=b),self.assertRaises(ValueError):I.verify_fixed_transfer(o,t,q)
  r['synthesis']['weights']['square_weights']=['1']
  with self.assertRaises(ValueError):I.verify_fixed_transfer(o,t,r)
 def test_nonzero_Gram_and_dropped_proof(self):
  b,o,t,r=self.fixture();t['synthesis']['grams']['joint_parent'][1][1]='1';r['synthesis']['grams']['joint_parent'][1][1]='1'
  with self.assertRaises(ValueError):I.verify_fixed_transfer(o,t,r)
  b,o,t,r=self.fixture();r['synthesis']['certificates'][0]['Gram_proofs'].pop('old_child')
  with patch.object(I.B,'build',return_value=b),self.assertRaises(ValueError):I.verify_fixed_transfer(o,t,r)
if __name__=='__main__':unittest.main()
