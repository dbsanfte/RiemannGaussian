import unittest,os,time
import detector_parallel as P
# Importable anonymous worker. Every job is executed inside a process, even workers=1.
def fixture_worker(job):
 if job.get('kind')=='resource':raise OverflowError('fixture cap')
 if job.get('kind')=='error':raise ValueError('fixture invalid')
 if job.get('kind')=='delay':time.sleep(job['seconds'])
 return dict(result=job['n']**2,pid=os.getpid(),threads={k:os.environ.get(k)for k in P.THREAD_VARIABLES})
class Tests(unittest.TestCase):
 def test_process_order_limits_and_failures(self):
  parent=os.getpid();out=P.run_jobs([dict(n=3),dict(kind='resource'),dict(n=2),dict(kind='error')],worker='test_detector_parallel:fixture_worker',workers=2,max_in_flight=2)
  self.assertEqual([r['status']for r in out['results']],['available','missing_resource','available','error']);self.assertEqual(out['results'][0]['value']['result'],9);self.assertNotEqual(out['results'][0]['value']['pid'],parent);self.assertTrue(all(v=='1'for v in out['results'][0]['value']['threads'].values()));self.assertFalse(out['cost']['serial_fallback'])
 def test_global_timeout_preserved(self):
  out=P.run_jobs([dict(kind='delay',seconds=2,n=1),dict(n=2)],worker='test_detector_parallel:fixture_worker',workers=1,max_in_flight=1,timeout_seconds=.1)
  self.assertEqual([r['status']for r in out['results']],['missing_resource','missing_resource'])
 def test_explicit_memory_and_queue_bounds(self):
  with self.assertRaises(ValueError):P.run_jobs([dict(n=1)],worker='test_detector_parallel:fixture_worker',workers=1,max_in_flight=3)
  with self.assertRaises(ValueError):P.run_jobs([],worker='test_detector_parallel:fixture_worker',memory_budget_bytes=100)
  result=P.run_jobs([dict(n=1)],worker='test_detector_parallel:fixture_worker',worker_memory_bytes=512*1024**2,memory_budget_bytes=512*1024**2)
  self.assertEqual(result['results'][0]['status'],'available');self.assertTrue(result['cost']['worker_memory_limit_enforced'])
 def test_aggregate_reservation_is_deterministic(self):
  r=P.run_jobs([dict(n=1),dict(n=2)],worker='test_detector_parallel:fixture_worker',max_total_result_bytes=10)
  self.assertEqual([v['status']for v in r['results']],['missing_resource','missing_resource']);self.assertEqual(r['cost']['available'],0)
 def test_cpu_and_payload_bounds(self):
  self.assertEqual(P._quota_cpu_count('250000 100000'),2);self.assertIsNone(P._quota_cpu_count('max 100000'));self.assertGreaterEqual(P.available_cpu_count(),1)
  with self.assertRaises(OverflowError):P.run_jobs([dict(n='x'*100)],worker='test_detector_parallel:fixture_worker',max_payload_bytes=20)
  with self.assertRaises(ValueError):P.run_jobs([],worker='bad',workers=1)
if __name__=='__main__':unittest.main()
