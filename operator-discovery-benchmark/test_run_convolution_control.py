"""Development orchestration fixtures; no actual arithmetic search run."""
import tempfile,unittest
from pathlib import Path
import run_convolution_control as r
import convolution_control_search as s
class Tests(unittest.TestCase):
 def test_final_generation_after_seal_deterministic(self):
  spec=dict(final_levels=[3,12,13,17])
  c=r.final_cases(spec,'0'*64);self.assertEqual(c['base_scales'],[8192,9001,16384]);self.assertTrue(c['generated_after_seal'])
  c=r.final_cases(spec,'f'*64);odd=next(x for x in c['base_scales'] if x%2)
  self.assertTrue(9001<=odd<=11999);self.assertEqual(c,r.final_cases(spec,'f'*64))
 def test_diversity_alias_and_exact_rank(self):
  fid=s.FEATURE_DICTIONARY[0]['feature_id']
  def c(pid,constants,origins,terms=[]):return dict(program_id=pid,program=dict(terms=terms,constants=constants),origins=origins)
  candidates=[c('a',{'2':'1/3'},[dict(kind='baseline'),dict(kind='lp',group='all')]),c('b',{'2':'1/2'},[dict(kind='singleton',feature_id=fid)]),c('c',{'2':None},[dict(kind='lp',group='gram')])]
  results=[dict(program_id=c['program_id'],score=dict(missing_cases=0,finite_failures=0)) for c in candidates]
  queue,decisions=r.select(dict(candidates=candidates),results)
  self.assertEqual([x['program_id'] for x in queue],['a','b']);self.assertEqual(queue[0]['selection_origins'],['baseline','all'])
  self.assertEqual(next(x for x in decisions if x['group']=='gram')['selected_id'],'b')
  self.assertEqual(queue[0]['exact_program_sha256'],r.digest(queue[0]['exact_program']))
 def test_write_exclusive_and_worker_refuses_seal(self):
  with tempfile.TemporaryDirectory() as td:
   d=Path(td);r.write(d/'protocol.json',{})
   with self.assertRaises(FileExistsError):r.write(d/'protocol.json',{})
   r.write(d/'seal.json',{})
   with self.assertRaises(FileExistsError):r.worker(d)
 def test_synthetic_worker_guard_and_byte_replay(self):
  with tempfile.TemporaryDirectory() as td:
   d=Path(td);spec=dict(training_scales=[1],validation_scales=[1],levels=[2],budgets=dict(bit=1000000))
   r.write(d/'protocol.json',spec)
   features={f['feature_id']:'0' for f in s.FEATURE_DICTIONARY}
   table=dict(status='available',value=dict(rows=[dict(X=X,E='0',features=features) for X in (1,2)]))
   data=dict(protocol_sha256=r.digest(spec),base_scales=[1],table=table)
   for name in r.INPUTS:r.write(d/name,data)
   r.worker(d)
   self.assertTrue(all(r.read(d/'candidate_batch.json')['access_denials'].values()))
   self.assertTrue(all(r.replay_worker(d)['files_match'].values()))
if __name__=='__main__':unittest.main()
