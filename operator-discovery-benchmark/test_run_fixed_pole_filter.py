"""Synthetic workflow regressions; no large actual arithmetic scoring."""
import tempfile,unittest
from pathlib import Path
import run_fixed_pole_filter as runner
import fixed_pole_filter_search as search
class Tests(unittest.TestCase):
 def test_normalized_cross_target_selection_and_dedup(self):
  def make(t,C,kind='baseline'):
   filt=[dict(divisor=1,weight='1')]
   if kind!='baseline':filt+=[dict(divisor=2,weight='-1')]
   program=dict(target=t,filter=filt,constants={m:{'2':str(C)} for m in ('direct','innovation')})
   origins=[dict(kind=kind)]
   if kind!='baseline':origins.append(dict(kind='composition_square'))
   return dict(program_id=runner.digest(program),program=program,origins=origins,admission=dict(estimate_proved=False,RH_proved=False))
  candidates=[make(t,100 if t==dict(r=2,l=1) else 10) for t in search.TARGETS]
  a=make(dict(r=1,l=1),2,'inferred');b=make(dict(r=2,l=1),10,'inferred');candidates+=[a,b]
  results=[dict(program_id=c['program_id'],score=dict(modes={m:dict(missing_cases=0,finite_failures=0) for m in ('direct','innovation')})) for c in candidates]
  queue,decisions=runner.select(dict(candidates=candidates),results)
  self.assertEqual(next(x for x in decisions if x['group']['kind']=='inferred')['selected_id'],b['program_id'])
  self.assertEqual(next(x for x in decisions if x['group']['kind']=='composition_square')['selected_id'],b['program_id'])
  q=next(x for x in queue if x['program_id']==b['program_id']);self.assertEqual(len(q['selection_origins']),3)
  self.assertEqual(len(queue),len({x['program_id'] for x in queue}))
  self.assertTrue(all(x['exact_program_sha256']==runner.digest(x['exact_program']) and x['precise_claim_sha256']==runner.digest(runner.CLAIM) for x in queue))
 def test_postseal_cases_bindings(self):
  spec=dict(final_levels=[3,12,17,29]);h='f'*64;c=runner.final_cases(spec,h)
  self.assertEqual(c['protocol_sha256'],runner.digest(spec));self.assertEqual(c['seal_sha256'],h);self.assertTrue(c['generated_after_seal'])
  self.assertEqual(c['base_scales'],sorted([32768,65536,40001+2*(int(h[:16],16)%5000)]))
  self.assertEqual(c,runner.final_cases(spec,h));self.assertEqual(c['levels'],spec['final_levels'])
 def test_synthetic_worker_guard_full_archive_and_replay(self):
  prefix=list(range(16));cov=search.covariance_table(prefix,[1,2,4],use_numpy=False)['value']
  data=dict(status='available',value=dict(base_scales=[1,2],scales=[1,2,4],targets=[dict(target=t,coefficients=[0]*16,prefix=prefix,**cov) for t in search.TARGETS]))
  with tempfile.TemporaryDirectory() as td:
   d=Path(td);spec=dict(code_sha256={},training_scales=[1,2],validation_scales=[1,2],levels=[2],budgets=dict(bit=1000000))
   runner.write(d/'protocol.json',spec)
   for name in runner.INPUTS:runner.write(d/name,dict(protocol_sha256=runner.digest(spec),data=data))
   runner.worker(d)
   batch=runner.read(d/'candidate_batch.json');factory=batch['factory']
   self.assertTrue(all(batch['access_denials'].values()))
   self.assertEqual(len(factory['proposal_archive']),3959)
   self.assertTrue(factory['candidates'])
   self.assertTrue(all(c['program_id']==runner.digest(c['program']) for c in factory['candidates']))
   self.assertEqual(len(factory['candidates']),len({c['program_id'] for c in factory['candidates']}))
   with self.assertRaises(FileExistsError):runner.worker(d)
   replay=runner.replay(d);self.assertTrue(all(replay['files_match'].values()))
   self.assertFalse(replay['independent_implementation']);self.assertFalse(replay['python_guard_is_OS_sandbox'])
if __name__=='__main__':unittest.main()
