"""Synthetic runner contracts only; no actual large-data scoring."""
import tempfile,unittest
from pathlib import Path
import run_factor_region as r
import factor_region_search as s
class Tests(unittest.TestCase):
 def test_selection_exact_rank_origins_and_dedup(self):
  t=r.TARGETS[1];tid=s.digest(t);f=s.dictionary(r.SCHEMES[:1])[0]
  def make(weight,C,origins):
   terms=[] if not weight else [dict(feature=f,weight=str(weight))]
   program=dict(target=t,terms=terms,constants={'2':str(C)})
   return dict(program_id=s.digest(program),program=program,origins=[dict(kind=k) for k in origins])
  a=make(0,2,['baseline','lp']);b=make(1,1,['singleton','lp']);c=make(4,1,['singleton'])
  candidates=[a,b,c];results=[dict(program_id=c['program_id'],score=dict(missing_cases=0,finite_failures=0)) for c in candidates]
  queue,decisions=r.select([dict(target_id=tid,candidates=candidates)],results)
  self.assertEqual(next(x for x in decisions if x['group']=='all')['selected_id'],b['program_id'])
  q=next(x for x in queue if x['program_id']==b['program_id']);self.assertEqual(q['selection_origins'],['all','singleton','lp'])
  self.assertEqual(len(queue),2);self.assertTrue(all(x['exact_program_sha256']==s.digest(x['exact_program']) for x in queue))
  self.assertTrue(all(x['conditional_admission']['estimate_proved'] is False for x in queue))
  import check_factor_region_run as independent
  independent_queue,independent_decisions=independent.selected([dict(target_id=tid,candidates=candidates)],results)
  self.assertEqual(decisions,independent_decisions)
  self.assertEqual({x['program_id']:x['selection_origins'] for x in queue},{pid:v['origins'] for pid,v in independent_queue.items()})
 def test_runner_checker_source_and_dictionary_contract(self):
  import check_factor_region_run as independent
  self.assertEqual(r.CODE,independent.CODE)
  self.assertEqual(len(r.CODE),18)
  spec=r.specification()
  self.assertEqual(set(spec['code_sha256']),set(independent.CODE))
  self.assertEqual(spec['features'],independent.independent.feature_dictionary(spec['schemes']))
  self.assertEqual(spec['dictionary_sha256'],s.digest(spec['features']))
  self.assertEqual(spec['selection_groups'],['baseline','all','singleton','lp'])
 def test_postseal_generation_from_protocol(self):
  spec=dict(final_levels=[3,12,17,29],final_generation=dict(fixed=[32768,65536],odd_min=50001,odd_count=5000))
  c=r.final_cases(spec,'f'*64)
  self.assertEqual(c['base_scales'],sorted([32768,65536,50001+2*(int('f'*16,16)%5000)]))
  self.assertEqual(c['protocol_sha256'],s.digest(spec));self.assertEqual(c['seal_sha256'],'f'*64);self.assertTrue(c['generated_after_seal'])
  self.assertEqual(c,r.final_cases(spec,'f'*64));self.assertEqual(c['levels'],spec['final_levels'])
 def test_full_synthetic_worker_guard_and_byte_replay(self):
  v=[2,-1,3,-2,0,1,-1,2,-3];rows=[]
  for target in r.TARGETS:
   for scheme in r.SCHEMES:
    for X in (1,2,4):
     mass=sum(n*n for n in range(X,2*X));rows.append(dict(X=X,target_id=s.digest(target),scheme_id=s.digest(scheme),gram_numerators=[[mass*a*b for b in v] for a in v],gram_denominator=X*X,E=str(__import__('fractions').Fraction(mass,X*X))))
  table=s.feature_table(rows,r.TARGETS,r.SCHEMES);self.assertEqual(table['status'],'available')
  with tempfile.TemporaryDirectory() as td:
   d=Path(td);spec=dict(code_sha256={},targets=r.TARGETS,schemes=r.SCHEMES,features=s.dictionary(r.SCHEMES),training_scales=[1,2],validation_scales=[1,2],levels=[2],budgets=dict(bit=1000000))
   r.write(d/'protocol.json',spec)
   data=dict(protocol_sha256=s.digest(spec),base_scales=[1,2],scales=[1,2,4],table=table)
   for name in r.INPUTS:r.write(d/name,data)
   r.worker(d);batch=r.read(d/'candidate_batch.json')
   self.assertEqual(len(batch['factories']),3);self.assertEqual(sum(len(f['proposal_archive']) for f in batch['factories']),3951)
   self.assertTrue(all(batch['access_denials'].values()))
   self.assertTrue(all(c['program_id']==s.digest(c['program']) for f in batch['factories'] for c in f['candidates']))
   with self.assertRaises(FileExistsError):r.worker(d)
   replay=r.replay(d);self.assertTrue(all(replay['files_match'].values()));self.assertFalse(replay['independent_implementation']);self.assertFalse(replay['python_guard_is_OS_sandbox'])
if __name__=='__main__':unittest.main()
