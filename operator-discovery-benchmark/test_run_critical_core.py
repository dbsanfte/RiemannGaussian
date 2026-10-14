"""Synthetic contracts; no actual scoring above the pre-freeze fixture limit."""
import tempfile,unittest
from fractions import Fraction as F
from pathlib import Path
import run_critical_core as r
import critical_core_search as s
class Tests(unittest.TestCase):
 def test_selection_prioritizes_direct_validation_and_keeps_baseline(self):
  t=r.TARGETS[1];feature=s.FEATURES[0]
  def make(w,C,origins):
   program=dict(target=t,corrections=[] if not w else [dict(feature=feature,weight=str(w))],constants={m:{'2':str(C)} for m in ('direct','innovation')})
   return dict(program_id=s.digest(program),program=program,origins=[dict(kind=k) for k in origins])
  a=make(0,1,['baseline']);b=make(-1,1,['singleton','ridge_fit']);c=make(4,1,['singleton'])
  candidates=[a,b,c]
  def score(E):return dict(modes={'direct':dict(missing_cases=0,finite_failures=0,observations=[dict(X=2,observed=str(E))])})
  results=[dict(program_id=c['program_id'],score=score(E)) for c,E in zip(candidates,[2,1,3])]
  queue,decisions=r.select([dict(target_id=s.digest(t),candidates=candidates)],results)
  self.assertEqual(next(x for x in decisions if x['group']=='all')['selected_id'],b['program_id'])
  self.assertEqual(len(queue),2)
  q=next(x for x in queue if x['program_id']==b['program_id']);self.assertEqual(q['selection_origins'],['all','singleton','ridge_fit'])
  self.assertFalse(q['additive_recovery']['actual_H_energy_bound_proved'])
  import check_critical_core_run as checker
  selected,expected=checker.selected([dict(target_id=s.digest(t),candidates=candidates)],results)
  self.assertEqual(decisions,expected);self.assertEqual(set(selected),{x['program_id'] for x in queue})
  for item in queue:checker.check_additive_recovery(item)
 def test_runner_checker_manifest_and_postseal_generation(self):
  import check_critical_core_run as checker
  self.assertEqual(r.CODE,checker.CODE)
  spec=r.specification();self.assertEqual(set(spec['code_sha256']),set(r.CODE))
  self.assertEqual(spec['features'],[checker.independent.feature_descriptor(f) for f in checker.independent.FEATURES])
  cases=r.final_cases(spec,'f'*64);self.assertEqual(cases['base_scales'],sorted([131072,262144,170001+2*(int('f'*16,16)%10000)]))
  self.assertEqual(cases['levels'],[3,12,17,29]);self.assertTrue(cases['generated_after_seal'])
 def test_synthetic_worker_guard_and_byte_replay(self):
  rows=[];features=s.FEATURES;v=[1]+[(-1)**i*(i+1) for i in range(len(features))]
  for t in r.TARGETS:
   for X in (1,2,4):
    rows.append(dict(X=X,target_id=s.digest(t),feature_ids=['base_G']+[f['feature_id'] for f in features],gram_numerators=[[X*a*b for b in v] for a in v],gram_base_denominator=X*X,correction_denominators=[1]*len(v)))
  profile=dict(status='available',value=dict(rows=rows,features=features))
  with tempfile.TemporaryDirectory() as td:
   d=Path(td);spec=dict(code_sha256={},targets=r.TARGETS,features=features,training_scales=[1,2],validation_scales=[1,2],levels=[2],budgets=dict(bit=1000000))
   r.write(d/'protocol.json',spec);data=dict(protocol_sha256=s.digest(spec),base_scales=[1,2],scales=[1,2,4],profile=profile)
   for n in r.INPUTS:r.write(d/n,data)
   r.worker(d);batch=r.read(d/'candidate_batch.json');self.assertTrue(all(batch['access_denials'].values()))
   self.assertEqual(sum(len(f['proposal_archive']) for f in batch['factories']),363)
   with self.assertRaises(FileExistsError):r.worker(d)
   self.assertTrue(all(r.replay(d)['files_match'].values()))
if __name__=='__main__':unittest.main()
