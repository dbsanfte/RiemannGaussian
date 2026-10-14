"""Synthetic workflow contracts; no large actual responses before source freeze."""
import tempfile,unittest
from pathlib import Path
import run_prime_pair_forcing as r
import prime_pair_forcing_search as s
import prime_pair_forcing as a

def synthetic_profile():
 rows=[]
 for target in r.TARGETS:
  for cutoff in r.CUTOFFS:
   for X in (1,2):
    rows.append(dict(X=X,target=target,cutoff=cutoff,normalized_negative_remainder=dict(lower='-1',upper='1'),component_certificate=a.prefix_certificate(target,cutoff),coverage=dict(prefix_triples=1,remainder_triples=1,all_triples=2,complete=True),original_energy=dict(A_X=X*X,A_2X=4*X*X)))
 return dict(status='available',value=dict(rows=rows))
class Tests(unittest.TestCase):
 def test_independent_selection_excludes_unsupported_power_cutoffs(self):
  import check_prime_pair_forcing_run as c
  p=synthetic_profile();factories=[s.candidate_factory(p,t,[1,2],[2]) for t in r.TARGETS]
  results=[dict(program_id=x['program_id'],score=s.score(x['program'],p,[1,2],[2])) for f in factories for x in f['candidates']]
  queue,decisions=r.select(factories,results);expected,other=c.selected(factories,results)
  self.assertEqual(decisions,other);self.assertEqual({x['program_id'] for x in queue},set(expected));self.assertEqual(len(queue),6)
  self.assertTrue(all(x['prefix_certificate']['cofinal_critical_component_bound'] for x in queue))
  self.assertTrue(all(x['exact_program']['cutoff']['kind']!='power' for x in queue))
  for f in factories:c.check_archive(f,p,r.CUTOFFS,[1,2],[2])
 def test_manifest_and_postseal_cases(self):
  import check_prime_pair_forcing_run as c
  self.assertEqual(r.CODE,c.CODE);self.assertEqual(r.CUTOFFS,c.CUTOFFS)
  spec=r.specification();cases=r.final_cases(spec,'f'*64)
  self.assertEqual(cases['base_scales'],sorted([512,1024,769+2*(int('f'*16,16)%50)]));self.assertTrue(cases['generated_after_seal'])
 def test_worker_guard_and_replay(self):
  with tempfile.TemporaryDirectory() as td:
   d=Path(td);spec=dict(code_sha256={},targets=r.TARGETS,cutoffs=r.CUTOFFS,training_scales=[1,2],validation_scales=[1,2],levels=[2],budgets=dict(bit=1000000))
   r.write(d/'protocol.json',spec);data=dict(protocol_sha256=s.digest(spec),base_scales=[1,2],scales=[1,2],profile=synthetic_profile())
   for n in r.INPUTS:r.write(d/n,data)
   r.worker(d);batch=r.read(d/'candidate_batch.json');self.assertTrue(all(batch['access_denials'].values()));self.assertEqual(sum(len(f['proposal_archive']) for f in batch['factories']),28)
   with self.assertRaises(FileExistsError):r.worker(d)
   self.assertTrue(all(r.replay(d)['files_match'].values()))
if __name__=='__main__':unittest.main()
