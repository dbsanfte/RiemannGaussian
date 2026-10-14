import copy,tempfile,unittest
import prime_pair_forcing_search as s
import check_prime_pair_forcing_run as c
from test_run_prime_pair_forcing import synthetic_profile
class Tests(unittest.TestCase):
 def test_interval_decisions_and_unknown_levels_independently_match(self):
  p=synthetic_profile();program=dict(target='mu',cutoff=s.CUTOFFS[0],constants={'2':'0'})
  self.assertEqual(c.exact_score(program,p,[1,2],[2,17]),s.score(program,p,[1,2],[2,17]))
  score=c.exact_score(program,p,[1,2],[2,17]);self.assertEqual(score['unresolved_intervals'],2);self.assertEqual(score['missing_cases'],2)
  program['constants']['2']='1';self.assertEqual(c.exact_score(program,p,[1,2],[2])['finite_passes'],2)
 def test_archive_detects_missing_proposals_and_changed_lower_bound_fit(self):
  p=synthetic_profile();f=s.candidate_factory(p,'mu',[1,2],[2]);self.assertTrue(c.check_archive(f,p,s.CUTOFFS,[1,2],[2])['verified'])
  bad=copy.deepcopy(f);bad['proposal_archive'].pop()
  with self.assertRaises(ValueError):c.check_archive(bad,p,s.CUTOFFS,[1,2],[2])
  bad=copy.deepcopy(f);bad['candidates'][0]['program']['constants']['2']='0'
  with self.assertRaises(ValueError):c.check_archive(bad,p,s.CUTOFFS,[1,2],[2])
  with self.assertRaises(ValueError):c.no_promotions({'full_signed_bound_proved':True})
 def test_missing_run_cannot_certify(self):
  with tempfile.TemporaryDirectory() as d:
   with self.assertRaises(FileNotFoundError):c.audit_run(d)
if __name__=='__main__':unittest.main()
