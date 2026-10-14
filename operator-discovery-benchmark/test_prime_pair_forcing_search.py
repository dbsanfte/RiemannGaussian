import unittest
from prime_pair_forcing_search import *
def fixture(lower='1',upper='3'):
 return {'status':'available','value':{'rows':[dict(target='mu',cutoff=c,X=X,normalized_negative_remainder=dict(lower=lower,upper=upper),coverage=dict(prefix_nonempty=c.get('value')!=0,remainder_nonempty=True)) for c in CUTOFFS for X in (1,2)]}}
class Tests(unittest.TestCase):
 def test_interval_decisions_unknown_level(self):
  p=dict(target='mu',cutoff=CUTOFFS[0],constants={'2':'2','3':'0'})
  s=score(p,fixture(),[1],[2,3,17]);self.assertEqual([o['status'] for o in s['observations']],['unresolved_interval','fail','missing']);self.assertEqual(s['finite_passes'],0)
  p['constants']['2']='3';self.assertEqual(score(p,fixture(),[1],[2])['finite_passes'],1)
 def test_conservative_fit_and_missing(self):
  p=dict(target='mu',cutoff=CUTOFFS[0],constants={});c,e=fit_constants(p,fixture(),[1,2],[2]);self.assertEqual(c,{'2':'3'})
  c,e=fit_constants(p,fixture(),[1,3],[2]);self.assertIsNone(c['2'])
 def test_dictionary_and_admission(self):
  f=candidate_factory(fixture(),'mu',[1,2],[2]);self.assertEqual(len(f['proposal_archive']),14);self.assertEqual(len({c['program_id'] for c in f['candidates']}),14)
  self.assertEqual(sum(c['conditional_auxiliary']['auxiliary_bound_admitted'] for c in f['candidates']),10)
  self.assertTrue(all(c['training_score']['finite_passes']==2 for c in f['candidates']))
 def test_supplied_certificate_binding_and_auxiliary_cost(self):
  from prime_pair_forcing import prefix_certificate
  for target in ('mu','c'):
   for c in CUTOFFS:
    self.assertEqual(auxiliary_certificate(target,c),prefix_certificate(target,c))
    cert=auxiliary_certificate(target,c)
    if cert['cofinal_critical_component_bound']:
     self.assertEqual(auxiliary_cost(target,c,1),F(cert['scalar'])*3**cert['log_4X_power'])
    else:self.assertIsNone(auxiliary_cost(target,c,1))
 def test_exact_inputs_resource_and_negative_interval(self):
  with self.assertRaises(TypeError):cutoff_spec({'kind':'power','power':.5})
  with self.assertRaises(ValueError):interval({'lower':'2','upper':'1'})
  p=dict(target='mu',cutoff=CUTOFFS[0],constants={});c,_=fit_constants(p,fixture('-3','-1'),[1,2],[2]);self.assertEqual(c,{'2':'0'})
  from unittest.mock import patch
  from detector_safe_evaluation import EvaluationResult,Status
  p['constants']={'2':'1'}
  with patch('prime_pair_forcing_search.rational_ceiling',return_value=EvaluationResult(Status.MISSING,reason='resource')):
   self.assertEqual(score(p,fixture(),[2],[2])['missing_cases'],1)
if __name__=='__main__':unittest.main()
