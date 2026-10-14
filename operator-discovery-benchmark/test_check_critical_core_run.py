import copy,tempfile,unittest
from fractions import Fraction as F
import critical_core_grammar as g
import critical_core_search as s
import check_critical_core_run as c
class Tests(unittest.TestCase):
 def test_scores_independent_with_unseen_levels_and_signed_cross_terms(self):
  t=dict(r=1,l=1,filter=[dict(divisor=1,weight='1')]);features=s.FEATURES
  p=g.profile([1,2,4,8,16], [t],features)
  program=dict(target=t,corrections=[dict(feature=features[0],weight='-3/2')]);program['constants']=s.fit_constants(program,p,features,[1,2,4],[2,3])[0]
  a=s.score(program,p,features,[4,8],[2,3,17]);b=c.exact_score(program,p,features,[4,8],[2,3,17]);self.assertEqual(a,b)
  self.assertEqual(b['modes']['direct']['missing_cases'],2)
  c.no_promotions(b)
 def test_bridge_requires_recovery_before_mellin(self):
  t=dict(r=1,l=1,filter=[dict(divisor=1,weight='1')]);program=dict(target=t,corrections=[dict(feature=s.FEATURES[0],weight='-2')])
  rec=g.recovery_certificate(t,program['corrections']);item=dict(exact_program=program,additive_recovery=rec,conditional_admission=rec['conditional_original_G_pole_bridge'])
  self.assertTrue(c.check_additive_recovery(item));self.assertEqual(c.pole_bridge(t)['retained_pole_order_at_least'],2)
  broken=copy.deepcopy(item);broken['additive_recovery']['ordinary_Mellin_pole_argument_applies_directly_to_H']=True
  with self.assertRaises(ValueError):c.check_additive_recovery(broken)
  broken=copy.deepcopy(item);broken['exact_program']['corrections'][0]['weight']='1'
  with self.assertRaises(ValueError):c.check_additive_recovery(broken)
  with self.assertRaises(ValueError):c.no_promotions({'nested':[{'actual_H_energy_bound_proved':True}]})
 def test_missing_run_cannot_certify(self):
  with tempfile.TemporaryDirectory() as d:
   with self.assertRaises(FileNotFoundError):c.audit_run(d)
if __name__=='__main__':unittest.main()
