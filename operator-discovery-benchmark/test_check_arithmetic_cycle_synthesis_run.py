import unittest
import check_arithmetic_cycle_synthesis_run as c
class Tests(unittest.TestCase):
 def test_root_boundaries(self):
  self.assertEqual(c.rootceil(1,10**30),1);self.assertEqual(c.rootceil(2,10**30),2);self.assertEqual(c.rootceil(64,3),4);self.assertEqual(c.rootceil(65,3),5)
 def test_negative_attempt_complete_target(self):
  m=c.mathcheck;X=1;H=9;lhs=m.canonical(m.add({():c.F(2)},m.parse(m.complete_defect(X),H),c.F(-1)))
  a=dict(case=dict(target='mu',X=X,q=2,C='2',mode='none'),template=dict(horizon=H,lhs=lhs,square_basis=[],relation_columns=[]),synthesis=dict(status='no_certificate_found'))
  self.assertFalse(c.verify_attempt(a)['finite_verified']);a['template']['lhs']=[]
  with self.assertRaises(ValueError):c.verify_attempt(a)
 def test_no_promotion(self):
  with self.assertRaises(ValueError):c.no_promotions({'nested':[{'RH_proved':True}]})
  c.no_promotions({'global_bound_proved':False})
 def test_independent_template_generator_and_controls(self):
  import run_arithmetic_cycle_synthesis as producer
  for target in ('mu','c'):
   for mode in ('atomic_local','grouped_cycles'):
    case=dict(target=target,X=2,q=6,C=4,mode=mode)
    a=c.independent_template(case);b=producer.template(case)
    for k,v in a.items():self.assertEqual(v,b[k])
  import arithmetic_cycle_controls as controls
  spec=dict(P=[2],pair_limit=4,row_limit=8,scales=[1,2])
  self.assertTrue(c.verify_controls(controls.audit_counterfeit(**spec),spec)['verified'])
 def test_calibration_template_tamper(self):
  cal=dict(lhs=[dict(m=[2,3,6],c='1')],square_basis=[[dict(m=[],c='1')],[dict(m=[2],c='1')],[dict(m=[3],c='1')],[dict(m=[6],c='1')],[dict(m=[2,3],c='1')]],synthesis=dict(status='no_certificate_found'))
  cal['relation_columns']=[[dict(spec=dict(kind='coprime_product',a=2,b=3),multiplier=p)] for p in cal['square_basis']]
  c.verify_calibration(cal);cal['lhs']=[]
  with self.assertRaises(ValueError):c.verify_calibration(cal)
 def test_post_synthesis_actual_truth(self):
  x=c.actual_truth(dict(target='mu',X=2,q=2,C=1));self.assertEqual(x['Delta'],6);self.assertEqual(x['D'],'8');self.assertTrue(x['bound_true'])
  x=c.actual_truth(dict(target='c',X=1,q=2,C=1));self.assertEqual(x['Delta'],6);self.assertFalse(x['bound_true'])
if __name__=='__main__':unittest.main()
