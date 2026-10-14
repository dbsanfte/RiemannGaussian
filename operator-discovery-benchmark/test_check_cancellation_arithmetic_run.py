import unittest
import check_cancellation_arithmetic_run as C
class Tests(unittest.TestCase):
 def test_complete_independent_extension(self):
  import cancellation_arithmetic_templates as producer
  self.assertEqual(C.descriptors(),producer.descriptors())
  for X in (1,2):
   p=dict(target='mu',q=3,C=8,claim='critical',allow_constant_slack=True,dictionary_mode='extended');a=C.build(p,X);b=producer.build_instance('mu',X,3,8)
   for k,v in a.items():self.assertEqual(v,b[k],k)
 def test_baseline_lhs_retained_and_ast_no_sign_lookup(self):
  p=dict(target='mu',q=2,C=2,claim='critical',allow_constant_slack=True,dictionary_mode='baseline');a=C.build(p,2);p['dictionary_mode']='extended';b=C.build(p,2)
  self.assertEqual(a['instance']['lhs'],b['instance']['lhs']);self.assertEqual(b['instance']['square_groups'][:52],a['instance']['square_groups']);self.assertEqual(b['instance']['relation_groups'][:195],a['instance']['relation_groups']);self.assertEqual(len(b['ast_archive']),162)
 def test_gamma_constraint_independent(self):
  import cancellation_cubic_gate as producer
  d=C.descriptors();a=C.auxiliary_constraint(d);b=producer.build_constraint(d)
  for k,v in a.items():self.assertEqual(v,b[k])
  self.assertEqual(len(a['instance']['square_groups']),106);self.assertEqual(sum(bool(g) for g in a['instance']['relation_groups']),3)
  rw=['0']*231;rw[9]='-1'
  with self.assertRaises(ValueError):C.G.verify_joint([a['instance']],['0']*106,rw,allow_constant_slack=True)
 def test_external_resource_failure_has_no_validation(self):
  row=dict(X=7,status='missing_resource',reason='work',external_resource_failure=True,case_sha256=None,ast_sha256=None,scalar_budget=None,added_scalar_audit=None)
  C.verify_external_final(row);row['certificate']={}
  with self.assertRaises(ValueError):C.verify_external_final(row)
  a=dict(external_resource_failure=True,requested_scales=[1,2,3,5],case_hashes=[],ast_hashes=[],auxiliary_hashes=[],added_scalar_audits=[],budgets=[],gamma=None,independent_check=None,dual=None,independent_dual_check=None,synthesis=dict(status='missing_resource',reason='work',scope='missing',global_bound_proved=False,RH_proved=False))
  C.verify_external_training(a,[1,2,3,5]);a['case_hashes']=['fake']
  with self.assertRaises(ValueError):C.verify_external_training(a,[1,2,3,5])
if __name__=='__main__':unittest.main()
