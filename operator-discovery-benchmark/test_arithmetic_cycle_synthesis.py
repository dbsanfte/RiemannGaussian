import copy,sys,types,unittest
from unittest.mock import patch
from fractions import Fraction as F
import arithmetic_cycle_language as l
import arithmetic_cycle_synthesis as s

def fake_solver(weights,success=True):
 module=types.ModuleType('scipy.optimize')
 module.linprog=lambda *a,**k:types.SimpleNamespace(status=0 if success else 2,success=success,message='test anonymous support proposal',x=weights if success else None,fun=sum(weights) if success else None)
 return patch.dict(sys.modules,{'scipy':types.ModuleType('scipy'),'scipy.optimize':module})
class Tests(unittest.TestCase):
 def test_anonymous_polynomial_recovery(self):
  p=l.add(l.scale(l.variable(2),F(2,3)),l.scale(l.variable(7),-5),l.constant(F(3,2)));lhs=l.dump_poly(l.scale(l.mul(p,p),F(7,11)))
  with fake_solver([7/11]):result=s.synthesize('mu',7,lhs,[l.dump_poly(p)],[])
  self.assertEqual(result['status'],'finite_certificate');self.assertEqual(result['certificate']['squares'][0]['weight'],'7/11');self.assertFalse(result['global_bound_proved'])
  bad=copy.deepcopy(result['certificate']);bad['lhs'][0]['c']=str(F(bad['lhs'][0]['c'])+1)
  with self.assertRaises(ValueError):l.compile_certificate(bad)
 def test_negative_square_cannot_be_admitted(self):
  p=l.variable(2);lhs=l.dump_poly(l.scale(l.mul(p,p),-1))
  with fake_solver([1]):result=s.synthesize('mu',2,lhs,[l.dump_poly(p)],[])
  self.assertEqual(result['status'],'no_certificate_found')
  with fake_solver([],False):result=s.synthesize('mu',2,lhs,[l.dump_poly(p)],[])
  self.assertEqual(result['status'],'no_certificate_found');self.assertIn('no mathematical infeasibility',result['reason'])
 def test_native_solver_limit_is_missing(self):
  module=types.ModuleType('scipy.optimize');module.linprog=lambda *a,**k:types.SimpleNamespace(status=1,success=False,message='Time limit',x=None,fun=None)
  p=l.variable(2)
  with patch.dict(sys.modules,{'scipy':types.ModuleType('scipy'),'scipy.optimize':module}):result=s.synthesize('mu',2,l.dump_poly(l.mul(p,p)),[l.dump_poly(p)],[])
  self.assertEqual(result['status'],'missing_resource')
 def test_cycle_and_grouped_columns(self):
  spec={'kind':'coprime_product','a':2,'b':3};lhs=l.dump_poly(l.mul(l.mul(l.variable(2),l.variable(3)),l.variable(6)));basis=[l.dump_poly(l.variable(6))];group=[[{'spec':spec,'multiplier':l.dump_poly(l.variable(6))}]]
  with fake_solver([1,1,0]):result=s.synthesize('mu',6,lhs,basis,group)
  self.assertEqual(result['status'],'finite_certificate')
  groups=[[{'spec':{'kind':'unit'},'multiplier':l.dump_poly(l.variable(2))},{'spec':{'kind':'unit'},'multiplier':l.dump_poly(l.variable(3))}]]
  p=l.add(l.mul(l.variable(2),l.relation({'kind':'unit'},'mu',3)),l.mul(l.variable(3),l.relation({'kind':'unit'},'mu',3)))
  with fake_solver([0,2]):result=s.synthesize('mu',3,l.dump_poly(l.scale(p,-2)),[],groups)
  self.assertEqual(result['status'],'finite_certificate');self.assertEqual(len(result['certificate']['relations']),2)
 def test_exact_rref_and_resources(self):
  self.assertEqual(s.exact_support_solution([{(2,):F(3)},{(2,):F(6)}],{(2,):F(1)},[0,1]),[F(1,3),F(0)])
  self.assertIsNone(s.exact_support_solution([{(2,):F(1)}],{(3,):F(1)},[0]))
  poly=l.dump_poly(l.variable(2))
  self.assertEqual(s.synthesize('mu',2,poly,[poly],[],max_columns=1,max_monomials=1)['status'],'missing_resource')
  with fake_solver([1]):result=s.synthesize('mu',2,l.dump_poly(l.scale(l.mul(l.variable(2),l.variable(2)),F(1,101))),[poly],[],max_denominator=100)
  self.assertEqual(result['status'],'missing_resource')
 def test_real_scipy_and_independent_checker(self):
  try:import scipy.optimize
  except ImportError:self.skipTest('SciPy runtime unavailable')
  import check_arithmetic_cycle_certificate as independent
  p=l.add(l.variable(2),l.scale(l.variable(3),F(-2,5)));lhs=l.dump_poly(l.scale(l.mul(p,p),F(3,7)))
  result=s.synthesize('mu',3,lhs,[l.dump_poly(p)],[])
  self.assertEqual(result['status'],'finite_certificate');self.assertTrue(independent.verify_certificate(result['certificate'])['finite_identity_verified'])
  result=s.synthesize('mu',3,l.dump_poly(l.scale(l.mul(p,p),-1)),[l.dump_poly(p)],[])
  self.assertEqual(result['status'],'no_certificate_found')
 def test_zero_and_invalid(self):
  self.assertEqual(s.synthesize('c',1,[],[],[])['status'],'finite_certificate')
  self.assertEqual(s.synthesize('mu',1,l.dump_poly(l.variable(2)),[],[])['status'],'no_certificate_found')
if __name__=='__main__':unittest.main()
