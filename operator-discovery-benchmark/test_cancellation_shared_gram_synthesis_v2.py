import unittest,copy
from fractions import Fraction as F
from unittest.mock import patch
import cancellation_shared_gram_synthesis_v2 as S
import grouped_arithmetic_language as L
import check_cancellation_shared_gram as I

def fixture():
 a=L.dump_poly({(1,):F(1)});b=L.dump_poly({():F(-1,2),(2,):F(1)})
 p=L.add(L.load_poly(a),L.scale(L.load_poly(b),-2))
 return [dict(target='mu',horizon=2,lhs=L.dump_poly(L.mul(p,p)),square_groups=[],relation_groups=[])],[{'g':[[a,b]]}],{'g':2}

class V2Tests(unittest.TestCase):
 def test_exact_certificate_normalization_and_checkpoint(self):
  i,b,s=fixture();saved=[]
  r=S.synthesize(i,b,gram_specs=s,on_checkpoint=saved.append,row_normalization=True,time_limit=15)
  self.assertEqual(r['status'],'finite_PSD_certificate',r)
  self.assertTrue(I.verify_primal(i,b,s,r)['verified'])
  self.assertGreaterEqual(len(saved),2)
  self.assertEqual(saved[0]['reconstruction_attempts'],[])
  self.assertTrue(saved[1]['reconstruction_attempts'])
  self.assertEqual(saved[0]['source_hashes'],[S.digest(i[0])])
  self.assertEqual(saved[0]['row_order_hash'],S.digest(saved[0]['monomials']))
 def test_old_misbudget_gate_removed(self):
  i,b,s=fixture();seen=[];original=S.exact_support_solution
  def exact(*args,**kw):seen.append(kw);return original(*args,**kw)
  # Complete row/support proxy=6*3^2=54, exceeds expansion budget50.
  with patch.object(S,'exact_support_solution',side_effect=exact):
   r=S.synthesize(i,b,gram_specs=s,max_operations=50,time_limit=15)
  self.assertTrue(seen,r)
  self.assertEqual(seen[0]['max_work'],450000000)
 def test_checkpoint_precedes_native_cap(self):
  i,b,s=fixture();saved=[]
  r=S.synthesize(i,b,gram_specs=s,max_exact_work=1,on_checkpoint=saved.append,time_limit=15)
  self.assertEqual(r['status'],'missing_resource',r)
  self.assertTrue(saved)
  self.assertIn('float_vector',r['proposal_checkpoint'])
  self.assertIn('failure',r['proposal_checkpoint'])
 def test_checkpoint_callback_failure_honest(self):
  i,b,s=fixture()
  def fail(x):raise OSError('disk full')
  with patch.object(S,'exact_support_solution',side_effect=AssertionError('must not run')):
   r=S.synthesize(i,b,gram_specs=s,on_checkpoint=fail,time_limit=15)
  self.assertEqual(r['status'],'uncertified',r)
  self.assertIn('checkpoint callback failed',r['reason'])
 def test_inaccurate_proposal_preserved_before_gate(self):
  import cvxpy as cp
  original=cp.Problem.solve
  def inaccurate(problem,*args,**kwargs):
   result=original(problem,*args,**kwargs);problem._status='optimal_inaccurate';return result
  i,b,s=fixture();saved=[]
  with patch.object(cp.Problem,'solve',new=inaccurate):
   r=S.synthesize(i,b,gram_specs=s,on_checkpoint=saved.append,max_exact_work=1,time_limit=15)
  self.assertEqual(r['status'],'missing_resource')
  self.assertEqual(saved[0]['solver_status'],'optimal_inaccurate')
 def test_solver_error_with_values_checkpointed_honestly(self):
  import cvxpy as cp
  original=cp.Problem.solve
  def fails_after_values(problem,*args,**kwargs):
   original(problem,*args,**kwargs);raise cp.error.SolverError('postsolve failure')
  i,b,s=fixture();saved=[]
  with patch.object(cp.Problem,'solve',new=fails_after_values):
   r=S.synthesize(i,b,gram_specs=s,on_checkpoint=saved.append,time_limit=15)
  self.assertEqual(r['status'],'uncertified')
  self.assertTrue(saved)
  self.assertIn('postsolve failure',r['reason'])
 def test_checkpoint_byte_cap(self):
  i,b,s=fixture();r=S.synthesize(i,b,gram_specs=s,max_checkpoint_bytes=1,time_limit=15)
  self.assertEqual(r['status'],'missing_resource',r)
  self.assertIn('checkpoint byte cap',r['reason'])
if __name__=='__main__':unittest.main()
