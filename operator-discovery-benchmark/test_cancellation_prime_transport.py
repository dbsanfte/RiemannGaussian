import unittest,copy
import cancellation_prime_transport as T
import arithmetic_cycle_language as L
from arithmetic_cycle_controls import coefficients
class TestTransport(unittest.TestCase):
 def test_shell_all_endpoints(self):
  for X in [1,2,4]:
   for p in [2,3,7]:
    for a in range(1,4*X):
     for b in range(1,4*X):
      count=sum(a<=n<p*a and b<=n<p*b for n in range(X,2*X))
      self.assertEqual(T.shell_kernel(X,p,a,b),count)
 def test_complete_equality_and_kernel(self):
  for X,p in [(1,2),(2,2),(2,3),(2,11)]:
   r=T.build_transport(X,p,max_n=31);N=r['horizon'];transport={}
   for a in range(1,N+1):
    for b in range(1,N+1):
     if a%p and b%p:
      w=T.shell_kernel(2*X,p,a,b)-4*T.shell_kernel(X,p,a,b)
      transport=L.add(transport,{tuple(sorted((a,b))):w})
   self.assertEqual(L.load_poly(r['transported_defect']),transport)
   for c in [r['equality_certificate'],r['reverse_equality_certificate']]:self.assertTrue(L.compile_certificate(c)['finite_identity_verified'])
 def test_mutations_rejected(self):
  r=T.build_transport(2,2);c=copy.deepcopy(r['equality_certificate']);c['relations'].pop()
  with self.assertRaises(ValueError):L.compile_certificate(c)
  c=copy.deepcopy(r['equality_certificate']);c['relations'][0]['multiplier']=L.dump_poly(L.scale(L.load_poly(c['relations'][0]['multiplier']),-1))
  with self.assertRaises(ValueError):L.compile_certificate(c)
 def test_counterfeit_passes_local_transform(self):
  r=T.build_transport(2,2);f=coefficients(7,'counterfeit',[2])['coefficients'];v={n:f[n] for n in range(1,8)}
  self.assertEqual(L.evaluate(L.load_poly(r['equality_certificate']['lhs']),v),0)
  self.assertEqual(f[3],1);self.assertFalse(r['RH_proved'])
 def test_limits(self):
  with self.assertRaises(ValueError):T.build_transport(2,4)
  with self.assertRaises(OverflowError):T.build_transport(8,2,max_operations=1)
if __name__=='__main__':unittest.main()
