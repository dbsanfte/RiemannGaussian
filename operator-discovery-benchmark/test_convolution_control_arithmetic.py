import unittest
from fractions import Fraction as F
import convolution_control_arithmetic as m
class Tests(unittest.TestCase):
 def test_complete_gram(self):
  r=m.arithmetic_profile([1,2,8],control='actual_h'); self.assertEqual(r['status'],'available')
  v=r['value']; a=list(map(F,v['coefficients'])); h=list(map(F,v['control'])); C=list(map(F,v['prefix']))
  for row in v['rows']:
   X=row['X']; S=sum(sum(h[d]**2*C[t//d]**2 for d in range(1,t+1)) for t in range(X,2*X))
   self.assertEqual(F(row['S_X']),S)
   full=sum((sum(h[d]*C[t//d] for d in range(1,t+1)))**2 for t in range(X,2*X))
   self.assertEqual(full,X); self.assertEqual(F(row['cross_X']),full-S)
  for n in range(1,len(a)):
   z=n; omega=0; parity=0; p=2
   while p*p<=z:
    if z%p==0:
     omega+=1
     while z%p==0:z//=p;parity+=1
    p+=1
   if z>1:omega+=1;parity+=1
   self.assertEqual(a[n],(-1)**parity*2**omega);self.assertEqual(h[n],abs(a[n]))
 def test_missing_invalid(self):
  self.assertEqual(m.arithmetic_profile([8],work_budget=1)['status'],'missing')
  self.assertEqual(m.arithmetic_profile([8],max_n=4)['status'],'missing')
  self.assertEqual(m.arithmetic_profile([2],shift=-1)['status'],'invalid')
 def test_generic_signed_inverse(self):
  a=[0,1,1,0,0,0,0,0]; b=m.inverse(a,7,m.Budget(100))
  r=m.profile_from_coefficients(a,b,[2]);self.assertEqual(r['status'],'available')
  self.assertTrue(r['value']['inverse_identity_verified'])
 def test_unsigned_no_false_identity(self):
  r=m.arithmetic_profile([2],sequence='unsigned_h',control='inverse_abs')
  self.assertEqual(r['status'],'available');self.assertIsNone(r['value']['inverse_identity_verified']);self.assertIsNotNone(r['value']['rows'][0]['cross_X'])
 def test_tau_filtered_forcing_and_nonnegative_difference(self):
  from math import isqrt
  r=m.arithmetic_profile([1,4,16],return_tau_profile=True)
  self.assertEqual(r['status'],'available')
  v=r['value']; tp=v['tau_profile']
  for row in tp['rows']:
   X=row['X']; self.assertEqual(F(row['gram_energy_X']),sum(isqrt(t)**2 for t in range(X,2*X)))
  for row in v['tau_minus_h_diagonal']:
   self.assertGreaterEqual(F(row['at_X']),0);self.assertGreaterEqual(F(row['at_2X']),0)
  direct=m.arithmetic_profile([4],control='divisor_count')
  self.assertEqual(direct['value']['rows'],tp['rows'][1:2])
 def test_shifted_sampling_and_lookahead(self):
  r=m.arithmetic_profile([2],shift=-3,dilate=3,control='one')
  self.assertEqual(r['status'],'available'); self.assertEqual(r['lookahead'],18)
  a=list(map(F,r['value']['coefficients']))
  _,_,c,_=m.complete_arithmetic(18,m.Budget(10000))
  self.assertEqual(a,[0,0]+[c[3*(n-1)] for n in range(2,8)])
  r=m.arithmetic_profile([4],shift=-100,control='actual_h')
  self.assertEqual(r['lookahead'],15);self.assertEqual(r['status'],'invalid')
 def test_strict_types_and_rationals(self):
  for kwargs in ({'work_budget':True},{'max_n':False},{'max_n':2.5}):
   self.assertEqual(m.arithmetic_profile([2],**kwargs)['status'],'invalid')
  for x in (True,1.5):
   self.assertEqual(m.profile_from_coefficients([0,1,x,0],[0,1,0,0],[1],verify_inverse=False)['status'],'invalid')
  r=m.profile_from_coefficients([0,1,F(1,2),0],[0,1,0,0],[1],verify_inverse=False)
  self.assertEqual(r['status'],'available')
  self.assertEqual(r['value']['coefficients'][2],'1/2')
if __name__=='__main__':unittest.main()
