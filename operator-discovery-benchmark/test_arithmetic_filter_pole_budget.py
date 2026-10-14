import unittest
from fractions import Fraction as F
from math import comb
import arithmetic_filter_pole_budget as p
class Tests(unittest.TestCase):
 def test_gate_and_aliases(self):
  r=p.certify(1,1,[(1,1),(2,'-1/2')]);self.assertEqual(r['status'],'admitted_conditional');self.assertEqual(r['minimum_surviving_pole_order'],1);self.assertFalse(r['estimate_proved']);self.assertFalse(r['RH_proved'])
  self.assertEqual(p.certify(1,0,[(1,2),(1,-1),(2,1),(2,-1)])['support_size'],1)
  self.assertEqual(p.certify(1,1,[(1,1),(1,-1)])['status'],'unsupported')
  self.assertEqual(p.certify(2,1,[(1,1),(2,-1),(3,1)])['status'],'admitted_conditional')
 def test_sharpness_and_bad_types(self):
  for k in (1,2,5):
   f=p.sharpness_filter(k);self.assertEqual(len(f),k+1);self.assertEqual(sum(F(t['weight']) for t in f),0)
   self.assertEqual(p.certify(k,0,f)['status'],'unsupported')
  for bad in (True,0.5):
   self.assertEqual(p.certify(bad,1,[(1,1)])['status'],'invalid')
   self.assertEqual(p.certify(1,1,[(1,bad)])['status'],'invalid')
  self.assertEqual(p.certify(1,1,[dict(divisor=2,weight=1,moving=True)])['status'],'unsupported')
 def test_complete_actual_local_formula_and_filter_convolution(self):
  for r,l in ((1,1),(2,1),(0,2),(3,0)):
   out=p.actual_coefficients(40,r,l);self.assertEqual(out['status'],'available');a=out['coefficients']
   for n in range(1,41):
    rest=n;expected=1;q=2
    while q<=rest:
     e=0
     while rest%q==0:rest//=q;e+=1
     if e:
      local=0
      for t in range(e//2+1):
       j=e-2*t
       if j<=r+l and (l or t==0):local+=(-1)**j*comb(r+l,j)*(comb(l+t-1,t) if l else 1)
      expected*=local
     q+=1
    self.assertEqual(a[n],expected)
   terms=[(1,1),(2,F(-1,2)),(5,2)];G=p.filtered_prefix(a,terms)
   b=[0]+[sum(F(w)*a[n//d] for d,w in terms if n%d==0) for n in range(1,41)]
   self.assertEqual(G,[sum(b[:n+1]) for n in range(41)])
 def test_offcritical_generic_sharpness(self):
  from math import factorial
  for k in (1,2,4):
   f=p.sharpness_filter(k,base=4,amplitude=3)
   # At 4^-s=1/3, logarithmic derivative moments vanish through k-1.
   for t in range(k):self.assertEqual(sum(F(term['weight'])*F(1,3)**j*j**t for j,term in enumerate(f)),0)
   self.assertEqual(sum(F(term['weight'])*F(1,3)**j*j**k for j,term in enumerate(f)),(-1)**k*factorial(k))
   self.assertEqual(p.certify(k,0,f)['status'],'unsupported')
 def test_budget_no_partial_answer(self):
  r=p.actual_coefficients(100,2,2,work_budget=1);self.assertEqual(r['status'],'missing');self.assertIsNone(r['coefficients'])
if __name__=='__main__':unittest.main()
