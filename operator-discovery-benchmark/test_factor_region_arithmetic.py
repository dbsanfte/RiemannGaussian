import unittest,math
from fractions import Fraction as F
import factor_region_arithmetic as m
T=[{'r':1,'l':0,'filter':[{'divisor':1,'weight':'1'}]},{'r':1,'l':1,'filter':[{'divisor':1,'weight':'1'}]},{'r':1,'l':1,'filter':[{'divisor':1,'weight':'1'},{'divisor':6,'weight':'-11/4'}]}]
S=[{'prime_power':'1/3','core_power':'1/2'},{'prime_power':'1','core_power':'1/3'}]
def coefficient(n,r,l):
 v=1;p=2
 while p*p<=n:
  e=0
  while n%p==0:e+=1;n//=p
  if e:v*=sum((-1)**j*math.comb(r,j)*((-1)**(e-j)*math.comb(l+e-j-1,e-j) if l else int(j==e)) for j in range(min(r,e)+1))
  p+=1
 if n>1:v*=-(r+l)
 return v
class Tests(unittest.TestCase):
 def test_reconstruction(self):
  ans=m.profile([1,2,3,8,16,32,64],T,S,use_numpy=False);self.assertEqual(ans['status'],'available')
  for row in ans['value']['rows']:
   t=next(t for t in T if m.canonical_id(t)==row['target_id']);X=row['X'];P=[0]
   for n in range(1,2*X):P.append(P[-1]+coefficient(n,t['r'],t['l']))
   E=sum(sum(F(v['weight'])*P[n//v['divisor']] for v in t['filter'])**2 for n in range(X,2*X))/X**2
   self.assertEqual(F(row['E']),E);self.assertEqual(F(row['E']),F(row['diagonal'])+F(row['cross']));self.assertTrue(row['source_coverage_complete'])
   g=row['gram_numerators'];self.assertEqual(g,list(map(list,zip(*g))));self.assertTrue(all(g[i][i]>=0 for i in range(9)))
 def test_numpy_equivalence(self):
  a=m.profile([8,32],T,S,use_numpy=False);b=m.profile([8,32],T,S,use_numpy=True)
  self.assertEqual([r['gram_numerators'] for r in a['value']['rows']],[r['gram_numerators'] for r in b['value']['rows']])
 def test_cutoffs(self):
  for X in range(1,129):
   for power in ['1/2','1/3','2/3','3/2']:
    q=F(power);z=m._cut(X,power,100000)
    self.assertLessEqual(z**q.denominator,X**q.numerator);self.assertGreater((z+1)**q.denominator,X**q.numerator)
 def test_complete_calibrations(self):
  for r,l in [(1,0),(0,1),(1,1),(2,1),(0,3),(4,0)]:
   for x in [1,2,7,16,31,64,128]:
    self.assertTrue(m.log_prime_forcing(x,r,l)['identity_verified'])
    for z in [0,2,5,128]:
     v=m.least_prime_decomposition(x,z,r,l)
     self.assertEqual(v['value'],v['reconstructed']);self.assertEqual(v['value'],m.rough_prefix(x,z,r,l));self.assertEqual(v['remainder'],0)
 def test_no_partial_resource_result(self):
  for kwargs in [dict(work_budget=10),dict(max_n=3),dict(bit_budget=2)]:
   v=m.profile([8],T,S,**kwargs);self.assertEqual(v['status'],'missing');self.assertIsNone(v['value'])
 def test_prime_obstruction_gate(self):
  scheme={'prime_power':'1/2','core_power':'1/2'}
  for t in T[:2]:
   c=m.prime_singleton_obstruction(t,scheme,'1/3','2')
   self.assertTrue(c['applies']);self.assertEqual(c['component_index'],5);self.assertFalse(c['direct_target_energy_claim_refuted'])
  self.assertFalse(m.prime_singleton_obstruction(T[2],scheme,'0','1')['applies'])
  self.assertFalse(m.prime_singleton_obstruction(T[0],scheme,'1','1')['applies'])
  self.assertFalse(m.prime_singleton_obstruction(T[0],scheme,'0','0')['applies'])
  a=m.profile([16,32,64],T[:2],[scheme],use_numpy=False)
  for row in a['value']['rows']:
   X=row['X'];t=next(t for t in T if m.canonical_id(t)==row['target_id']);k=t['r']+t['l'];z=math.isqrt(X)
   def pi(y):return sum(all(p%d for d in range(2,math.isqrt(p)+1)) for p in range(2,y+1))
   expected=sum((k*(pi(n)-pi(z)))**2 for n in range(X,2*X))
   self.assertEqual(row['gram_numerators'][5][5],expected)
 def test_invalid(self):
  for scales,targets,schemes in [([True],T,S),([1,1],T,S),([1],T,[{'prime_power':'0','core_power':'1'}]),([1],[{'r':0,'l':0,'filter':T[0]['filter']}],S)]:
   v=m.profile(scales,targets,schemes);self.assertEqual(v['status'],'invalid');self.assertIsNone(v['value'])
if __name__=='__main__':unittest.main()
