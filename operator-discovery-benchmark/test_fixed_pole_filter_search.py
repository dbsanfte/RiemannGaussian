"""Synthetic/development contracts only: no scored large actual dataset."""
import unittest
from fractions import Fraction as F
import fixed_pole_filter_search as s
class Tests(unittest.TestCase):
 def test_complete_covariance_and_integer_guard(self):
  prefix=[0]+[(-1)**n*n for n in range(1,32)]
  a=s.covariance_table(prefix,[2,4,8],use_numpy=False);b=s.covariance_table(prefix,[2,4,8])
  self.assertEqual(a['status'],'available');self.assertEqual(b['status'],'available')
  for x,y in zip(a['value']['moments'],b['value']['moments']):
   self.assertEqual(x['matrix'],y['matrix']);X=x['X']
   self.assertEqual(F(x['matrix'][2][3]),sum(F(prefix[n//3])*prefix[n//4] for n in range(X,2*X))/X**2)
  huge=[0]+[10**30]*31
  r=s.covariance_table(huge,[4]);self.assertEqual(r['value']['moments'][0]['backend'],'python_integer')
  self.assertEqual(s.covariance_table(prefix,[4],work_budget=1)['status'],'missing')
 def test_exact_box_solvers_and_singular_missing(self):
  M=[[F(0)]*len(s.DIVISORS) for _ in s.DIVISORS];M[0][0]=100;M[1][1]=M[2][2]=1;M[0][1]=M[1][0]=10;M[0][2]=M[2][0]=-20
  r=s.least_squares(M,[2,3]);self.assertEqual(r['exact_weights'],['-8','8']);self.assertTrue(any(c['kind']=='corner' for c in r['choices']))
  M[0][1]=M[1][0]=F(1,3);self.assertEqual(s.least_squares(M,[2])['exact_weights'],['-1/3'])
  M[1][2]=M[2][1]=1;self.assertEqual(s.least_squares(M,[2,3])['status'],'missing')
 def test_fixed_normalization_fit_and_unknown_level(self):
  prefix=list(range(16));cov=s.covariance_table(prefix,[1,2,4],use_numpy=False)['value'];data=dict(targets=[dict(target=t,coefficients=[0]*16,prefix=prefix,**cov) for t in s.TARGETS])
  out=s.candidate_factory(data,[1,2],levels=[2]);self.assertEqual(len(s.TARGETS),9)
  self.assertTrue(all(c['admission']['conditional_bridge_admitted'] for c in out['candidates']))
  for c in out['candidates']:
   self.assertEqual(c['program']['filter'][0],dict(divisor=1,weight='1'))
   for mode in ('direct','innovation'):self.assertEqual(c['training_score']['modes'][mode]['finite_failures'],0)
  probe=dict(target=s.TARGETS[-1],filter=[dict(divisor=1,weight='1'),dict(divisor=3,weight='-1/2')])
  _,_,cache,_=s._evaluation_cache(probe,data,[1,2],[2],1000000)
  for mode in ('direct','innovation'):
   for X in (1,2):self.assertEqual(cache[(mode,X)],s._observed(probe,data,X,mode))
  r=s.score(out['candidates'][0]['program'],data,[2],[13]);self.assertEqual(r['modes']['direct']['missing_cases'],1)
  self.assertTrue(any(p.get('status')=='missing' for p in out['proposal_archive']))
  comp=[p for p in out['proposal_archive'] if p['origin']['kind']=='composition_square']
  self.assertEqual(len(comp),4*3*len(s.TWO_WEIGHTS))
  self.assertTrue(all(len(p['exact_program']['filter'])==3 for p in comp))
 def test_small_actual_builder_no_scores(self):
  r=s.build_dataset([1,2],targets=[dict(r=1,l=1)],use_numpy=False)
  self.assertEqual(r['status'],'available');self.assertEqual(r['lookahead'],7)
  self.assertEqual(r['value']['targets'][0]['coefficients'],[0,1,-2,-2,2,-2,4,-2])
  self.assertEqual(r['value']['scales'],[1,2,4])
  self.assertEqual(s.build_dataset([True])['status'],'invalid')
if __name__=='__main__':unittest.main()
