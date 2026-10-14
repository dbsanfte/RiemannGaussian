"""Declared development unit fixtures only; no actual-arithmetic search scores."""
import unittest
from fractions import Fraction as F
import convolution_control_search as s

def fixture(scales):
 N=4*max(scales)-1; C=[0]+list(range(1,N+1));rows=[];trows=[]
 for X in scales:
  A=sum(C[n]**2 for n in range(X,2*X))
  rows.append(dict(X=X,A_X=A,S_X=A))
  S=sum(sum(C[n//d]**2 for d in range(1,n+1)) for n in range(X,2*X))
  trows.append(dict(X=X,A_X=A,S_X=S))
 return dict(prefix=C,rows=rows,tau_profile=dict(rows=trows))
class Tests(unittest.TestCase):
 def test_complete_squares_and_child_transition(self):
  tab=s.featuretable(fixture([8,16]),[8,16]);self.assertEqual(tab['status'],'available')
  rows={r['X']:r for r in tab['value']['rows']}
  f=next(f for f in s.FEATURE_DICTIONARY if f['kind']=='root' and f['divisor']==2 and f['weight']=='-1/2')
  for X,d in ((8,2),(16,4)):
   self.assertEqual(rows[X]['feature_metadata'][f['feature_id']]['divisor_at_scale'],d)
   self.assertEqual(F(rows[X]['features'][f['feature_id']]),sum((F(n)-F(n//d,2))**2 for n in range(X,2*X))/X**2)
 def test_missing_and_zero_weight(self):
  t=s.featuretable(fixture([2,4]),[2,4],work_budget=1)
  fid=s.FEATURE_DICTIONARY[-1]['feature_id'];p=dict(terms=[dict(feature_id=fid,weight='0')],constants={'2':'100'})
  r=s.score(p,t,[2],[2,3]);self.assertEqual(r['missing_cases'],1);self.assertEqual(r['finite_passes'],1)
  p['terms'][0]['weight']='1';self.assertEqual(s.score(p,t,[2],[2])['missing_cases'],1)
 def test_exact_refit_archive_and_alias(self):
  t=s.featuretable(fixture([1,2,4]),[1,2,4])
  out=s.candidate_factory(t,[1,2],levels=[2],use_lp=False)
  self.assertEqual(len(out['proposal_archive']),1+3*len(s.FEATURE_DICTIONARY))
  for c in out['candidates']:
   score=c['training_score'];self.assertEqual(score['finite_failures'],0);self.assertEqual(score['missing_cases'],0)
  self.assertEqual(out,s.candidate_factory(t,[1,2],levels=[2],use_lp=False))
 def test_huge_root_and_dictionary_binding(self):
  self.assertEqual(s.integer_root(2,10**100),1)
  self.assertEqual(s.digest(s.FEATURE_DICTIONARY),s.FEATURE_DICTIONARY_SHA256)
  self.assertEqual(s.featuretable(fixture([1]),[True])['status'],'invalid')
 def test_parent_child_extraction_and_disagreement(self):
  p=fixture([2,4]); r=p['rows'][0]; t=p['tau_profile']['rows'][0]
  r.update(A_2X=p['rows'][1]['A_X'],S_2X=p['rows'][1]['S_X'])
  t.update(A_2X=p['tau_profile']['rows'][1]['A_X'],S_2X=p['tau_profile']['rows'][1]['S_X'])
  p['rows']=p['rows'][:1];p['tau_profile']['rows']=p['tau_profile']['rows'][:1]
  self.assertEqual(s.featuretable(p,[2,4])['status'],'available')
  p['rows'].append(dict(X=4,A_X=0,S_X=0))
  self.assertEqual(s.featuretable(p,[2,4])['status'],'invalid')
 def test_lp_proposal_alias_retains_float_and_exact_refit(self):
  import sys,types
  from unittest.mock import patch
  scipy=types.ModuleType('scipy');opt=types.ModuleType('scipy.optimize')
  def lp(c,**kwargs):return types.SimpleNamespace(success=True,status=0,message='synthetic proposal',x=[0.0]*len(c),fun=0.0)
  opt.linprog=lp
  t=s.featuretable(fixture([1,2,4]),[1,2,4])
  with patch.dict(sys.modules,{'scipy':scipy,'scipy.optimize':opt}):out=s.candidate_factory(t,[1,2],levels=[2])
  lp_rows=[r for r in out['proposal_archive'] if r['origin']['kind']=='lp']
  self.assertEqual(len(lp_rows),15)
  self.assertTrue(all(r['solver']['float_solution'] is not None and r['alias_of'] for r in lp_rows))
  self.assertTrue(all(c['training_score']['finite_failures']==0 for c in out['candidates']))
if __name__=='__main__':unittest.main()
