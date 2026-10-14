"""Synthetic complete Gram tests only; no actual response data."""
import unittest
from fractions import Fraction as F
import factor_region_search as s
TARGET=dict(r=1,l=1,filter=[dict(divisor=1,weight='1')])
SCHEMES=[dict(prime_power=a,core_power=b) for a in ('1/6','1/3','1/2') for b in ('1/6','1/3','1/2')]
def fixture(schemes=SCHEMES,scales=(1,2,4)):
 v=[2,-1,3,-2,0,1,-1,2,-3];assert sum(v)==1
 rows=[]
 for X in scales:
  mass=sum(n*n for n in range(X,2*X))
  for scheme in schemes:
   rows.append(dict(X=X,target_id=s.digest(TARGET),scheme_id=s.digest(scheme),gram_numerators=[[mass*a*b for b in v] for a in v],gram_denominator=X*X,E=str(F(mass,X*X))))
 return rows
class Tests(unittest.TestCase):
 def test_dictionary_and_full_signed_cross(self):
  fs=s.dictionary(SCHEMES);self.assertEqual(len(fs),432);self.assertEqual(len({f['feature_id'] for f in fs}),432)
  t=s.feature_table(fixture(),[TARGET],SCHEMES);self.assertEqual(t['status'],'available')
  row=next(r for r in t['value']['rows'] if r['X']==2)
  f=next(f for f in fs if f['vector']==[0,1,-1,0,0,0,0,0,0] and f['eta']=='0')
  self.assertEqual(F(row['features'][f['feature_id']]),F(16*(4+9),4))
  self.assertTrue(t['value']['full_signed_Gram_retained'])
 def test_missing_child_unknown_level_and_zero_weights(self):
  scheme=SCHEMES[:1];t=s.feature_table(fixture(scheme),[TARGET],scheme,work_budget=0)
  f=t['value']['features'][0];p=dict(target=TARGET,terms=[dict(feature=f,weight='0')],constants={'2':'100'})
  r=s.score(p,t,[1],[2,13]);self.assertEqual(r['finite_passes'],1);self.assertEqual(r['missing_cases'],1)
  p['terms'][0]['weight']='1';self.assertEqual(s.score(p,t,[1],[2])['missing_cases'],1)
  t=s.feature_table(fixture(scheme,(1,)),[TARGET],scheme);p['terms']=[]
  self.assertEqual(s.score(p,t,[1],[2])['missing_cases'],1)
  unavailable=dict(status='missing',value=None,reason='resource')
  out=s.candidate_factory(unavailable,TARGET,[f],[1],[2],use_lp=False)
  self.assertTrue(all(c['training_score']['missing_cases']==1 for c in out['candidates']))
 def test_exact_refit_and_lp_archive_aliases(self):
  import sys,types
  from unittest.mock import patch
  scheme=SCHEMES[:1];t=s.feature_table(fixture(scheme),[TARGET],scheme);fs=t['value']['features']
  scipy=types.ModuleType('scipy');opt=types.ModuleType('scipy.optimize')
  def lp(c,**kw):return types.SimpleNamespace(success=True,status=0,message='synthetic',x=[0.0]*len(c),fun=0.0)
  opt.linprog=lp
  with patch.dict(sys.modules,{'scipy':scipy,'scipy.optimize':opt}):out=s.candidate_factory(t,TARGET,fs,[1,2],[2])
  self.assertEqual(len(out['proposal_archive']),1+3*48+4)
  self.assertTrue(all(c['training_score']['finite_failures']==0 for c in out['candidates']))
  lp_rows=[a for a in out['proposal_archive'] if a['origin']['kind']=='lp']
  self.assertTrue(all(a['solver']['float_solution'] is not None and a['alias_of'] for a in lp_rows))
  self.assertTrue(all(c['program_id']==s.digest(c['program']) for c in out['candidates']))
 def test_complete_partition_and_types_rejected(self):
  rows=fixture(SCHEMES[:1]);rows[0]['E']='99'
  self.assertEqual(s.feature_table(rows,[TARGET],SCHEMES[:1])['status'],'invalid')
  rows=fixture(SCHEMES[:1]);rows[0]['gram_numerators'][0][0]=True
  self.assertEqual(s.feature_table(rows,[TARGET],SCHEMES[:1])['status'],'invalid')
  self.assertEqual(s.feature_table(fixture(SCHEMES[:1]),[TARGET],SCHEMES[:1],work_budget=True)['status'],'invalid')
  table=s.feature_table(fixture(SCHEMES[:1]),[TARGET],SCHEMES[:1])
  f=dict(table['value']['features'][0]);f['vector']=[9]*9;f['feature_id']=s.digest({k:v for k,v in f.items() if k!='feature_id'})
  with self.assertRaises(ValueError):s.score(dict(target=TARGET,terms=[dict(feature=f,weight='1')],constants={'2':'1'}),table,[1],[2])
  f=s.dictionary(SCHEMES[1:2])[0]
  with self.assertRaises(ValueError):s.score(dict(target=TARGET,terms=[dict(feature=f,weight='1')],constants={'2':'1'}),table,[1],[2])
if __name__=='__main__':unittest.main()
