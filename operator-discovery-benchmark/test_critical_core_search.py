"""Exact solver and synthetic corrected-Gram contracts; no actual data scores."""
import unittest
from fractions import Fraction as F
import critical_core_search as s
TARGET=dict(r=1,l=1,filter=[dict(divisor=1,weight='1')])
def fixture():
 rows=[]
 for X in (1,2,4):
  # Rank-one complete synthetic Gram with signed correction components.
  v=[2]+[(-1)**i*(i+1) for i in range(12)];mass=sum(n*n for n in range(X,2*X))
  ds=[1]+[2]*12
  rows.append(dict(X=X,target_id=s.digest(TARGET),feature_ids=['base_G']+[f['feature_id'] for f in s.FEATURES],gram_numerators=[[mass*a*b for b in v] for a in v],gram_base_denominator=X*X,correction_denominators=ds))
 return dict(status='available',value=dict(features=s.FEATURES,rows=rows))
class Tests(unittest.TestCase):
 def test_exact_box_optimum_and_signs(self):
  M=[[100,20,-20],[20,1,0],[-20,0,1]]
  r=s.box_fit(M,[1,2],'1',use_float=False)
  self.assertEqual(r['status'],'available');self.assertEqual(r['exact_weights'],['-8','8']);self.assertTrue(r['KKT_certificate']['all_KKT_verified'])
  self.assertEqual(r['KKT_certificate']['half_gradients'],['4','-4'])
  # Exact interior and finite-face fallback even with active iteration budget0.
  M=[[1,1,1],[1,4,1],[1,1,4]]
  r=s.box_fit(M,[1,2],'1',use_float=False,max_iterations=0)
  self.assertEqual(r['exact_weights'],['-1/6','-1/6']);self.assertEqual(r['solver_method'],'finite_face_fallback')
  self.assertEqual(r['quadratic_matrix'],[['4','1'],['1','4']])
 def test_large_group_resource_failure_no_false_optimum(self):
  M=[[0]*13 for _ in range(13)]
  r=s.box_fit(M,list(range(1,13)),'1',use_float=False,max_iterations=0)
  self.assertEqual(r['status'],'failed');self.assertIsNone(r['exact_weights'])
  self.assertEqual(s.box_fit([[0,0],[0,-2]],[1],'1',use_float=False)['status'],'invalid')
 def test_complete_normalized_crosses_fit_and_unknown_q(self):
  p=fixture();program=dict(target=TARGET,corrections=[dict(feature=s.FEATURES[0],weight='-1/2')])
  constants,evidence=s.fit_constants(program,p,s.FEATURES,[1,2],[2]);program['constants']=constants
  # G(t)=2t, T0(t)=t/2; H(t)=7t/4, so complete square uses the signed cross.
  direct=next(o for o in evidence if o['mode']=='direct' and o['X']==2)
  self.assertEqual(F(direct['observed']),F(49,16)*F(4+9,4))
  r=s.score(program,p,s.FEATURES,[1,2],[2,13]);self.assertEqual(r['modes']['direct']['finite_failures'],0);self.assertEqual(r['modes']['direct']['missing_cases'],2)
  records=s._records(p,s.FEATURES)[0];self.assertEqual(records[s.digest(TARGET),2][0][1],F(13,4))
 def test_factory_attempts_aliases_and_missing(self):
  out=s.candidate_factory(fixture(),TARGET,s.FEATURES,[1,2],[2],use_float=False)
  self.assertEqual(len(out['proposal_archive']),121)
  self.assertTrue(all(c['training_score']['modes']['direct']['finite_failures']==0 for c in out['candidates']))
  fits=[p for p in out['proposal_archive'] if p['origin']['kind']=='ridge_fit']
  self.assertTrue(all(p['origin']['solver']['KKT_certificate']['all_KKT_verified'] for p in fits))
  self.assertTrue(all(c['program_id']==s.digest(c['program']) for c in out['candidates']))
  missing=s.candidate_factory(dict(status='missing',value=None),TARGET,s.FEATURES,[1],[2],use_float=False)
  self.assertEqual(len(missing['proposal_archive']),121);self.assertTrue(all(c['training_score']['modes']['direct']['missing_cases']==1 for c in missing['candidates']))
if __name__=='__main__':unittest.main()
