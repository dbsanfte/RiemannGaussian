import unittest,copy,math
from fractions import Fraction as F
import critical_core_checks as c
TARGETS=[{'r':1,'l':0,'filter':[{'divisor':1,'weight':'1'}]},{'r':1,'l':1,'filter':[{'divisor':1,'weight':'1'},{'divisor':6,'weight':'-11/4'}]}]
class Tests(unittest.TestCase):
 def test_exact_regions_and_grams(self):
  for X in [1,2,4,8,16,32,64]:
   for t in TARGETS:
    row=c.reconstruct_row(X,t);M=c.normalized_matrix(row);self.assertEqual(len(M),13)
    for i in range(13):self.assertGreaterEqual(M[i][i],0)
    for k,s in enumerate(c.FEATURES,1):
     coverage=row['coverage'][k-1];self.assertEqual(sorted(coverage['retained']+coverage['removed']),coverage['eligible'])
     for n in coverage['retained']:self.assertTrue(row['source_arrays'][k][n]!=0)
    self.assertEqual(c.corrected_energy(row,['0']*12),M[0][0])
    Q=row['weight_common_denominator'];self.assertEqual(row['gram_base_denominator'],X*X*Q*Q)
 def test_ceil_and_prime_omega(self):
  for X in range(1,129):
   for d in [4,6,8,12]:
    r=c.ceil_root(X,d);self.assertGreaterEqual(r**d,X);self.assertLess((r-1)**d,X)
  tab=c.factor_tables(128);self.assertEqual(tab[3][12],3);self.assertEqual(tab[2][12],3);self.assertEqual(tab[1][12],2)
 def test_profile_faults(self):
  rows=[c.reconstruct_row(X,t) for t in TARGETS for X in [2,4]];profile={'rows':rows};self.assertTrue(c.verify_profile(profile,[2,4],TARGETS)['verified'])
  fake=copy.deepcopy(profile);fake['rows'][0]['gram_numerators'][0][1]+=1
  with self.assertRaises(ValueError):c.verify_profile(fake,[2,4],TARGETS)
  fake=copy.deepcopy(profile);fake['rows'][0]['correction_denominators'][1]+=1
  with self.assertRaises(ValueError):c.verify_profile(fake,[2,4],TARGETS)
 def test_kkt(self):
  self.assertTrue(c.verify_ridge_kkt([[2,0],[0,1]],[-2,1],[1,-1],0))
  self.assertTrue(c.verify_ridge_kkt([[1]],[-20],[8],0))
  self.assertTrue(c.verify_ridge_kkt([[1]],[20],[-8],0))
  self.assertTrue(c.verify_ridge_kkt([[0]],[0],[0],0))
  for args in [([[1,2],[2,1]],[0,0],[0,0],0),([[1]],[-20],[-8],0),([[1]],[0],[1],0)]:
   with self.assertRaises(ValueError):c.verify_ridge_kkt(*args)
 def test_fit_and_quantization(self):
  rows=[c.reconstruct_row(X,TARGETS[0]) for X in [1,2,4,8]];w=['0']*12
  for mode in ['direct','innovation']:
   constants,obs=c.refit(rows,w,[1,2,4],[2,3],mode);scores=c.score(rows,w,[1,2,4],[2,3],constants,mode);self.assertTrue(all(o['finite_pass'] for o in scores))
  self.assertTrue(c.verify_quantization([0.333333333],[str(F(1,3))]))
  with self.assertRaises(ValueError):c.verify_quantization([0.333333333],['1/2'])
 def test_search_archive_synthetic(self):
  import critical_core_search as search
  f=c.feature_descriptor(c.FEATURES[0]);target=TARGETS[0]
  rows=[dict(X=X,target_id=c.digest(target),feature_ids=['base_G',f['feature_id']],gram_numerators=[[X,X],[X,X]],gram_base_denominator=X*X,correction_denominators=[1,c.ceil_root(X,4)]) for X in [1,2,4]]
  profile={'rows':rows,'features':[f]}
  archive=search.candidate_factory(profile,target,[f],[1,2],[2,3],use_float=False)
  self.assertTrue(c.verify_search_archive(archive,profile,[f])['verified'])
  bad=copy.deepcopy(archive);bad['proposal_archive'][0]['exact_program']['constants']['direct']['2']='999'
  with self.assertRaises(ValueError):c.verify_search_archive(bad,profile,[f])
  bad=copy.deepcopy(archive);bad['proposal_archive'].pop()
  with self.assertRaises(ValueError):c.verify_search_archive(bad,profile,[f])
 def test_profile_bundle_reference(self):
  import critical_core_grammar as producer
  scales=[1,2,4,8,16,32,64];profile=producer.profile(scales,TARGETS,c.FEATURES)
  self.assertTrue(c.verify_profile_bundle(profile,scales,TARGETS)['verified'])
  self.assertTrue(c.verify_profile_bundle(profile,scales,TARGETS,use_numpy=False)['verified'])
  bad=copy.deepcopy(profile);bad['value']['source_profiles'][0]['class_counts'][0]+=1
  with self.assertRaises(ValueError):c.verify_profile_bundle(bad,scales,TARGETS)
  bad=copy.deepcopy(profile);bad['value']['source_provenance'][0]['absolute_coefficient_sum']+=1
  with self.assertRaises(ValueError):c.verify_profile_bundle(bad,scales,TARGETS)
 def test_source_metadata(self):
  f=c.FEATURES[0];s=c.source_profile(64,f);self.assertEqual(sum(s['class_counts']),127);self.assertEqual(s['source_horizon'],127)
  self.assertNotEqual(s['full_prefix_sha256'],s['removed_prefix_sha256'])
if __name__=='__main__':unittest.main()
