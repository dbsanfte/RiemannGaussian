import copy,unittest
from fractions import Fraction as F
import prime_pair_forcing_checks as c
CUTOFFS=[{'kind':'fixed','value':0},{'kind':'fixed','value':2},{'kind':'bit_length_power','power':'1/2'},{'kind':'power','power':'1/3'}]
class Tests(unittest.TestCase):
 def test_exact_identity_small_original_pairs(self):
  for X in [1,2,4,8]:
   for target in ['mu','c']:
    truth=c.original_pair_terms(X,target,2,16);D=truth['ratio_denominator'];S=F(truth['exact_total_forcing']);self.assertLessEqual(F(truth['total_interval'][0],D),S);self.assertGreaterEqual(F(truth['total_interval'][1],D),S)
    self.assertEqual(sum(truth['counts'].values()),len(truth['terms']));self.assertEqual(truth['Delta'],truth['J_unit']-2*truth['kappa']*S)
 def test_rational_log_enclosure(self):
  for n in range(1,33):
   lo,hi=c.log_interval(n,64);self.assertLessEqual(lo,hi);self.assertLessEqual(hi-lo,F(1,2**64))
  self.assertEqual(c.ratio_interval(2,8),(F(1,3),F(1,3)))
  self.assertTrue(c.validate_ratio_enclosure(2,8,1,1,3))
  with self.assertRaises(ValueError):c.validate_ratio_enclosure(2,8,2,2,3)
 def test_producer_and_mutations(self):
  import prime_pair_forcing as p
  profile=p.profile([1,2,4,8],['mu','c'],CUTOFFS,work_budget=10000000,max_n=31,bits=16)
  self.assertTrue(c.verify_profile(profile,[1,2,4,8],['mu','c'],CUTOFFS)['verified'])
  for mode in ['log','histogram','coverage','sign','source']:
   bad=copy.deepcopy(profile)
   if mode=='log':bad['value']['log_bounds'][1]=[0,0];bad['value']['logs_sha256']=c.digest(bad['value']['log_bounds'])
   elif mode=='histogram':
    h=next(iter(bad['value']['histograms']));k=next(iter(bad['value']['histograms'][h]));bad['value']['histograms'][h][k]['lo']+=1
   elif mode=='coverage':bad['value']['rows'][0]['coverage']['all_triples']+=1
   elif mode=='sign':bad['value']['rows'][0]['normalized_negative_remainder']['lower']='999'
   else:bad['value']['rows'][0]['coefficients_sha256']='0'*64
   with self.assertRaises(ValueError):c.verify_profile(bad,[1,2,4,8],['mu','c'],CUTOFFS)
 def test_component_certificate(self):
  import prime_pair_forcing as p
  for target in ['mu','c']:
   for cutoff in CUTOFFS:
    self.assertEqual(c.prefix_certificate(target,cutoff),p.prefix_certificate(target,cutoff))
    self.assertEqual(c.prefix_certificate(target,cutoff)['cofinal_critical_component_bound'],cutoff['kind']!='power')
 def test_height_and_zero_cutoff(self):
  tab=c.factor_data(31);a=c.coefficients(31,'c',tab);self.assertEqual(a[12],-4);self.assertEqual(c.cutoff_value(8,{'kind':'fixed','value':0}),0)
  for X in range(1,9):
   for cutoff in CUTOFFS:self.assertGreaterEqual(c.cutoff_value(X,cutoff),0)
if __name__=='__main__':unittest.main()
