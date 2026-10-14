import unittest
from fractions import Fraction as F
import prime_pair_forcing as p
class TestPrimePair(unittest.TestCase):
 def test_complete_pair_and_partitions(self):
  a=p.profile([1,2,4,8],['mu','c'],[{'kind':'fixed','value':b} for b in [0,1,2,32]],work_budget=2000000,max_n=31,bits=24)
  self.assertEqual(a['status'],'available')
  for r in a['value']['rows']:
   histogram=a['value']['histograms'][r['histogram_id']]
   self.assertEqual(p.digest(histogram),r['histogram_sha256'])
   D=r['D'];exact=F(r['J1']-r['Delta'],2*r['kappa'])
   self.assertLessEqual(F(r['S']['lo'],D),exact);self.assertGreaterEqual(F(r['S']['hi'],D),exact)
   for end in ('lo','hi'):self.assertEqual(r['S'][end],r['prefix'][end]+r['remainder'][end])
   self.assertEqual(r['complete_triples'],sum(h['triples'] for h in histogram.values()))
   self.assertEqual(r['zero_terms'],sum(h['zero_terms'] for h in histogram.values()))
   if r['B']==0:self.assertEqual(r['prefix'],dict(lo=0,hi=0))
   if r['B']>=r['N']:self.assertEqual(r['remainder'],dict(lo=0,hi=0))
 def test_log_enclosure_and_precision(self):
  lo,hi=p.log_interval(2,32)
  # log2=sum (-1)^(j+1)/j; even/odd partial sums independently enclose it.
  lower=sum((F(1 if j%2 else -1,j) for j in range(1,1001)),F(0));upper=lower+F(1,1001)
  self.assertGreater(lo,lower);self.assertLess(hi,upper)
  self.assertLess(hi-lo,F(1,2**32));self.assertEqual(p.log_interval(1,32),(0,0))
  l4,h4=p.log_interval(4,32);self.assertGreaterEqual(l4,2*lo);self.assertLessEqual(h4,2*hi)
 def test_cutoff_and_missing(self):
  self.assertEqual(p.cutoff_value(8,dict(kind='power',power='1/3')),2)
  self.assertEqual(p.cutoff_value(9,dict(kind='power',power='1/3')),2)
  self.assertEqual(p.cutoff_value(8,dict(kind='bit_length_power',power='1/2')),2)
  a=p.profile([8],['mu'],[dict(kind='fixed',value=0)],work_budget=1,max_n=31,bits=16)
  self.assertEqual(a['status'],'missing');self.assertIsNone(a['value'])
  with self.assertRaises(OverflowError):p.cutoff_value(8,dict(kind='power',power='1/'+str(10**100)))
 def test_certificate_scope(self):
  for target in ['mu','c']:
   self.assertEqual(p.prefix_certificate(target,dict(kind='fixed',value=0))['scalar'],'0')
   a=p.prefix_certificate(target,dict(kind='bit_length_power',power='3/2'))
   self.assertTrue(a['cofinal_critical_component_bound']);self.assertFalse(a['full_signed_bound_proved'])
   self.assertFalse(p.prefix_certificate(target,dict(kind='power',power='1/6'))['cofinal_critical_component_bound'])
 def test_domains(self):
  with self.assertRaises(ValueError):p.cutoff_descriptor(dict(kind='fixed',value=True))
  with self.assertRaises(ValueError):p.profile([1],['unsigned'],[],work_budget=100,max_n=3)
if __name__=='__main__':unittest.main()
