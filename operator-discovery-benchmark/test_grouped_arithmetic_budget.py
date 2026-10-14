import unittest
from fractions import Fraction as F
import grouped_arithmetic_budget as B
import grouped_arithmetic_templates as T
import grouped_arithmetic_language as L
class Tests(unittest.TestCase):
 def test_full_expansion_constant(self):
  d=T.descriptors()
  for target in ('mu','c'):
   for X in (1,2,4):
    build=T.build_instance(target,X,2,1,'unsigned_calibration')
    sw=['0']*52;rw=['0']*195
    for i,v in enumerate(d['square']):
     if v['family']=='prefix' and v['region']=='parent' and v['weight']=='one':sw[i]='4'
     if v['family']=='pair' and v['domain']=='all' and v['sign']==-1 and v['weight']=='child_kernel':sw[i]='1'
    for i,v in enumerate(d['relation']):
     if v['family']=='norm' and v['region']=='all' and v['weight']=='child_rowmass' and v['multiplier']=='one':rw[i]='-1'
    report=B.extract_budget(build,dict(square_weights=sw,relation_weights=rw));self.assertEqual(report['B'],build['D'])
    # Diverse weights exercise all possible scalar-producing groups.
    sw[0]='2/3';rw=[str(F(i-90,13)) for i in range(195)];rhs={}
    for w,group in zip(sw,build['instance']['square_groups']):
     for term in group:rhs=L.add(rhs,L.scale(L.mul(L.load_poly(term['poly']),L.load_poly(term['poly'])),F(w)*F(term['weight'])))
    for w,group in zip(rw,build['instance']['relation_groups']):
     for term in group:rhs=L.add(rhs,L.scale(L.mul(L.load_poly(term['multiplier']),L.relation(term['spec'],target,4*X-1)),F(w)))
    report=B.extract_budget(build,dict(square_weights=sw,relation_weights=rw));self.assertEqual(F(report['B']),rhs.get((),F(0)))
 def test_rejected_weights(self):
  b=T.build_instance('mu',1,2,1)
  with self.assertRaises(ValueError):B.extract_budget(b,dict(square_weights=['0'],relation_weights=[]))
if __name__=='__main__':unittest.main()
