import unittest,copy
from fractions import Fraction as F
import grouped_arithmetic_language as L
import cancellation_shared_gram_synthesis as S
import cancellation_shared_gram_language as P

def poly(p):return L.dump_poly({m:F(q)for m,q in p.items()})
def fixture():
 a=poly({(1,):1});b=poly({():F(-1,2),(2,):1})
 q=L.add(L.load_poly(a),L.scale(L.load_poly(b),-2))
 lhs=L.dump_poly(L.mul(q,q))
 return [dict(target='mu',horizon=2,lhs=lhs,square_groups=[],relation_groups=[])],[{'cell':[[a,b]]}],{'cell':2}

class SharedGramTests(unittest.TestCase):
 def test_mix_constants(self):
  instances,blocks,specs=fixture();r=S.synthesize(instances,blocks,gram_specs=specs,time_limit=20)
  self.assertEqual(r['status'],'finite_PSD_certificate',r)
  self.assertEqual(r['grams']['cell'],[['1','-2'],['-2','4']])
  self.assertEqual(r['constant_slacks'],['0'])
 def test_constant_cross_sos_and_tamper(self):
  _,b,_=fixture();p=P.instantiate_sos([['1','-2'],['-2','4']],b[0]['cell'])
  self.assertIn({'m':[],'c':'1'},p['polynomial'])
  with self.assertRaises(ValueError):P.instantiate_sos([['1','-2'],['-2','3']],b[0]['cell'])
 def test_zero_gram_skips_products_but_checks_atoms(self):
  atoms=[poly({(j,):1 for j in range(1,41)})]*2
  proof=P.instantiate_sos([['0','0'],['0','0']],[atoms],max_operations=200)
  self.assertEqual(proof['squares'],[])
  self.assertEqual(proof['polynomial'],[])
  bad=copy.deepcopy(atoms);bad[0][0]['c']='1.0'
  with self.assertRaises(ValueError):P.instantiate_sos([['0','0'],['0','0']],[bad],max_operations=200)
  with self.assertRaises(OverflowError):P.instantiate_sos([['1','0'],['0','0']],[atoms],max_operations=200)
 def test_partial_gram_active_products_only(self):
  atoms=[poly({(1,):1}),poly({(j,):1 for j in range(1,41)})]
  proof=P.instantiate_sos([['1','0'],['0','0']],[atoms],max_operations=200)
  self.assertEqual(proof['polynomial'],poly({(1,1):1}))
  with self.assertRaises(TimeoutError):P.instantiate_sos([['0','0'],['0','0']],[atoms],deadline=0)
 def test_resource_caps(self):
  i,b,s=fixture()
  for limits in ({'max_columns':3},{'max_operations':1},{'max_exact_cells':1}):
   r=S.synthesize(i,b,gram_specs=s,time_limit=20,**limits)
   self.assertEqual(r['status'],'missing_resource',r)
 def test_empty_aux_and_sort(self):
  i,b,s=fixture();i.append(dict(target='mu',horizon=1,lhs=[],square_groups=[],relation_groups=[]));b.append({'cell':[]})
  r=S.synthesize(i,b,gram_specs=s,time_limit=20);self.assertEqual(r['status'],'finite_PSD_certificate',r)
 def test_zero_weight_scalar_skips_expansion(self):
  i,b,s=fixture();i=i[0];i['square_groups']=[[{'weight':'1','poly':poly({(1,):1,(2,):1})}]]
  r=S.instantiate_certificate(i,{'square_weights':['0'],'relation_weights':[]},{'cell':[['1','-2'],['-2','4']]},b[0],max_operations=500,max_horizon=2)
  self.assertTrue(r['Gram_proofs']['cell']['shared_Gram_verified'])
if __name__=='__main__':unittest.main()
