import unittest,copy
import check_cancellation_gram as C
class Tests(unittest.TestCase):
 def test_all_principal_minors(self):
  C.verify_psd([['1','1'],['1','1']])
  for m in [[['0','1'],['1','0']],[['1','2'],['2','1']]]:
   with self.assertRaises(ValueError):C.verify_psd(m)
 def test_exact_input_guards(self):
  for q in [True,1.0,'1e10000000']:
   with self.assertRaises(ValueError):C.verify_psd([[q]])
 def fixture(self):
  z=[['0']*5 for _ in range(5)];p=copy.deepcopy(z);p[0][0]='1'
  poly=[dict(m=[1,1],c='1')];inst=dict(target='mu',horizon=3,lhs=poly,square_groups=[],relation_groups=[])
  cert=dict(target='mu',horizon=3,lhs=poly,squares=[dict(weight='1',poly=[dict(m=[1],c='1')])],relations=[])
  r=dict(status='finite_PSD_certificate',weights=dict(square_weights=[],relation_weights=[]),grams=dict(parent=p,child=z),constant_slacks=['0'],certificates=[dict(certificate=cert)])
  return inst,r
 def test_actual_blocks_and_full_cross(self):
  i,r=self.fixture();C.verify_primal([i],[1],r)
  bad=copy.deepcopy(r);bad['grams']['parent'][0][1]=bad['grams']['parent'][1][0]='1'
  with self.assertRaises(ValueError):C.verify_primal([i],[1],bad)
 def test_slack_target_binding(self):
  i,r=self.fixture();r['constant_slacks']=['1']
  with self.assertRaises(ValueError):C.verify_primal([i],[1],r)
  i,r=self.fixture();r['certificates'][0]['certificate']['horizon']=4
  with self.assertRaises(ValueError):C.verify_primal([i],[1],r)
if __name__=='__main__':unittest.main()
