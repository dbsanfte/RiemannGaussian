import unittest
from fractions import Fraction as F
import grouped_arithmetic_language as L
import cancellation_gram_synthesis as S
from check_arithmetic_cycle_certificate import verify_certificate
class Tests(unittest.TestCase):
 def test_anonymous_shared_PSD_cross(self):
  instances=[];blocks=[]
  for offset in (0,5):
   atoms=[L.dump_poly(L.variable(i+offset+1))for i in range(5)];p=L.add(L.variable(offset+1),L.scale(L.variable(offset+2),F(-2,3)))
   lhs=L.dump_poly(L.add(L.scale(L.mul(p,p),F(5,9)),L.constant(offset+3)))
   instances.append(dict(target='mu',horizon=offset+5,lhs=lhs,square_groups=[],relation_groups=[]));blocks.append(dict(parent=[atoms],child=[]))
  result=S.synthesize(instances,gram_blocks=blocks,time_limit=30)
  self.assertEqual(result['status'],'finite_PSD_certificate',result)
  self.assertEqual(result['grams']['parent'][0][1],'-10/27')
  for record in result['certificates']:self.assertTrue(verify_certificate(record['certificate'])['finite_identity_verified'])
  self.assertFalse(result['RH_proved'])
 def test_negative_square_no_false_admission(self):
  atoms=[L.dump_poly(L.variable(i))for i in range(1,6)];i=dict(target='mu',horizon=5,lhs=L.dump_poly(L.scale(L.mul(L.variable(1),L.variable(1)),-1)),square_groups=[],relation_groups=[])
  r=S.synthesize([i],gram_blocks=[dict(parent=[atoms],child=[])],time_limit=10)
  self.assertIn(r['status'],('uncertified','missing_resource'));self.assertFalse(r['global_bound_proved'])
  import json
  json.dumps(r,allow_nan=False)
  self.assertEqual(S.synthesize([i],gram_blocks=[dict(parent=[atoms],child=[])],time_limit='bad')['status'],'uncertified')
 def test_complete_actual_preparation_only(self):
  import cancellation_arithmetic_templates as T
  import cancellation_cubic_gate as C
  b=T.build_instance('mu',1,6,32);aux=C.build_constraint(T.descriptors())['instance']
  cols,lhs,ms,shape,offset,blocks=S.prepare([b['instance'],aux],[1])
  self.assertEqual(len(cols),offset+30);self.assertEqual(blocks[1],dict(parent=[],child=[]));self.assertEqual(len(blocks[0]['parent']),1);self.assertEqual(len(blocks[0]['child']),2)
if __name__=='__main__':unittest.main()
