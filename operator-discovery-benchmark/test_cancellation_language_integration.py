"""Bounded generic AST calibration; supplied identity family, inferred shared weights.
No actual signed coefficients and no RH or unseen-operator discovery claim.
"""
import unittest
from fractions import Fraction as F
import grouped_arithmetic_language as L
import cancellation_arithmetic_synthesis as S
from check_grouped_arithmetic import verify_joint_result,verify_joint

def fixture(target,X,a=F(5,9),b=F(-7,11)):
 from cancellation_arithmetic_language import compile_expression
 N=6*X
 P=['sum','j',['int',1],['imul',['int',2],['v','X']],['add',['x',['imul',['int',2],['v','j']]],['scale','-1',['x',['imul',['int',3],['v','j']]]]]]
 Q=['sum','j',['int',1],['v','X'],['x',['v','j']]]
 p=compile_expression(P,X=X,horizon=N)['poly'];m=compile_expression(['mul',P,Q],X=X,horizon=N)['poly']
 rho={'kind':'coprime_product','a':2,'b':3}
 lhs=L.add(L.scale(L.mul(L.load_poly(p),L.load_poly(p)),a),L.scale(L.mul(L.load_poly(m),L.relation(rho,target,N)),b),L.constant(X+2))
 return dict(target=target,horizon=N,lhs=L.dump_poly(lhs),square_groups=[[dict(weight='1',poly=p)]],relation_groups=[[dict(spec=rho,multiplier=m)]])
class Tests(unittest.TestCase):
 def test_prime_dilate_signed_multiplier_shared_recovery(self):
  for target in ('mu','c'):
   train=[fixture(target,1),fixture(target,2)]
   result=S.synthesize(train)
   self.assertEqual(result['status'],'finite_certificate')
   self.assertEqual(result['weights'],dict(square_weights=['5/9'],relation_weights=['-7/11']))
   self.assertTrue(verify_joint_result(train,result,allow_constant_slack=True)['verified'])
   self.assertTrue(verify_joint([fixture(target,3)],**result['weights'],allow_constant_slack=True)['verified'])
 def test_wrong_shared_signed_weight_rejected(self):
  weights=dict(square_weights=['5/9'],relation_weights=['7/11'])
  with self.assertRaises(ValueError):verify_joint([fixture('mu',2)],**weights,allow_constant_slack=True)
if __name__=='__main__':unittest.main()
