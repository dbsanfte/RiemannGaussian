import copy
import unittest
from fractions import Fraction as Q
import check_mobius_full_mode_gate_080 as C

def logs(r):
 r=Q(r);z=(r-1)/(r+1);t=abs(z);lo=2*sum((t**(2*i+1)/Q(2*i+1) for i in range(32)),Q(0));hi=lo+2*t**65/(65*(1-t*t))
 return (-hi,-lo) if z<0 else (lo,hi)
def logspec(g):
 r=(3-2*Q(g))/(2*Q(g));lo,hi=logs(r);return {'argument':str(r),'terms':32,'lower':str(lo),'upper':str(hi)}
def rho():
 lower=logs(3)[0];lower=Q((lower*2**40).__floor__(),2**40);summands=[]
 for i in range(1,65):
  v=Q(64+i,64);x=logs(v)[1]/(64*(v+1));summands.append(Q((x*2**40).__ceil__(),2**40))
 return {'mesh':64,'bits':40,'log_terms':32,'lower_log_three':str(lower),'upper_riemann_summands':list(map(str,summands)),'rho_three_upper':str(1-lower+sum(summands))}
def ray():return [['0','0'] for i in range(10)]
def cert(a,g='5/8',mass=Q(1),delta=Q(1)):
 lo,hi=logs((3-2*Q(g))/(2*Q(g)));rv=Q(rho()['rho_three_upper']);aa=[list(map(Q,x)) for x in a];values=[]
 for R in (Q(0),rv):
  poly=[mass*delta/2*(-aa[1][0]+aa[8][0]+(aa[7][0]-aa[8][0])*R),mass*delta/2*(-aa[1][1]+aa[8][1]+aa[9][0]-aa[8][0]+(aa[7][1]-aa[8][1])*R),mass*delta/2*(aa[9][1]-aa[8][1])]
  evaluate=lambda x:poly[0]+poly[1]*x+poly[2]*x*x
  values += [evaluate(lo),evaluate(hi)]
  if poly[2]:
   x=-poly[1]/(2*poly[2])
   if lo<=x<=hi:values.append(evaluate(x))
 return {'mass':str(mass),'delta':str(delta),'leading_lower':str(min(values)),'leading_upper':str(max(values))}
K=[{'divisor':1,'weight':'1'}]
class Tests(unittest.TestCase):
 def test_rho_exact_endpoint_certificate_and_mutations(self):
  r=rho();v=C.verify_rho(r);self.assertEqual(v['status'],'VERIFIED_DICKMAN_ENVELOPE');self.assertLess(Q(v['rho_three_upper']),Q(1,16))
  for key,value in [('mesh',63),('bits',39),('log_terms',31),('rho_three_upper','1/16'),('lower_log_three','1')]:
   bad=copy.deepcopy(r);bad[key]=value;self.assertEqual(C.verify_rho(bad)['status'],'INVALID')
  bad=copy.deepcopy(r);bad['upper_riemann_summands'][0]='0';self.assertEqual(C.verify_rho(bad)['status'],'INVALID')
 def test_observed_complement_full_mode_and_negative_mass(self):
  a=ray();a[1]=['1','-1'];a[7]=['1/2','0'];g='5/8'
  v=C.verify_full_mode(K,[],g,a,logspec(g),rho(),cert(a,g));self.assertEqual(v['status'],'VERIFIED_FULL_MODE_OBSTRUCTION');self.assertLess(Q(v['leading_upper']),0)
  self.assertFalse(v['arithmetic_residual_refuted']);self.assertFalse(v['RH_proved']);self.assertFalse(v['finite_u_threshold_supplied'])
  neg=[{'divisor':1,'weight':'-1'}];v=C.verify_full_mode(neg,[2,3],g,a,logspec(g),rho(),cert(a,g,Q(-1),Q(1,3)));self.assertEqual(v['status'],'VERIFIED_FULL_MODE_OBSTRUCTION');self.assertGreater(Q(v['leading_lower']),0)
 def test_zero_mode_zero_mass_and_unknown_domain(self):
  a=ray();a[1]=['0','1'];a[9]=['1','0'];g='5/8'
  self.assertEqual(C.verify_full_mode(K,[],g,a,logspec(g),rho(),cert(a,g))['status'],'UNPAID')
  a[1]=['1','0'];self.assertEqual(C.verify_full_mode([],[],g,a,logspec(g),rho(),cert(a,g,Q(0)))['status'],'UNPAID')
  a[2]=['1','0'];self.assertEqual(C.verify_full_mode(K,[],g,a,logspec(g),rho(),cert(a,g))['status'],'UNSUPPORTED')
  a[2]=['0','0'];self.assertEqual(C.verify_full_mode(K,[],'1/2',a,logspec('1/2'),rho(),cert(a,'1/2'))['status'],'UNSUPPORTED')
  self.assertEqual(C.verify_full_mode(K,[],'3/4',a,logspec('3/4'),rho(),cert(a,'3/4'))['status'],'UNSUPPORTED')
 def test_coupled_affine_quadratic_vertex_and_tampered_sign(self):
  a=ray();a[1]=['1','-2'];a[9]=['0','1'];g='2/3'
  v=C.verify_full_mode(K,[],g,a,logspec(g),rho(),cert(a,g));self.assertEqual(v['status'],'VERIFIED_FULL_MODE_OBSTRUCTION')
  bad=cert(a,g);bad['mass']='2';self.assertEqual(C.verify_full_mode(K,[],g,a,logspec(g),rho(),bad)['status'],'INVALID')
  self.assertEqual(C.verify_full_mode(K,[],g,a,logspec('5/8'),rho(),cert(a,g))['status'],'INVALID')
  self.assertEqual(C.verify_full_mode(K,[3,2],g,a,logspec(g),rho(),cert(a,g))['status'],'INVALID')
 def test_strict_positive_rho_only_without_fake_numeric_lower(self):
  a=ray();a[7]=['1','1'];g='5/8';v=C.verify_full_mode(K,[],g,a,logspec(g),rho(),cert(a,g))
  self.assertEqual(v['status'],'VERIFIED_FULL_MODE_OBSTRUCTION');self.assertTrue(v['strict_positive_rho_reason']);self.assertFalse(v['numerical_nonzero_lower_bound_supplied']);self.assertNotIn('eventual_square_lower_coefficient',v)
 def test_second_mode_exact_moment_and_first_identity(self):
  a=ray();a[1]=['0','1'];a[9]=['1','0'];g='5/8';kernel=[{'divisor':4,'weight':'1'}]
  c={'mass':'1/4','delta':'1','moment_lower':'1/4','moment_upper':'1/4','leading_lower':'-3/14','leading_upper':'-3/14'}
  v=C.verify_second_mode(kernel,[],g,a,logspec(g),c);self.assertEqual(v['status'],'VERIFIED_SECOND_MODE_OBSTRUCTION');self.assertFalse(v['RH_proved'])
  a[1]=['0','2'];self.assertEqual(C.verify_second_mode(kernel,[],g,a,logspec(g),c)['status'],'INVALID')
  a[1]=['0','1'];a[7]=['1','0'];self.assertEqual(C.verify_second_mode(kernel,[],g,a,logspec(g),c)['status'],'UNSUPPORTED')
 def test_second_mode_prime_log_and_negative_weight(self):
  a=ray();a[1]=['0','-1'];a[9]=['-1','0'];g='2/3';lp,up=logs(2)
  # Tfixed=-1/4, mass=-1/4, delta1/2; Tfold=(-1+log2)/8.
  ml=(-1+lp)/8;mh=(-1+up)/8;factor=Q(9,10)
  c={'mass':'-1/4','delta':'1/2','moment_lower':str(ml),'moment_upper':str(mh),'leading_lower':str(factor*ml),'leading_upper':str(factor*mh)}
  kernel=[{'divisor':4,'weight':'-1'}]
  self.assertEqual(C.verify_second_mode(kernel,[2],g,a,logspec(g),c)['status'],'VERIFIED_SECOND_MODE_OBSTRUCTION')
  bad=dict(c);bad['delta']='1';self.assertEqual(C.verify_second_mode(kernel,[2],g,a,logspec(g),bad)['status'],'INVALID')
  self.assertEqual(C.verify_second_mode(kernel,[17],g,a,logspec(g),c)['status'],'INVALID')

 def test_prospective_memory_and_noncanonical(self):
  m=C.Meter();m.reserve=lambda x:(_ for _ in ()).throw(C.ResourceLimit('test cap'));self.assertEqual(C.verify_rho(rho(),m)['status'],'INVALID')
  r=rho();r['rho_three_upper']='2/2';self.assertEqual(C.verify_rho(r)['status'],'INVALID')
if __name__=='__main__':unittest.main()
