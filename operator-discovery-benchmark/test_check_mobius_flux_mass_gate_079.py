import copy
import unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_flux_mass_gate_079 as C

def ray(a1='1',a9='0'):
    result=['0']*10;result[1]=a1;result[9]=a9;return result

def certificate(m='1/2',P=(2,3),gamma='2/3',q='1',a=None):
    a=ray() if a is None else a;mass=Q(m);delta=Q(1)
    for p in P:delta*=Q(p-1,p)
    if Q(a[9]):
        alpha=2*Q(gamma)/3;z=1-2*alpha;N=32
        lo=2*sum((z**(2*k+1)/Q(2*k+1) for k in range(N)),Q(0));hi=lo+2*z**(2*N+1)/((2*N+1)*(1-z*z))
        vals=[mass*delta*(-Q(a[1])+Q(a[9])*x)/2 for x in (lo,hi)];lower,upper=min(vals),max(vals)
    else:N=0;lower=upper=-mass*delta*Q(a[1])/2
    return {'mass':str(mass),'delta':str(delta),'leading_lower':str(lower),'leading_upper':str(upper),'sigma':str(2-Q(q)),'log_terms':N}
class Tests(unittest.TestCase):
    def test_pure_prime_and_scope(self):
        kernel=[{'divisor':2,'weight':'1'}];r=C.verify_gate(kernel,[2,3],'17/31','1001/1000',ray(),certificate(q='1001/1000'))
        self.assertEqual(r['status'],'VERIFIED_FLUX_MASS_OBSTRUCTION');self.assertEqual(r['leading_lower'],'-1/12');self.assertEqual(r['leading_upper'],'-1/12');self.assertEqual(r['eventual_square_lower_coefficient'],'1/576');self.assertFalse(r['arithmetic_residual_refuted']);self.assertFalse(r['residual_lower_bound_proved']);self.assertFalse(r['RH_proved']);self.assertFalse(r['finite_u_threshold_supplied'])
    def test_coupled_log_interval_and_signed_mass(self):
        for mass,weight in (('1/2','1'),('-1/2','-1')):
            kernel=[{'divisor':2,'weight':weight}];a=ray('2','1');cert=certificate(m=mass,a=a)
            r=C.verify_gate(kernel,[2,3],'2/3','1',a,cert);self.assertEqual(r['status'],'VERIFIED_FLUX_MASS_OBSTRUCTION');self.assertLess(Q(r['log_lower']),Q(r['log_upper']));self.assertTrue(Q(r['leading_lower'])>0 or Q(r['leading_upper'])<0)
        a=ray('0','-2');r=C.verify_gate([{'divisor':2,'weight':'1'}],[2,3],'17/31','1',a,certificate(gamma='17/31',a=a))
        self.assertEqual(r['status'],'VERIFIED_FLUX_MASS_OBSTRUCTION');self.assertLess(Q(r['leading_upper']),0)
    def test_unpaid_log_interval_and_zero_mass(self):
        alpha=Q(4,9);z=1-2*alpha;N=32;lo=2*sum((z**(2*k+1)/Q(2*k+1) for k in range(N)),Q(0));hi=lo+2*z**65/(65*(1-z*z));a=ray(str((lo+hi)/2),'1')
        r=C.verify_gate([{'divisor':2,'weight':'1'}],[2,3],'2/3','1',a,certificate(a=a));self.assertEqual(r['status'],'UNPAID');self.assertFalse(r['uniform_covariance_leaf_obstructed'])
        kernel=[{'divisor':1,'weight':'1'},{'divisor':2,'weight':'-2'}]
        self.assertEqual(C.verify_gate(kernel,[],'2/3','1',ray(),certificate(m='0',P=()))['status'],'UNPAID')
    def test_domain_and_other_bins_unpaid(self):
        kernel=[{'divisor':2,'weight':'1'}];a=ray('1','1')
        for gamma in ('1/2','3/4','4/5'):
            self.assertEqual(C.verify_gate(kernel,[] ,gamma,'1',a,certificate(P=(),a=a))['status'],'UNSUPPORTED')
        a=ray();a[7]='1';self.assertEqual(C.verify_gate(kernel,[],'2/3','1',a,certificate(P=()))['status'],'UNSUPPORTED')
        for gamma in ('0','1','-1/2'):
            self.assertEqual(C.verify_gate(kernel,[],gamma,'1',ray(),certificate(P=()))['status'],'UNSUPPORTED')
        for q in ('0','2','3'):
            self.assertEqual(C.verify_gate(kernel,[],'2/3',q,ray(),certificate(P=()))['status'],'INVALID')
    def test_tampered_mass_density_sign_terms_threshold(self):
        kernel=[{'divisor':2,'weight':'1'}];a=ray('1','1');cert=certificate(a=a)
        for key,value in [('mass','1'),('delta','1'),('leading_lower','0'),('leading_upper','0'),('sigma','2'),('log_terms',31)]:
            bad=copy.deepcopy(cert);bad[key]=value;self.assertEqual(C.verify_gate(kernel,[2,3],'2/3','1',a,bad)['status'],'INVALID')
        bad=copy.deepcopy(cert);bad['finite_u_threshold']=1;self.assertEqual(C.verify_gate(kernel,[2,3],'2/3','1',a,bad)['status'],'INVALID')
        pure=certificate();pure['log_terms']=32;self.assertEqual(C.verify_gate(kernel,[2,3],'2/3','1',ray(),pure)['status'],'INVALID')
        for P in ([3,2],[2,2],[4]):self.assertEqual(C.verify_gate(kernel,P,'2/3','1',ray(),certificate())['status'],'INVALID')
    def test_normalization_canonical_and_resource(self):
        kernel=[{'divisor':2,'weight':'2'},{'divisor':2,'weight':'-1'},{'divisor':7,'weight':'0'}]
        self.assertEqual(C.verify_gate(kernel,[2,3],'2/3','1',ray(),certificate())['status'],'VERIFIED_FLUX_MASS_OBSTRUCTION')
        kernel[0]['weight']='2/2';self.assertEqual(C.verify_gate(kernel,[2,3],'2/3','1',ray(),certificate())['status'],'INVALID')
        with patch.object(C.Meter,'reserve',side_effect=C.ResourceLimit('prospective memory')):
            r=C.verify_gate([],[],'2/3','1',ray(),certificate(m='0',P=()))
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['resource_limit'])
if __name__=='__main__':unittest.main()
