import copy
import unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_prime_mass_gate_078 as C

def program(a=None,eta='0',weight='1',q='1',tau='1/2'):
    return {'schema':'rough-energy-program-v1','q':q,'tau':tau,'rays':[{'a':['0','2']+['0']*8 if a is None else a,'eta':eta,'lambda':weight}],'innovation_C':'0'}
def certificate(m='1/2',P=(2,3),a='2',eta='0',weight='1',q='1'):
    mass=Q(m);delta=Q(1)
    for p in P:delta*=Q(p-1,p)
    sigma=2-2*Q(eta)-Q(q);leading=-mass*delta;lower=Q(weight)*(Q(a)*leading)**2/4
    return {'mass':str(mass),'delta':str(delta),'leading_prime':str(leading),'sigma':str(sigma),'eventual_lower_coefficient':str(lower),'ray_index':0}
class Tests(unittest.TestCase):
    def test_prime_mass_gate_and_no_promotion(self):
        kernel=[{'divisor':2,'weight':'1'}];cert=certificate();r=C.verify_prime_mass_gate(kernel,[2,3],'17/31',program(),cert)
        self.assertEqual(r['status'],'VERIFIED_PRIME_MASS_OBSTRUCTION');self.assertEqual(r['leading_prime'],'-1/6');self.assertEqual(r['eventual_lower_coefficient'],'1/36');self.assertTrue(r['uniform_drift_obstructed']);self.assertFalse(r['arithmetic_residual_refuted']);self.assertFalse(r['uniform_source_bound_proved']);self.assertFalse(r['RH_proved']);self.assertFalse(r['finite_u_threshold_supplied']);self.assertEqual(r['imported_theorem']['statement'],'pi(x)~x/log(x)')
    def test_normalization_and_signed_mass(self):
        kernel=[{'divisor':2,'weight':'2'},{'divisor':2,'weight':'-1'},{'divisor':7,'weight':'0'}]
        self.assertEqual(C.verify_gate(kernel,[2,3],'1/2',program(),certificate())['status'],'VERIFIED_PRIME_MASS_OBSTRUCTION')
        kernel=[{'divisor':2,'weight':'-1'}];cert=certificate('-1/2')
        r=C.verify_gate(kernel,[2,3],'1/2',program(),cert);self.assertEqual(r['status'],'VERIFIED_PRIME_MASS_OBSTRUCTION');self.assertEqual(r['leading_prime'],'1/6')
    def test_mass_zero_and_critical_unpaid(self):
        kernel=[{'divisor':1,'weight':'1'},{'divisor':2,'weight':'-2'}]
        self.assertEqual(C.verify_gate(kernel,[],'1/2',program(),certificate('0',()))['status'],'UNSUPPORTED')
        kernel=[{'divisor':2,'weight':'1'}]
        for eta in ('1/2','2/3'):
            self.assertEqual(C.verify_gate(kernel,[],'1/2',program(eta=eta),certificate(P=(),eta=eta))['status'],'UNSUPPORTED')
        self.assertEqual(C.verify_gate(kernel,[],'1/2',program(eta='17/100'),certificate(P=(),eta='17/100'))['status'],'VERIFIED_PRIME_MASS_OBSTRUCTION')
    def test_nonpure_negative_lambda_domains(self):
        kernel=[{'divisor':2,'weight':'1'}]
        for gamma in ('0','1','3/2'):
            self.assertEqual(C.verify_gate(kernel,[] ,gamma,program(),certificate(P=()))['status'],'INVALID')
        a=['1','2']+['0']*8;self.assertEqual(C.verify_gate(kernel,[],'1/2',program(a=a),certificate(P=()))['status'],'UNSUPPORTED')
        for weight in ('0','-1'):self.assertEqual(C.verify_gate(kernel,[],'1/2',program(weight=weight),certificate(P=()))['status'],'INVALID')
        for tau in ('-1','3/2'):self.assertEqual(C.verify_gate(kernel,[],'1/2',program(tau=tau),certificate(P=()))['status'],'INVALID')
        for q in ('0','2'):self.assertEqual(C.verify_gate(kernel,[],'1/2',program(q=q),certificate(P=()))['status'],'INVALID')
    def test_certificate_fold_density_tampering_and_threshold(self):
        kernel=[{'divisor':2,'weight':'1'}];cert=certificate()
        for key,value in [('mass','1'),('delta','1'),('leading_prime','1/6'),('sigma','2'),('eventual_lower_coefficient','1/2')]:
            bad=copy.deepcopy(cert);bad[key]=value;self.assertEqual(C.verify_gate(kernel,[2,3],'1/2',program(),bad)['status'],'INVALID')
        bad=copy.deepcopy(cert);bad['u_threshold']=100;self.assertEqual(C.verify_gate(kernel,[2,3],'1/2',program(),bad)['status'],'INVALID')
        for P in ([3,2],[2,2],[4]):self.assertEqual(C.verify_gate(kernel,P,'1/2',program(),cert)['status'],'INVALID')
    def test_generic_direct_source_kernel_binding(self):
        base=[{'divisor':3,'weight':'2'},{'divisor':7,'weight':'-1'}]
        spec={'grid':80,'theta':['1/2','3/4'],'multipliers':[2,5]}
        source={'spec':spec,'atoms':[{'column':1,'gamma':'17/31'},{'column':1,'gamma':'1'},{'column':2,'gamma':'1001/1000'}],'operator':['1/3','-1/6','-2']}
        derived=base+[{'divisor':6,'weight':'-1/3'},{'divisor':14,'weight':'1/6'},{'divisor':15,'weight':'4'},{'divisor':35,'weight':'-2'}]
        r=C.verify_kernel(base,source,derived);self.assertEqual(r['status'],'VERIFIED_FIXED_KERNEL');self.assertTrue(r['source_program_admission_still_required'])
        bad=copy.deepcopy(derived);bad[-1]['weight']='2';self.assertEqual(C.verify_kernel(base,source,bad)['status'],'INVALID')
        bad=copy.deepcopy(source);bad['atoms'][0]['column']=0;self.assertEqual(C.verify_kernel(base,bad,derived)['status'],'UNSUPPORTED')
    def test_empty_rays_resource_and_canonical(self):
        kernel=[{'divisor':2,'weight':'1'}];p=program();p['rays']=[]
        self.assertEqual(C.verify_gate(kernel,[],'1/2',p,certificate(P=()))['status'],'UNSUPPORTED')
        self.assertEqual(C.verify_gate([{'divisor':True,'weight':'1'}],[],'1/2',program(),certificate(P=()))['status'],'INVALID')
        self.assertEqual(C.verify_gate([{'divisor':2,'weight':'2/4'}],[],'1/2',program(),certificate(P=()))['status'],'INVALID')
        with patch.object(C.Meter,'reserve',side_effect=C.ResourceLimit('prospective memory')):
            r=C.verify_gate(kernel,[],'1/2',program(),certificate(P=()))
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['resource_limit'])
if __name__=='__main__':unittest.main()
