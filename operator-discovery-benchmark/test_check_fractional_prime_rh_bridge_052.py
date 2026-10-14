"""Synthetic admission/calculus calibrations; no source values or zero scans."""
import copy
from fractions import Fraction as Q
import unittest
import check_fractional_prime_rh_bridge_052 as C
import fractional_prime_rh_bridge_052 as P
from prime_bank_candidates import Meter as PipelineMeter

M=C.Meter(); PM=P.KERNEL.Meter()


def fixture(a='2/3',b='1/3',alpha='1/2'):
    request={'kernel':{'a':a,'b':b,'alpha':alpha,'sign':-1},
        'error_bound':{'kind':'all_epsilon_square_root','minimum':2,'uniform_x':True,
            'constants':'depend_on_epsilon_and_fixed_kernel_only'},
        'centering':{'kind':'full_positive_density_integral'}}
    return request,P.build_certificate(request,PM)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_fractional_prime_rh_bridge_052 operations='+str(M.operations+PM.operations))


class AdmissionTests(unittest.TestCase):
    def bad(self,mutate):
        r,c=fixture();mutate(r,c)
        with self.assertRaises(ValueError):C.verify(r,c,M)

    def test_forward_implication_only(self):
        r,c=fixture();v=C.verify(r,c,M)
        self.assertIs(v['verified'],True);self.assertIs(v['RH_proved'],False)
        self.assertEqual(v['error_status'],'OPEN')

    def test_zero_b_full_density(self):
        r,c=fixture('1','0','3/7');v=C.verify(r,c,M)
        self.assertTrue(v['all_zero_multiplicities'])
        self.assertIn('m(1)/(s-1)',c['mellin_bridge']['H_continuation_domain'])

    def test_arbitrary_parameter_denominators(self):
        for a,b,alpha in [('193/257','64/257','123/257'),('1000/1001','1/1001','1/4097')]:
            r,c=fixture(a,b,alpha);self.assertTrue(C.verify(r,c,M)['verified'])

    def test_real_pipeline_meter(self):
        r,c=fixture();m=PipelineMeter(cap=100000,seconds=30)
        self.assertTrue(C.verify(r,c,m)['verified']);self.assertGreater(m.operations,0)
        M.charge(m.operations)

    def test_wrong_kernel_family(self):
        for changes in [{'a':'1/3','b':'2/3'},{'a':'1/2','b':'1/2'},
                {'a':'2/3','b':'1/2'},{'sign':1},{'b':'-1/3','a':'4/3'}]:
            r,c=fixture();r['kernel'].update(changes)
            with self.assertRaises(ValueError):C.verify(r,c,M)

    def test_concavity_endpoints(self):
        for alpha in ['0','1','2','-1/3']:
            r,c=fixture();r['kernel']['alpha']=alpha
            with self.assertRaises(ValueError):C.verify(r,c,M)

    def test_strict_rational_and_bool_types(self):
        for value in ['2/4','0.5',Q(1,2),.5,True]:
            r,c=fixture();r['kernel']['alpha']=value
            with self.assertRaises(ValueError):C.verify(r,c,M)
        self.bad(lambda r,c:r['kernel'].update(sign=True))
        self.bad(lambda r,c:r['error_bound'].update(minimum=True))
        self.bad(lambda r,c:c.update(conditional_RH_implication_proved=1))

    def test_capacity_guard(self):
        r,c=fixture();r['kernel']['alpha']='1/'+str(1<<4096)
        with self.assertRaises(ValueError):C.verify(r,c,M)
        with self.assertRaises(OverflowError):C.verify(*fixture(),C.Meter(cap=1))

    def test_request_and_certificate_source_binding(self):
        self.bad(lambda r,c:c['request']['kernel'].update(alpha='1/3'))
        self.bad(lambda r,c:c['pointwise_dependency']['request'].update(b='1/4'))
        self.bad(lambda r,c:c['parameters'].update(c='1/2'))
        self.bad(lambda r,c:r.update(extra='unlicensed'))

    def test_all_real_all_epsilon_quantifiers(self):
        self.bad(lambda r,c:r['error_bound'].update(kind='one_fixed_epsilon'))
        self.bad(lambda r,c:r['error_bound'].update(uniform_x=False))
        self.bad(lambda r,c:c['open_premise'].update(quantifiers='finite sampled integers'))
        self.bad(lambda r,c:c['open_premise'].update(source='registered primes only'))

    def test_full_center_not_asymptotic(self):
        self.bad(lambda r,c:r['centering'].update(kind='leading_asymptotic'))
        self.bad(lambda r,c:c['center'].update(density='fitted density'))
        self.bad(lambda r,c:c['center'].update(fitted_or_asymptotic_center_allowed=True))
        self.bad(lambda r,c:c['center'].update(primitive='M(x)=m(1)*x'))

    def test_initial_domain_and_compact_head(self):
        self.bad(lambda r,c:c['mellin_bridge'].update(initial_domain='Re(s)>1/2'))
        self.bad(lambda r,c:c['mellin_bridge'].update(centered_identity='integral_2^infinity only'))
        self.bad(lambda r,c:c['mellin_bridge'].update(H_initial='leading main only'))

    def test_rightmost_at_fixed_height_and_reflection(self):
        self.bad(lambda r,c:c['zero_obstruction'].update(choice='globally rightmost zero'))
        self.bad(lambda r,c:c['zero_obstruction'].update(continuation_path='zero-free half-plane'))
        self.bad(lambda r,c:c['zero_obstruction'].pop('reflection'))

    def test_multiple_zero_and_integrated_remainder(self):
        self.bad(lambda r,c:c['zero_obstruction'].update(multiplicity='simple zeros only'))
        self.bad(lambda r,c:c['zero_obstruction'].update(local_error='O(delta+t) without subtraction'))
        self.bad(lambda r,c:c['zero_obstruction'].update(coefficient_sign='nonpositive maybe zero'))

    def test_open_premise_cannot_be_paid(self):
        for key in ['error_bound_proved','finite_samples_can_pay','pointwise_kernel_bound_can_pay']:
            self.bad(lambda r,c,key=key:c['open_premise'].update({key:True}))
        self.bad(lambda r,c:c['open_premise'].update(status='PAID'))
        self.bad(lambda r,c:c['pointwise_dependency'].update(pays_centered_error=True))

    def test_no_unconditional_or_converse_claims(self):
        for key in ['RH_proved','RH_refuted','centered_error_proved','converse_proved',
            'unconditional_continuation_to_half_plane_proved','original_floor_energy_bound_proved',
            'numerical_evidence_used']:
            self.bad(lambda r,c,key=key:c.update({key:True}))

    def test_strict_local_coefficient_calculus(self):
        # An arbitrary multiplicity has a nonzero sign, rather than relying on
        # a guessed simple zero or a floating numerical zero experiment.
        for a,b in [(Q(2,3),Q(1,3)),(Q(1),Q(0)),(Q(193,257),Q(64,257))]:
            for d in [1,2,7,20]:
                for u in [Q(1,100),Q(1),Q(100)]:
                    ratio=((1+b*u)/(1+a*u))**d
                    self.assertLess(ratio-1,0);self.assertGreaterEqual(ratio,0)
                    M.charge(10*d)
                # At zero, derivative = d*(b-a)<0; at infinity bracket
                # stays bounded and has nonzero limit, including b=0.
                self.assertLess(d*(b-a),0)
                self.assertLess((b/a)**d-1,0)

    def test_g_ratio_error_vanishes_with_t(self):
        # Local nonzero analytic G(z)=1+z is an exact calibration of the
        # cancellation needed for an integrable O(t), uniformly in delta.
        a,b=Q(2,3),Q(1,3)
        for delta in [Q(1,1000),Q(1,100),Q(1,10)]:
            for t in [Q(1,1000),Q(1,100),Q(1,10)]:
                error=(1+delta+b*t)/(1+delta+a*t)-1
                self.assertEqual(error,-(a-b)*t/(1+delta+a*t))
                self.assertLessEqual(abs(error), (a-b)*t);M.charge(20)


if __name__=='__main__':unittest.main()
