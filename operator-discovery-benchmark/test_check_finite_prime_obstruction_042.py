"""Synthetic formal local parameters and scoped certificate attacks only."""
import unittest,time
from copy import deepcopy
from fractions import Fraction as F
from prime_bank_candidates import Meter
import check_finite_prime_obstruction_042 as V
import finite_prime_obstruction_042 as P

METER=Meter(cap=50000000,seconds=180)
FIXTURE_METER=P.Meter(cap=50000000,seconds=180)
START=time.monotonic()

def fixture(primes=None,**kwargs):
    return P.generate_certificate([2,3] if primes is None else primes,meter=FIXTURE_METER,**kwargs)

def verify(c):return V.verify(c,meter=METER)

def local_u(v,e):return F(1) if e==0 else (v-1)*v**(e-1)
def local_h(v,e):
    if e==0:return F(1)
    if e==1:return v-2
    return (1-v)**2*v**(e-2)

def factors(n):
    out={};p=2
    while p*p<=n:
        while n%p==0:out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=1
    return out

def u(n,values):
    result=F(1)
    for p,e in factors(n).items():
        if p in values:result*=local_u(values[p],e)
    return result

def h(n,values):
    result=F(1)
    for p,e in factors(n).items():
        if p not in values:return F(0)
        result*=local_h(values[p],e)
    return result

class IndependentObstruction(unittest.TestCase):
    def test_registered_and_empty_models_have_correct_limited_scope(self):
        for primes in ([],[2],[2,3],[2,3,5,7,11]):
            c=fixture(primes);out=verify(c)
            self.assertTrue(out['verified']);self.assertTrue(out['finite_prime_only_rule_obstructed'])
            self.assertFalse(out['actual_source_refuted']);self.assertFalse(out['RH_refuted'])
            self.assertFalse(out['existing_041_source_binding_refuted'])
            self.assertFalse(out['retains_actual_source_global_residue_identity'])
            self.assertEqual(F(out['uniform_fake_prefix_bound']),(2+1)*4**len(primes))

    def test_local_convolution_coefficients_and_exact_infinite_l1_tail(self):
        for v in (F(1,7),F(2,5),F(9,10)):
            for e in range(1,31):
                self.assertEqual(local_h(v,e),local_u(v,e)-local_u(v,e-1))
            for M in (2,3,7,20):
                partial=sum(abs(local_h(v,e)) for e in range(M+1))
                exact_tail=(1-v)*v**(M-1)
                self.assertEqual(partial+exact_tail,4-2*v)
                self.assertLess(partial+exact_tail,4)
                METER.charge(180)

    def test_unit_and_global_One_convolution_from_independent_factorization(self):
        values={2:F(2,5),3:F(1,7)}
        self.assertEqual(u(1,values),1);self.assertEqual(h(1,values),1)
        for n in range(1,121):
            self.assertEqual(u(n,values),sum(h(d,values) for d in range(1,n+1) if n%d==0))
            self.assertLessEqual(abs(u(n,values)),1)
            METER.charge(n+80)

    def test_full_floor_identity_and_essential_d_greater_x_tail(self):
        values={2:F(2,5),3:F(1,7)}
        for q in (2,6):
            def g(d):return h(d,values)-(q*h(d//q,values) if d%q==0 else 0)
            def c(n):return u(n,values)-(q*u(n//q,values) if n%q==0 else 0)
            for numerator in range(1,100):
                x=F(numerator,7);N=int(x)
                actual=sum(c(n) for n in range(1,N+1))
                floor=sum(g(d)*(N//d) for d in range(1,N+1))
                short_fraction=sum(g(d)*((N//d)-x/d) for d in range(1,N+1))
                full_tail=x*sum(g(d)/d for d in range(1,N+1)) # sum_all g/d=0
                self.assertEqual(actual,floor);self.assertEqual(actual,short_fraction+full_tail)
                self.assertLessEqual(abs(actual),(q+1)*4**len(values))
                METER.charge(120)
            self.assertNotEqual(sum(c(n) for n in range(1,2)),sum(g(d)*(1-F(1,d)) for d in range(1,2)))

    def test_exact_finite_alias_and_explicit_missing_prime_failure(self):
        # Generic exact local parameters; all primes through H are included.
        H=30;values={p:F(1,p+1) for p in (2,3,5,7,11,13,17,19,23,29)}
        def full_b(n):
            result=F(1)
            for p,e in factors(n).items():result*=local_u(F(1,p+1),e)
            return result
        for n in range(1,H+1):
            self.assertEqual(u(n,values),full_b(n));METER.charge(80)
        self.assertEqual(u(31,values),1);self.assertLess(full_b(31),0)
        self.assertGreater(u(31,values)-full_b(31),1)

    def test_composite_period_and_genuine_denominator257(self):
        c=fixture([],r_text='123/257',q=6,k_text='1/100',K=9)
        out=verify(c)
        self.assertEqual(c['parameters']['theta'],'134/257')
        self.assertEqual(out['subpower_counterexample_epsilon'],'11/514')
        self.assertEqual(out['first_missing_prime'],2)
        self.assertFalse(c['source_scope']['fake_periodic_has_theta_pole'])

    def test_exact_minimal_threshold_and_positive_power_near_boundary(self):
        for r in ('1/3','128/257'):
            c=fixture([],r_text=r,k_text='1/100');out=verify(c)
            theta=F(c['parameters']['theta']);k=F(c['parameters']['k_lower']);L=int(c['norms']['g_l1_upper'])
            X=int(c['threshold']['X']);j=c['threshold']['j']
            a,b=theta.numerator,theta.denominator
            self.assertGreaterEqual(k**b*X**a,(2*L)**b)
            if j:self.assertLess(k**b*(X//2)**a,(2*L)**b)
            self.assertGreater(F(out['fake_energy_lower']['power']),0)
            self.assertLess(F(out['subpower_counterexample_epsilon']),F(out['fake_energy_lower']['power']))
            METER.charge(6000)

    def test_underpriced_and_nonminimal_thresholds_rejected(self):
        c=fixture();bad=deepcopy(c);t=bad['threshold'];t['j']-=1;t['X']=str(1<<t['j'])
        t['lhs']=str(int(t['powered_numerator'])<<(t['j']*t['theta_numerator']))
        with self.assertRaises(ValueError):verify(bad)
        bad=deepcopy(c);t=bad['threshold'];t['j']+=1;t['X']=str(1<<t['j'])
        t['lhs']=str(int(t['powered_numerator'])<<(t['j']*t['theta_numerator']))
        with self.assertRaises(ValueError):verify(bad)

    def test_forged_exact_power_witness_and_boolean_exponent(self):
        c=fixture()
        for field,value in (('powered_numerator','2'),('powered_denominator','1'),
                            ('lhs','1'),('rhs','0'),('theta_numerator',True),('minimal_dyadic',1)):
            bad=deepcopy(c);bad['threshold'][field]=value
            with self.assertRaises(ValueError):verify(bad)

    def test_wrong_scalar_lower_upper_rejected_independently(self):
        with self.assertRaises(ValueError):verify(fixture(k_text='1',K=1))
        # q4096 has kappa>1; alternating-series bounds already certify this.
        with self.assertRaises(ValueError):verify(fixture(q=4096,k_text='1/10',K=1))
        self.assertTrue(verify(fixture(q=4096,k_text='1/10',K=32))['verified'])

    def test_malformed_parameters_and_composite_registered_value(self):
        c=fixture()
        for key,value in (('r','2/6'),('r','1/2'),('k_lower',0.1),('q',True),('K_upper',True),
                          ('primes',[2,9]),('primes',[2,2]),('primes',[3,2])):
            bad=deepcopy(c);bad['parameters'][key]=value
            with self.assertRaises((ValueError,OverflowError)):verify(bad)

    def test_underpriced_norm_and_wrong_infinite_local_tail(self):
        c=fixture()
        for path,value in ((('norms','h_l1_upper'),'1'),(('norms','g_l1_upper'),'1'),
                           (('local_laws','registered',0,'h_e_ge2'),'(1-v)*v^(e-2)'),
                           (('local_laws','registered',0,'h_l1'),'3-2*v')):
            bad=deepcopy(c);item=bad
            for key in path[:-1]:item=item[key]
            item[path[-1]]=value
            with self.assertRaises(ValueError):verify(bad)

    def test_harmonic_cancellation_unit_and_full_real_floor_domain_protected(self):
        c=fixture()
        for key,value in (('harmonic_multiplier','1'),('prefix_abs_bound','0'),
                          ('prefix_identity','prefix(c)(x)=sum_(d<=x)g(d)*(floor(x/d)-x/d)'),
                          ('prefix_domain','integer x>=1 only'),('absolute_series_justifies_interchange',False)):
            bad=deepcopy(c);bad['periodic'][key]=value
            with self.assertRaises(ValueError):verify(bad)
        for key in ('u_unit','c_unit'):
            bad=deepcopy(c);bad['definitions'][key]='0'
            with self.assertRaises(ValueError):verify(bad)

    def test_missing_prime_witness_must_be_checked_and_first(self):
        c=fixture()
        for prime in (2,7,9,True):
            bad=deepcopy(c);bad['first_missing_prime']['prime']=prime
            with self.assertRaises(ValueError):verify(bad)
        bad=deepcopy(c);bad['first_missing_prime']['required_value_range']='[0,1]'
        with self.assertRaises(ValueError):verify(bad)

    def test_actual_source_and_RH_refutation_claims_fail_closed(self):
        c=fixture()
        for key in ('source_counterexample','RH_proved','RH_refuted','actual_all_prime_bound_proved',
                    'actual_source_values_generated','covariance_bound_proved'):
            bad=deepcopy(c);bad[key]=True
            with self.assertRaises(ValueError):verify(bad)
        for key in ('retains_actual_global_meromorphic_identity','retains_actual_center_as_its_own_residue',
                    'fake_periodic_has_theta_pole'):
            bad=deepcopy(c);bad['source_scope'][key]=True
            with self.assertRaises(ValueError):verify(bad)

    def test_energy_cost_quantifier_and_ordinary_series_scope_protected(self):
        c=fixture()
        for key,value in (('lower_constant','1'),('exponent','1'),('domain','selected finite X'),
                          ('energy_exponent_strictly_positive',1)):
            bad=deepcopy(c);bad['energy_obstruction'][key]=value
            with self.assertRaises(ValueError):verify(bad)
        bad=deepcopy(c);bad['assumptions']['ordinary_mu_theta_series_convergence_used']=True
        with self.assertRaises(ValueError):verify(bad)
        bad=deepcopy(c);bad.pop('source_scope')
        with self.assertRaises(ValueError):verify(bad)

    def test_external_meter_requires_only_charge(self):
        self.assertFalse(hasattr(METER,'number'));self.assertFalse(hasattr(METER,'reserve_bits'))
        self.assertTrue(verify(fixture())['verified'])

def tearDownModule():
    print(f'SYNTHETIC_WORK module=test_check_finite_prime_obstruction_042 operations={METER.operations+FIXTURE_METER.operations} elapsed_seconds={time.monotonic()-START:.6f} checker_operations={METER.operations} fixture_operations={FIXTURE_METER.operations}')

if __name__=='__main__':unittest.main(verbosity=2)
