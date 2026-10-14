"""Independent symbolic calibrations and hard schema mutations for051."""
import copy
from fractions import Fraction as Q
import unittest
import check_fractional_prime_kernel_051 as C
import fractional_prime_kernel_051 as P
from prime_bank_candidates import Meter as ExternalMeter

CHECKER=C.Meter(50000000,180)
PRODUCER=P.Meter(50000000,180)


def request(a='3/4',b='1/4',alpha='2/3',sign=-1):
    return {'a':a,'b':b,'alpha':alpha,'sign':sign}

def build(r):return P.build_certificate(r,PRODUCER)
def verify(r,c):return C.verify_certificate(r,c,CHECKER)


def independent_factors(n):
    out=[];p=2
    while p*p<=n:
        e=0
        while n%p==0:n//=p;e+=1
        if e:out.append((p,e))
        p+=1
    if n>1:out.append((n,1))
    return out

def mu(n):
    factors=independent_factors(n)
    return 0 if any(e>1 for _,e in factors) else (-1)**len(factors)


def log_polynomial_kernel(n,a,b,alpha,sign):
    # Give each log(prime) a positive independent rational coordinate. At
    # integer exponents the exact polynomial identity holds for every such
    # coordinate and therefore for the actual logarithms, without observing
    # transcendental kernel values or source arrays.
    primes=[p for p,_ in independent_factors(n)]
    coordinates={p:Q(j+2,j+1) for j,p in enumerate(primes)}
    def logm(d):return sum((e*coordinates[p] for p,e in independent_factors(d)),Q(0))
    value=sum((mu(d)*(a*logm(d)+b*logm(n//d))**alpha
        for d in range(1,n+1) if n%d==0),Q(0))*sign
    def mangoldt(d):
        f=independent_factors(d)
        return coordinates[f[0][0]] if len(f)==1 else Q(0)
    lam=mangoldt(n)
    convolution=sum((mangoldt(d)*mangoldt(n//d) for d in range(1,n+1) if n%d==0),Q(0))
    return value,lam,convolution,logm(n)


class FractionalKernelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.r=request();cls.c=build(cls.r)

    def reject(self,r,c):
        with self.assertRaises((ValueError,OverflowError,ArithmeticError)):
            verify(r,c)

    def test_forward_normalized_laplace_and_pointwise_bounds(self):
        result=verify(self.r,self.c)
        self.assertTrue(result['verified']);self.assertTrue(result['uniform_pointwise_control_proved'])
        self.assertFalse(result['original_floor_energy_bound_proved'])
        self.assertEqual(self.c['product_bound']['omega_ratio'],'1')
        self.assertFalse(self.c['product_bound']['exponential_omega_decay'])

    def test_b_zero_has_no_derivative_denominator_provider(self):
        r=request('1','0','1/257',-1);c=build(r)
        self.assertTrue(verify(r,c)['verified']);self.assertIsNone(c['product_bound'])
        c['product_bound']=copy.deepcopy(self.c['product_bound']);self.reject(r,c)

    def test_arbitrary_rational_parameters_and_omega_decay_gate(self):
        for r in (request('193/257','64/257','123/257',-1),
                  request('3/5','2/5','1/257',-1),
                  request('1/257','256/257','1',1),
                  request('123/257','134/257','2',1)):
            c=build(r);self.assertTrue(verify(r,c)['verified'])
        r=request('3/5','2/5');c=build(r)
        self.assertEqual(c['product_bound']['omega_ratio'],'1/4')
        self.assertIs(c['product_bound']['exponential_omega_decay'],True)
        c['product_bound']['omega_ratio']='1/8';self.reject(r,c)

    def test_product_factor_count_bound_exact_rational_inequality(self):
        # This independently checks the numeric rational part of the generic
        # AMGM reduction underlying the symbolic log(n)^alpha factor.
        alpha=Q(123,257)
        for k in range(1,18):
            coefficient=alpha
            for j in range(1,k):coefficient*=j-alpha
            self.assertGreater(coefficient,0)
            self.assertLessEqual(coefficient/Q(k**k),Q(2)*alpha/Q(2**k*k))
            CHECKER.charge(100*k)

    def test_linear_exact_formula_for_both_orientations(self):
        for r in (request('4/5','1/5','1',-1),request('1/5','4/5','1',1)):
            certificate=build(r);verify(r,certificate)
            for n in (2,4,8,6,12,30,72):
                value,lam,_,_=log_polynomial_kernel(n,Q(r['a']),Q(r['b']),1,r['sign'])
                self.assertEqual(value,r['sign']*(Q(r['b'])-Q(r['a']))*lam)
                CHECKER.charge(100*n)

    def test_quadratic_full_mangoldt_convolution_and_prime_powers(self):
        r=request('1/4','3/4','2',1);verify(r,build(r));c=Q(1,2)
        for n in (2,4,8,16,6,12,18,36,30,60,210):
            value,lam,convolution,logn=log_polynomial_kernel(n,Q(1,4),Q(3,4),2,1)
            self.assertEqual(value,c*lam*logn+c*c*convolution)
            self.assertGreaterEqual(value,0);self.assertLessEqual(value,c*logn*logn)
            if len(independent_factors(n))>=3:self.assertEqual(value,0)
            CHECKER.charge(100*n)

    def test_quadratic_a_zero_endpoint(self):
        r=request('0','1','2',1);certificate=build(r)
        self.assertTrue(verify(r,certificate)['uniform_pointwise_control_proved'])
        for n in (2,4,6,12,30):
            value,_,_,logn=log_polynomial_kernel(n,Q(0),Q(1),2,1)
            self.assertGreaterEqual(value,0);self.assertLessEqual(value,logn*logn)
            CHECKER.charge(100*n)

    def test_all_strict_negative_witness_families(self):
        examples=((request(sign=1),'negative_prime',2),
                  (request(alpha='1',sign=1),'negative_prime',2),
                  (request(alpha='3/2'),'negative_two_prime_convex',6),
                  (request(alpha='2'),'negative_two_prime_convex',6),
                  (request('1/4','3/4','2/3',1),'negative_two_prime_concave',6),
                  (request('1/4','3/4','3/2',1),'negative_three_prime',30),
                  (request('1/4','3/4','2',-1),'negative_prime',2))
        for r,branch,n in examples:
            c=build(r);out=verify(r,c)
            self.assertTrue(out['uniform_nonnegativity_refuted'])
            self.assertFalse(out['RH_refuted'])
            self.assertEqual(c['branch'],branch);self.assertEqual(c['witness']['n'],n)

    def test_negative_prime_can_have_zero_base(self):
        for r in (request('0','1','1/257',-1),request('1','0','257/129',-1),
                  request('0','1','257/129',1)):
            c=build(r);self.assertTrue(verify(r,c)['uniform_nonnegativity_refuted'])

    def test_normalizer_orientation_and_one_factor_mutations(self):
        mutations=(('identity','c','1/4'),('identity','normalizer_finite_positive',False),
                   ('identity','normalizer','I_alpha=Gamma(alpha)'),
                   ('upper_bound','step_coefficient','1/4'),('upper_bound','power','1'),
                   ('proof','finite_difference_constant_cancels',False),
                   ('proof','all_factors_between_zero_and_one',False))
        for section,field,value in mutations:
            c=copy.deepcopy(self.c);c[section][field]=value;self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['identity']['normalizer_value']='1';self.reject(self.r,c)

    def test_product_bound_sign_and_domain_mutations(self):
        for field,value in (('coefficient','alpha*prod_{j=1}^{k-1}(alpha-j)'),
                            ('b_strictly_positive',False),('k','number of prime powers'),
                            ('exponential_omega_decay',True),
                            ('omega_upper','K(n)<=1/omega(n)')):
            c=copy.deepcopy(self.c);c['product_bound'][field]=value;self.reject(self.r,c)

    def test_linear_and_quadratic_zero_scope_mutations(self):
        for r in (request(alpha='1'),request('1/4','3/4','2',1)):
            c=build(r);c['strict_positive_scope']='every integer n>=2';self.reject(r,c)
            c=build(r);c['exact_zero_scope']='none';self.reject(r,c)
        r=request('1/4','3/4','2',1);c=build(r)
        c['identity']['formula']='K(n)=c*Lambda(n)*log(n)';self.reject(r,c)
        c=build(r);c['upper_bound']['coefficient']='1/4';self.reject(r,c)

    def test_negative_witness_and_numerical_boolean_mutations(self):
        r=request('1/4','3/4','3/2',1)
        for field,value in (('n',6),('primes',[2,3]),('exact_sign_proved',False),
                            ('numerical_evaluation_required',True),('conclusion','K(n)>0')):
            c=build(r);c['witness'][field]=value;self.reject(r,c)
        c=build(r);c['nonnegative_for_all_n']=True;self.reject(r,c)

    def test_dirichlet_initial_domain_and_missing_unit_subtraction(self):
        for field,value in (('domain','Re(s)>1/2'),('subtracted_constant','0'),
                            ('numerator_shift','3/4'),('denominator_shift','1/4'),
                            ('absolute_convergence_proved',False)):
            c=copy.deepcopy(self.c);c['zeta_bridge'][field]=value;self.reject(self.r,c)
        for r in (request(alpha='1'),request('1/4','3/4','2',1)):
            c=build(r);c['zeta_bridge']['domain']='all complex s';self.reject(r,c)

    def test_source_unit_prime_power_and_full_scope_guards(self):
        for section,field,value in (('domain','extension_at_one','K(1)=1'),
            ('domain','n','every squarefree integer n>=2'),
            ('domain','rounding','rounded logarithms'),
            ('divisor_reduction','prime_powers_retained_in','none'),
            ('divisor_reduction','all_distinct_prime_factors_retained',False)):
            c=copy.deepcopy(self.c);c[section][field]=value;self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['arithmetic_source']='bounded arbitrary weights';self.reject(self.r,c)

    def test_false_global_distribution_and_rh_claims(self):
        for field in ('source_values_evaluated','numerical_evidence_used','prime_distribution_bound_proved',
            'uniform_mobius_partial_sum_bound_proved','original_floor_energy_bound_proved',
            'analytic_continuation_proved','RH_proved','RH_refuted'):
            c=copy.deepcopy(self.c);c[field]=True;self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['RH_proved']=0;self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['uniform_original_source_bound']=True;self.reject(self.r,c)

    def test_source_swaps_and_strict_canonical_parameter_guards(self):
        for field,value in (('a','1/2'),('a','2/4'),('a',0.75),('b','-1/4'),
                            ('alpha','0'),('alpha','3'),('alpha',True),('sign',True),('sign',-1.0)):
            r=copy.deepcopy(self.r);r[field]=value;self.reject(r,self.c)
        r=request('1/2','1/2');self.reject(r,self.c)
        r=copy.deepcopy(self.r);r['unit_bound']='1';self.reject(r,self.c)
        r=copy.deepcopy(self.r);r['alpha']='1/257';self.reject(r,self.c)
        c=copy.deepcopy(self.c);c['request']['a']='3/5';self.reject(self.r,c)

    def test_charge_only_meter_alias_and_capacity(self):
        m=ExternalMeter(cap=1000000,seconds=60)
        self.assertTrue(C.verify(self.r,self.c,m)['verified']);CHECKER.charge(m.operations)
        with self.assertRaises(OverflowError):C.verify(self.r,self.c,C.Meter(1))
        r=copy.deepcopy(self.r);r['alpha']='1/'+str(2**4097);self.reject(r,self.c)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_fractional_prime_kernel_051 operations='+str(CHECKER.operations+PRODUCER.operations))
    print('SYNTHETIC_SPLIT checker='+str(CHECKER.operations)+' fixture='+str(PRODUCER.operations))

if __name__=='__main__':unittest.main()
