"""Independent filter admission and symbolic finite/calculus calibrations."""
from fractions import Fraction as Q
import unittest
import check_prime_scale_filter_053 as C
import prime_scale_filter_053 as P
from prime_bank_candidates import Meter as PipelineMeter

M=C.Meter();PM=P.Meter()


def fixture(q=2,cs=None,alpha='1/2',eta='1/3'):
    r={'alpha':alpha,'q':q,'coefficients':[-q,1] if cs is None else cs,
        'bound':{'C':'1','log_power':eta,'minimum':2,'normalization':'divide_by_alpha'}}
    return r,P.build_certificate(r,PM)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_prime_scale_filter_053 operations='+str(M.operations+PM.operations))


class FilterTests(unittest.TestCase):
    def bad(self,f):
        r,c=fixture();f(r,c)
        with self.assertRaises(ValueError):C.verify_filter(r,c,M)

    def test_basic_conditional_only(self):
        v=C.verify_filter(*fixture(),M)
        self.assertTrue(v['verified']);self.assertFalse(v['uniform_arithmetic_bound_proved'])
        self.assertEqual(v['open_premise_status'],'OPEN');self.assertFalse(v['RH_proved'])

    def test_prime_and_composite_scales(self):
        for q in [2,3,5,6,64]:self.assertTrue(C.verify_filter(*fixture(q=q),M)['verified'])

    def test_arbitrary_fractional_alpha_and_log(self):
        for alpha,eta in [('1/257','123/257'),('256/257','0'),('1/1001','1000/3')]:
            self.assertTrue(C.verify_filter(*fixture(alpha=alpha,eta=eta),M)['verified'])

    def test_annulus_roots_do_not_prevent_admission(self):
        # Real, repeated real and complex roots of modulus3 lie inside the
        # sqrt(5)<|z|<5 annulus; no root-position oracle is an admission gate.
        for cs in [[15,-8,1],[-45,39,-11,1],[-45,9,-5,1]]:
            v=C.verify_filter(*fixture(q=5,cs=cs),M)
            self.assertTrue(v['all_polynomial_root_locations_allowed'])

    def test_boundary_roots_and_repeated_mean_root(self):
        for cs in [[4,-2,-2,1],[-8,12,-6,1],[2,-3,1]]:
            r,c=fixture(cs=cs);C.verify_filter(r,c,M)
            self.assertEqual(c['main_term_cancellation']['affine_center_annihilated'],sum(cs)==0)

    def test_degree_capacity_and_zero_order(self):
        # Use (z-2)(z^15+1): primitive degree16 with nonzero constant.
        cs=[-2,1]+[0]*13+[-2,1]
        r,c=fixture(cs=cs);self.assertEqual(C.verify_filter(r,c,M)['degree'],16)
        self.bad(lambda r,c:r.update(coefficients=[-2]+[0]*16+[1]))
        self.bad(lambda r,c:r.update(coefficients=[1]))

    def test_exact_primitive_mean_neutrality(self):
        for cs in [[-4,2],[0,-2,1],[2,-1],[-2,1,0],[-3,1],[0,0]]:
            r,c=fixture();r['coefficients']=cs
            with self.assertRaises(ValueError):C.verify_filter(r,c,M)

    def test_strict_types_and_canonical_rationals(self):
        for q in [True,2.,'2',1,65]:
            self.bad(lambda r,c,q=q:r.update(q=q))
        for alpha in ['2/4','0.5',Q(1,2),True,'0','1','2']:
            self.bad(lambda r,c,alpha=alpha:r.update(alpha=alpha))
        self.bad(lambda r,c:r.update(coefficients=[-2,True]))
        self.bad(lambda r,c:c['polynomial'].update(nonzero=1))
        self.bad(lambda r,c:r['bound'].update(minimum=True))

    def test_exact_bound_scope_and_normalization(self):
        for k,v in [('C','0'),('C','-1'),('log_power','-1'),('minimum',3),('normalization','none')]:
            self.bad(lambda r,c,k=k,v=v:r['bound'].update({k:v}))
        self.bad(lambda r,c:c['open_premise'].update(quantifiers='finite training scales only'))
        self.bad(lambda r,c:c['source'].update(normalized_target='alpha*T_P(x)'))

    def test_source_and_parameter_binding(self):
        self.bad(lambda r,c:c['kernel'].update(alpha='1/3'))
        self.bad(lambda r,c:c['request'].update(q=3))
        self.bad(lambda r,c:c['polynomial'].update(P_at_one=0))
        self.bad(lambda r,c:c['source'].update(ordinary_mobius=False))
        self.bad(lambda r,c:c['source'].update(all_prime_and_composite_terms_retained=False))

    def test_jump_budget_and_unit_head(self):
        self.bad(lambda r,c:c['integer_to_real'].update(integer_jump_budget=0))
        self.bad(lambda r,c:c['mellin_identity'].update(head='0'))
        self.bad(lambda r,c:c['mellin_identity'].update(initial_domain='Re(s)>1/2'))
        self.bad(lambda r,c:c['source'].update(K='K_alpha(1)=1'))

    def test_full_center_retained(self):
        self.bad(lambda r,c:c['main_term_cancellation'].update(filtered_center='0'))
        self.bad(lambda r,c:c['main_term_cancellation'].update(kappa_evaluation_or_fitting_required=True))
        self.bad(lambda r,c:c['main_term_cancellation'].update(full_center='fitted slope*x'))

    def test_finite_order_and_taylor_scope(self):
        self.bad(lambda r,c:c['fractional_zero_survival'].update(k_positive='polynomial root cancels the zero'))
        self.bad(lambda r,c:c['fractional_zero_survival'].update(multiplier_order='simple roots only'))
        self.bad(lambda r,c:c['fractional_zero_survival'].update(all_polynomial_root_locations_allowed=False))
        self.bad(lambda r,c:c['fractional_zero_survival'].pop('dependency'))

    def test_error_remains_open(self):
        for k in ['finite_samples_can_pay','pointwise_K_bound_can_pay','polynomial_cancellation_can_pay','arithmetic_bound_proved']:
            self.bad(lambda r,c,k=k:c['open_premise'].update({k:True}))
        self.bad(lambda r,c:c['open_premise'].update(status='PAID'))
        for k in ['uniform_arithmetic_bound_proved','centered_error_bound_proved','original_floor_energy_bound_proved','converse_proved','RH_proved','RH_refuted','numerical_evidence_used']:
            self.bad(lambda r,c,k=k:c.update({k:True}))

    def test_capacity_and_pipeline_meter(self):
        self.bad(lambda r,c:r.update(coefficients=[-(1<<1025),1<<1024]))
        self.bad(lambda r,c:r.update(alpha='1/'+str(1<<4096)))
        m=PipelineMeter(cap=100000,seconds=30);self.assertTrue(C.verify_filter(*fixture(),m)['verified']);M.charge(m.operations)
        with self.assertRaises(OverflowError):C.verify_filter(*fixture(),C.Meter(cap=1))

    def test_finite_divisor_rewrite_as_formal_identity(self):
        # Arbitrary signed formal divisor columns; no real source evaluations.
        q=2;cs=[2,-3,1];N=3;top=q**2*N
        direct={d:sum(c*(q**j*N//d) for j,c in enumerate(cs)) for d in range(2,top+1)}
        expanded={d:0 for d in range(2,top+1)}
        for j,c in enumerate(cs):
            for n in range(2,q**j*N+1):
                for d in range(2,n+1):
                    if n%d==0:expanded[d]+=c
                    M.charge()
        self.assertEqual(direct,expanded)
        self.assertEqual(sum(cs[j]*q**j for j in range(len(cs))),0)

    def test_fractional_exponent_never_integer(self):
        for alpha in [Q(1,257),Q(1,2),Q(256,257)]:
            for k in range(1,17):
                exponent=k-alpha
                self.assertGreater(exponent,k-1);self.assertLess(exponent,k)
                self.assertLessEqual(k+1-alpha,k+1);self.assertGreater(k+1-alpha,k)
                M.charge(20)

    def test_linear_center_and_jump_budget_symbolic(self):
        for q,cs in [(2,[-2,1]),(3,[3,-4,1]),(5,[-45,39,-11,1])]:
            r,c=fixture(q=q,cs=cs)
            x=Q(123,7);slope=Q(19,11)
            filtered=sum(cj*slope*(q**j*x-1) for j,cj in enumerate(cs))
            self.assertEqual(filtered,-slope*sum(cs))
            v=C.verify_filter(r,c,M)
            self.assertEqual(v['integer_jump_budget'],sum(abs(cj)*q**j for j,cj in enumerate(cs)))


if __name__=='__main__':unittest.main()
