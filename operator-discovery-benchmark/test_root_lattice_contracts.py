"""Generic arithmetic, rational-root and proof-scope contracts."""
from collections import defaultdict
from fractions import Fraction as Q
import unittest
import flint
import root_lattice_grammar as g
from root_lattice_search import anonymous_prony,build
import check_root_lattices as independent
from mellin_kernel_grammar import real,power


class Contracts(unittest.TestCase):
    def setUp(self):flint.ctx.prec=640

    def test_small_root_domain_checks_the_actual_convergence_threshold(self):
        g.parameters('7','1/3','1/6');g.parameters('10008','1/10009','1/10007')
        for row in [('6','1/3','1/6'),('3','1','0'),('3','0','1/2')]:
            with self.assertRaises(ValueError):g.parameters(*row)

    def test_sixth_root_complete_arithmetic_matches_rectangular_prime_sieve(self):
        counts=defaultdict(int);table=g.complete_table(['7','1/3','1/6'],[1,8,64],maximum_moment=2)
        independent.rectangular_table(table,[1,8,64],counts)
        self.assertEqual(counts['independent_complete_rectangle_atoms'],18)
        self.assertFalse(flint.arb(table['values']['inverse']['0:8']).overlaps(flint.arb(table['values']['unit']['0:8'])))

    def test_singular_dilation_has_true_signed_finite_support(self):
        params=['2','1/2','1'];shape=g.shape([[0,1],[1,Q(-1,3)],[2,Q(1,7)]]);points=[1,3,17];table=g.complete_table(params,points,maximum_moment=2)
        for M,row in g.responses(shape,table,points).items():self.assertTrue(flint.arb(row['actual_raw_ball']).overlaps(g.finite_response(shape,params,M)))
        self.assertEqual(g.profile('inverse','1')['remaining_factors'],[])
        self.assertEqual(g.profile('unit','1')['remaining_factors'],[['1',2]])

    def test_exact_signed_profile_does_not_certify_the_unit_reference(self):
        shape=g.shape([[0,1]]);cert=g.rapid_certificate(shape,['2','1/2','1'],'1/6')
        g.enforce_type(cert,'inverse')
        with self.assertRaises(ValueError):g.enforce_type(cert,'unit')
        self.assertFalse(g.rapid_certificate(shape,['2','1/2','1'],'1/6','unit')['global_premise_proved'])

    def test_global_signed_decay_retains_small_and_large_real_scales(self):
        params=['2','1/3','1'];shape=g.shape([[0,-1],[1,1]]);cert=g.rapid_certificate(shape,params,'1/3')
        for M in [Q(1,9),Q(1),Q(17),Q(4096)]:
            self.assertLessEqual(abs(g.finite_response(shape,params,M)),flint.arb(cert['constant_ball'])*power(real(M),Q(-1,3)))
        self.assertFalse(cert['RH_consequence'])

    def test_kernel_preservation_alone_cannot_prove_RH_after_arithmetic_erasure(self):
        bridge=g.zero_bridge(g.shape([[0,1]]),['2','1/2','1'])
        self.assertTrue(bridge['kernel_certificate']['all_right_half_ordinary_zeros_preserved'])
        self.assertFalse(bridge['RH_sufficient_if_uniform'])
        self.assertEqual(bridge['kind'],'exact_arithmetic_zero_erasure')

    def test_small_root_zero_chain_has_a_finite_exact_escape(self):
        for r in [Q(1,6),Q(1,3),Q(1,2),Q(4,5)]:
            params=list(map(str,(1+1/r,Q(1,3),r)));p=build(g.shape([[0,1]]),params,'generic')
            independent.bridge_check(p,defaultdict(int));bridge=p['zero_bridge']
            self.assertTrue(bridge['RH_sufficient_if_uniform']);self.assertGreater(Q(3,4)/r**bridge['worst_case_divisions'],1)

    def test_resource_exhaustion_is_not_a_counterexample(self):
        r=Q(10000,10001);params=list(map(str,(1+1/r,Q(1,3),r)));bridge=g.zero_bridge(g.shape([[0,1]]),params,maximum_steps=2)
        self.assertEqual(bridge['kind'],'missing_escape_resource');self.assertFalse(bridge['counterexample_to_growth'])
        with self.assertRaises(ArithmeticError):g.complete_table(['2','1/2','1'],[256],max_terms=16)

    def test_unavailable_native_box_at_zeta_pole_does_not_abort_the_audit(self):
        # P(v)=(v-2)*(v*v+1), with rho=(7-v/2)/6. The real root
        # maps to the pole at one; this backend honestly lacks its exclusion.
        shape=g.shape([[0,-2],[1,56],[2,-980],[3,2744]]);p=build(shape,['7','1/2','1/6'],'generic-missing-certificate-regression')
        independent.bridge_check(p,defaultdict(int))
        self.assertFalse(p['zero_bridge']['RH_sufficient_if_uniform'])
        self.assertFalse(p['zero_bridge']['kernel_certificate']['counterexample_to_growth_bound'])

    def test_true_weak_and_unit_bounds_use_the_normalized_index(self):
        params=['3','1/3','1/2'];shape=g.shape([[0,1],[1,Q(-1,5)]]);p=build(shape,params,'generic');counts=defaultdict(int)
        res=independent.residues(p,counts);B,J,local=independent.global_check(p,res,counts);points=[7,Q(22,3)];table=g.complete_table(params,points,maximum_moment=1);obs=g.responses(shape,table,points)
        self.assertLessEqual(abs(flint.arb(obs['7']['actual_centered_ball'])),B*7)
        self.assertLessEqual(abs(flint.arb(obs['22/3']['actual_centered_ball'])-flint.arb(obs['7']['actual_centered_ball'])),J/3)

    def test_unseen_counterfeit_tail_is_enclosed_without_rounding_it_to_zero(self):
        params=['7','1/6','1/6'];shape=g.shape([[0,1]]);bound=g.late_tail_bound(shape,params,256)
        self.assertGreater(bound,0);self.assertLess(bound,real(Q(1,2**500)))
        self.assertEqual(g.late_tail_pole(shape,params)['pole_order'],1)
        self.assertEqual(g.late_tail_pole(shape,['2','1/2','1'])['pole_order'],2)

    def test_pole_masking_makes_this_counterfeit_control_inapplicable(self):
        params=['7','1/2','1/6'];R=Q(14);beta=Q(2);shape=g.shape([[0,-beta/R],[1,1]])
        self.assertFalse(g.late_tail_pole(shape,params)['applies'])

    def test_anonymous_recurrence_recovers_more_than_the_constant_case(self):
        rule={'training_count':8,'total_count':14,'maximum_order':3,'quantization_bits':80,'coefficient_denominator':4096,'tolerance':'1/100000000'}
        const=anonymous_prony(['1']*14,rule)[0];self.assertEqual(const['coefficients'],['-1','1'])
        values=[(real(3)*power(real(Q(1,2)),h)-real(2)*power(real(Q(2,3)),h)).str(85) for h in range(14)]
        rel=anonymous_prony(values,rule)[1];self.assertEqual(list(map(Q,rel['coefficients'])),[Q(1,3),Q(-7,6),Q(1)])
        self.assertTrue(rel['validation_passed']);self.assertFalse(rel['universal_from_numeric_fit'])

    def test_mellin_geometry_charges_the_root_jacobian(self):
        K,ell,r=Q(3),Q(1,2),Q(1,2);R=K/ell;s=flint.acb(real(Q(5,8)),real(Q(1,3)));beta=r*K-Q(5,8);left,right=Q(-128),Q(16)
        integral=flint.acb.integral(lambda t,analytic:((real(r*K)-s)*t+real(R)-real(R)*(real(r*ell)*t).exp()).exp(),real(left),real(right),
            abs_tol=real(Q(1,2**100)),rel_tol=real(Q(1,2**100)),eval_limit=200000,depth_limit=50)
        lower=real(R).exp()*(real(beta*left)).exp()/real(beta);alpha=beta/(r*ell);Y=real(R)*(real(r*ell*right)).exp()
        upper=real(R).exp()*power(real(R),-alpha)*power(Y,alpha-1)*(-Y).exp()/(real(r*ell)*(1-real(alpha-1)/Y))
        error=lower+upper;integral+=flint.acb(flint.arb(0,error),flint.arb(0,error));v,base,num=g.observer_base(str(K),str(ell),str(r),'5/8','1/3',640)
        self.assertTrue(integral.overlaps(base));self.assertFalse(integral.overlaps(base*real(r)))


if __name__=='__main__':unittest.main()
