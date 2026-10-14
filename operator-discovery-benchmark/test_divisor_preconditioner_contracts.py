"""Arithmetic support, retained signs and analytic proof-scope contracts."""
from collections import defaultdict
from fractions import Fraction as Q
import unittest
import flint
import divisor_preconditioner_grammar as g
import check_divisor_preconditioners as independent
from mellin_kernel_grammar import real


class Contracts(unittest.TestCase):
    def setUp(self):flint.ctx.prec=640

    def test_actual_first_jet_matches_independent_prime_power_weights(self):
        t=g.coefficients('1',64);counts=defaultdict(int);v=independent.arithmetic(t,counts)
        for n in range(2,65):
            f=independent.factors(n);expected=real(f[0][0]).log() if len(f)==1 else flint.arb(0)
            self.assertTrue(v[n].overlaps(expected))

    def test_logarithmic_square_cube_and_sixth_roots_have_signed_composite_support(self):
        for a in ['1/2','1/3','1/6','1/10007']:
            t=g.coefficients(a,64);v=independent.arithmetic(t,defaultdict(int));independent.support(g.sign_signature(a),a,v,defaultdict(int))
            self.assertLess(v[6],0);self.assertGreater(v[30],0)

    def test_fractional_root_support_continues_after_every_integer_cutoff(self):
        sig=g.sign_signature('1/6')
        for r in [1,2,3,12,31,10007]:self.assertEqual(g.sign_from_signature(sig,r),(-1)**(r-1))

    def test_integer_order_has_exact_almost_prime_support(self):
        t=g.coefficients('2',64);v=independent.arithmetic(t,defaultdict(int));independent.support(g.sign_signature('2'),'2',v,defaultdict(int))
        self.assertGreater(v[6],0);self.assertTrue(v[30].contains(0))

    def test_domain_and_proof_backend_are_separate(self):
        g.coefficients('1/10007',8)
        with self.assertRaises(ValueError):g.coefficients('0',8)
        with self.assertRaises(ValueError):g.complete_preconditioner(Q(1,2))

    def test_signed_preconditioner_cannot_be_relabelled_as_unit_reference(self):
        c=g.complete_preconditioner(2);g.enforce_domain(c,'inverse_one')
        with self.assertRaises(ValueError):g.enforce_domain(c,'unit')

    def test_complete_rewrites_cover_irregular_real_scales(self):
        for k in [1,2,3]:
            t=g.coefficients(str(k),32);v=independent.arithmetic(t,defaultdict(int));c=g.complete_preconditioner(k)
            independent.witnesses(c,v,[Q(3,2),Q(13,3),32],defaultdict(int))

    def test_only_first_jet_has_verified_ordinary_zero_recovery(self):
        self.assertTrue(g.complete_preconditioner(1)['first_derivative_recovers_every_ordinary_zero'])
        self.assertFalse(g.complete_preconditioner(3)['first_derivative_recovers_every_ordinary_zero'])
        self.assertFalse(g.complete_preconditioner(1)['RH_strength'])

    def test_first_harmonic_log_constant_has_the_correct_limit_sign(self):
        N=4096;limit=sum((real(n).log()/real(n) for n in range(1,N+1)),flint.arb(0))-real(N).log()**2/2
        gamma=g.gamma_constants(2,512)[1];error=(2*real(N).log()+2)/real(N)
        self.assertLess(gamma,0);self.assertLessEqual(abs(limit-gamma),error)

    def test_completed_third_jet_matches_an_independent_Mellin_pole_expansion(self):
        c=g.complete_preconditioner(3);gamma0,gamma1=g.gamma_constants(2,512)
        # Expansion of -zeta'''(1+w)/((1+w)*zeta(1+w)) at the pole.
        expected=6*(1+gamma0+gamma0**2+gamma1)
        self.assertTrue(flint.arb(c['polynomial_coefficients'][0]).overlaps(expected))

    def test_generic_fractional_differences_include_the_zero_endpoint(self):
        for a in ['1/6','3/2','2']:
            for base in [0,Q(2,7)]:
                for r in range(1,6):
                    hs=[Q(j+2,7) for j in range(r)];v=g.generic_difference(a,base,hs);product=Q(1)
                    for j in range(r):product*=Q(a)-j
                    self.assertTrue(v.contains(0) if product==0 else (v>0 if product>0 else v<0))

    def test_all_integer_bell_coefficients_match_partition_formula(self):
        from math import factorial
        for k,P in enumerate(g.bell_polynomials(6)):
            for mon,c in P.items():
                den=1
                for r in set(mon):den*=factorial(r+1)**mon.count(r)*factorial(mon.count(r))
                self.assertEqual(Q(c),Q(factorial(k),den))

    def test_learned_feature_language_extends_to_nonmultiplicative_generic_inputs(self):
        f=[flint.arb(0),flint.arb(1)]+[real(Q((-1)**n*(n%3),n+1)) for n in range(2,17)];inv=g.generic_inverse(f);first=g.convolution(inv,[flint.arb(0)]+[f[n]*real(n).log() for n in range(1,17)])
        for k,P in enumerate(g.bell_polynomials(4)[1:],1):
            actual=g.convolution(inv,[flint.arb(0)]+[f[n]*real(n).log()**k for n in range(1,17)])
            for n in range(1,17):
                predicted=sum((real(c)*independent.feature(mon,n,first) for mon,c in P.items()),flint.arb(0))
                self.assertTrue(predicted.overlaps(actual[n]))


if __name__=='__main__':unittest.main()
