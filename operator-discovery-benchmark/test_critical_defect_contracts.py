"""Public arithmetic, kernel, scope, fractional cutoff and counterfeit checks."""
import unittest
from fractions import Fraction as Q
from math import gcd
import flint
import critical_defect_grammar as g
from check_signed_control import independent_inverse
from check_critical_defects import density


class Contracts(unittest.TestCase):
    def test_full_actual_inverse(self):
        self.assertEqual(g.inverse_one_prefix(512),independent_inverse(512)[0])

    def test_exact_kernel_energy(self):
        mu=g.inverse_one_prefix(128)
        for X in [1,2,4,8]:
            direct=sum(mu[n]*mu[m]*g.kernel(X,max(n,m)) for n in range(1,2*X+1) for m in range(1,2*X+1));self.assertEqual(g.whole(mu,X)['energy'],direct)

    def test_full_primitive_cutoff_recovers_off_diagonal(self):
        mu=g.inverse_one_prefix(256)
        for X in [1,2,4]:self.assertEqual(g.projection(mu,X,4*X)['signed_projection_defect'],g.whole(mu,X)['off_diagonal_defect'])

    def test_every_primitive_prime_product(self):
        mu=g.inverse_one_prefix(512)
        for a in range(1,12):
            for r in range(a+1,13):
                if gcd(a,r)>1:continue
                for common in range(1,512//r+1):self.assertEqual(mu[a*common]*mu[r*common],mu[a]*mu[r]*mu[common]**2*int(gcd(common,a*r)==1))

    def test_independent_density_products(self):
        mu=g.inverse_one_prefix(512);flint.ctx.prec=512
        for k in [1,2,6,12,15,30,77,210]:
            c,tau=g.divisor_density(mu,k);d,tau2=density(k);self.assertTrue(c.overlaps(d));self.assertEqual(tau,tau2)

    def test_every_scale_component_witnesses(self):
        mu=g.inverse_one_prefix(512)
        for X in [1,2,4,8]:
            for B in [1,2,3,6]:
                c=g.projection(mu,X,B);self.assertLessEqual(abs(c['signed_projection_defect']),flint.arb(c['sharp_component_bound_ball']));self.assertFalse(c['full_defect_bound_proved'])

    def test_fractional_root_cutoffs_exact(self):
        for n,b,value in [(1024,'1/2',32),(1000,'1/3',10),(4096,'1/6',4),(729,'2/3',81)]:self.assertEqual(g.floor_power(n,b),value)

    def test_denominator_beyond_native_word(self):
        self.assertEqual(g.floor_power(8192,Q(1,10**100)),1);self.assertTrue(g.component_certificate(Q(1,10**100))['admitted'])

    def test_cutoff_domains(self):
        for b in ['-1/6','7/6']:
            with self.assertRaises(ValueError):g.floor_power(16,b)
        with self.assertRaises(ValueError):g.floor_power(Q(3,2),'1/3')

    def test_shared_cutoff_required(self):
        self.assertFalse(g.component_certificate('1/3',False)['admitted'])

    def test_component_not_full_critical_bound(self):
        c=g.component_certificate('1/3');self.assertTrue(c['component_admits_every_positive_epsilon_critical_bound']);self.assertFalse(c['global_full_signed_defect_proved']);self.assertTrue(c['dense_residual_still_required'])

    def test_cofinal_epsilon_and_all_scale_quantifiers(self):
        self.assertTrue(g.cofinal_recovery()['admitted']);self.assertFalse(g.cofinal_recovery(epsilon_tends_to_zero=False)['admitted']);self.assertFalse(g.cofinal_recovery(all_dyadic_scales=False)['admitted']);self.assertFalse(g.cofinal_recovery(arithmetic_model='generic_sequence')['admitted'])

    def test_no_zero_simplicity_assumption(self):
        c=g.cofinal_recovery();self.assertFalse(c['critical_zero_simplicity_required']);self.assertTrue(c['all_heights_and_offcritical_multiplicities']);self.assertFalse(c['global_signed_defect_premise_proved'])

    def test_generic_density_transfer_rejected(self):
        with self.assertRaises(ValueError):g.projection_grid([0]+[1]*256,8,[2],'generic_sequence')

    def test_positive_control_cubic_full_defect(self):
        v=[0]+[1]*512
        for X in [4,16,64]:
            self.assertEqual(g.whole(v,X)['signed_defect'],Q(28*X**3-X,3));p=g.positive_projection(X,2);self.assertLessEqual(abs(p['signed_defect']),p['all_scale_absolute_defect_upper'])


if __name__=='__main__':unittest.main()
