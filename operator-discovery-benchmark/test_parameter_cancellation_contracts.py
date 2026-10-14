"""Public mathematical domain, normalization, arithmetic and recovery checks."""
import unittest
from fractions import Fraction as Q
from math import factorial
import flint
import parameter_cancellation_grammar as g
from check_parameter_cancellation import prime_jet,gamma_coefficients,jet_center

R={'kind':'inverse_monomial','coefficient':'1','index_power':'-1','coordinate_power':'1'}


class Contracts(unittest.TestCase):
    def test_factorial_and_n1_mask(self):
        for m in range(4):
            t=g.jets(m,36)
            for n in range(1,37):self.assertTrue(flint.arb(t['values'][n]).overlaps(prime_jet(m,n)))
        self.assertLess(g.raw_jet(1,2),0)

    def test_zero_jet_is_shifted_mertens_not_unit(self):
        t=g.jets(0,12);self.assertEqual(flint.arb(t['values'][1]),0);self.assertEqual(flint.arb(t['values'][2]),1);self.assertEqual(flint.arb(t['values'][6]),-1)

    def test_independent_gamma_recurrence(self):
        saved=g.reciprocal_gamma(6,640)
        for x,y in zip(saved,gamma_coefficients(6)):self.assertTrue(x.overlaps(y))

    def test_full_center_coefficients(self):
        for m in [1,2,3]:self.assertTrue(flint.arb(g.jet_center(m,16)['value_ball']).contains(jet_center(m,'16')))

    def test_zero_center_boundary(self):
        for m in range(4):self.assertEqual(g.jet_center(m,1)['value_ball'],'0')

    def test_unbounded_denominator_radius(self):
        r=dict(R,coordinate_power=str(Q(1,10**100)));c=g.radius_certificate(r);self.assertTrue(c['admitted']);self.assertGreater(g.radius_value(r,g.real(32),2),0)

    def test_uniform_normalization_parameters(self):
        p=g.canonical([('1/2',1),('1/4',-3),('1/8',2)]);c=g.family_parameters(p);self.assertEqual(c['moment'],2);self.assertEqual(Q(c['uniform_center_derivative_guard']),12*Q(c['weight_norm'])/Q(c['radius_cap'])**2)
        for q in [2,19,10**100]:self.assertTrue(g.certified_family_bound(p,R,q,16)['uniform_in_normalization_level'])

    def test_missing_cauchy_circle_rejected(self):
        with self.assertRaises(ValueError):g.family_parameters(g.canonical([('3/4',1)]),1)

    def test_actual_prime_bound_does_not_transfer(self):
        f=['0','1','1000'];t=g.jets(1,2,input_coefficients=f);coefficient=abs(flint.arb(t['values'][2]));native=g.certified_jet_bound(1,R,2);self.assertGreater(coefficient,flint.arb(native['bound_ball']))
        with self.assertRaises(ValueError):g.certified_jet_bound(1,R,2,'generic_sequence')

    def test_invalid_radius_domains(self):
        for r in [{'kind':'constant','value':'0'},dict(R,coefficient='-1'),dict(R,coordinate_power='0'),dict(R,coordinate_power='-1/6'),{'kind':'unsupported'}]:
            self.assertFalse(g.radius_certificate(r)['admitted'])
            with self.assertRaises(ValueError):g.certified_jet_bound(1,r,4)

    def test_fractional_indices_are_not_integer_parameter_jets(self):
        for m in [-1,Q(1,2),True]:
            with self.assertRaises(ValueError):g.jets(m,8)

    def test_all_real_scale_certificate_scope(self):
        c=g.certified_jet_bound(2,R,'27/5');self.assertTrue(c['all_real_x_ge_one']);self.assertEqual(c['ordinary_power'],'1');self.assertFalse(c['RH_strength'])

    def test_compact_limit_keeps_factorial(self):
        self.assertTrue(g.feature_limit_admission('nested_log_integer_2','1/2',2)['admitted']);self.assertFalse(g.feature_limit_admission('nested_log_integer_2','1',2)['admitted'])

    def test_limit_not_infinite_scale_exchange(self):
        c=g.feature_limit_admission('nested_log_integer_3','1/6',3);self.assertTrue(c['uniform_on_compact_x_only']);self.assertFalse(c['same_as_fixed_q_parent']);self.assertFalse(c['infinite_x_limit_exchange_claimed'])

    def test_entire_integer_tail_gate(self):
        self.assertTrue(g.jet_bank_recovery(17)['admitted']);self.assertFalse(g.jet_bank_recovery(17,False)['admitted']);self.assertFalse(g.jet_bank_recovery(17,True,'generic_sequence')['admitted'])

    def test_finite_bank_is_not_critical_premise(self):
        c=g.jet_bank_recovery(0);self.assertFalse(c['global_critical_signed_premise_proved']);self.assertFalse(c['RH_proved']);self.assertTrue(c['finite_positive_jet_RH_recovery_unproved'])

    def test_observer_resource_exhaustion_is_missing(self):
        c=g.jet_observer(9);self.assertTrue(c['missing']);self.assertTrue(c['missing_not_counterexample'])

    def test_radius_cap_and_level_domains(self):
        with self.assertRaises(ValueError):g.radius_value(R,g.real(1),1,Q(3,4))
        with self.assertRaises(ValueError):g.certified_family_bound(g.canonical([('1/2',1)]),R,Q(5,2),4)
        with self.assertRaises(ValueError):g.certified_jet_bound(1,R,'1/2')


if __name__=='__main__':unittest.main()
