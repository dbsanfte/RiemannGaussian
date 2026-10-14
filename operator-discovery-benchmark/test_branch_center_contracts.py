"""Public contracts for universal scope, arithmetic typing and rational roots."""
import unittest
from fractions import Fraction as Q
import flint
import branch_center_grammar as g
from check_branch_centers import parameter_certificate,independent_profile,cb
from collections import defaultdict

class Contracts(unittest.TestCase):
    def test_arbitrary_denominator_moments(self):
        p=g.canonical([('1/30021',1),('1/60042',-1)]);c=g.recovery(p);self.assertTrue(c['admitted']);self.assertEqual(c['first_nonzero_moment_order'],1)
    def test_square_cube_sixth_roots(self):
        for b in ['1/2','1/3','1/6']:
            t=g.coefficients(b,12,384);self.assertFalse(t['prime_or_factor_oracle_used']);self.assertLess(flint.arb(t['values'][6]),0)
    def test_all_real_scale_weak_bound_scope(self):
        c=g.weak_certificate(g.canonical([('1/2',1),('1/3',-2)]),23);self.assertTrue(c['global_signed_premise_proved']);self.assertFalse(c['RH_strength']);self.assertEqual(c['ordinary_exponent'],'1')
    def test_high_pass_recovery(self):
        p=g.canonical([('1/2',1),('1/4',-1)]);c=g.recovery(p);self.assertTrue(c['sum_weights_zero']);parameter_certificate(p,c,defaultdict(int))
    def test_second_moment_recovery(self):
        p=g.canonical([('1/2',1),('1/4',-3),('1/8',2)]);c=g.recovery(p);self.assertEqual(c['first_nonzero_moment_order'],2);self.assertTrue(c['admitted'])
    def test_nonuniform_constants_are_allowed(self):
        c=g.recovery(g.canonical([('1/2',1)]));self.assertTrue(c['RH_if_cofinal_critical_signed_estimates']);self.assertFalse(c['global_signed_premise_proved'])
    def test_generic_arithmetic_alias_rejected(self):
        p=dict(g.canonical([('1/2',1)]),arithmetic_model='generic_sequence');self.assertFalse(g.recovery(p)['admitted'])
    def test_incomplete_center_alias_rejected(self):
        p=dict(g.canonical([('1/2',1)]),center='leading_only');self.assertFalse(g.recovery(p)['admitted'])
    def test_zero_family_rejected(self):
        with self.assertRaises(ValueError):g.canonical([('1/2',1),('1/2',-1)])
    def test_level_domain(self):
        with self.assertRaises(ValueError):g.normalization(g.canonical([('1/2',1)]),0)
    def test_root_domain(self):
        for v in ['0','1','3/2','-1/3']:
            with self.assertRaises(ValueError):g.canonical([(v,1)])
    def test_complete_center_boundary(self):
        self.assertEqual(g.complete_center('1/6',1)['value_ball'],'0')
    def test_leading_control_global_obstruction(self):
        p=g.canonical([('1/2',1),('1/4',-1)]);c=g.leading_only_obstruction(p,11);self.assertTrue(c['all_scale_power_below_one_impossible']);self.assertEqual(Q(c['uncancelled_branch_exponent']),Q(21,22))
    def test_recovery_resource_failure_is_missing(self):
        p=g.canonical([('1/2',1),('499/1000',-100)]);c=g.recovery(p,limit=1);self.assertFalse(c['admitted']);self.assertTrue(c['missing_not_counterexample'])
    def test_continued_profile_zero_parameter_calibration(self):
        F=cb(g.fractional_profile('1/30021')['value_ball']);s=flint.acb(g.real(Q(5,8)),16);self.assertLess(float(abs(F-(s.zeta()-1))),0.001)
    def test_serialized_observer_lower_is_strictly_outward(self):
        p=g.canonical([('1/2',1),('1/4',-1)]);o=g.observer(p,28);F=cb(o['normalized_full_profile_ball']);self.assertLess(flint.arb(o['profile_modulus_lower_ball']).upper(),abs(F).lower())

if __name__=='__main__':unittest.main()
