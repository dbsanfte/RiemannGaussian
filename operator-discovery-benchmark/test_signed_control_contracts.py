"""Moment, interpolation and ordinary-zeta control boundaries."""
from fractions import Fraction as Q
import unittest
import flint
from signed_control_grammar import (atoms, prefix, residual, operator_certificate,
    moment_transfer_certificate, complete_window_moments, unit_moment_numerator)


class SignedControlContracts(unittest.TestCase):
    def test_constant_and_sign_crossing_moments(self):
        self.assertEqual(unit_moment_numerator(3,3,4),5*81)
        self.assertEqual(unit_moment_numerator(-1,1,2),1)
        self.assertEqual(Q(unit_moment_numerator(-1,1,4),5),Q(1,5))
        for order in (0,1,3,True):
            with self.assertRaises(ValueError): unit_moment_numerator(0,1,order)

    def test_fractional_scaled_argument_is_interpolated(self):
        mu=[0,1,-1,0,1]; M=prefix(mu)
        self.assertEqual(residual(mu,M,[[2,"1/2"]],3),Q(-1,4))

    def test_complete_window_with_zero_slope_and_sign_changes(self):
        mu=[0,1,-1,0,1]; M=prefix(mu)
        moments=complete_window_moments(mu,M,[],[1,2],[2,4])
        self.assertEqual(moments[1],{2:Q(1,3),4:Q(1,5)})
        self.assertEqual(moments[2],{2:Q(1,3),4:Q(1,5)})

    def test_root_bridge_rejects_large_inverse_cost(self):
        self.assertFalse(operator_certificate([[2,"3"]])["nonvanishing_multiplier_Re_s_ge_half_certified"])
        good=operator_certificate([[2,"-1/2"],[7,"1/3"]])
        self.assertTrue(good["nonvanishing_multiplier_Re_s_ge_half_certified"])
        self.assertFalse(good["global_signed_cancellation_estimate_proved"])
        self.assertFalse(good["historical_priority_is_acceptance_gate"])

    def test_global_moment_premise_is_required(self):
        certificate=moment_transfer_certificate([],2,2)
        self.assertEqual(certificate["pointwise_exponent"],"2/3")
        self.assertFalse(certificate["uniform_moment_premise_proved"])
        self.assertIn("finite moment order is insufficient",certificate["RH_family_obligation"])
        self.assertFalse(moment_transfer_certificate([[2,"3"]],2,2)["inverse_at_this_exponent_certified"])

    def test_invalid_scales_and_duplicate_normalization(self):
        for rows in ([[1,"1"]],[[True,"1"]],[[2.0,"1"]]):
            with self.assertRaises(ValueError): atoms(rows)
        self.assertEqual(atoms([[3,"1/2"],[3,"-1/2"]]),())


if __name__=="__main__": unittest.main()
