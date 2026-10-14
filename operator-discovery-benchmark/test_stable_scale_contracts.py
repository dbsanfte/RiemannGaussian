"""Meaningful calibration and failure tests, outside the discovery protocol."""
from fractions import Fraction as Q
import unittest
import flint

import stable_scale_grammar as grammar
from check_stable_scale import independent_disk, newton_inverse


class StableScaleContracts(unittest.TestCase):
    def setUp(self): flint.ctx.prec=256

    def test_noncontractive_signed_polynomial_is_admissible(self):
        # A calibration example, never supplied as an expected discovery answer.
        p=[1,-3,Q(9,4)]
        cert=grammar.operator_certificate(4,p)
        self.assertFalse(cert["triangle_certificate_available"])
        self.assertTrue(cert["all_height_critical_multiplier_certified"])
        self.assertTrue(cert["outside_triangle_domain_certified"])
        bound=flint.arb(cert["critical_weight_inverse_norm_upper_ball"])
        self.assertTrue(bound>=16)
        self.assertTrue(bound<17)

    def test_root_erasing_filter_cannot_pass_disk_certificate(self):
        cert=grammar.operator_certificate(2,[1,-2])
        self.assertFalse(cert["all_height_critical_multiplier_certified"])
        self.assertEqual(sum(Q(c)/2**k for k,c in enumerate(cert["polynomial"])),0)
        self.assertFalse(grammar.transfer_certificate(cert,4,Q(5,2),1)["inverse_transfer_certified"])

    def test_boundary_zero_and_interior_zero_are_rejected(self):
        for p in ([1,-1],[1,0,-1],[1,0,Q(-4,3)]):
            self.assertFalse(grammar.schur_certificate(p,1)["certified"])
        self.assertTrue(grammar.schur_certificate([1,Q(-3,4)],1)["certified"])

    def test_independent_recursions_agree_at_all_degrees(self):
        for p in ([1],[1,Q(3,4)],[1,Q(-7,8),Q(1,4)],
                  [1,Q(-3,4),Q(5,8),Q(-1,8)],[1,Q(1,2),Q(-1,3),Q(1,4),Q(1,8)]):
            cert=grammar.schur_certificate(p,Q(5,8))
            ok,steps,delta,failed=independent_disk(p,Q(5,8))
            self.assertEqual(cert["certified"],ok)
            self.assertEqual(cert["steps"],steps)
            if ok: self.assertEqual(Q(cert["uniform_multiplier_lower_bound"]),delta)
            self.assertEqual(grammar.inverse_coefficients(p,64),newton_inverse([Q(c) for c in p],64))

    def test_composition_keeps_original_scale_semantics(self):
        product=grammar.multiply([1,Q(-3,2)],[1,Q(-3,2)])
        self.assertEqual(product,[1,-3,Q(9,4)])
        self.assertEqual(grammar.scale_rows(4,product),[[4,"3"],[16,"-9/4"]])

    def test_transfer_does_not_certify_its_uniform_premise(self):
        cert=grammar.operator_certificate(4,[1,-3,Q(9,4)])
        transferred=grammar.transfer_certificate(cert,8,Q(19,4),2)
        self.assertTrue(transferred["inverse_transfer_certified"])
        self.assertEqual(transferred["pointwise_exponent"],"19/36")
        self.assertFalse(transferred["uniform_premise_proved"])
        self.assertFalse(transferred["RH_proved"])
        self.assertFalse(grammar.transfer_certificate(cert,8,4,2)["inverse_transfer_certified"])

    def test_finite_divisor_and_normalization_domains(self):
        for b in (True,1,-3,Q(3,2)):
            with self.assertRaises(ValueError): grammar.scale_rows(b,[1,1])
        for p in ([],[0,1],[2,1]):
            with self.assertRaises(ValueError): grammar.polynomial(p)
        self.assertEqual(grammar.polynomial([1,0,0]),[1])
        for b in (2,3,4,5,7,9):
            self.assertTrue(all(b*r*r>1 for r in grammar.outer_radii(b)))


if __name__=="__main__": unittest.main()
