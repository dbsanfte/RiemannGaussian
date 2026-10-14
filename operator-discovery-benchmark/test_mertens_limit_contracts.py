"""Normalization, limit scope, and mixed-family inverse-cost regressions."""
from fractions import Fraction as Q
import unittest
import flint
from fractional_remainder_grammar import canonical
from mertens_limit_audit import certificate
from check_mertens_limits import finite_inverse_calibration


def bound(C,kappa=0,ell=0):return {"constant":str(C),"theta":"1/2","parameter_power":str(kappa),"log_power":str(ell)}


class Contracts(unittest.TestCase):
    def test_pure_Mertens_constant_rejected_but_log_loss_retained(self):
        p=canonical([1],[0]);self.assertIsNotNone(certificate(p,bound(Q(887,512))))
        self.assertIsNone(certificate(p,bound(2)))
        self.assertIsNone(certificate(p,bound(1,ell=Q(1,2))))

    def test_mixed_family_inverse_cost_is_charged(self):
        p=canonical([1,Q(1,4),2,Q(3,4)],[2,Q(1,4),2,Q(3,4)])
        c=certificate(p,bound(Q(1317,512)));self.assertIsNotNone(c)
        self.assertEqual(c['inverse_asymptotic_norm_constant'],'2/3')
        self.assertEqual(c['implied_Mertens_lim_abs_upper'],'439/256')

    def test_zero_limit_and_critical_inverse_remain_outside_this_gate(self):
        self.assertIsNone(certificate(canonical([1,-1]),bound(1,kappa=0)))
        self.assertIsNone(certificate(canonical([1],[Q(1,2)]),bound(Q(1,10))))

    def test_inverse_retains_signed_normalization(self):
        flint.ctx.prec=256
        witnesses=finite_inverse_calibration();self.assertEqual(len(witnesses),20)
        self.assertTrue(any(r['coefficient_sum']=='-2' for r in witnesses))


if __name__=='__main__':unittest.main()
