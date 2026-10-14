"""Boundary exponents and quantitative transfer calibration."""
from fractions import Fraction as Q
import unittest
import flint
import signed_mellin_transfer as transfer
from check_signed_mellin_transfer import independent_bound


class SignedMellinContracts(unittest.TestCase):
    def setUp(self): flint.ctx.prec=256

    def test_one_finite_moment_order_can_be_RH_sufficient(self):
        for q in (2,4,6,8):
            cert=transfer.certificate(q,Q(q,2)+1,3)
            self.assertEqual(cert["mellin_exponent"],"1/2")
            self.assertTrue(cert["RH_sufficient_if_uniform_and_all_height_multiplier_nonzero"])
            self.assertFalse(cert["contradicted_if_critical_zero_multiplier_nonzero"])
            self.assertFalse(cert["uniform_signed_moment_premise_proved"])

    def test_stronger_obstruction_rejects_old_pointwise_lead(self):
        beta=Q(43,16); self.assertGreater(beta/5,Q(1,2))
        cert=transfer.certificate(4,beta,4)
        self.assertEqual(cert["mellin_exponent"],"27/64")
        self.assertTrue(cert["contradicted_if_critical_zero_multiplier_nonzero"])

    def test_power_function_holder_calibration(self):
        for q in (2,4,6,8):
            beta=Q(q,2)+1; C=Q(2**int(beta)-1)/beta
            bound=transfer.mellin_bound(q,beta,C,Q(3,4))
            # R(t)=sqrt(t) has Mellin integral exactly four on sigma=3/4.
            self.assertTrue(bound>=4)

    def test_compact_correction_removable_at_one(self):
        rows=[[2,"-1"],[9,"2/3"]]
        at_one=transfer.compact_correction_bound(rows,1)
        exact=flint.arb(2).log()/2+transfer.real(Q(2,27))*flint.arb(9).log()
        self.assertTrue(at_one.overlaps(exact))
        self.assertTrue(transfer.compact_correction_bound(rows,Q(3,4))>at_one)

    def test_reciprocal_cost_independent_formulas_and_input_domains(self):
        rows=[[3,"-1/4"]]
        value=transfer.reciprocal_bound(rows,Q(1,2),4,3,2,Q(3,4))
        checked=independent_bound(rows,Q(1,2),4,Q(3),Q(2),Q(3,4))
        self.assertTrue(value.overlaps(checked))
        with self.assertRaises(ValueError): transfer.mellin_bound(4,3,2,Q(1,2))
        with self.assertRaises(ValueError): transfer.reciprocal_bound(rows,0,4,3,2,Q(3,4))
        with self.assertRaises(ValueError): transfer.certificate(3,3,2)
        with self.assertRaises(ValueError): transfer.certificate(4,3,0)


if __name__=="__main__": unittest.main()
