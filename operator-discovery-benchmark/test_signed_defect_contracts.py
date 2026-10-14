"""Numerical recurrence inference calibrations, outside the discovery run."""
from fractions import Fraction as Q
import random
import unittest
import flint
from signed_defect_search import learned_rhos,slope_of_positive_defects,generic_defect_coefficient
from stable_scale_grammar import operator_certificate


class SignedDefectContracts(unittest.TestCase):
    def setUp(self): flint.ctx.prec=256

    def test_recover_dyadic_multiplier_from_generic_positive_energy(self):
        scales=[2**j for j in range(2,10)]
        values={X:{2:Q(7,3)*X**3} for X in set(scales+[2*X for X in scales])}
        rhos=learned_rhos(values,2,scales,random.Random(53),{"rho_rounding_denominator":64,"random_rhos_per_program_order":2})
        found=dict(rhos)
        self.assertIn(Q(8),found)
        self.assertTrue(any(r<0 for r,origin in rhos))
        self.assertIn(Q(0),found)

    def test_positive_defect_fit_recovers_a_growth_exponent(self):
        values={X:Q(3,7)*X**2 for X in (16,32,64,128,256,512)}
        self.assertAlmostEqual(slope_of_positive_defects(values),2)
        self.assertIsNone(slope_of_positive_defects({16:0,32:0,64:0}))

    def test_generic_signed_defect_upper_cost_has_correct_interval_scaling(self):
        p={"operator_certificate":operator_certificate(2,[1])}
        self.assertEqual(generic_defect_coefficient(p,2,0),Q(56,3))
        self.assertEqual(generic_defect_coefficient(p,2,-4),28)
        self.assertEqual(generic_defect_coefficient(p,4,7),Q(992,5))


if __name__=="__main__": unittest.main()
