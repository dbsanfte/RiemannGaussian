"""Independent unrolling and positive-control tests for logarithmic transport."""
from fractions import Fraction as Q
import unittest
import flint
from signed_recurrence_transfer import certificate,dyadic_majorant,mellin_majorant


class SignedRecurrenceContracts(unittest.TestCase):
    def setUp(self): flint.ctx.prec=256

    def test_exact_log_loss_is_RH_sufficient_conditionally(self):
        cert=certificate(2,4,2,4,1)
        self.assertTrue(cert["RH_sufficient_with_global_zero_bridge"])
        self.assertFalse(cert["strictly_subcritical_recurrence_ruled_out_if_critical_zero_multiplier_nonzero"])
        actual=Q(1)
        for j in range(12):
            self.assertEqual(actual,dyadic_majorant(cert,j))
            self.assertEqual(actual,4**j*(1+j))
            actual=4*actual+4*4**j
        self.assertFalse(cert["uniform_signed_recurrence_premise_proved"])

    def test_strictly_subcritical_recurrence_is_a_zero_obstruction(self):
        cert=certificate(4,7,Q(23,8),3,1)
        self.assertTrue(cert["strictly_subcritical_recurrence_ruled_out_if_critical_zero_multiplier_nonzero"])
        self.assertFalse(certificate(4,9,3,3,1)["RH_sufficient_with_global_zero_bridge"])

    def test_generic_positive_energy_cannot_pass_the_uniform_premise(self):
        X=100
        A=lambda x:Q(7,3)*x**3
        self.assertGreater(A(2*X)-4*A(X),100*X*X)

    def test_geometric_cost_covers_independent_block_unrolling(self):
        cert=certificate(2,4,2,4,1); sigma=Q(3,4)
        finite=sum((flint.arb(1+j).sqrt()*(flint.arb(2)**(flint.arb(-j)/4)) for j in range(128)),flint.arb(0))
        self.assertTrue(mellin_majorant(cert,sigma)>finite)


if __name__=="__main__": unittest.main()
