"""Primary proof-lead gating, independent of a nominated search answer."""
from fractions import Fraction as Q
import unittest
import flint
from stable_scale_grammar import operator_certificate
from mellin_search import add_direct_transfer


class MellinSelectionContracts(unittest.TestCase):
    def setUp(self): flint.ctx.prec=256

    def record(self,beta,failures=None):
        return {"program":{"base":2,"polynomial":["1"],"operator_certificate":operator_certificate(2,[1])},
                "estimates":[{"order":4,"beta":str(beta),"constant":"2", "sampled_validation_failure_windows":failures or []}]}

    def test_old_pointwise_lead_is_ineligible_after_stronger_obstruction(self):
        row=add_direct_transfer(self.record(Q(43,16)),flint.acb(0.5,14))
        self.assertIsNone(row["primary_mellin_score"])
        self.assertEqual(row["estimates"][0]["direct_mellin_transfer"]["status"],"ruled_out_by_actual_zeta_zero")

    def test_exact_RH_threshold_is_eligible_but_unproved(self):
        row=add_direct_transfer(self.record(3),flint.acb(0.5,14))
        self.assertEqual(row["primary_mellin_score"][0],"1/2")
        leaf=row["estimates"][0]["direct_mellin_transfer"]["certificate"]
        self.assertTrue(leaf["RH_sufficient_if_uniform_and_all_height_multiplier_nonzero"])
        self.assertFalse(leaf["uniform_signed_moment_premise_proved"])

    def test_sampled_validation_failure_prevents_primary_rank(self):
        row=add_direct_transfer(self.record(3,[65536]),flint.acb(0.5,14))
        self.assertIsNone(row["primary_mellin_score"])
        self.assertEqual(row["estimates"][0]["direct_mellin_transfer"]["status"],"failed_sampled_validation")


if __name__=="__main__": unittest.main()
