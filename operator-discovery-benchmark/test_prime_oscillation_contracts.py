"""Generic scope contracts for the imported oscillation consequence."""
from fractions import Fraction as Q
import unittest
import flint
from prime_twist_grammar import canonical
from prime_oscillation_audit import certificate
from check_prime_oscillation import class_matches,check_certificate


class OscillationContracts(unittest.TestCase):
    def setUp(self):flint.ctx.prec=768

    def candidate(self,theta,ell=0):return {"theta":str(Q(theta)),"log_power":str(Q(ell))}

    def test_pure_critical_log_channel_is_rejected(self):
        p=canonical(1,[1],[1],"log");c=self.candidate(Q(1,2));cert=certificate(p,c)
        self.assertTrue(class_matches(p,c));self.assertIsNotNone(cert);check_certificate(p,cert)

    def test_fractional_log_loss_and_weighted_channel_are_retained(self):
        p=canonical(1,[1],[1],"log")
        self.assertIsNone(certificate(p,self.candidate(Q(1,2),Q(1,6))))
        self.assertFalse(class_matches(p,self.candidate(Q(1,2),Q(1,6))))
        p=canonical(1,[1],[1],"weighted")
        self.assertIsNone(certificate(p,self.candidate(Q(1,2))))

    def test_negative_growth_and_signed_eventual_inverse_are_supported(self):
        for d,cs in [(Q(2,3),[0,1]),(Q(1,6),[0,1,-4,Q(1,2)])]:
            p=canonical(d,cs,cs,"log");c=self.candidate(Q(1,2)-Q(p["leading_shift"]));cert=certificate(p,c)
            self.assertTrue(class_matches(p,c));self.assertIsNotNone(cert);check_certificate(p,cert)

    def test_mismatched_real_poles_have_separate_scope(self):
        p=canonical(Q(1,6),[1,-1],[1,0],"log");c=self.candidate(Q(1,2))
        self.assertIsNone(certificate(p,c));self.assertFalse(class_matches(p,c))
        p=canonical(Q(1,2),[1,-1],[1,0],"log");cert=certificate(p,c)
        self.assertIsNotNone(cert);check_certificate(p,cert)


if __name__=="__main__":unittest.main()
