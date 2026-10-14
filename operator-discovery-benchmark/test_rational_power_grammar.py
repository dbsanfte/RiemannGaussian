"""Domain, sign, branch and recovery checks separate from discovery."""
from fractions import Fraction as Q
import unittest
import flint

from rational_power_grammar import (real_power, complex_power, PowerDomainError,
    unit_absolute_moment, complete_absolute_moments, transfer_certificate,
    evaluate, infer)
from signed_control_grammar import complete_window_moments, prefix


class Contracts(unittest.TestCase):
    def test_general_roots_and_domains(self):
        for d in (2, 3, 6, 11, 17):
            self.assertEqual(real_power(Q(5)**d, Q(1,d)), 5)
            self.assertEqual(real_power(-Q(5)**d, Q(1,d), "signed"), -5)
        self.assertEqual(real_power(-8, Q(1,3)), -2)
        self.assertEqual(real_power(-8, Q(2,3)), 4)
        for x, a in ((-4,Q(1,2)),(-64,Q(1,6)),(0,Q(-1,3)),(0,Q(0))):
            with self.assertRaises(PowerDomainError): real_power(x,a)
        self.assertEqual(real_power(0,Q(1,6)),0)

    def test_signed_recovery_and_nonlaw(self):
        flint.ctx.prec=256
        for d in (2,3,6,11):
            for x in (-19,-1,0,2,29):
                y=real_power(x,Q(1,d),"signed")
                restored=real_power(y,Q(d),"signed")
                if isinstance(restored,Q): self.assertEqual(restored,x)
                else: self.assertTrue(restored.contains(x))
        self.assertEqual(real_power(real_power(-5,2),Q(1,2)),5)
        self.assertNotEqual(real_power(real_power(-5,2),Q(1,2)),-5)

    def test_complex_cut_and_monodromy_conditions(self):
        flint.ctx.prec=256
        for d in (2,3,6,17):
            z=flint.acb(2,3); root=complex_power(z,Q(1,d))
            self.assertTrue((root**d).contains(z))
        for z in (flint.acb(-1),flint.acb(0),flint.acb(flint.arb(-1),flint.arb(0,1))):
            with self.assertRaises(PowerDomainError): complex_power(z,Q(1,6))

    def test_complete_fractional_integration(self):
        flint.ctx.prec=256
        mu=[0,1,-1,0,1,-1,1,-1,0,-1,1,-1,1,0,-1,1,0,1,-1,1,0]
        M=prefix(mu); rows=[[2,"3/4"],[3,"-1/7"]]
        for q in (2,4,6):
            exact=complete_window_moments(mu,M,rows,[1,2,3,7,9],[q])
            balls=complete_absolute_moments(mu,M,rows,[1,2,3,7,9],[Q(q)])
            for X in exact: self.assertTrue(balls[X][Q(q)].contains(flint.arb(str(exact[X][q]))))
        for q in (Q(1,2),Q(1,3),Q(1,6),Q(3,2),Q(7,6)):
            self.assertTrue(unit_absolute_moment(-1,1,q).contains(flint.arb(q.denominator)/ (q.numerator+q.denominator)))
            self.assertEqual(unit_absolute_moment(0,0,q),0)

    def test_transfer_does_not_shrink_recovery_target(self):
        for q in (Q(1),Q(3,2),Q(7,6),Q(11,3)):
            c=transfer_certificate(q,q/2+1,2,1)
            self.assertEqual(Q(c["mellin_exponent"]),Q(1,2))
        c=transfer_certificate(Q(1,6),Q(13,12),2,1)
        self.assertGreater(Q(c["mellin_exponent"]),Q(1,2))
        self.assertIn("Lipschitz",c["method"])
        self.assertFalse(c["uniform_signed_moment_premise_proved"])

    def test_composable_typed_language(self):
        term=["rpow",["add",["rpow",["input",0],"1/6","signed"],["q","1/2"]],"3/2","signed"]
        self.assertEqual(infer(term),"real_sequence")
        self.assertEqual(len(evaluate(term,[[-64,0,729],[1,2,3]])),3)
        power=["dpow",["input",0],"1/6"]
        root=evaluate(power,[[1]*32,[]])
        restored=evaluate(["dpow",["input",0],"6"],[root,[]])
        self.assertEqual(restored,[Q(1)]*32)
        with self.assertRaises(ValueError): evaluate(power,[[2]*32,[]])


if __name__ == "__main__": unittest.main()
