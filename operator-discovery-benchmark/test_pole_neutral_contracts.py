"""Independent special-case and branch-obstruction calibration checks."""
from fractions import Fraction as Q
import unittest
import flint
from pole_neutral_grammar import coefficients,kernel,point_value,transfer
from estimate_grammar import inverse_one_prefix


class Contracts(unittest.TestCase):
    def test_kernel_calibrations(self):
        flint.ctx.prec=256
        for u in (flint.arb(2).log(),flint.arb(29).log()):
            self.assertTrue(kernel(1,1,u).overlaps(u.exp()-1))
            self.assertTrue(kernel(Q(1,2),1,u).overlaps(u.sqrt().erfi()))
            for b in (Q(1,3),Q(1,6)):
                self.assertTrue(kernel(b,0,u).overlaps(u**(flint.arb(b.numerator)/b.denominator)*(flint.arb(b.numerator)/b.denominator+1).rgamma()))
        self.assertEqual(kernel(Q(1,6),1,flint.arb(0)),0)

    def test_classical_smoothed_signed_inverse(self):
        flint.ctx.prec=256;mu=inverse_one_prefix(128);f=coefficients(1,128)
        self.assertEqual(f,list(map(Q,mu)))
        for x in (1,2,7,29,128):
            target=sum((Q(mu[n])*(Q(x,n)-1) for n in range(1,x+1)),Q(0))
            ball=point_value(f,1,1,x)
            self.assertTrue(ball.contains(flint.arb(target.numerator)/target.denominator))

    def test_distinct_coefficient_roots_and_all_multiplicity_bridge(self):
        f=coefficients(Q(1,6),64)
        self.assertEqual(f[2],Q(-1,6))
        self.assertNotEqual(f[4],0)
        self.assertTrue(transfer(Q(1,6),Q(1,6),1,Q(1,2),2,0)["zero_multiplicities_preserved"])

    def test_pole_and_shift_obstructions(self):
        for a in (Q(1,2),Q(1,3),Q(1,6)):
            self.assertTrue(transfer(a,a,1,Q(1,2),2,0)["RH_sufficient_if_uniform"])
            self.assertFalse(transfer(a,0,0,Q(1,2),2,0)["RH_sufficient_if_uniform"])
            self.assertTrue(transfer(a,0,0,Q(1,2),2,0)["local_divisor_obstructions"])
        self.assertTrue(transfer(1,Q(1,6),0,Q(1,2),2,0)["RH_sufficient_if_uniform"])
        self.assertTrue(transfer(1,Q(1,6),Q(3,2),Q(1,2),2,0)["local_divisor_obstructions"])
        self.assertEqual(Q(transfer(1,Q(1,6),Q(3,2),0,2,0)["mellin_exponent"]),Q(1,2))


if __name__=="__main__":unittest.main()
