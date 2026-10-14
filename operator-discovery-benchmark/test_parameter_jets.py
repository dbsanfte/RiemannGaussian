import unittest
from fractions import Fraction as Q
import flint
from estimate_grammar import inverse_one_prefix
from parameter_jets import (power_parameter_jet, logarithmic_kernel_zero_jet,
                           family_zero_jet, root_count_decode, real)
from check_parameter_jets import direct_binomial_jets


class ParameterJetContracts(unittest.TestCase):
    def setUp(self):
        flint.ctx.prec = 256

    def test_general_inputs_and_negative_centre_use_exact_jets(self):
        f = [Q(0),Q(1),Q(-2),Q(1,3),Q(4),Q(-1),Q(3,2),Q(0),Q(-3)]
        for centre in (Q(-2,3),Q(0),Q(5,6)):
            self.assertEqual(power_parameter_jet(f,centre,4),
                             direct_binomial_jets(f,centre,4))

    def test_fixed_x_limit_and_independent_slopes(self):
        mu = list(map(Q,inverse_one_prefix(32)))
        for x in (Q(2),Q(4),Q(9,2),Q(16)):
            d = power_parameter_jet(mu,0,1)[1]
            cut = (x.numerator-1)//x.denominator
            prime_term = real(sum(d[2:cut+1],Q(0)))
            for q,r in ((1,1),(2,1),(1,2)):
                jets = family_zero_jet(mu,x,2,q,r)
                self.assertTrue(jets[0].contains(1))
                self.assertTrue(jets[1].overlaps(r*real(x).log().ei()+q*prime_term))

    def test_root_decoder_keeps_strict_prime_power_endpoints(self):
        mu = list(map(Q,inverse_one_prefix(32)))
        lam = [-v for v in power_parameter_jet(mu,0,1)[1]]
        for x,expected in ((2,0),(Q(201,100),1),(3,1),(4,2),
                           (Q(401,100),2),(8,4),(Q(801,100),4),(16,6)):
            self.assertEqual(root_count_decode(lam,mu,x),expected)

    def test_singular_domains_and_uncertified_tail_are_rejected(self):
        with self.assertRaises(ValueError):
            logarithmic_kernel_zero_jet(flint.arb(0),2)
        with self.assertRaises(ValueError):
            logarithmic_kernel_zero_jet(flint.arb(10),2,terms=1)
        with self.assertRaises(ValueError):
            family_zero_jet([Q(0),Q(1)],1,1)
        with self.assertRaises(ValueError):
            power_parameter_jet([Q(0),Q(0)],0,1)


if __name__ == "__main__":
    unittest.main()
