import unittest
from fractions import Fraction as Q
import flint
from prime_error_grammar import (canonical_atoms,logarithmic_coefficients,
    prefix,response,value,multiplier,transfer,increment_cost,cost,real)
from check_prime_error import prime_coefficients,support_table,independent_response


class PrimeErrorContracts(unittest.TestCase):
    def setUp(self):
        flint.ctx.prec=320
        self.f=logarithmic_coefficients(128)
        self.counts=prefix(self.f)

    def test_factor_free_coefficients_match_actual_prime_powers(self):
        self.assertEqual(self.f,prime_coefficients(128))
        self.assertEqual(self.f[8],Q(1,3))
        self.assertEqual(self.f[6],Q(0))

    def test_multiplier_zero_at_one_remains_admissible(self):
        p={"atoms":[["1","1"],["2","-2"]],"beta":"1"}
        self.assertTrue(multiplier(p,flint.acb(1)).contains(0))
        cert=transfer(p,Q(1,2),Q(1,6),2,0)
        self.assertTrue(cert["RH_sufficient_if_uniform"])
        self.assertFalse(cert["all_height_multiplier_nonvanishing_required"])
        self.assertFalse(cert["uniform_signed_premise_proved"])

    def test_strict_endpoint_and_compact_truncation(self):
        self.assertEqual(value(self.counts,Q(255,128)),0)
        self.assertTrue(value(self.counts,2).overlaps(real(2).li()))
        self.assertTrue(value(self.counts,Q(257,128)).overlaps(real(Q(257,128)).li()-1))
        with self.assertRaises(ValueError):value(self.counts,0)

    def test_rational_delays_and_prime_jumps_fit_proved_increment_cost(self):
        p={"atoms":[["1","1"],["3/2","-3"],["5/2","2"]],"beta":"1"}
        B=increment_cost(p)
        for n in range(1,32):
            points=[Q(n),Q(n)+Q(1,127),Q(n)+Q(126,127)]
            source=response(p,self.counts,points)
            audit=independent_response(p,support_table(prime_coefficients(128)),points)
            for t in points:self.assertTrue(source[str(t)].overlaps(audit[str(t)]))
            for t in points[1:]:self.assertLessEqual(abs(source[str(t)]-source[str(Q(n))]).upper(),B.lower())

    def test_wrong_prime_weights_keep_pole_obstruction(self):
        for beta in (0,Q(1,2),2):
            p={"atoms":[["1","1"],["2","-2"]],"beta":str(beta)}
            c=transfer(p,Q(1,2),Q(1,2),2,0)
            self.assertTrue(c["uncancelled_pole_logarithm_at_one"])
            self.assertFalse(c["RH_sufficient_if_uniform"])

    def test_normalization_excludes_identically_zero_filter(self):
        with self.assertRaises(ValueError):canonical_atoms([[1,1],[1,-1]])
        with self.assertRaises(ValueError):canonical_atoms([[2,1]])
        self.assertEqual(canonical_atoms([[2,3],[1,1],[2,-1]]),[["1","1"],["2","2"]])

    def test_reciprocal_reconstruction_charges_increasing_constant(self):
        p={"atoms":[["1","1"]],"beta":"1"}
        first=cost(p,transfer(p,Q(1,2),Q(1,3),1,0),Q(5,8),16)
        second=cost(p,transfer(p,Q(1,2),Q(1,3),2,0),Q(5,8),16)
        self.assertGreater(second.lower(),first.upper())


if __name__=="__main__":unittest.main()
