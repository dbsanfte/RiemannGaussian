"""Public mathematical domain checks; named examples are calibration only."""
from fractions import Fraction as Q
import unittest
import flint
from prime_discrepancy_grammar import (carry_certificate,density_certificate,
    integer_error_values,increments,square_prefix,diagonal,complete_energy,
    discrepancy_density,off_diagonal_transfer)
from check_prime_discrepancy import prime_coefficients,tables,diagonal_entries,energy,real


class Contracts(unittest.TestCase):
    def setUp(self):
        flint.ctx.prec=384
        self.f=prime_coefficients(65)

    def test_floor_domain_rejections_and_full_period(self):
        self.assertEqual(carry_certificate([1,0])["status"],"nonzero_linear_drift")
        self.assertEqual(carry_certificate([1,-1,-3,2])["status"],"negative_period_cell")
        c=carry_certificate([1,-2])
        self.assertEqual(c["period_cells"],["0","1"])

    def test_uncertified_floor_and_short_patch_rejected(self):
        with self.assertRaises(ValueError):density_certificate({"status":"nonzero_linear_drift"},[],4)
        with self.assertRaises(ValueError):density_certificate(carry_certificate([1,-2]),[real(0)],4)

    def test_signed_prime_power_increments(self):
        v=integer_error_values(self.f,1);a=increments(v)
        self.assertGreater(real(2),real(2).li())
        self.assertGreater(real(1),1/(16*real(2).log()**2))
        for n in (2,3,4,8,9,16,25,27):
            self.assertTrue(a[n+1].overlaps(real(n+1).li()-real(n).li()-real(self.f[n])))
        self.assertGreater(real(0),a[4]) # the prime three supplies a negative increment
        self.assertGreater(a[7],real(0)) # a composite supplies a positive increment

    def test_rational_delay_complete_energies_and_diagonals(self):
        atoms=[["1","1"],["3/2","-1/3"],["5/2","4/7"]]
        v=integer_error_values(self.f,1);a=increments(v);count,weighted=square_prefix(a)
        independent=tables(self.f,["1"])["1"]
        for X in (1,2,3,15,32):
            K=diagonal_entries(atoms,X)
            D=sum((independent[2][n]*real(K[n]) for n in range(1,len(K))),real(0))
            self.assertTrue(D.overlaps(diagonal(atoms,a,count,weighted,X)))
            self.assertTrue(energy(atoms,independent[0],X)[0].overlaps(complete_energy(atoms,v,X)))

    def test_diagonal_duplicate_delay_identity(self):
        v=integer_error_values(self.f,1);a=increments(v);count,weighted=square_prefix(a)
        D=diagonal([["1","1"],["1","-1"]],a,count,weighted,16)
        self.assertTrue(D.contains(0))

    def test_density_patch_domain_and_transfer_thresholds(self):
        a=increments(integer_error_values(self.f,1))
        with self.assertRaises(ValueError):discrepancy_density(a,1,4,7)
        d=discrepancy_density(a,1,4,32)
        p={"atoms":[["1","1"]],"beta":"1"}
        self.assertEqual(off_diagonal_transfer(p,0,0,1,d)["mellin_exponent"],"1/2")
        self.assertTrue(off_diagonal_transfer(p,0,0,1,d)["RH_sufficient_if_uniform"])
        self.assertTrue(off_diagonal_transfer(p,-1,1,1,d)["analytic_status"].startswith("uniform_claim_ruled_out_by_actual"))
        self.assertFalse(off_diagonal_transfer(p,0,Q(9,4),1,d)["RH_sufficient_if_uniform"])

    def test_certificate_beta_and_domain_must_match(self):
        a=increments(integer_error_values(self.f,1));d=discrepancy_density(a,1,4,32)
        with self.assertRaises(ValueError):off_diagonal_transfer({"atoms":[["1","1"]],"beta":"0"},0,1,1,d)
        with self.assertRaises(ValueError):off_diagonal_transfer({"atoms":[["1/2","1"]],"beta":"1"},0,1,1,d)
        with self.assertRaises(ValueError):off_diagonal_transfer({"atoms":[["1","1"]],"beta":"1"},0,-1,1,d)


if __name__=="__main__":unittest.main()
