"""Public mathematical contracts, independent of any sealed search outcomes."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest
import flint
from prime_twist_grammar import (canonical,semantics_digest,twist,normalizer,
    finite_part_center,polynomial_range,observe,transfer,recovery_cost,weak_uniform_bound)
from check_prime_twists import (real,power,kernel,center,independent_observe,
    inverse_cost,program_checks,shifted_pole)


class PrimeTwistContracts(unittest.TestCase):
    def setUp(self):flint.ctx.prec=384

    def program(self,delta,c,b,channel="weighted"):
        p=canonical(delta,c,b,channel);p["id"]=semantics_digest(p)
        p["exact_center"]=finite_part_center(p)
        p["coefficient_range_certificate"]=polynomial_range(p["coefficients"])
        p["weak_uniform_bound"]=weak_uniform_bound(p,"359/128")
        return p

    def test_fractional_roots_include_arbitrary_denominators_and_inverses(self):
        for a in (Q(1,2),Q(1,3),Q(1,6),Q(5,17),Q(-1,6)):
            self.assertTrue(twist(73,a).overlaps(power(73,a)))
            self.assertTrue((twist(73,a)**a.denominator*real(73)**a.numerator).contains(1))
        with self.assertRaises(ValueError):twist(0,Q(1,6))

    def test_regular_zero_exponent_kernels_and_negative_exponents(self):
        for channel in ("weighted","log"):
            for alpha in (Q(0),Q(1,6),Q(-1,3)):
                self.assertTrue(normalizer(alpha,Q(19,2),channel).overlaps(kernel(alpha,Q(19,2),channel)))
                self.assertTrue(normalizer(alpha,2,channel).contains(0))
                self.assertEqual(normalizer(alpha,1,channel),0)

    def test_negative_growth_costs_shift_and_requires_exact_center(self):
        p=self.program(1,[0,1],[0,1],"log")
        A=p["exact_center"];self.assertTrue(flint.arb(A["value_ball"]).overlaps(flint.arb.const_euler()-real(2).log()))
        tr=transfer(p,Q(-1,2),0,1,A)
        self.assertEqual(tr["ordinary_zeta_exponent"],"1/2")
        self.assertTrue(tr["RH_sufficient_if_uniform"])
        self.assertTrue(transfer(p,Q(-1,2),0,1)["analytic_status"].startswith("negative_growth"))
        corrupted=dict(A,semantic_digest="wrong")
        self.assertTrue(transfer(p,Q(-1,2),0,1,corrupted)["analytic_status"].startswith("negative_growth"))
        self.assertTrue(transfer(p,Q(-5,8),0,1,A)["analytic_status"].startswith("uniform_claim_ruled_out_by_actual"))

    def test_preceding_normalizer_and_inverse_shift_loss_are_charged(self):
        p=self.program(1,[0,1],[1,1],"log")
        tr=transfer(p,Q(-1,2),0,1,p["exact_center"])
        self.assertEqual(tr["output_mellin_exponent"],"0")
        self.assertEqual(tr["ordinary_zeta_exponent"],"1")
        self.assertTrue(tr["analytic_status"].startswith("uniform_claim_ruled_out_by_shifted"))
        shifted=self.program(Q(3,2),[0,1],[0,1])
        self.assertGreaterEqual(Q(transfer(shifted,0,0,1)["ordinary_zeta_exponent"]),Q(3,2))

    def test_positive_prime_weight_can_still_have_a_fatal_shifted_pole(self):
        p=self.program(Q(1,6),[1,-1],[1,0])
        self.assertEqual(p["coefficient_range_certificate"]["status"],"proved_between_zero_and_one")
        self.assertTrue(p["coefficient_range_certificate"]["strictly_positive_in_open_interval"])
        tr=transfer(p,Q(1,2),0,1)
        self.assertEqual(tr["uncancelled_pole_residues_in_output_half_plane"],[{"location":"5/6","residue":"-1"}])
        self.assertFalse(tr["RH_sufficient_if_uniform"])
        self.assertEqual(shifted_pole(Q(1,6))["location"],"5/6")

    def test_unrelated_signed_inputs_have_independent_finite_semantics(self):
        f=[Q(0),Q(0),Q(-2,3),Q(1,7),Q(0),Q(5,6),Q(-1,2),Q(4,3),Q(0)]
        ps=[self.program(Q(1,6),[1,-2,Q(1,3)],[1,0,1],channel) for channel in ("weighted","log")]
        stored=observe(ps,f,[1,2,3,5,8]);flint.ctx.prec=768
        independent=independent_observe(ps,f,[1,2,3,5,8])
        for p in ps:
            for n,v in independent[p["id"]].items():self.assertTrue(flint.arb(stored[p["id"]][n]).contains(v))
        f[1]=1
        with self.assertRaises(ValueError):observe(ps,f,[2])

    def test_full_path_costs_and_horizontal_recovery_are_independently_checked(self):
        for channel in ("weighted","log"):
            flint.ctx.prec=384;p=self.program(Q(1,6),[1,-1,1],[1,-1,1],channel)
            A={"kind":"rational","value":"0"};tr=transfer(p,Q(1,2),0,10,A);cost=recovery_cost(p,tr,Q(5,8),16)
            c={"theta":"1/2","log_power":"0","constant":"10","offset":A,"transfer":tr,
                "cost_sigma":"5/8","cost_height":"16","full_recovery_cost":cost,
                "log_reciprocal_cost":float(flint.arb(cost["log_reciprocal_zeta_bound_ball"]).upper())}
            flint.ctx.prec=768;inverse_cost(c,p)
            broken=deepcopy(c);broken["full_recovery_cost"]["recurrence_nodes"][0]["conditional_transform_bound_ball"]="0"
            with self.assertRaises(AssertionError):inverse_cost(broken,p)

    def test_absolute_majorants_do_not_pass_the_RH_gate(self):
        for channel in ("weighted","log"):
            for d,c in [(1,[1]),(1,[0,1]),(Q(3,2),[0,1])]:
                flint.ctx.prec=384;p=self.program(d,c,c,channel);flint.ctx.prec=768;program_checks(p,"359/128")
                self.assertFalse(p["weak_uniform_bound"]["RH_sufficient"])
                self.assertGreaterEqual(Q(p["weak_uniform_bound"]["ordinary_zeta_exponent_after_shift_recovery"]),1)


if __name__=="__main__":unittest.main()
