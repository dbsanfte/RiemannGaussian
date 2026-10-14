"""Critical scope and convention regressions, separate from discovery."""
from fractions import Fraction as Q
import unittest
import flint
from estimate_grammar import inverse_one_prefix
from fractional_remainder_grammar import canonical,primitive_tables,transfer,order,power,complex_ball


class Contracts(unittest.TestCase):
    def setUp(self):flint.ctx.prec=256

    def test_zero_order_is_the_positive_order_limit_not_the_unit_identity(self):
        rows=primitive_tables(inverse_one_prefix(3),[Q(0)],[1,2,3])['0']
        self.assertTrue(flint.arb(rows['1']['remainder']).contains(0))
        self.assertTrue(flint.arb(rows['2']['remainder']).contains(0))
        self.assertTrue(flint.arb(rows['3']['remainder']).contains(flint.arb(1)/2))

    def test_high_pass_family_retains_conditional_zero_bridge_and_charges_rate(self):
        p=canonical([1,-3,3,-1]);self.assertEqual(p['parameter_vanishing_order'],3)
        good=transfer(p,Q(1,2),3,0,1)
        self.assertTrue(good['RH_sufficient_if_uniform'])
        self.assertFalse(good['finite_parameter_grid_suffices'])
        self.assertEqual(good['numerator_parameter_pole_residue'],'1/3')
        self.assertEqual(transfer(p,Q(1,2),Q(7,2),0,1)['analytic_status'],'ruled_out_by_exact_parameter_vanishing_order')
        self.assertEqual(transfer(p,Q(1,4),3,1,1)['analytic_status'],'ruled_out_by_actual_critical_zero_and_infinite_parameter_family')

    def test_positive_order_branch_gate_keeps_independent_zero_normalizer(self):
        self.assertTrue(transfer(canonical([1,-1],[0,-1]),Q(1,2),0,1,1)['RH_sufficient_if_uniform'])
        self.assertEqual(transfer(canonical([1,-1],[1,0]),Q(1,2),0,1,1)['analytic_status'],'ruled_out_by_uncompensated_fractional_pole_at_one')

    def test_fractional_denominators_have_no_semantic_ceiling(self):
        p=canonical([1,-1]);a=order(p,1013,1)
        self.assertEqual(a,Q(1,1013))
        v=power(flint.arb(2).log(),a)
        self.assertTrue(v.is_finite() and v>0)
        self.assertTrue(power(flint.arb(0),Q(1,6))==0)

    def test_native_complex_intervals_round_trip_with_separate_components(self):
        z=flint.acb(flint.arb('1 +/- 0.01'),flint.arb('-2 +/- 0.02'))
        row=complex_ball(z);decoded=flint.acb(flint.arb(row['real']),flint.arb(row['imag']))
        self.assertTrue(decoded.contains(z))


if __name__=='__main__':unittest.main()
