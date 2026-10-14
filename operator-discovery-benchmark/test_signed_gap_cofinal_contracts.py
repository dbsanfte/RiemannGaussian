"""Exact cofinal plateaus, unknown constants and distinct signed margins."""
import unittest
from fractions import Fraction as Q
from signed_gap_cofinal_audit import bounded_constant,plateau_threshold,endpoint
from check_signed_gap_cofinal import entry
from signed_gap_profile_grammar import epsilon,ceil_power


def program(s=None,law=None,C='1/100'):
    return {'arithmetic_model':'inverse_one','exponent_schedule':s or {'kind':'power','power':'1/6'},'constant_law':law or {'kind':'constant'},'log_power':'0','fitted_coefficient':C}


class Contracts(unittest.TestCase):
    def test_exact_plateau_for_square_cube_sixth_root_parameter_schedules(self):
        for a in ['1/2','1/3','1/6','2']:
            s={'kind':'power','power':a};q=plateau_threshold(s,8192);self.assertEqual(ceil_power(8192,epsilon(s,q)),2);self.assertEqual(ceil_power(8192,epsilon(s,2*q)),2)

    def test_exponential_and_factorial_plateau_thresholds(self):
        for s in [{'kind':'exponential','power':'1/2'},{'kind':'factorial'}]:q=plateau_threshold(s,1024);self.assertEqual(ceil_power(1024,epsilon(s,q)),2)

    def test_zero_or_noncofinal_scale_excluded(self):
        self.assertIsNone(plateau_threshold({'kind':'fixed','epsilon':'1/6'},8192));self.assertIsNone(plateau_threshold({'kind':'power','power':'1'},1))

    def test_unknown_or_growing_constant_not_inferred_from_finite_values(self):
        for law in [{'kind':'free_per_level'},{'kind':'power','power':'1/6'},{'kind':'factorial'}]:self.assertIsNone(bounded_constant(program(law=law)))

    def test_power_zero_has_bounded_endpoint_with_correct_factor(self):
        self.assertEqual(bounded_constant(program(law={'kind':'power','power':'0'},C='1/3')),Q(2,3))

    def test_half_gap_failure_does_not_imply_other_failures(self):
        p=program(C='1');row={'X':4,'signed_defect':12,'squarefree_count_through_4X':2};v=endpoint(p,row);self.assertEqual(v,entry(p,row));self.assertLess(Q(v['half_gap_margin']),0);self.assertGreater(Q(v['nullspace_PSD_margin']),0);self.assertGreater(Q(v['fully_charged_bound_margin']),0)


if __name__=='__main__':unittest.main()
